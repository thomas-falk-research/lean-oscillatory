#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Validator, commitment and draw for the CENSUS held-out pool (docs/prereg/2026-11-09-CENSUS-spec.md, section 3).

Committed before the pool exists, so that the selector cannot fit the checks to the pool. The pool file itself is never
committed: it stays with the owner until the reveal.

The sealed file is a JSON object {"pool": [...], "examined": [...]}:
  pool      entries {id, domain, source, parameters, G, u, domain_type}, sorted by id, ids unique;
  examined  entries {source, outcome}, one per examined source in the order examined; outcome is the pool id the source
            contributed, or the rule of spec section 3 that excluded it.
Every value is a string of printable ASCII, so JCS (RFC 8785) of the file is the compact sorted-key JSON that
json.dumps(separators=(",", ":"), sort_keys=True) writes; this script refuses anything else.

Usage (run from the repository root with python3 -I; the files stay outside the tree):
  validate_pool.py check  SEALED.json                 validate; prints one line per problem, exit 1 if any
  validate_pool.py commit SEALED.json SALT_HEX        validate, then print SHA-256(salt || JCS(file)) as hex
  validate_pool.py draw   SEALED.json RANDOMNESS_HEX  validate, then print every entry's original rank and H
  validate_pool.py selftest                           planted defects must each be reported; prints SELFTEST PASS

The draw takes the round's randomness as hex (64 hex digits). Verifying the round's BLS signature against the chain's
public key is done separately at the reveal with drand's own client; this script does not do it.
"""
import hashlib
import json
import re
import sys

import mpmath
import sympy as sp

DOMAINS = {"L", "T", "W", "N", "P"}
INTERVALS = {  # open interval J of each outer function G (spec section 1)
    "id": (None, None), "sqrt": (0, None), "arccos": (-1, 1), "arcsin": (-1, 1), "2arcsin_sqrt": (0, 1)}
POOL_KEYS = {"id", "domain", "source", "parameters", "G", "u", "domain_type"}
VARS = {"torus": ("c1", "s1", "c2", "s2"), "box": ("x", "y")}
TOKEN = re.compile(r"\s*(?:(\d+)|([a-z][a-z0-9]*)|(.))")


def parse_poly(text, names):
    """Parse u in the corpus grammar: integers, a/b, + - * ^ and parentheses, in the given variables. No eval."""
    syms = {n: sp.Symbol(n, real=True) for n in names}
    toks, pos = [], 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if m.group(0).strip() == "":
            break
        num, name, op = m.groups()
        if num is not None:
            toks.append(("num", int(num)))
        elif name is not None:
            if name not in syms:
                raise ValueError(f"unknown name {name!r}")
            toks.append(("var", syms[name]))
        elif op in "+-*/^()":
            toks.append(("op", op))
        else:
            raise ValueError(f"bad character {op!r}")
        pos = m.end()
    toks.append(("end", None))
    i = 0

    def peek():
        return toks[i]

    def take(kind, val=None):
        nonlocal i
        t = toks[i]
        if t[0] != kind or (val is not None and t[1] != val):
            raise ValueError(f"expected {val or kind}, got {t[1]!r}")
        i += 1
        return t[1]

    def expr():
        v = term()
        while peek() in (("op", "+"), ("op", "-")):
            v = v + term() if take("op") == "+" else v - term()
        return v

    def term():
        v = unary()
        while peek() in (("op", "*"), ("op", "/")):
            if take("op") == "*":
                v = v * unary()
            else:
                d = unary()
                if not (d.is_Rational and d != 0):
                    raise ValueError("division only by a nonzero rational constant")
                v = v / d
        return v

    def unary():
        if peek() == ("op", "-"):
            take("op")
            return -unary()
        if peek() == ("op", "+"):
            take("op")
            return unary()
        return power()

    def power():
        b = atom()
        if peek() == ("op", "^"):
            take("op")
            e = take("num")
            return b**e
        return b

    def atom():
        t = peek()
        if t[0] == "num":
            return sp.Integer(take("num"))
        if t[0] == "var":
            return take("var")
        take("op", "(")
        v = expr()
        take("op", ")")
        return v

    v = expr()
    take("end")
    return sp.expand(v), syms


def printable_ascii(x):
    return isinstance(x, str) and all(32 <= ord(ch) < 127 for ch in x)


def validate(doc):
    probs = []
    if not isinstance(doc, dict) or set(doc) != {"pool", "examined"}:
        return ["top level must be an object with exactly the keys pool and examined"]
    pool, examined = doc["pool"], doc["examined"]
    if not isinstance(pool, list) or not isinstance(examined, list):
        return ["pool and examined must be lists"]
    ids = [e.get("id") if isinstance(e, dict) else None for e in pool]
    if ids != sorted(ids, key=str) or len(set(ids)) != len(ids):
        probs.append("pool must be sorted by id, ids unique")
    for e in examined:
        if not isinstance(e, dict) or set(e) != {"source", "outcome"} or not all(map(printable_ascii, e.values())):
            probs.append(f"examined entry {e!r}: keys source, outcome; printable ASCII strings")
    if len(examined) > 60:
        probs.append(f"{len(examined)} examined sources; the rule stops at 60")
    per_domain = {}
    for e in pool:
        tag = e.get("id") if isinstance(e, dict) else e
        if not isinstance(e, dict) or set(e) != POOL_KEYS:
            probs.append(f"{tag}: keys must be exactly {sorted(POOL_KEYS)}")
            continue
        if not all(map(printable_ascii, e.values())):
            probs.append(f"{tag}: every value must be a string of printable ASCII")
            continue
        if e["domain"] not in DOMAINS:
            probs.append(f"{tag}: domain {e['domain']!r} not in {sorted(DOMAINS)}")
        per_domain[e["domain"]] = per_domain.get(e["domain"], 0) + 1
        if e["G"] not in INTERVALS:
            probs.append(f"{tag}: G {e['G']!r} not in {sorted(INTERVALS)}")
            continue
        if e["domain_type"] not in VARS:
            probs.append(f"{tag}: domain_type must be torus or box")
            continue
        try:
            u, syms = parse_poly(e["u"], VARS[e["domain_type"]])
        except ValueError as err:
            probs.append(f"{tag}: u does not parse: {err}")
            continue
        if e["domain_type"] == "torus":
            c1, s1, c2, s2 = (syms[n] for n in VARS["torus"])
            red = sp.reduced(u, [s1**2 + c1**2 - 1, s2**2 + c2**2 - 1], s1, s2, c1, c2)[1]
            if sp.Poly(red, s1, s2, c1, c2).is_ground:
                probs.append(f"{tag}: u is constant on the torus (FLAT)")
                continue
            f = sp.lambdify([c1, s1, c2, s2], u, "mpmath")
            pts = [f(mpmath.cos(a), mpmath.sin(a), mpmath.cos(b), mpmath.sin(b))
                   for a in (mpmath.mpf(j) * 2 * mpmath.pi / 37 for j in range(37))
                   for b in (mpmath.mpf(j) * 2 * mpmath.pi / 41 for j in range(41))]
        else:
            x, y = syms["x"], syms["y"]
            if sp.Poly(u, x, y).is_ground:
                probs.append(f"{tag}: u is constant (FLAT)")
                continue
            f = sp.lambdify([x, y], u, "mpmath")
            pts = [f(mpmath.mpf(2 * i) / 36 - 1, mpmath.mpf(2 * j) / 40 - 1) for i in range(37) for j in range(41)]
        lo, hi = INTERVALS[e["G"]]
        if not any((lo is None or p > lo) and (hi is None or p < hi) for p in pts):
            probs.append(f"{tag}: u never lies in J of {e['G']} at the 1517 sample points (phase undefined)")
    if any(n > 3 for n in per_domain.values()):
        probs.append(f"more than three models in a domain: {per_domain}")
    if len(pool) < 12 or len(per_domain) < 4:
        probs.append(f"pool has {len(pool)} models in {len(per_domain)} domains; the rule needs >= 12 in >= 4 "
                     "(otherwise the held-out step is abandoned, spec section 3)")
    return probs


def jcs(doc):
    return json.dumps(doc, separators=(",", ":"), sort_keys=True, ensure_ascii=True).encode("ascii")


def draw(pool, randomness_hex):
    """Spec section 3, draw procedure: original ranks, first 5, then the domain-coverage replacement."""
    r = bytes.fromhex(randomness_hex)
    if len(r) != 32:
        raise ValueError("randomness must be 32 bytes (64 hex digits)")
    keyed = sorted(pool, key=lambda e: (hashlib.sha256(r + b"\x00" + e["id"].encode("utf-8")).digest(), e["id"]))
    rank = {e["id"]: n + 1 for n, e in enumerate(keyed)}
    h = keyed[:5]
    while len({e["domain"] for e in h}) < 3:
        counts = {}
        for e in h:
            counts[e["domain"]] = counts.get(e["domain"], 0) + 1
        out = max((e for e in h if counts[e["domain"]] >= 2), key=lambda e: rank[e["id"]])
        have = {e["domain"] for e in h}
        cand = [e for e in keyed if e["domain"] not in have and e not in h]
        if not cand:
            break
        h = [e for e in h if e is not out] + [cand[0]]
    return rank, h


def selftest():
    """Synthetic entries only (not a pool): each planted defect must be reported, the clean file accepted."""
    def entry(i, dom, u="c1 + 1/2*c2", G="id"):
        return {"id": f"X{i:02d}", "domain": dom, "source": f"test:{i}", "parameters": "none", "G": G, "u": u,
                "domain_type": "torus"}
    clean = {"pool": [entry(i, "LTWNP"[i % 5]) for i in range(12)], "examined": [{"source": "test:0", "outcome": "X00"}]}
    ok = []
    ok.append(("clean file accepted", validate(clean) == []))

    def planted(name, mutate, needle):
        doc = json.loads(json.dumps(clean))
        mutate(doc)
        ok.append((name, any(needle in p for p in validate(doc))))
    planted("unsorted ids", lambda d: d["pool"].reverse(), "sorted")
    planted("unknown variable", lambda d: d["pool"][0].update(u="c1 + z"), "does not parse")
    planted("eval attempt", lambda d: d["pool"][0].update(u="__import__('os')"), "does not parse")
    planted("constant on the torus", lambda d: d["pool"][0].update(u="s1^2 + c1^2"), "constant")
    planted("never in J", lambda d: d["pool"][0].update(G="sqrt", u="-2 - c1"), "never lies in J")
    planted("non-string value", lambda d: d["pool"][0].update(parameters=1), "printable ASCII")
    planted("non-ASCII value", lambda d: d["pool"][0].update(source="café"), "printable ASCII")
    planted("bad domain", lambda d: d["pool"][0].update(domain="Q"), "domain")
    planted("four in a domain", lambda d: d["pool"][1].update(domain="L"), "more than three")
    planted("too small", lambda d: d.update(pool=d["pool"][:11]), "needs >= 12")
    planted("division by a variable", lambda d: d["pool"][0].update(u="1/c1"), "does not parse")
    # draw: with 10 L, 1 T, 1 W the first five cover fewer than three domains for most randomness values, so the
    # replacement step runs; check its rule on 64 randomness values (both branches occur)
    pool = [entry(i, "L" if i < 10 else ("T" if i == 10 else "W")) for i in range(12)]
    branches, good = set(), True
    for t in range(64):
        rank, h = draw(pool, hashlib.sha256(bytes([t])).hexdigest())
        first5 = sorted(pool, key=lambda e: rank[e["id"]])[:5]
        need = max(0, 3 - len({e["domain"] for e in first5}))
        branches.add(need)
        added = [e for e in h if e not in first5]
        removed = [e for e in first5 if e not in h]
        kept_l = sorted(rank[e["id"]] for e in h if e["domain"] == "L")
        good &= (len(h) == 5 and len({e["domain"] for e in h}) == 3 if need else h == first5)
        good &= len(added) == len(removed) == need
        # removed members are the largest-ranked L entries of the first five; added are the T and W entries
        good &= all(rank[e["id"]] > max(kept_l) for e in removed) and {e["domain"] for e in added} <= {"T", "W"}
    ok.append(("draw replacement rule on 64 randomness values", good and branches >= {1, 2}))
    ok.append(("jcs is compact sorted ASCII", jcs({"b": "1", "a": "x\"y"}) == b'{"a":"x\\\"y","b":"1"}'))
    for name, good in ok:
        print(f"SELFTEST {'PASS' if good else 'FAIL'}: {name}")
    print("SELFTEST PASS" if all(g for _, g in ok) else "SELFTEST FAIL")
    return 0 if all(g for _, g in ok) else 1


def main(argv):
    if len(argv) == 2 and argv[1] == "selftest":
        return selftest()
    if len(argv) < 3 or argv[1] not in ("check", "commit", "draw"):
        print(__doc__)
        return 2
    doc = json.load(open(argv[2], encoding="utf-8"))
    probs = validate(doc)
    for p in probs:
        print(f"PROBLEM {p}")
    if probs:
        return 1
    print(f"VALID {len(doc['pool'])} models, {len(doc['examined'])} examined sources")
    if argv[1] == "commit":
        salt = bytes.fromhex(argv[3])
        if len(salt) != 16:
            print("salt must be 16 bytes (32 hex digits)")
            return 2
        print(f"COMMITMENT {hashlib.sha256(salt + jcs(doc)).hexdigest()}")
    elif argv[1] == "draw":
        rank, h = draw(doc["pool"], argv[3])
        for e in sorted(doc["pool"], key=lambda e: rank[e["id"]]):
            print(f"RANK {rank[e['id']]} {e['id']} {e['domain']}")
        print("H " + " ".join(e["id"] for e in h))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
