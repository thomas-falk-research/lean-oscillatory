#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Differential test of two independent checkers on a shared corpus of certificates
(docs/contract/certificate-v0.md, section 6).
Usage: python3 tests/differential.py PYTHON_PKG_DIR RUST_BINARY STATEMENTS OUTDIR
  e.g. from python/:  python3 tests/differential.py . ../rust/oscint-cert/target/release/oscint-cert ../stamps/statements.json /tmp/corpus
Certificates are produced by the reference `make` and then mutated; each is checked by both implementations
through their command lines. Compared: the status, the exit code, the set of verdict keys, `certificate_sha256`,
`statements_sha256` and `statements_pinned`; then the command-line behaviour that gives no verdict (exit code 3 with
an empty standard output). Fixed seed; the first 1429 certificates are those of the runs of revision 2."""
import copy, json, os, random, subprocess, sys
from fractions import Fraction as F

pkg, rust, statements, out = sys.argv[1:5]
sys.path.insert(0, pkg)
from oscint_cert import cert as C
from oscint_cert import rational as R

ST, SHA = C.load_statements(statements)
rng = random.Random(20261116)
os.makedirs(out, exist_ok=True)
corpus = []  # (category, raw text)


def add(cat, obj=None, raw=None):
    """raw may be text or bytes."""
    corpus.append((cat, raw if raw is not None else json.dumps(obj)))


def rq(lo, hi, den):
    return R.fmt(F(rng.randint(int(lo * den), int(hi * den)), den))


def rand_inputs(kind):
    if kind == "bessel-j":
        return {"n": rng.randint(-40, 40), "x": rq(-60, 60, rng.choice([1, 10, 1000]))}
    if kind == "lattice-population":
        return {"n": rng.randint(-30, 30), "t": rq(-20, 20, rng.choice([1, 4, 100]))}
    if kind == "lattice-envelope":
        t = rq(-50, 50, rng.choice([1, 4, 100]))
        return {"d": rng.randint(0, 6), "t": t if F(t) != 0 else "1/7"}
    while True:
        terms = [{"amp": rq(-3, 3, 4), "freq": rng.randint(1, 4), "fn": rng.choice(["cos", "sin"])}
                 for _ in range(rng.randint(1, 3))]
        a = F(rng.randint(-30, 20), 10)
        inp = {"phase": terms, "order": rng.randint(2, 4), "a": R.fmt(a), "b": R.fmt(a + F(rng.randint(0, 10), 10)),
               "mu": rq(F(1, 100), 2, 100), "t": rq(F(1, 10), 200, 10)}
        if F(inp["mu"]) > 0:
            return inp


valid = []
for kind in C.KINDS:
    n = 0
    while n < 40:
        inp = rand_inputs(kind)
        try:
            c = C.make(kind, inp, ST, rng.choice([12, 20, 35]))
        except (C.CertError, R.Unresolved):
            if kind == "vdc-hypothesis":
                # keep the failing/unresolved hypothesis as a case: claim a plausible bound anyway
                c = {"format": C.CERT_FORMAT, "kind": kind,
                     "statement": {"label": "S1.k", "name": ST["S1.k"]["name"], "commitment": ST["S1.k"]["commitment"]},
                     "inputs": inp, "claim": {"holds": True, "bound": {"lo": "0", "hi": "1000000"}},
                     "assumptions": ["amplitude-one"], "producer": "corpus"}
                add("vdc-hypothesis-not-established", c)
            continue
        valid.append(c)
        add("valid", c)
        n += 1


def box(c):
    return c["claim"]["bound"] if c["kind"] == "vdc-hypothesis" else c["claim"]


for c in valid[::4]:
    lo, hi = F(box(c)["lo"]), F(box(c)["hi"])
    w = max(hi - lo, F(1, 10**30))
    m = copy.deepcopy(c); box(m)["lo"], box(m)["hi"] = R.fmt(lo + 7 * w), R.fmt(hi + 7 * w); add("claim-shifted", m)
    m = copy.deepcopy(c); box(m)["lo"], box(m)["hi"] = R.fmt(lo - w), R.fmt(hi + w); add("claim-widened", m)
    m = copy.deepcopy(c); box(m)["lo"], box(m)["hi"] = R.fmt(hi), R.fmt(lo) ; add("claim-reversed", m) if hi != lo else None
    m = copy.deepcopy(c); box(m)["hi"] = R.fmt(lo + w / 3); add("claim-cut", m)
    m = copy.deepcopy(c); m["producer"] = "someone else"; add("producer-changed", m)
    m = copy.deepcopy(c); m["extra"] = 1; add("extra-key", m)
    m = copy.deepcopy(c); del m["producer"]; add("missing-key", m)
    m = copy.deepcopy(c); m["assumptions"] = list(reversed(m["assumptions"])) + ["x"]; add("assumptions-altered", m)
    m = copy.deepcopy(c); m["format"] = "oscint-certificate/0.2"; add("wrong-format", m)
    if c["statement"]:
        m = copy.deepcopy(c); m["statement"]["commitment"] = "0" * 64; add("wrong-commitment", m)
        m = copy.deepcopy(c); m["statement"]["label"] = "S1.1"; add("wrong-label", m)
    else:
        m = copy.deepcopy(c); m["statement"] = {"label": "LS-D", "name": "n", "commitment": "c"}; add("statement-on-none", m)
    for bad in [1.5, "1e3", "nan", None, True, "+1", " 1", "1/-2", ".5", "5.", "1_0", "01", "-0", "2/4"]:
        m = copy.deepcopy(c); box(m)["lo"] = bad; add(f"claim-lo-{bad!r}", m)
    k0 = sorted(c["inputs"])[-1]
    for bad in [1.5, "1e3", None, True, "x"]:
        m = copy.deepcopy(c); m["inputs"][k0] = bad; add(f"input-{k0}-{bad!r}", m)

# range and hypothesis-of-statement cases
S = lambda lab: {"label": lab, "name": ST[lab]["name"], "commitment": ST[lab]["commitment"]}
wide = {"lo": "-1000000", "hi": "1000000"}
add("bessel-x-401", {"format": C.CERT_FORMAT, "kind": "bessel-j", "statement": None, "inputs": {"n": 0, "x": "401"}, "claim": wide, "assumptions": [], "producer": "c"})
add("bessel-n-huge", {"format": C.CERT_FORMAT, "kind": "bessel-j", "statement": None, "inputs": {"n": 20000, "x": "1"}, "claim": wide, "assumptions": [], "producer": "c"})
add("bessel-n-float", {"format": C.CERT_FORMAT, "kind": "bessel-j", "statement": None, "inputs": {"n": 1.0, "x": "1"}, "claim": wide, "assumptions": [], "producer": "c"})
add("bessel-point-claim-exact", {"format": C.CERT_FORMAT, "kind": "bessel-j", "statement": None, "inputs": {"n": 0, "x": "0"}, "claim": {"lo": "1", "hi": "1"}, "assumptions": [], "producer": "c"})
add("population-t0", {"format": C.CERT_FORMAT, "kind": "lattice-population", "statement": S("LS-K"), "inputs": {"n": 0, "t": "0"}, "claim": {"lo": "1", "hi": "1"}, "assumptions": ["bessel-identification", "single-site-datum"], "producer": "c"})
add("population-t-201", {"format": C.CERT_FORMAT, "kind": "lattice-population", "statement": S("LS-K"), "inputs": {"n": 0, "t": "201"}, "claim": wide, "assumptions": ["bessel-identification", "single-site-datum"], "producer": "c"})
for d, t, cat in [(1, "0", "envelope-t0"), (-1, "1", "envelope-d-neg"), (65, "1", "envelope-d-65"), (0, "5", "envelope-d0"), (1, "1/1000", "envelope-saturated")]:
    add(cat, {"format": C.CERT_FORMAT, "kind": "lattice-envelope", "statement": S("LS-D"), "inputs": {"d": d, "t": t}, "claim": {"lo": "1", "hi": "1"} if cat in ("envelope-d0", "envelope-saturated") else wide, "assumptions": ["unit-l1-datum"], "producer": "c"})
base = {"phase": [{"amp": "1", "freq": 1, "fn": "cos"}], "order": 2, "a": "-1/2", "b": "1/2", "mu": "4/5", "t": "100"}
for cat, ch in [("vdc-mu-too-big", {"mu": "9/10"}), ("vdc-order-1", {"order": 1}), ("vdc-order-17", {"order": 17}), ("vdc-a-gt-b", {"a": "1"}),
                ("vdc-mu-0", {"mu": "0"}), ("vdc-t-0", {"t": "0"}), ("vdc-b-100", {"b": "100"}), ("vdc-empty-phase", {"phase": []}),
                ("vdc-freq-0", {"phase": [{"amp": "1", "freq": 0, "fn": "cos"}]}), ("vdc-freq-1001", {"phase": [{"amp": "1", "freq": 1001, "fn": "cos"}], "a": "0", "b": "1/100"}),
                ("vdc-a-eq-b", {"a": "0", "b": "0"}), ("vdc-third-derivative-zero", {"order": 3, "mu": "1/1000"}),
                ("vdc-near-threshold-below", {"mu": "0.877582561890"}), ("vdc-near-threshold-above", {"mu": "0.877582561891"})]:
    inp = dict(base); inp.update(ch)
    add(cat, {"format": C.CERT_FORMAT, "kind": "vdc-hypothesis", "statement": S("S1.k"), "inputs": inp, "claim": {"holds": True, "bound": {"lo": "0", "hi": "1000000"}}, "assumptions": ["amplitude-one"], "producer": "c"})
good = json.dumps(valid[0])
add("raw-duplicate-key", raw=good[:-1] + ', "kind": "bessel-j"}')
add("raw-not-json", raw="{not json")
add("raw-empty", raw="")
add("raw-array", raw="[" + good + "]")
add("raw-nan-token", raw=good.replace('"producer"', '"z": NaN, "producer"', 1))
add("raw-bom", raw="﻿" + good)



# cases added for revision 3 (after the first 1429, whose order is unchanged)
def cert(kind, inputs, claim):
    label, asm = C.KINDS[kind]
    return {"format": C.CERT_FORMAT, "kind": kind, "statement": None if label is None else S(label), "inputs": inputs,
            "claim": claim, "assumptions": asm, "producer": "c"}


vb = {"holds": True, "bound": {"lo": "0", "hi": "1000000"}}
add("raw-null", raw="null")
add("raw-number", raw="3")
add("raw-string", raw='"x"')
add("raw-not-utf8", raw=b"\xff\xfe\x00")
add("raw-latin1-in-producer", raw=good.encode().replace(b'"producer": "', b'"producer": "\xe9'))
for n in (100, 101):
    x = "1." + "0" * (n - 2)
    add(f"numeral-x-{n}-chars", cert("bessel-j", {"n": 0, "x": x}, wide))
    add(f"numeral-t-{n}-chars", cert("lattice-population", {"n": 1, "t": x}, {"lo": "0", "hi": "1"}))
    add(f"numeral-envelope-t-{n}-chars", cert("lattice-envelope", {"d": 1, "t": x}, {"lo": "0", "hi": "1"}))
    for key in ("a", "b", "mu", "t"):
        inp = dict(base); inp[key] = {"a": "-0." + "5" + "0" * (n - 4), "b": "0.5" + "0" * (n - 3),
                                      "mu": "0.8" + "0" * (n - 3), "t": "100." + "0" * (n - 4)}[key]
        assert len(inp[key]) == n
        add(f"numeral-vdc-{key}-{n}-chars", cert("vdc-hypothesis", inp, vb))
for n in (101, 4000, 4001):
    inp = dict(base); inp["phase"] = [{"amp": "1." + "0" * (n - 2), "freq": 1, "fn": "cos"}]
    add(f"numeral-amp-{n}-chars", cert("vdc-hypothesis", inp, vb))
tiny = "1/" + "9" * 98
add("tiny-mu-claim-false", cert("vdc-hypothesis", dict(base, mu=tiny, t="1"), {"holds": True, "bound": {"lo": "0", "hi": "1"}}))
add("tiny-mu-claim-true", cert("vdc-hypothesis", dict(base, mu=tiny, t="1"), {"holds": True, "bound": {"lo": "0", "hi": "1" + "0" * 51}}))
add("tiny-t-envelope-is-one", cert("lattice-envelope", {"d": 64, "t": "1/1" + "0" * 97}, {"lo": "1", "hi": "1"}))
add("tiny-t-envelope-false", cert("lattice-envelope", {"d": 64, "t": "1/1" + "0" * 97}, {"lo": "0", "hi": "1/2"}))
add("huge-t-envelope", cert("lattice-envelope", {"d": 3, "t": "9" * 99}, {"lo": "0", "hi": "1/1" + "0" * 90}))
add("fail-on-long-interval", cert("vdc-hypothesis", dict(base, a="0", b="20", mu="1/2"), vb))
add("fail-on-long-interval-2", cert("vdc-hypothesis", dict(base, a="-64", b="64", mu="1/2"), vb))
many = [{"amp": "1", "freq": (j % 7) + 1, "fn": "cos"} for j in range(64)]
add("phase-64-terms", cert("vdc-hypothesis", dict(base, phase=many, a="0", b="9", mu="1/1000"), vb))
add("phase-65-terms", cert("vdc-hypothesis", dict(base, phase=many + many[:1]), vb))
add("bessel-large-order", cert("bessel-j", {"n": 10000, "x": "400"}, {"lo": "-1/1" + "0" * 30, "hi": "1/1" + "0" * 30}))
add("bessel-order-10001", cert("bessel-j", {"n": 10001, "x": "1"}, wide))
add("bessel-x-400", cert("bessel-j", {"n": 0, "x": "-400"}, {"lo": "-1", "hi": "1"}))

import hashlib

KEYS = {"format", "status", "kind", "reasons", "checker", "statements_sha256", "statement", "numeric_rung", "assumptions",
        "recomputed", "hypothesis", "certificate_sha256", "statements_pinned"}
CMD = {"python": [sys.executable, "-m", "oscint_cert"], "rust": [rust]}


def run(who, args):
    r = subprocess.run(CMD[who] + args, cwd=pkg if who == "python" else None, capture_output=True)
    try:
        v = json.loads(r.stdout.decode("utf-8"))
        return v["status"], r.returncode, v, r.stdout
    except Exception:
        return f"EXIT{r.returncode}", r.returncode, None, r.stdout


EXIT = {"CERTIFIED": 0, "REJECTED": 1, "UNRESOLVED": 2}
rows, table, defects = [], {}, []
for i, (cat, raw) in enumerate(corpus):
    path = os.path.join(out, f"c{i:04d}.json")
    data = raw if isinstance(raw, bytes) else raw.encode("utf-8")
    open(path, "wb").write(data)
    h = hashlib.sha256(data).hexdigest()
    res = {}
    for who in ("python", "rust"):
        st, rc, v, _ = run(who, ["check", path, "--statements", statements])
        res[who] = st
        if v is None or rc != EXIT.get(st) or set(v) != KEYS or v["certificate_sha256"] != h \
                or v["statements_sha256"] != SHA or v["statements_pinned"] is not False:
            defects.append((i, cat, who, st, rc, sorted(set(v) ^ KEYS) if v else None))
    a, b = res["python"], res["rust"]
    table[(a, b)] = table.get((a, b), 0) + 1
    rows.append((i, cat, a, b))
print(f"corpus: {len(corpus)} certificates")
for (a, b), n in sorted(table.items()):
    print(f"  python {a:11s} rust {b:11s}: {n}")
dis = [r for r in rows if r[2] != r[3]]
print(f"disagreements: {len(dis)}")
cats = {}
for i, cat, a, b in dis:
    key = (cat.split("-'")[0] if cat.startswith(("claim-lo", "input-")) else cat, a, b)
    cats.setdefault(key, []).append(i)
for (cat, a, b), ids in sorted(cats.items()):
    print(f"  {cat}: python {a}, rust {b}: {len(ids)} (e.g. c{ids[0]:04d})")
unsafe = [r for r in rows if "CERTIFIED" in (r[2], r[3]) and r[2] != r[3]]
print(f"disagreements in which exactly one side says CERTIFIED: {len(unsafe)}")
for i, cat, a, b in unsafe[:20]:
    print(f"    c{i:04d} {cat}: python {a}, rust {b}")
print(f"verdict-shape defects (exit code, key set, certificate hash, list hash, pin flag): {len(defects)}")
for d in defects[:20]:
    print(f"    c{d[0]:04d} {d[1]}: {d[2]} status {d[3]} exit {d[4]} key difference {d[5]}")
print("revision-3 cases:")
for i, cat, a, b in rows[1429:]:
    print(f"    c{i:04d} {cat}: python {a}, rust {b}")

# command-line behaviour: the pin option and unusable statement lists
gp = os.path.join(out, "good.json")
open(gp, "w").write(good)
entry = '{"label": "LS-D", "name": "n", "commitment": "c", "proved_by": "trust me"}'
lists = {"bare-array": "[]", "empty-object": "{}", "no-statements-key": '{"format": "oscint-statements 1"}',
         "wrong-format": '{"format": "oscint-statements 2", "statements": []}',
         "duplicate-label": '{"format": "oscint-statements 1", "statements": [%s, %s]}' % (entry, entry),
         "entry-without-commitment": '{"format": "oscint-statements 1", "statements": [{"label": "LS-D", "name": "n"}]}',
         "entry-with-empty-name": '{"format": "oscint-statements 1", "statements": [{"label": "LS-D", "name": "", "commitment": "c"}]}',
         "not-json": "not json", "duplicate-key": '{"format": "oscint-statements 1", "format": "oscint-statements 1", "statements": []}'}
cli = []
for name, text in lists.items():
    lp = os.path.join(out, f"list-{name}.json")
    open(lp, "w").write(text)
    cli.append((f"statement list: {name}", ["check", gp, "--statements", lp], 3, None))
lp = os.path.join(out, "list-not-utf8.json")
open(lp, "wb").write(b"\xff\xfe")
cli.append(("statement list: not UTF-8", ["check", gp, "--statements", lp], 3, None))
cli += [("pin: match", ["check", gp, "--statements", statements, "--expect-statements-sha256", SHA], 0, True),
        ("pin: match, upper case", ["check", gp, "--statements", statements, "--expect-statements-sha256", SHA.upper()], 0, True),
        ("pin: mismatch", ["check", gp, "--statements", statements, "--expect-statements-sha256", "0" * 64], 3, None),
        ("no subcommand", [], 3, None), ("check without --statements", ["check", gp], 3, None),
        ("missing certificate file", ["check", os.path.join(out, "nonexistent.json"), "--statements", statements], 3, None),
        ("missing statement list", ["check", gp, "--statements", os.path.join(out, "nonexistent.json")], 3, None),
        ("make: unknown kind", ["make", "no-such-kind", "--inputs", "{}", "--statements", statements], 3, None),
        ("make: hypothesis fails", ["make", "vdc-hypothesis", "--inputs", json.dumps(dict(base, mu="9/10")), "--statements", statements], 3, None),
        ("make: hypothesis undecided", ["make", "vdc-hypothesis", "--inputs", json.dumps(dict(base, b="100")), "--statements", statements], 3, None),
        ("make: beyond the range", ["make", "bessel-j", "--inputs", '{"n": 0, "x": "401"}', "--statements", statements], 3, None),
        ("make: outside the statement", ["make", "lattice-envelope", "--inputs", '{"d": 1, "t": "0"}', "--statements", statements], 3, None)]
bad = 0
print(f"command-line cases: {len(cli)}")
for name, args, want_rc, want_pin in cli:
    got = {}
    for who in ("python", "rust"):
        st, rc, v, stdout = run(who, args)
        ok = rc == want_rc and ((want_rc == 3 and stdout == b"") or (want_rc != 3 and v is not None and v["statements_pinned"] is want_pin))
        got[who] = "ok" if ok else f"NOT AS SPECIFIED (exit {rc}, {len(stdout)} bytes on standard output)"
        bad += not ok
    print(f"    {name}: expected exit {want_rc}; python {got['python']}; rust {got['rust']}")
print(f"command-line cases not as specified: {bad}")
# make on one side, check on the other
cross = 0
for kind, inp in [("lattice-envelope", {"d": 2, "t": "7/2"}), ("lattice-population", {"n": 3, "t": "1.16"}), ("bessel-j", {"n": -5, "x": "12.5"}), ("vdc-hypothesis", base)]:
    for maker, checker in (("python", "rust"), ("rust", "python")):
        _, rc, c, stdout = run(maker, ["make", kind, "--inputs", json.dumps(inp), "--statements", statements])
        cp = os.path.join(out, f"cross-{maker}-{kind}.json")
        open(cp, "wb").write(stdout)
        st, rc2, v, _ = run(checker, ["check", cp, "--statements", statements])
        cross += st != "CERTIFIED"
        print(f"    made by {maker}, checked by {checker}, {kind}: {st}")
print(f"cross make/check not CERTIFIED: {cross}")
json.dump(rows, open(os.path.join(out, "results.json"), "w"))
