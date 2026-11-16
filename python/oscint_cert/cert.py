# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Make and check certificates (contract: docs/contract/certificate-v0.md).

Trust boundary: `check` is the only function whose verdict may be CERTIFIED. It trusts nothing in the certificate: it
recomputes every number with exact rational arithmetic, looks the statement up in the statement list it is given, and
derives the list of assumptions itself. A producer, a wrapper or a display layer can never confer CERTIFIED.
"""
import copy
import hashlib
import json
from fractions import Fraction as F

from . import CERT_FORMAT, VERDICT_FORMAT, __version__, kernels, phase
from . import rational as R

PRODUCER = f"oscint-cert {__version__}"

# Assumptions are identified by key; their text lives here, never in a certificate.
ASSUMPTIONS = {
    "bessel-identification": "I(t, n) = 2 pi i^n J_n(t) for the lattice kernel (DLMF 10.9.2): proved on paper (L3), "
                             "validated numerically (L2), not machine-checked",
    "single-site-datum": "the initial datum is the unit vector at site 0 of the infinite lattice Z",
    "unit-l1-datum": "the bound is for a datum of l^1 norm 1 on the infinite lattice Z^d; a device is finite",
    "amplitude-one": "the bound is for the amplitude 1 on [a, b] (ampNorm = 1) and the phase t*omega(k) + xi*k, any xi",
}

# kind -> (statement label or None, assumption keys)
KINDS = {
    "bessel-j": (None, []),
    "lattice-population": ("LS-K", ["bessel-identification", "single-site-datum"]),
    "lattice-envelope": ("LS-D", ["unit-l1-datum"]),
    "vdc-hypothesis": ("S1.k", ["amplitude-one"]),
}
TOP_KEYS = {"format", "kind", "statement", "inputs", "claim", "assumptions", "producer"}


class CertError(ValueError):
    pass


def _no_duplicates(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            raise CertError(f"duplicate key {k!r}")
        d[k] = v
    return d


def _no_constants(name):
    raise CertError(f"{name} is not allowed")


def loads_strict(text):
    """JSON with duplicate keys, NaN and Infinity refused (contract section 3)."""
    return json.loads(text, object_pairs_hook=_no_duplicates, parse_constant=_no_constants)


def load_statements(path):
    """The statement list as {label: entry} and the SHA-256 of the file's bytes. Any defect is a CertError."""
    raw = open(path, "rb").read()
    try:
        data = loads_strict(raw.decode("utf-8"))
        if not isinstance(data, dict) or data.get("format") != "oscint-statements 1":
            raise CertError("unknown statement-list format")
        out = {}
        for s in data["statements"]:
            if not all(isinstance(s.get(k), str) and s.get(k) for k in ("label", "name", "commitment")):
                raise CertError("a statement entry lacks label, name or commitment")
            if s["label"] in out:
                raise CertError(f"duplicate statement label {s['label']!r}")
            out[s["label"]] = s
    except (ValueError, KeyError, TypeError, AttributeError) as e:
        if isinstance(e, CertError):
            raise
        raise CertError(f"unusable statement list: {e}") from None
    return out, hashlib.sha256(raw).hexdigest()


BIG = 10**300  # integers beyond this are refused as malformed


def _int(v, name, lo, hi, soft_hi=None):
    """A JSON integer. Below lo or above hi: malformed (REJECTED). Between soft_hi and hi: a valid input beyond the
    checker's supported range (UNRESOLVED)."""
    if isinstance(v, bool) or not isinstance(v, int) or not lo <= v <= hi:
        lo_txt = "" if lo == -BIG else f", at least {lo}"
        raise CertError(f"{name}: a JSON integer is required{lo_txt}, of at most 300 digits")
    if soft_hi is not None and abs(v) > soft_hi:
        raise R.Unresolved(f"{name}: beyond the supported range (|{name}| <= {soft_hi})")
    return v


def _rat(v, name, max_len=4000):
    if not isinstance(v, str):
        raise CertError(f"{name}: a string holding an exact rational is required")
    if len(v) > max_len:
        raise R.Unresolved(f"{name}: numeral longer than {max_len} characters (computation budget)")
    return R.parse_rational(v)


INPUT_LEN = 100  # input numerals longer than this are beyond the computation budget (UNRESOLVED)




def _enc(i, digits=80):
    """An enclosure for printing: rounded outward to multiples of 10^-digits, so its size is bounded."""
    r = R.round_out(i, digits)
    return {"lo": R.fmt(r[0]), "hi": R.fmt(r[1])}


def _dec(obj, name):
    if not isinstance(obj, dict) or set(obj) != {"lo", "hi"}:
        raise CertError(f"{name}: an object with exactly 'lo' and 'hi' is required")
    lo, hi = _rat(obj["lo"], name + ".lo"), _rat(obj["hi"], name + ".hi")
    if lo > hi:
        raise CertError(f"{name}: lo exceeds hi")
    return (lo, hi)


def _compute(kind, inputs, digits):
    """Recompute the certified quantity. Returns a dict of named results; raises R.Unresolved or CertError."""
    if not isinstance(inputs, dict):
        raise CertError("inputs: an object is required")
    try:
        if kind == "bessel-j":
            if set(inputs) != {"n", "x"}:
                raise CertError("bessel-j inputs: exactly n, x")
            return {"enclosure": kernels.bessel_j(_int(inputs["n"], "n", -BIG, BIG, kernels.MAX_ORDER),
                                                  _rat(inputs["x"], "x", INPUT_LEN), digits)}
        if kind == "lattice-population":
            if set(inputs) != {"n", "t"}:
                raise CertError("lattice-population inputs: exactly n, t")
            return {"enclosure": kernels.population(_int(inputs["n"], "n", -BIG, BIG, kernels.MAX_ORDER),
                                                    _rat(inputs["t"], "t", INPUT_LEN), digits)}
        if kind == "lattice-envelope":
            if set(inputs) != {"d", "t"}:
                raise CertError("lattice-envelope inputs: exactly d, t")
            t = _rat(inputs["t"], "t", INPUT_LEN)
            d = _int(inputs["d"], "d", 0, BIG, 64)
            if t == 0:
                raise CertError("lattice-envelope: t = 0 is excluded by the statement")
            return {"enclosure": kernels.ls_d_envelope(d, t, digits)}
        if kind == "vdc-hypothesis":
            if set(inputs) != {"phase", "order", "a", "b", "mu", "t"}:
                raise CertError("vdc-hypothesis inputs: exactly phase, order, a, b, mu, t")
            order = _int(inputs["order"], "order", 2, BIG, 16)
            a, b = _rat(inputs["a"], "a", INPUT_LEN), _rat(inputs["b"], "b", INPUT_LEN)
            mu, t = _rat(inputs["mu"], "mu", INPUT_LEN), _rat(inputs["t"], "t", INPUT_LEN)
            if not a <= b or mu <= 0 or t <= 0:
                raise CertError("vdc-hypothesis: need a <= b, mu > 0, t > 0")
            terms = phase.parse_phase(inputs["phase"])
            status, detail = phase.check_lower_bound(terms, order, a, b, mu, min(digits, 24))
            return {"hypothesis": status, "detail": detail, "enclosure": phase.vdc_bound(order, mu, t, digits)}
    except ValueError as e:
        if isinstance(e, CertError):
            raise
        raise CertError(str(e)) from None
    raise CertError(f"unknown kind {kind!r}")


def make(kind, inputs, statements, digits=30):
    """Produce a certificate. The producer is not trusted; `check` decides."""
    if kind not in KINDS:
        raise CertError(f"unknown kind {kind!r}")
    label, assumptions = KINDS[kind]
    res = _compute(kind, inputs, digits)
    claim = dict(_enc(res["enclosure"], digits))
    if kind == "vdc-hypothesis":
        if res["hypothesis"] != "PASS":
            raise CertError(f"hypothesis not established: {res['hypothesis']} {json.dumps(res['detail'])}")
        claim = {"holds": True, "bound": _enc(res["enclosure"], digits)}
    stmt = None
    if label is not None:
        s = statements[label]
        stmt = {"label": label, "name": s["name"], "commitment": s["commitment"]}
    return {"format": CERT_FORMAT, "kind": kind, "statement": stmt, "inputs": copy.deepcopy(inputs), "claim": claim,
            "assumptions": list(assumptions), "producer": PRODUCER}


def _verdict(status, cert, reasons, extra=None):
    kind = cert.get("kind") if isinstance(cert, dict) else None
    v = {"format": VERDICT_FORMAT, "status": status, "kind": kind if isinstance(kind, str) else None,
         "reasons": reasons, "checker": PRODUCER, "statements_sha256": None, "statement": None,
         "numeric_rung": None, "assumptions": None, "recomputed": None, "hypothesis": None,
         "certificate_sha256": None, "statements_pinned": False}
    v.update(extra or {})
    return v


def check(cert, statements, statements_sha256, digits=30):
    """The checker. Returns a verdict object whose status is CERTIFIED, REJECTED or UNRESOLVED."""
    if not isinstance(cert, dict):
        return _verdict("REJECTED", {}, ["certificate is not an object"], {"statements_sha256": statements_sha256})
    try:
        if set(cert) != TOP_KEYS:
            raise CertError(f"top-level keys must be exactly {sorted(TOP_KEYS)}")
        if cert["format"] != CERT_FORMAT:
            raise CertError(f"format must be {CERT_FORMAT!r}")
        if not isinstance(cert["producer"], str):
            raise CertError("producer must be a string")
        kind = cert["kind"]
        if not isinstance(kind, str) or kind not in KINDS:
            raise CertError(f"unknown kind {kind!r}")
        label, assumptions = KINDS[kind]
        if cert["assumptions"] != assumptions:
            raise CertError(f"assumptions must be exactly {assumptions}")
        extra = {"statements_sha256": statements_sha256, "numeric_rung": "L2 (exact rational arithmetic)",
                 "assumptions": [{"key": k, "text": ASSUMPTIONS[k]} for k in assumptions]}
        unproved = None
        if label is None:
            if cert["statement"] is not None:
                raise CertError("this kind carries no statement")
            extra["statement"] = None
        else:
            s = statements.get(label)
            st = cert["statement"]
            if s is None:
                raise CertError(f"statement {label} is not in the statement list")
            if not isinstance(st, dict) or set(st) != {"label", "name", "commitment"}:
                raise CertError("statement: exactly label, name, commitment")
            if not all(isinstance(st[k], str) for k in st) or \
                    (st["label"], st["name"], st["commitment"]) != (label, s["name"], s["commitment"]):
                raise CertError("statement label, name or commitment does not match the statement list")
            extra["statement"] = {"label": label, "name": s["name"], "commitment": s["commitment"],
                                  "proved_by": s.get("proved_by"), "rung": "L4 (machine-checked; fidelity "
                                  "reviewed by AI referees, not yet by a human expert)" if s.get("proved_by")
                                  else "stated, not proved"}
            if not (isinstance(s.get("proved_by"), str) and s.get("proved_by")):
                unproved = f"statement {label} has no machine-checked proof in this statement list"
        res = None
        last = None
        for dg in (digits, 2 * digits):
            try:
                res = _compute(kind, cert["inputs"], dg)
            except R.Unresolved as e:
                return _verdict("UNRESOLVED", cert, [str(e)], extra)
            except RecursionError:
                return _verdict("UNRESOLVED", cert, ["computation budget exceeded"], extra)
            if kind == "vdc-hypothesis":
                c = cert["claim"]
                if not isinstance(c, dict) or set(c) != {"holds", "bound"} or c["holds"] is not True:
                    raise CertError("vdc-hypothesis claim: exactly holds (true) and bound")
                claimed = _dec(c["bound"], "claim.bound")
                extra["hypothesis"] = {"status": res["hypothesis"], "detail": res["detail"]}
                if res["hypothesis"] == "FAIL":
                    return _verdict("REJECTED", cert, ["the hypothesis fails at an exhibited point"], extra)
                if res["hypothesis"] != "PASS":
                    why = res["detail"].get("reason", "no reason recorded")
                    return _verdict("UNRESOLVED", cert, [f"the hypothesis could not be decided: {why}"], extra)
            else:
                claimed = _dec(cert["claim"], "claim")
            extra["recomputed"] = _enc(res["enclosure"])
            if R.contains(claimed, res["enclosure"]):
                if unproved:
                    return _verdict("UNRESOLVED", cert, [unproved], extra)
                return _verdict("CERTIFIED", cert, [], extra)
            if R.disjoint(claimed, res["enclosure"]):
                return _verdict("REJECTED", cert, ["the claimed enclosure is disjoint from the recomputed one"], extra)
            last = "the claimed enclosure neither contains nor is disjoint from the recomputed one"
        # the claim cuts through the true value's enclosure at both precisions: it is too narrow to be confirmed
        return _verdict("UNRESOLVED", cert, [last], extra)
    except R.Unresolved as e:
        return _verdict("UNRESOLVED", cert, [str(e)], {"statements_sha256": statements_sha256})
    except (CertError, ValueError, KeyError, TypeError) as e:
        return _verdict("REJECTED", cert, [f"malformed certificate: {e}"], {"statements_sha256": statements_sha256})
