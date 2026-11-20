#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Second registered numeric test of the draft statement TSD-C (docs/prereg/2026-11-20-TSD-core-2.md).
Tooling, not evidence for a Lean theorem. It reuses the cases, families and formulas of tsd_core_checks.py
unchanged (the file is loaded and its SHA-256 is checked against the registered value) and differs in two things:
every disagreement between quadrature routes is printed by itself, and the route on the real line of case C9 is
computed in 40-digit arithmetic (mpmath), with Gauss-Legendre nodes and weights computed to that precision and a
longer truncation, because binary64 cannot resolve that route to the registered tolerance.
"""
import datetime
import hashlib
import importlib.util
import os
import sys

import mpmath as mp
import numpy as np

BASE_SHA = "c057a781a5dd1db0d09dd48159369c2569d8235d0de3e5299e1de41e6ea0201e"
HERE = os.path.dirname(os.path.abspath(__file__))
BASE_PATH = os.path.join(HERE, "tsd_core_checks.py")


def load_base():
    sha = hashlib.sha256(open(BASE_PATH, "rb").read()).hexdigest()
    if sha != BASE_SHA:
        sys.exit(f"tsd_core_checks.py has sha256 {sha}, not the registered {BASE_SHA}")
    spec = importlib.util.spec_from_file_location("tsd_core_checks", BASE_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def gl12_mp():
    """12-point Gauss-Legendre nodes and weights on [-1, 1] at the working precision (Newton on P_12)."""
    xs, ws = [], []
    for x0 in np.polynomial.legendre.leggauss(12)[0]:
        x = mp.mpf(float(x0))
        for _ in range(8):
            p, pm = mp.legendre(12, x), mp.legendre(11, x)
            dp = 12 * (pm - x * p) / (1 - x * x)
            x = x - p / dp
        p, pm = mp.legendre(12, x), mp.legendre(11, x)
        dp = 12 * (pm - x * p) / (1 - x * x)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws


def line_c9_mp(case, X, refine, xs, ws):
    """int_{-X}^{X} sech(kap v) e^{i t (sig^2 v - v^3/3)} dv in mpmath; the panels follow the registered rule."""
    kap, t, sig = mp.mpf(case.am.kap), mp.mpf(case.t), mp.mpf(case.ph.sig)
    hf = case.h(lambda p: p + 0j)
    edges = [-X]
    p = -X
    while p < X:
        p = min(X, p + hf(p) / refine)
        edges.append(p)
    total = mp.mpc(0)
    for lo, hi in zip(edges[:-1], edges[1:]):
        lo, hi = mp.mpf(lo), mp.mpf(hi)
        mid, half = (lo + hi) / 2, (hi - lo) / 2
        acc = mp.mpc(0)
        for x, w in zip(xs, ws):
            v = mid + half * x
            acc += w * mp.expj(t * (sig * sig * v - v ** 3 / 3)) / mp.cosh(kap * v)
        total += half * acc
    return total, len(edges) - 1


def main():
    base = load_base()
    mp.mp.dps = 40
    print("tsd_core_checks2.py sha256", hashlib.sha256(open(__file__, "rb").read()).hexdigest())
    print("base tsd_core_checks.py sha256", BASE_SHA, "(checked)")
    print("run", datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
          "python", sys.version.split()[0], "numpy", np.__version__, "mpmath", mp.__version__, "dps", mp.mp.dps)
    xs, ws = gl12_mp()
    print(f"mp Gauss-Legendre: sum of weights - 2 = {mp.nstr(sum(ws) - 2, 3)}; "
          f"max |node - binary64 node| = {max(abs(float(x) - y) for x, y in zip(xs, base.GLX)):.1e}")
    ok = {"h": True, "a": True, "q": True, "im": True}
    k1 = k2 = 0
    for c in base.CASES:
        bad = [k for k, v in c.hyp().items() if not v]
        ok["h"] &= not bad
        core, tr, mid, far = c.eps()
        tot = core + 2 * tr + mid + far
        G = c.G()
        J2, J2h = c.J_contour(c.ell, 1), c.J_contour(c.ell, 2)
        J3, J3h = c.J_contour(c.ell / 2, 1), c.J_contour(c.ell / 2, 2)
        d = {"R2 vs refined": abs(J2 - J2h) / G, "R3 vs refined": abs(J3 - J3h) / G,
             "R2 vs R3": abs(J2h - J3h) / G}
        im = None
        note = ""
        if c.label == "C9":
            X = 60.0 / c.am.kap
            (J1, n1), (J1h, n1h) = line_c9_mp(c, X, 1, xs, ws), line_c9_mp(c, X, 2, xs, ws)
            d["R1 vs refined"] = float(abs(J1 - J1h)) / G
            d["R1 vs R2"] = float(abs(J1h.real - mp.mpf(float(J2h)))) / G
            im = float(abs(J1h.imag)) / G
            note = f" [R1 in {mp.mp.dps}-digit arithmetic, X={X}, {n1} and {n1h} panels]"
        elif c.am.line:
            J1, J1h = c.J_line(1), c.J_line(2)
            d["R1 vs refined"] = abs(J1 - J1h) / G
            d["R1 vs R2"] = abs(J1h.real - J2h) / G
            im = abs(J1h.imag) / G
        else:
            note = " [no line route for this amplitude]"
        E = abs(J2h - c.lead()) / G
        Ek1 = abs(J2h - c.lead(quarter=np.conj(base.E4))) / G
        Ek2 = abs(J2h - c.lead(alpha=c.alpha / 2)) / G
        a_ok = E <= tot + 1e-9
        q_ok = max(d.values()) < 1e-8
        im_ok = im is None or im < 1e-8
        ok["a"] &= a_ok
        ok["q"] &= q_ok
        ok["im"] &= im_ok
        k1 += Ek1 > tot
        k2 += Ek2 > tot
        print(f"{c.label} {c.ph.name} {c.am.name} delta={c.delta} t={c.t}: "
              f"hypotheses (6),(7): {'all hold' if not bad else 'FAIL ' + ', '.join(bad)}")
        print(f"   J={J2h:.12e} lead={c.lead():.12e} G={G:.6e} total={tot:.4e} "
              f"E={E:.4e} bound/measured={tot / E:.4g} (a) {'PASS' if a_ok else 'FAIL'}")
        print("   disagreements/G: " + "; ".join(f"{k}={v:.2e}" for k, v in d.items())
              + f" (q) {'PASS' if q_ok else 'FAIL'}" + note)
        print("   |Im J|/G=" + ("not measured" if im is None else f"{im:.2e}")
              + f" (im) {'PASS' if im_ok else 'FAIL'}")
        print(f"   controls: wrong quarter phase E={Ek1:.4e} ({'exceeds' if Ek1 > tot else 'within'} the bound); "
              f"alpha halved E={Ek2:.4e} ({'exceeds' if Ek2 > tot else 'within'} the bound)")
    n = len(base.CASES)
    lines = [("(h) the inequalities of hypotheses (6) and (7) hold in all cases", ok["h"]),
             ("(a) |J - lead| <= G * total in all cases", ok["a"]),
             ("(q) quadrature routes and refinements agree within 1e-8 G", ok["q"]),
             ("(im) |Im J| < 1e-8 G where the line route exists", ok["im"]),
             (f"K1 wrong quarter phase exceeds the bound in {k1} of {n} cases (required: at least 4)", k1 >= 4),
             (f"K2 halved alpha exceeds the bound in {k2} of {n} cases (required: at least 4)", k2 >= 4)]
    for text, good in lines:
        print(("PASS " if good else "FAIL ") + text)
    allok = all(g for _, g in lines)
    print("OVERALL:", "PASS" if allok else "FAIL", f"({sum(g for _, g in lines)} of {len(lines)} lines PASS)")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
