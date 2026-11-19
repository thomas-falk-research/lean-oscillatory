#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical checks of the blueprint propositions of batch FR (Blueprint/FiniteRing.lean), transcribed from the Lean
text, run by the lead before the parts are proved. Tooling, not evidence for a Lean theorem. mpmath, 40 digits.
RingEnergyFacts and ChainEnergyFacts are uniqueness statements and cannot be tested by sampling; they are not here."""
import sys
import random
from mpmath import mp, mpf, exp, cos, pi, cosh, fabs, mpc
mp.dps = 40
ok = True
def report(name, cond, detail=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
def ring(N, t, r):
    if N == 0: return mpc(0)
    return sum(exp(1j * (2 * t * (cos(2 * pi * j / N) - 1) + r * (2 * pi * j / N))) for j in range(N)) / N
rng = random.Random(20261116)
# RingEvenFacts
w = 0
for N in range(0, 10):
    for _ in range(12):
        t = mpf(rng.uniform(-9, 9)); r = rng.randint(-40, 40)
        w = max(w, fabs(ring(N, t, -r) - ring(N, t, r)))
report("RingEvenFacts: R_N(t, -r) = R_N(t, r), N = 0..9, 120 points", w < mpf(10) ** -30, f"max diff {mp.nstr(w, 3)}")
# RingDatumFacts (exact)
bad = 0; n = 0
for N in range(1, 13):
    vals = [complex(rng.randint(-9, 9), rng.randint(-9, 9)) for _ in range(N)]
    f = lambda z: vals[z % N]
    for x in range(-3 * N - 2, 3 * N + 3):
        s = sum((1 if (x - y) % N == 0 else 0) * f(y) for y in range(N)); n += 1
        bad += (s != f(x))
report("RingDatumFacts: sum over one period of [N | x - y] f(y) = f(x), N = 1..12", bad == 0, f"{n} cases")
# ImageSumFacts
def image_case(N, r, eta, A, mode):
    K = int(60 / (eta * N)) + 8
    g = {}
    def gv(n):
        if n not in g:
            b = A * exp(-abs(n) * eta)
            if mode == "extremal": g[n] = mpc(b)
            elif mode == "alternating": g[n] = mpc(b * (-1) ** n)
            else: g[n] = b * rng.uniform(0, 1) * exp(1j * rng.uniform(0, 6.283185307179586))
        return g[n]
    S = sum(gv(r + m * N) for m in range(-K, K + 1))
    lhs = fabs(S - gv(r)); rhs = 2 * A * cosh(r * eta) / (exp(eta * N) - 1)
    return lhs, rhs
worst = 0; n = 0; viol = 0
for mode in ("extremal", "alternating", "random"):
    for N in (1, 2, 3, 5, 8, 13):
        for r in list(range(-2 * N - 1, 2 * N + 2)) + [7 * N, -5 * N + 1]:
            for eta in (mpf("0.01"), mpf("0.3"), mpf(1), mpf(4)):
                lhs, rhs = image_case(N, r, eta, mpf("1.7"), mode); n += 1
                worst = max(worst, lhs / rhs); viol += (lhs > rhs * (1 + mpf(10) ** -25))
report("ImageSumFacts: |S - g(r)| <= 2A cosh(r eta)/(e^{eta N} - 1)", viol == 0, f"{n} cases, largest ratio {mp.nstr(worst, 12)}")
# controls
lhs, rhs = image_case(3, 1, mpf(1), mpf(1), "extremal")
report("control: constant 1 in place of 2 fails (extremal g, N = 3, r = 1)", lhs > rhs / 2)
lhs, rhs = image_case(3, 2, mpf(1), mpf(1), "extremal")
report("control: cosh(r eta) replaced by 1 fails (extremal g, N = 3, r = 2)", lhs > 2 / (exp(mpf(3)) - 1))
print("ALL PASS" if ok else "SOME FAIL")
sys.exit(0 if ok else 1)   # a failed check must fail the process (external review of VC2, 2026-11-19)
