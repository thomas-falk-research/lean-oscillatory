#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical check of the batch-LE2 route interfaces (docs/proof-LE2.md; CONTRIBUTING step 6). FLOAT only: tooling,
never evidence for a statement.

I1 BandLow, BandHigh, CapLow, CapHigh, Whole (Blueprint/LatticeCubeRoot.lean) against |I(t, tv)| at seeded random
   (t, v, delta) in their hypothesis ranges, t in [0.05, 60], including the edge cases v = 0 and v = delta;
   I(t, xi) by Gauss-Legendre with n >= 1.3 (t + |xi|) + 200 nodes, checked by node doubling.
I2 VarFacts, both branches, against direct quadrature.
I3 the regime-3 <= t <= 8 sub-range bounds after the route referee's split at v = 1/8 (exact rational end values are in
   followup_checks.py): the band piece max over v in [0, 1/4] of t^(1/3) (2(arcsin(v+1/2) - arcsin(v-1/2)) + 12/t).
E1 exact rational steps added after the route referee (docs/proof-LE2.md, revision): the split of 0 <= v <= 1/4
   at v = 1/8 for 3 <= t <= 8 (arcsin(5/8) <= 17/25, arcsin(3/8) <= 2/5, pi/6 < 11/21, four end values < 97/10) and the
   t >= 8, v <= delta bound (48/7) tau + 16/3 - 4 tau^2 <= 163/21 (the referee's cruder (72/7) tau gives 199/21; both
   < 97/10) at tau = 1/2.
Exit status 0 iff every bound holds with margin >= 0 on every sample. Seed 20261111.
Usage: python3 -I numerics/review/le2_interface_checks.py (numpy 2.3.5)
"""
import sys
import numpy as np
from numpy.polynomial.legendre import leggauss

rng = np.random.default_rng(20261111)
_gl = {}


def gl(n):
    if n not in _gl:
        x, w = leggauss(n)
        _gl[n] = x, w
    return _gl[n]


def J(t, xi, a, b, n=None):
    if n is None:
        n = int(1.3 * (t + abs(xi)) * (b - a) / (2 * np.pi)) + 200
    x, w = gl(n)
    k = (b - a) / 2 * x + (a + b) / 2
    return (b - a) / 2 * np.sum(w * np.exp(1j * (t * np.cos(k) + xi * k)))


def I(t, xi):
    return J(t, xi, -np.pi, np.pi)


asin = np.arcsin
facts = {
    'BandLow': (lambda t, v, d: 2 * (asin(v + d) - asin(v - d)) + 8 / (t * d) - 4 / (t * (1 - v**2)),
                lambda: (lambda d: (d, rng.uniform(0, min(d, 1 - d - 1e-6)) * (rng.random() > 0.1)))(rng.uniform(1e-3, 0.499))),
    'BandHigh': (lambda t, v, d: 2 * (asin(v + d) - asin(v - d)) + 8 / (t * d) - 4 / (t * (1 - v**2)) + 2 / (t * v),
                 lambda: (lambda d: (d, d if rng.random() < 0.1 else rng.uniform(d, 1 - d - 1e-6)))(rng.uniform(1e-3, 0.499))),
    'CapLow': (lambda t, v, d: np.pi - 2 * asin(v - d) + 4 / (t * d) - 2 / (t * (1 + v)),
               lambda: (lambda d: (d, rng.uniform(max(0, d - 1 + 1e-6), d) * (rng.random() > 0.1) + max(0, d - 1 + 1e-6) * 0))(rng.uniform(1e-3, 1.5))),
    'CapHigh': (lambda t, v, d: np.pi - 2 * asin(v - d) + 4 / (t * d) + 2 / (t * v * (v + 1)),
                lambda: (lambda d: (d, rng.uniform(d, d + 1 - 1e-6)))(rng.uniform(1e-3, 2))),
}
ok_all = True
for name, (bound, draw) in facts.items():
    worst, wpt = -np.inf, None
    for _ in range(1500):
        d, v = draw()
        if name == 'CapLow' and v - d <= -1:
            continue
        t = rng.uniform(0.05, 60)
        m = abs(I(t, t * v)) - bound(t, v, d)
        if m > worst:
            worst, wpt = m, (t, v, d)
    ok = worst < 0
    ok_all &= ok
    print(f"I1 {name} {'PASS' if ok else 'FAIL'} max(|I| - bound) = {worst:.4g} at (t, v, delta) = {tuple(round(x, 4) for x in wpt)}")
worst = -np.inf
for _ in range(1500):
    t = rng.uniform(0.05, 60); v = rng.uniform(1 + 1e-4, 4)
    worst = max(worst, abs(I(t, t * v)) - (2 / (t * (v - 1)) + 2 / (t * v * (v + 1))))
ok_all &= worst < 0
print(f"I1 Whole {'PASS' if worst < 0 else 'FAIL'} max(|I| - bound) = {worst:.4g}")
# node doubling at a few points
dd = max(abs(I(t, x) - J(t, x, -np.pi, np.pi, 2 * (int(1.3 * (t + x)) + 200))) for t, x in [(60, 60), (59.3, 31.7), (0.05, 0.02)])
print(f"I1 node-doubling max difference {dd:.2e}")
ok_all &= dd < 1e-10
# I2 VarFacts
err = 0
for _ in range(300):
    t = rng.uniform(0.1, 20); br = rng.integers(3)
    lo, hi = [(-np.pi / 2, np.pi / 2), (np.pi / 2, 1.5 * np.pi), (-1.5 * np.pi, -np.pi / 2)][br]
    a, b = np.sort(rng.uniform(lo, hi, 2))
    s = np.sin(np.linspace(a, b, 50))
    xi = t * (max(s) + rng.uniform(0.05, 2)) if rng.random() < 0.5 else t * (min(s) - rng.uniform(0.05, 2))
    x, w = gl(4000); k = (b - a) / 2 * x + (a + b) / 2
    lhs = (b - a) / 2 * np.sum(w * np.abs(t * np.cos(k)) / (xi - t * np.sin(k))**2)
    g = lambda k: xi - t * np.sin(k)
    rhs = 1 / g(b) - 1 / g(a) if br == 0 else 1 / g(a) - 1 / g(b)
    err = max(err, abs(lhs - rhs) / max(1, abs(rhs)))
ok_all &= err < 1e-8
print(f"I2 VarFacts {'PASS' if err < 1e-8 else 'FAIL'} max relative error {err:.2e}")
# I3 regime 3..8, band piece after the split at v = 1/8
vs = np.linspace(0, 0.25, 2001); m = 0
for t in np.linspace(3, 8, 101):
    m = max(m, np.max(t**(1 / 3) * (2 * (asin(vs + 0.5) - asin(vs - 0.5)) + 12 / t)))
ok_all &= m < 9.7
print(f"I3 regime 3..8 band piece max t^(1/3) bound = {m:.5f} (< 97/10 required)")
from fractions import Fraction as Fr
def sinlow(x):
    return x - x**3 / 6
e = []
e.append(sinlow(Fr(17, 25)) >= Fr(5, 8))
e.append(sinlow(Fr(2, 5)) >= Fr(3, 8))
e.append(Fr(22, 7) / 6 == Fr(11, 21))
c3, pi_u = Fr(13, 9), Fr(22, 7)
lo_band = 2 * (Fr(17, 25) + Fr(11, 21)); hi_band = 2 * (Fr(6, 7) + Fr(2, 5))
ends = [c3 * (lo_band + 4), 2 * (lo_band + Fr(12, 8)), c3 * (hi_band + 4), 2 * (hi_band + Fr(12, 8))]
e.append(all(x < Fr(97, 10) for x in ends))
e.append(Fr(72, 7) / 2 + Fr(16, 3) - 1 == Fr(199, 21) and Fr(199, 21) < Fr(97, 10))
e.append(Fr(48, 7) / 2 + Fr(16, 3) - 1 == Fr(163, 21))
ok_all &= all(e)
print(f"E1 exact revised-route steps {'PASS' if all(e) else 'FAIL'}: end values " + ", ".join(f"{x} = {float(x):.4f}" for x in ends) + "; 199/21 and 163/21 (t >= 8, v <= delta)")
print("RESULT", "PASS" if ok_all else "FAIL")
sys.exit(0 if ok_all else 1)
