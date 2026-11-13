#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical interface check of batch HC (docs/proof-HC.md; CONTRIBUTING step 6). FLOAT only, tooling, not evidence.

H1 TdF: K_d(t, x) computed directly on the d-dimensional grid (periodic trapezoid, no factorisation; exact for this
   2pi-periodic trigonometric integrand once the grid exceeds the bandwidth) against prod_j I(t, x_j) by 1D
   Gauss-Legendre, d = 2, 3, several (t, x) including t < 0; node doubling reported.
H2 TdE': |K_d(t, x)| <= C*^d t^(-d/3) at the same points with t > 0, and the d = 0 identity K_0 = 1.
H3 The DNLS bootstrap kernel of docs/design/dnls-scoping.md (route referee of the adversarial review): sup over t of
   (1 + t)^s int_0^t min(1, (t - u)^(-s)) (1 + u)^(-a) du, for (s, a) = (1/3, 5/3), (2/3, 2), (1, 3), (4/3, 4/3)
   (bounded; the last is d = 4, p = 1) and the control (1, 1) (grows like log t).
   Test, at t = 10, 100, 1000, 10000: a bounded case must have decade increments that shrink geometrically
   (|D_{k+1}| <= 0.6 |D_k|, or |D_{k+1}| < 1e-2); the control must have increments that do not shrink (>= 0.9 times the
   previous one), as for c log t. An absolute cut-off is not used: the (4/3, 4/3) case converges slowly, like t^(-1/3),
   to about 7. Floating point, a trapezoid rule with 2e5 panels; tooling, not a proof (the bound is proved by hand in
   docs/design/dnls-scoping.md).
Exit status 0 iff H1 discrepancies < 1e-10 and H2 holds and H3's cases behave as stated.
Usage: python3 -I numerics/review/hc_interface_checks.py (numpy 2.5.3)
"""
import platform
import sys
import itertools
import numpy as np
from numpy.polynomial.legendre import leggauss

C = 8 * (1 + np.sqrt(7)) / 3
ok = True


def I1(t, xi, n=600):
    x, w = leggauss(n)
    k = np.pi * x
    return np.pi * np.sum(w * np.exp(1j * (t * np.cos(k) + xi * k)))


def Kd(t, xs, n):
    d = len(xs)
    k = -np.pi + 2 * np.pi * np.arange(n) / n
    grids = np.meshgrid(*([k] * d), indexing='ij')
    ph = t * sum(np.cos(g) for g in grids) + sum(x * g for x, g in zip(xs, grids))
    return np.sum(np.exp(1j * ph)) * (2 * np.pi / n) ** d


pts = [(3.0, (1, -2)), (-2.0, (1, 0)), (0.3, (11, -12)), (8.0, (1, -2)), (20.0, (5, -7)),
       (3.0, (1, 0, -3)), (-2.0, (2, 1, 0)), (8.0, (1, 0, -3)), (20.0, (19, -20, 0))]
worst = 0
for t, xs in pts:
    n = 64 if len(xs) == 3 else 128
    a, b = Kd(t, xs, n), Kd(t, xs, 2 * n)
    prod = np.prod([I1(t, x) for x in xs])
    disc = max(abs(a - prod), abs(b - prod))
    worst = max(worst, disc)
    bound_ok = True if t <= 0 else abs(a) <= C ** len(xs) * t ** (-len(xs) / 3)
    ok &= bound_ok
    print(f"H1/H2 d={len(xs)} t={t:6.2f} x={xs}: |K - prod I| = {disc:.2e}, |K| = {abs(a):.4f}"
          + ("" if t <= 0 else f", bound {C ** len(xs) * t ** (-len(xs) / 3):.4f} {'OK' if bound_ok else 'FAIL'}"))
ok &= worst < 1e-10
print(f"H1 max discrepancy {worst:.2e} ({'PASS' if worst < 1e-10 else 'FAIL'}); H2 d = 0: K_0 = 1 by definition")


def boot(s, a, t, n=200000):
    u = np.linspace(0, t, n + 1)
    f = np.maximum(t - u, 1.0) ** (-s) * (1 + u) ** (-a)  # min(1, r^(-s)) = max(r, 1)^(-s) for s > 0
    return (1 + t) ** s * np.trapezoid(f, u)


for s, a, bounded in [(1 / 3, 5 / 3, True), (2 / 3, 2.0, True), (1.0, 3.0, True), (4 / 3, 4 / 3, True), (1.0, 1.0, False)]:
    vals = [boot(s, a, t) for t in [10, 100, 1000, 10000]]
    inc = np.diff(vals)
    if bounded:
        good = all(abs(inc[k + 1]) <= 0.6 * abs(inc[k]) or abs(inc[k + 1]) < 1e-2 for k in range(len(inc) - 1))
    else:
        good = all(inc[k] > 0 and inc[k + 1] >= 0.9 * inc[k] for k in range(len(inc) - 1))
    ok &= good
    print(f"H3 s={s:.3f} a={a:.3f}: " + ", ".join(f"{v:.3f}" for v in vals) + f" ({'bounded' if bounded else 'grows'}: {'PASS' if good else 'FAIL'})")
print(f"RUNTIME python {platform.python_version()} numpy {np.__version__}")
print("RESULT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
