#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical interface checks of the batch-LS route (docs/proof-LS.md; CONTRIBUTING step 6). FLOAT, tooling, not evidence.

I1 P-stencil: L_0 = delta_0, L_{n+1} = Delta L_n on Z^d (d = 1, 2), exactly in integers; sum_z |L_n(z)| <= (4d)^n for
   n <= 10 (EXACT, integer arithmetic).
I2 P-fourier: L_n(z) = (2 pi)^{-d} int (2 sum cos k_j - 2d)^n e^{i z.k} dk, by an n+1-point-exact trapezoid rule on the
   torus (exact for trigonometric polynomials of degree < N), d = 1, 2, n <= 6.
I3 P-series: G_d(t, z) = sum_n (i t)^n / n! L_n(z) against (2 pi)^{-d} e^{-2idt} K_d(2t, z) with K_1(s, z) =
   2 pi i^|z| J_|z|(s) and K_2 = K_1 K_1 (TdF), d = 1, 2, t in {-1.3, 0.4, 2.0}. The tolerance is 1e-15 e^{4d|t|}:
   the series alternates with terms up to about e^{4d|t|}, so double-precision cancellation alone is of that order (a
   first run with a fixed 1e-12 tolerance failed at 6.1e-12 for this reason).
Usage: python3 -I numerics/review/ls_interface_checks.py (numpy, scipy; versions printed at run time)
"""
import platform
import sys
import numpy as np
import scipy
from scipy.special import jv
from math import factorial

ok = True
R = 24


def lap(g, d):
    out = -2 * d * g
    for ax in range(d):
        out = out + np.roll(g, 1, axis=ax) + np.roll(g, -1, axis=ax)
    return out


def stencils(d, nmax):
    shape = (2 * R + 1,) * d
    L = np.zeros(shape, dtype=object)
    L[(R,) * d] = 1
    out = [L]
    for _ in range(nmax):
        L = lap(L, d)
        out.append(L)
    return out


for d in (1, 2):
    S = stencils(d, 10)
    good = all(sum(abs(int(v)) for v in Ln.flat) <= (4 * d) ** n for n, Ln in enumerate(S))
    ok &= good
    print(f"I1 d={d}: sum |L_n| <= (4d)^n for n <= 10 (exact integers): {'PASS' if good else 'FAIL'}"
          f"; sum |L_10| = {sum(abs(int(v)) for v in S[10].flat)} vs {(4 * d) ** 10}")

N = 64
k = -np.pi + 2 * np.pi * np.arange(N) / N
worst = 0.0
for d in (1, 2):
    S = stencils(d, 6)
    grids = np.meshgrid(*([k] * d), indexing='ij')
    sym = 2 * sum(np.cos(g) for g in grids) - 2 * d
    for n in range(7):
        for z in ([0, 1, -3, 5] if d == 1 else [(0, 0), (1, -2), (3, 0)]):
            zz = (z,) if d == 1 else z
            ph = sum(zj * g for zj, g in zip(zz, grids))
            val = np.mean(sym ** n * np.exp(1j * ph))
            exact = S[n][tuple(R + zj for zj in zz)]
            worst = max(worst, abs(val - complex(exact)))
good = worst < 1e-9
ok &= good
print(f"I2 Fourier representation of L_n: max error {worst:.1e} {'PASS' if good else 'FAIL'}")

worst = 0.0
for d in (1, 2):
    S = stencils(d, 60)
    for t in (-1.3, 0.4, 2.0):
        for z in ([0, 1, -3] if d == 1 else [(0, 0), (1, -2)]):
            zz = (z,) if d == 1 else z
            ser = sum((1j * t) ** n / factorial(n) * complex(S[n][tuple(R + zj for zj in zz)]) for n in range(61))
            K = np.prod([2 * np.pi * (1j) ** abs(zj) * jv(abs(zj), 2 * t) for zj in zz])
            G = (2 * np.pi) ** (-d) * np.exp(-2j * d * t) * K
            worst = max(worst, abs(ser - G) / (1e-15 * np.exp(4 * d * abs(t))))
good = worst < 1
ok &= good
print(f"I3 kernel series sum_n (it)^n/n! L_n(z) = G_d(t, z): max error / (1e-15 e^(4d|t|)) = {worst:.2f} (< 1) {'PASS' if good else 'FAIL'}")
print(f"RUNTIME python {platform.python_version()} numpy {np.__version__} scipy {scipy.__version__}")
print("RESULT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
