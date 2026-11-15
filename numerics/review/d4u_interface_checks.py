#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical interface check of batch D4U (docs/proof-D4U.md; CONTRIBUTING step 6). FLOAT only, tooling, not evidence.

U1 P-mod: for the C² amplitude A(κ) = (1 − |κ|²)³ on |κ| < 1 (Euclidean |·|; supported in the max-norm ball of
   radius 1) and offsets y, y' with ‖y‖, ‖y'‖ ≤ R = 2, the C² size of (e_y − e_{y'}) A, e_y(κ) = exp(i y·κ), measured as
   the operator norms for the max norm on ℝ² (order 1: |a| + |b|; order 2: Σ |H_ij|), maximised over a grid of the
   support, divided by ‖y − y'‖. The compactness route only needs this to tend to 0 with ‖y − y'‖ (uniform
   continuity); the check reports the ratio, which must stay bounded (a Lipschitz-type constant) as ‖y − y'‖ → 0.
U2 Assembly of S4.2O: oscInt2(tφ + y·κ, A) = oscInt2(tφ, e_y A) (pointwise identity of integrands) and
   (e_y A)(0) = A(0), checked on the grid for the generic cubic φ = x³ + 2x²y + 3xy² + 5y³.
U3 Assembly of S4.2U: with η = ε / (2 (C + |c| + 1)), (C + |c|) η < ε/2 for a range of C ≥ 0, |c|, ε > 0.
Exit status 0 iff U1's ratios are bounded by 50 and do not grow as ‖y − y'‖ decreases, U2's discrepancies are below
1e-12 and U3 holds.
Usage: python3 -I numerics/review/d4u_interface_checks.py
"""
import platform
import sys

import numpy as np

print(f"RUNTIME python {platform.python_version()} numpy {np.__version__}")

n = 401
g = np.linspace(-1.0, 1.0, n)
X, Y = np.meshgrid(g, g, indexing="ij")
r2 = X**2 + Y**2
inside = r2 < 1
w = np.where(inside, 1 - r2, 0.0)
A = w**3
Ax = np.where(inside, -6 * X * w**2, 0.0)
Ay = np.where(inside, -6 * Y * w**2, 0.0)
Axx = np.where(inside, -6 * w**2 + 24 * X**2 * w, 0.0)
Ayy = np.where(inside, -6 * w**2 + 24 * Y**2 * w, 0.0)
Axy = np.where(inside, 24 * X * Y * w, 0.0)


def c2_size(y1, y2):
    """Derivatives of order 0, 1, 2 of e_y A as arrays (value, (dx, dy), (dxx, dxy, dyy))."""
    e = np.exp(1j * (y1 * X + y2 * Y))
    f = e * A
    fx = e * (1j * y1 * A + Ax)
    fy = e * (1j * y2 * A + Ay)
    fxx = e * (-(y1**2) * A + 2j * y1 * Ax + Axx)
    fyy = e * (-(y2**2) * A + 2j * y2 * Ay + Ayy)
    fxy = e * (-(y1 * y2) * A + 1j * y1 * Ay + 1j * y2 * Ax + Axy)
    return f, (fx, fy), (fxx, fxy, fyy)


def diff_norm(y, z):
    f, (fx, fy), (fxx, fxy, fyy) = c2_size(*y)
    h, (hx, hy), (hxx, hxy, hyy) = c2_size(*z)
    o0 = np.abs(f - h).max()
    o1 = (np.abs(fx - hx) + np.abs(fy - hy)).max()
    o2 = (np.abs(fxx - hxx) + 2 * np.abs(fxy - hxy) + np.abs(fyy - hyy)).max()
    return max(o0, o1, o2)


ok = True
rng = np.random.default_rng(20261115)
R = 2.0
worst = {}
for k in range(8):
    y = rng.uniform(-R, R, 2)
    for s in (1e-1, 1e-2, 1e-3, 1e-4):
        d = rng.uniform(-1, 1, 2)
        d = d / np.abs(d).max() * s
        z = np.clip(y + d, -R, R)
        dist = np.abs(y - z).max()
        ratio = diff_norm(y, z) / dist
        worst[s] = max(worst.get(s, 0.0), ratio)
print("U1 max over 8 random offsets of C2-size(diff)/||y - y'|| by step:",
      {s: round(v, 4) for s, v in worst.items()})
ws = [worst[s] for s in (1e-1, 1e-2, 1e-3, 1e-4)]
if max(ws) > 50 or ws[-1] > 1.05 * ws[0] + 1e-9:
    ok = False
    print("U1 FAIL")

phi = X**3 + 2 * X**2 * Y + 3 * X * Y**2 + 5 * Y**3
dmax = 0.0
for t in (1.0, 17.0, 400.0):
    for y in ((0.0, 0.0), (1.5, -0.5), (-2.0, 2.0)):
        lhs = np.exp(1j * (t * phi + y[0] * X + y[1] * Y)) * A
        rhs = np.exp(1j * t * phi) * (np.exp(1j * (y[0] * X + y[1] * Y)) * A)
        dmax = max(dmax, np.abs(lhs - rhs).max())
i0 = n // 2
v0 = c2_size(1.5, -0.5)[0][i0, i0]
print(f"U2 max |integrand difference| = {dmax:.3e}; (e_y A)(0) = {v0:.15f}, A(0) = {A[i0, i0]:.15f}")
if dmax > 1e-12 or abs(v0 - A[i0, i0]) > 1e-12:
    ok = False
    print("U2 FAIL")

u3 = True
for C in (0.0, 0.5, 3.0, 100.0):
    for c in (0.0, 1.5485, 10.0):
        for eps in (1e-6, 0.1, 1.0):
            eta = eps / (2 * (C + c + 1))
            u3 &= (C + c) * eta < eps / 2
print(f"U3 (C + |c|) eta < eps/2 on the grid: {u3}")
ok &= u3
print("RESULT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
