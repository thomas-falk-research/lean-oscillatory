#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's independent checks of the external DNLS research packet (review/2026-11-12-DNLS-packet-answers.md).

Written by the lead without reading or reusing the packet's scripts.
D1 FLOAT: the kernel-to-group identity e^{itΔ}δ_0(x) = (2π)^{-d} e^{-2idt} K_d(2t, x), Δ the nearest-neighbour Laplacian
   on ℤ^d. Left side: matrix exponential (scipy.linalg.expm) on a periodic box of side 81 (wrap-around negligible for
   |t| ≤ 3: the kernel decays super-exponentially beyond |x| ≈ 2e|t|). Right side: K_1(s, x) = 2π i^|x| J_|x|(s) (Bessel),
   and K_d = ∏ K_1 by TdF. d = 1, 2; t = ±0.7, 2.9. Control: dropping the gauge e^{-2idt} or the factor 2 must fail.
D2 EXACT (Fraction): C* < 146/15 (√7 < 53/20); τ = (C*/(2π))³/2 < 2 (π > 157/50); the bite's ratios
   r(1/2 + r/4) with r = 1/72 equals (145/288) r, and r/4 + 1/4 = 73/288; 4608 (71/72)² = 40328/9.
D3 FLOAT: sup over t ≥ 0 of (1 + t)^σ min{1, c_d t^{-σ}} equals L_d = (1 + τ)^σ (d = 1, 2, 3, 4), attained at t = τ
   (the grid includes t = τ; a first run without it sampled maxima just below L_d and failed a 1e-6 tolerance).
D4 FLOAT: sup over t of (1 + t)^σ ∫_0^t (1 + t − s)^{-σ} (1 + s)^{-a} ds ≤ J_{σ,a} for (σ, a) = (1/3, 5/3), (2/3, 2),
   (1, 3), (4/3, 4/3), (2, 2); and the borderline identity ∫_0^t ds/((1 + t − s)(1 + s)) = 2 log(1 + t)/(t + 2).
D5 FLOAT: Track C spot checks. Whistler: h(q) = q²/(1 + q²) has h''(1/√3) = 0 and min |h'''| on [1/2, 2/3] ≥ 43740/28561.
   Kelvin: the reduced phase's third derivative −4√6/9 at the cusp line (symbolic, see the code for the reduction used).
Usage: python3 -I numerics/review/dnls_checks.py (needs numpy, scipy, sympy; versions printed at run time)
"""
import platform
import sys
from fractions import Fraction as F

import numpy as np
import scipy
import sympy as sp
from scipy.integrate import quad
from scipy.linalg import expm
from scipy.special import jv

ok = True
CS = 8 * (1 + np.sqrt(7)) / 3


def report(line):
    print(line, flush=True)


# D1 kernel-to-group identity
def lap_periodic(n, d):
    I1 = np.eye(n)
    S = np.roll(I1, 1, axis=0) + np.roll(I1, -1, axis=0) - 2 * I1
    if d == 1:
        return S
    return np.kron(S, I1) + np.kron(I1, S)


def K1(s, x):
    return 2 * np.pi * (1j) ** abs(x) * jv(abs(x), s)


n = 81
c0 = n // 2
worst = 0.0
ctrl_gauge = ctrl_two = 0.0
for d in (1, 2):
    D = lap_periodic(n, d)
    for t in (-0.7, 0.7, 2.9, -2.9):
        U = expm(1j * t * D)
        e0 = np.zeros(n**d, complex)
        idx = c0 if d == 1 else c0 * n + c0
        e0[idx] = 1
        v = U @ e0
        for x in ([0, 1, -3, 7] if d == 1 else [(0, 0), (1, -2), (3, 0), (-5, 4)]):
            if d == 1:
                lhs = v[(c0 + x) % n]
                Kd = K1(2 * t, x)
                Kd_no2 = K1(t, x)
            else:
                lhs = v[((c0 + x[0]) % n) * n + (c0 + x[1]) % n]
                Kd = K1(2 * t, x[0]) * K1(2 * t, x[1])
                Kd_no2 = K1(t, x[0]) * K1(t, x[1])
            rhs = (2 * np.pi) ** (-d) * np.exp(-2j * d * t) * Kd
            worst = max(worst, abs(lhs - rhs))
            ctrl_gauge = max(ctrl_gauge, abs(lhs - (2 * np.pi) ** (-d) * Kd))
            ctrl_two = max(ctrl_two, abs(lhs - (2 * np.pi) ** (-d) * np.exp(-2j * d * t) * Kd_no2))
good = worst < 1e-10 and ctrl_gauge > 1e-2 and ctrl_two > 1e-2
ok &= good
report(f"D1 max |e^(itΔ)δ0(x) - (2π)^-d e^(-2idt) K_d(2t,x)| = {worst:.1e}; controls (no gauge {ctrl_gauge:.2f}, "
       f"no factor 2 {ctrl_two:.2f}) rejected: {'PASS' if good else 'FAIL'}")

# D2 exact rationals
checks = [
    ('sqrt 7 < 53/20, so C* < 146/15', F(53, 20)**2 > 7 and 8 * (1 + F(53, 20)) / 3 == F(146, 15)),
    ('tau < (1/2)(146/15 / (2*157/50))^3 < 2', F(1, 2) * (F(146, 15) / (2 * F(157, 50)))**3 < 2),
    ('bite self-map ratio (1/2 + r/4) = 145/288 at r = 1/72', F(1, 2) + F(1, 72) / 4 == F(145, 288)),
    ('bite Lipschitz r/4 + 1/4 = 73/288', F(1, 72) / 4 + F(1, 4) == F(73, 288)),
    ('4608 (71/72)^2 = 40328/9', 4608 * F(71, 72)**2 == F(40328, 9)),
    ('Omega = 128 d n^2 = 4608 at d = 4, n = 3', 128 * 4 * 9 == 4608),
]
for name, good in checks:
    ok &= bool(good)
    report(f"D2 {name}: {'PASS' if good else 'FAIL'}")

# D3 L_d is the sup of the weighted envelope
tau = 0.5 * (CS / (2 * np.pi))**3
for d in (1, 2, 3, 4):
    s = d / 3
    cd = CS**d / ((2 * np.pi)**d * 2**(d / 3))
    ts = np.concatenate([np.linspace(1e-6, 10, 400001), np.geomspace(10, 1e6, 2001), [tau]])  # the sup is at t = tau
    val = np.max((1 + ts)**s * np.minimum(1, cd * ts**(-s)))
    Ld = (1 + tau)**s
    good = abs(val - Ld) < 1e-12 * Ld and abs(cd - tau**s) < 1e-12
    ok &= good
    report(f"D3 d={d}: sup (1+t)^s min(1, c_d t^-s) = {val:.8f} vs L_d = {Ld:.8f}; c_d = tau^s: {'PASS' if good else 'FAIL'}")
report(f"D3 tau = {tau:.10f} (< 2)")


# D4 the convolution constant
def Jsa(s, a):
    first = 2**s / (a - 1)
    if s < 1:
        return first + 2**a / (1 - s)
    if s == 1:
        return first + 2**a / (a - 1)
    return first + 2**a / (s - 1)


for s, a in [(1 / 3, 5 / 3), (2 / 3, 2.0), (1.0, 3.0), (4 / 3, 4 / 3), (2.0, 2.0)]:
    vals = []
    for t in np.geomspace(1e-3, 1e5, 161):
        f = lambda u: (1 + t - u)**(-s) * (1 + u)**(-a)
        pts = [t / 2] if t > 2 else None
        v = quad(f, 0, t, points=pts, limit=400, epsabs=1e-13, epsrel=1e-11)[0]
        vals.append((1 + t)**s * v)
    m = max(vals)
    good = m <= Jsa(s, a)
    ok &= good
    report(f"D4 (s, a) = ({s:.3f}, {a:.3f}): sup = {m:.4f} <= J = {Jsa(s, a):.4f} {'PASS' if good else 'FAIL'}")
mx = 0.0
for t in [0.5, 3.0, 40.0, 1e4]:
    v = quad(lambda u: 1 / ((1 + t - u) * (1 + u)), 0, t, limit=400, epsabs=1e-14, epsrel=1e-12)[0]
    mx = max(mx, abs(v - 2 * np.log(1 + t) / (t + 2)))
ok &= mx < 1e-10
report(f"D4 borderline identity max error {mx:.1e} {'PASS' if mx < 1e-10 else 'FAIL'}")

# D5 Track C spot checks
q = sp.symbols('q', positive=True)
h = q**2 / (1 + q**2)
h2 = sp.simplify(sp.diff(h, q, 2))
h3 = sp.diff(h, q, 3)
z = sp.simplify(h2.subs(q, 1 / sp.sqrt(3))) == 0
qs = np.linspace(0.5, 2 / 3, 200001)
f3 = sp.lambdify(q, h3, 'numpy')
mn = float(np.min(np.abs(f3(qs))))
good = z and mn >= 43740 / 28561
ok &= good
report(f"D5 whistler: h''(1/sqrt 3) = 0: {z}; min |h'''| on [1/2, 2/3] = {mn:.6f} >= 43740/28561 = {43740 / 28561:.6f} "
       f"{'PASS' if good else 'FAIL'}")
# Kelvin: phase psi(q) = sqrt(1 + q^2)(cos g - q sin g); stationary points solve psi'(q) = 0; at the cusp line
# (tan g = 1/(2 sqrt 2), the Kelvin angle) the two stationary points coalesce at q = 1/sqrt 2, where psi'' = 0.
g = sp.atan(1 / (2 * sp.sqrt(2)))
psi = sp.sqrt(1 + q**2) * (sp.cos(g) - q * sp.sin(g))
q0 = 1 / sp.sqrt(2)
d1 = sp.nsimplify(sp.simplify(sp.diff(psi, q).subs(q, q0)))
d2 = sp.nsimplify(sp.simplify(sp.diff(psi, q, 2).subs(q, q0)))
d3 = sp.nsimplify(sp.simplify(sp.diff(psi, q, 3).subs(q, q0)))
good = d1 == 0 and d2 == 0 and sp.simplify(d3 - (-4 * sp.sqrt(6) / 9)) == 0
ok &= good
report(f"D5 Kelvin at tan g = 1/(2 sqrt 2), q = 1/sqrt 2: psi' = {d1}, psi'' = {d2}, psi''' = {d3} (claim -4 sqrt 6/9): "
       f"{'PASS' if good else 'FAIL'}")
report(f"RUNTIME python {platform.python_version()} numpy {np.__version__} scipy {scipy.__version__} sympy {sp.__version__}")
report("RESULT " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
