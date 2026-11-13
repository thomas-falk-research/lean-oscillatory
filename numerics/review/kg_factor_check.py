#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Check of the zero-mass lower witness for the KG constant (review/2026-11-12-R2-KG-answers.md, addendum).

Claim (hand proof): with omega_0(k) = 2|sin(k/2)|, t = 7/8, b = 5/4,
  |J_0(7/8, 0)| >= int cos(t(omega_0 - b)) dk >= 2 pi - (t^2/2) int (omega_0 - b)^2 dk = 245/32 - 745 pi/1024 > 19245/3584,
so K_univ >= (7/8)^(1/3) |J_0(7/8, 0)| > (239/250)(19245/3584) > 513/100, and C*/K_univ < (146/15)/(513/100) < 19/10.
F1 EXACT (sympy): the moments int omega_0 = 8, int omega_0^2 = 4 pi, int (omega_0 - 5/4)^2 = 57 pi/8 - 20, and
   2 pi - (49/128)(57 pi/8 - 20) = 245/32 - 745 pi/1024.
F2 EXACT (Fraction): 245/32 - 745 (22/7)/1024 = 19245/3584; (239/250)^3 < 7/8; (239/250)(19245/3584) > 513/100;
   (53/20)^2 > 7 so C* < 146/15; (146/15)/(513/100) < 19/10. The only non-rational inputs are pi < 22/7 (for example
   from Mathlib's Real.pi_lt_d4, pi < 3.1416) and (7/8)^(1/3) > 239/250 (by cubing).
F3 FLOAT: |J_0(7/8, 0)| by Gauss-Legendre with doubling, and (7/8)^(1/3)|J_0(7/8, 0)|, against the witness 5.13.
Control: the same estimate with t = 2 (where u = t(omega_0 - b) is large) must give a lower bound below 0 or below the
  true value, i.e. the method is not misapplied there; reported, not asserted.
Usage: python3 -I numerics/review/kg_factor_check.py (needs sympy, numpy; versions printed at run time)
"""
import platform
import sys
from fractions import Fraction as F

import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss

ok = True
k = sp.symbols('k', real=True)
w = 2 * sp.sin(k / 2)  # omega_0 on [0, pi]; the integrands below are even in k, so integrate over [0, pi] and double
mom1 = sp.simplify(2 * sp.integrate(w, (k, 0, sp.pi)))
mom2 = sp.simplify(2 * sp.integrate(w**2, (k, 0, sp.pi)))
cen = sp.simplify(2 * sp.integrate((w - sp.Rational(5, 4))**2, (k, 0, sp.pi)))
low = sp.simplify(2 * sp.pi - sp.Rational(49, 128) * cen - (sp.Rational(245, 32) - sp.Rational(745, 1024) * sp.pi))
for name, val, want in [('int omega_0 = 8', mom1, 8), ('int omega_0^2 = 4 pi', mom2, 4 * sp.pi),
                        ('int (omega_0 - 5/4)^2 = 57 pi/8 - 20', cen, sp.Rational(57, 8) * sp.pi - 20),
                        ('2 pi - (49/128)(...) = 245/32 - 745 pi/1024', low, 0)]:
    good = sp.simplify(val - want) == 0
    ok &= good
    print(f"F1 {name}: {'PASS' if good else 'FAIL'}")
c1 = F(245, 32) - F(745, 1024) * F(22, 7) == F(19245, 3584)
c2 = F(239, 250)**3 < F(7, 8)
c3 = F(239, 250) * F(19245, 3584) > F(513, 100)
c4 = F(53, 20)**2 > 7 and 8 * (1 + F(53, 20)) / 3 == F(146, 15)
c5 = F(146, 15) / F(513, 100) < F(19, 10)
for name, good in [('245/32 - 745(22/7)/1024 = 19245/3584', c1), ('(239/250)^3 < 7/8', c2),
                   ('(239/250)(19245/3584) > 513/100', c3), ('sqrt 7 < 53/20 and 8(1 + 53/20)/3 = 146/15', c4),
                   ('(146/15)/(513/100) = %s < 19/10' % (F(146, 15) / F(513, 100)), c5)]:
    ok &= good
    print(f"F2 {name}: {'PASS' if good else 'FAIL'}")


def J0(t, n):
    x, wts = leggauss(n)
    tot = 0j
    for lo, hi in [(-np.pi, 0.0), (0.0, np.pi)]:
        kk = (hi - lo) / 2 * x + (hi + lo) / 2
        tot += np.sum((hi - lo) / 2 * wts * np.exp(1j * t * 2 * np.abs(np.sin(kk / 2))))
    return tot


a, b = abs(J0(7 / 8, 200)), abs(J0(7 / 8, 400))
val = (7 / 8)**(1 / 3) * b
good = abs(a - b) < 1e-13 and b > 19245 / 3584 and val > 5.13
ok &= good
print(f"F3 |J_0(7/8, 0)| = {b:.12f} (doubling change {abs(a - b):.1e}) > 19245/3584 = {19245 / 3584:.6f}; "
      f"(7/8)^(1/3)|J_0| = {val:.6f} > 5.13: {'PASS' if good else 'FAIL'}")
lb2 = 2 * np.pi - 2.0**2 / 2 * float(57 * sp.pi / 8 - 20)
print(f"Control t = 2: the cosine-moment lower bound gives {lb2:.4f} against |J_0(2, 0)| = {abs(J0(2.0, 400)):.4f} "
      "(the method is only informative for small t)")
print(f"RUNTIME python {platform.python_version()} numpy {np.__version__} sympy {sp.__version__}")
print("RESULT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
