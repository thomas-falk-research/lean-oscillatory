#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's independent checks of the external follow-up submissions of 2026-11-10
(answers: review/2026-11-10-external-followup-answers.md). Written from the lead's re-derivation, not from the
reviewer's scripts (which are not recorded, owner privacy rule).

Exact (SymPy / Fraction):
  R1  every rational and algebraic step of the cube-root cosine bound C* = 8(1+sqrt7)/3 (batch LE2, T0E'):
      R1a sqrt7 enclosure and C*, (C*/2pi)^3 enclosures; R1b regime t >= 8 (cap 2pi + 8/3 < 9; interior F(2) + 16/3 + 1 = C*;
      F' <= 0 algebra; low velocities 191/21 and 277/30 via the sine lower bounds); R1c regime 3 <= t <= 8 endpoint values;
      R1d t <= 3; R1e the band-length substitution identity; R1f the boundary/variation algebra of the IBP bounds;
      R1g the Taylor witness 119009/140625 and C* < 2 * (4/5)^(1/3) |I(4/5,0)|.
  Q1  two-orbital S/P model: B(k) = C0(-cos k I + 3Q), Q^2 = I, exp(izB) formula, Q = e^{ik}Q+ + e^{-ik}Q-, the conjugated
      kernel (Q24) and the singular values of the off-diagonal block; wrong propagation sign rejected.
  Q2  T0E threshold: b_LE(519) < 1 (rational), b_LE(518) > 1 (rational), and the four-site cycle returns at tau = 200 pi.
  Q3  finite open chain: the minimal escape path length d = 2(L+1) - |m+n| (brute-force path count on small chains).
FLOAT (labelled): the probability table of the quantum study and the C*-based improvements.
Exit status 0 iff every check passes.
Usage: SYMPY_GROUND_TYPES=python python3 -I numerics/review/followup_checks.py (env: numerics/census/requirements.txt)
"""
import sys
from fractions import Fraction as Fr
import sympy as sp

OK = []


def check(cid, ok, detail):
    OK.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}", flush=True)


s7 = sp.sqrt(7)
Cs = sp.Rational(8, 3) * (1 + s7)
# R1a: sqrt7 between rationals by squaring
lo7, hi7 = Fr(26457513110645905, 10**16), Fr(26457513110645906, 10**16)
check('R1a-sqrt7', lo7**2 < 7 < hi7**2, 'sqrt7 in (2.6457513110645905, 2.6457513110645906)')
Clo, Chi = Fr(8, 3) * (1 + lo7), Fr(8, 3) * (1 + hi7)
check('R1a-C', Fr(9722003496172, 10**12) < Clo and Chi < Fr(9722003496173, 10**12), f'C* in ({float(Clo):.13f}, {float(Chi):.13f})')
check('R1a-97/10', (Fr(211, 80))**2 < 7 and Fr(8, 3) * (1 + Fr(211, 80)) == Fr(97, 10), 'sqrt7 > 211/80 so C* > 97/10')
# pi enclosure by Machin with alternating remainders
def atan_bounds(x, n):
    s = Fr(0); terms = [(-1)**k * x**(2*k+1) / (2*k+1) for k in range(n)]
    s = sum(terms); nxt = x**(2*n+1) / (2*n+1)
    return (s, s + nxt) if n % 2 == 0 else (s - nxt, s)
a5 = atan_bounds(Fr(1, 5), 30); a239 = atan_bounds(Fr(1, 239), 30)
pilo, pihi = 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]
check('R1a-pi', Fr(314159265358979, 10**14) < pilo < pihi < Fr(314159265358980, 10**14), 'Machin enclosure of pi')
thr_lo = (Clo / (2 * pihi))**3; thr_hi = (Chi / (2 * pilo))**3
check('R1a-threshold', Fr(3704483917357, 10**12) < thr_lo and thr_hi < Fr(3704483917358, 10**12),
      f'(C*/2pi)^3 in ({float(thr_lo):.12f}, {float(thr_hi):.12f})')

# R1b, t >= 8
check('R1b-cap', 2 * pihi + Fr(8, 3) < 9 and Fr(2, 4) / (Fr(1, 2) * Fr(3, 2)) == Fr(2, 3), '2pi + 2 + 2/3 < 9')
D = sp.symbols('Delta', positive=True)
F = sp.Rational(8, 3) * sp.sqrt(2) * (sp.sqrt(D + sp.Rational(3, 2)) - sp.sqrt(D - sp.Rational(3, 2))) - 2 / D
check('R1b-F2', sp.simplify(F.subs(D, 2) + sp.Rational(16, 3) + 1 - Cs) == 0, 'F(2) + 16/3 + 1 = C*')
# F' <= -2 sqrt2 D^{-3/2} + 2 D^{-2} uses (1/sqrt(D-a) - 1/sqrt(D+a)) >= a D^{-3/2}; check that lower bound numerically exactly at rationals
ok = True
for Dv in [2, sp.Rational(5, 2), 3, 5, 10, 100]:
    lhs = 1 / sp.sqrt(Dv - sp.Rational(3, 2)) - 1 / sp.sqrt(Dv + sp.Rational(3, 2))
    ok &= bool(sp.N(lhs - sp.Rational(3, 2) * Dv**sp.Rational(-3, 2), 50) >= 0)
    ok &= bool(sp.N(sp.diff(F, D).subs(D, Dv), 50) <= 0)
check('R1b-Fdecr', ok, "rationalisation lower bound and F' <= 0 at sample Delta (50 digits)")
x = sp.Rational(6, 7)
check('R1b-sin67', x - x**3 / 6 == sp.Rational(258, 343) and sp.Rational(258, 343) > sp.Rational(3, 4), 'sin(6/7) >= 258/343 > 3/4')
y = sp.Rational(11, 10)
check('R1b-sin1110', y - y**3 / 6 == sp.Rational(5269, 6000) and sp.Rational(5269, 6000) > sp.Rational(7, 8), 'sin(11/10) >= 5269/6000 > 7/8')
check('R1b-H1', 4 * sp.Rational(6, 7) + sp.Rational(17, 3) == sp.Rational(191, 21) and Fr(191, 21) < Fr(97, 10), 'H1 <= 191/21')
check('R1b-H2', 4 * (sp.Rational(11, 10) - sp.Rational(1, 8)) + sp.Rational(16, 3) == sp.Rational(277, 30) and Fr(277, 30) < Fr(97, 10), 'H2 <= 277/30')
check('R1b-pi2', Fr(11, 10) < pilo / 2 and Fr(6, 7) < pilo / 2, '6/7 and 11/10 lie in [0, pi/2]')
# H1(1/2) = 2 arcsin(3/4)/(1/2) + 20/3 - 4/4
check('R1b-H1end', sp.Rational(20, 3) - 4 * sp.Rational(1, 4) == sp.Rational(17, 3), 'H1(1/2) = 4 arcsin(3/4) + 17/3')

# R1c, 3 <= t <= 8 (delta = 1/2), endpoint values with pi < 22/7, 3^(1/3) < 13/9
check('R1c-cbrt3', Fr(13, 9)**3 > 3 and Fr(22, 7) > pihi, '3^(1/3) < 13/9, pi < 22/7')
v31 = Fr(13, 9) * (Fr(22, 7) + Fr(32, 9)); v38 = 2 * (Fr(22, 7) + Fr(32, 24))
check('R1c-cap', v31 == Fr(5486, 567) and v38 == Fr(188, 21) and max(v31, v38) < Fr(97, 10), 'pi + 32/(3t): 5486/567, 188/21')
check('R1c-sin13', Fr(1, 3) - Fr(1, 3)**3 / 6 == Fr(53, 162) and Fr(53, 162) > Fr(1, 4), 'arcsin(1/4) <= 1/3')
v31 = Fr(13, 9) * (Fr(22, 7) + Fr(2, 3) + Fr(20, 9)); v38 = 2 * (Fr(22, 7) + Fr(2, 3) + Fr(20, 24))
check('R1c-mid', v31 == Fr(4940, 567) and v38 == Fr(65, 7) and max(v31, v38) < Fr(97, 10), 'pi + 2/3 + 20/(3t): 4940/567, 65/7')
check('R1c-tail', 8 - Fr(2, 1) / Fr(3, 2) == Fr(20, 3) and 16 - 4 == 12, 'tails 20/(3t) and 12/t')
v31 = Fr(13, 9) * (Fr(50, 21) + 4); v38 = 2 * (Fr(50, 21) + Fr(12, 8))
check('R1c-low', 2 * (Fr(6, 7) + Fr(1, 3)) == Fr(50, 21) and v31 == Fr(1742, 189) and v38 == Fr(163, 21) and max(v31, v38) < Fr(97, 10),
      'band 50/21 + 12/t: 1742/189, 163/21')
# R1d
check('R1d-small', Fr(44, 7) * Fr(13, 9) == Fr(572, 63) and Fr(572, 63) < Fr(97, 10), '2pi 3^(1/3) < 572/63')

# R1e band-length substitution: s = 1 - z tau^2 gives ds/sqrt(1-s^2) = tau dz / sqrt(z(2 - z tau^2))
z, tau = sp.symbols('z tau', positive=True)
sexpr = 1 - z * tau**2
check('R1e-subst', sp.simplify((1 - sexpr**2) - z * tau**2 * (2 - z * tau**2)) == 0, '1 - s^2 = z tau^2 (2 - z tau^2)')
# 2 - z tau^2 >= 9/8 on the band: 1 + s >= 1 + v - delta >= 1 + 1/2 - 3/8
check('R1e-98', 1 + Fr(1, 2) - Fr(3, 8) == Fr(9, 8) and Fr(3, 2) / 4 == Fr(3, 8), 'lower bound 9/8')
# 2 / sqrt(9/8) * 2 = 8 sqrt2 / 3
check('R1e-coef', sp.simplify(2 / sp.sqrt(sp.Rational(9, 8)) * 2 - 8 * sp.sqrt(2) / 3) == 0, '2 * (8/9)^(1/2) * 2 = 8 sqrt2/3')

# R1f IBP algebra: variation of 1/g and boundary terms
t, v, d = sp.symbols('t v delta', positive=True)
var_pos = 2 / (t * d) - 2 / (t * (v + 1))
check('R1f-3b', sp.simplify(2 / (t * d) + var_pos + 2 / (t * v) - (4 / (t * d) + 2 / (t * v * (v + 1)))) == 0, '(3b)')
check('R1f-3c', sp.simplify(2 / (t * v) + 2 / (t * (v - 1)) - 2 / (t * (v + 1)) - (2 / (t * (v - 1)) + 2 / (t * v * (v + 1)))) == 0, '(3c)')
check('R1f-5', sp.simplify(-2 / (t * (1 + v)) - 2 / (t * (1 - v)) + 4 / (t * (1 - v**2))) == 0, '(5) tail -4/(t(1-v^2))')
xi = sp.symbols('xi', real=True)
endpts = (sp.exp(sp.I * (-t + sp.pi * xi)) - sp.exp(sp.I * (-t - sp.pi * xi))) / (sp.I * t * v)
check('R1f-endpts', sp.expand(sp.simplify((endpts - 2 * sp.exp(-sp.I * t) * sp.sin(sp.pi * xi) / (t * v)).rewrite(sp.exp))) == 0,
      'combined endpoint term (exponential form)')
# 2.1: 2 arccos(1 - 4 tau^2) = 4 arcsin(sqrt2 tau); 4 sqrt2 arcsin(1/sqrt2)/(1/sqrt2)... = 2 pi
check('R1f-cap21', sp.simplify(sp.cos(2 * sp.asin(sp.sqrt(2) * tau)) - (1 - 4 * tau**2)) == 0 and
      sp.simplify(4 * sp.asin(1 / sp.sqrt(2)) / (1 / (2 * sp.sqrt(2))) / sp.sqrt(2) - 2 * sp.pi) == 0, 'cap term at tau = 1/2 is 2pi')

# R1g Taylor witness
zz = Fr(4, 25)
wit = 1 - zz + zz**2 / 4 - zz**3 / 36
check('R1g-witness', wit == Fr(119009, 140625), '1 - z + z^2/4 - z^3/36 at z = 4/25')
check('R1g-moments', sp.integrate(sp.cos(z)**4, (z, -sp.pi, sp.pi)) / (2 * sp.pi) == sp.Rational(3, 8) and
      sp.integrate(sp.cos(z)**6, (z, -sp.pi, sp.pi)) / (2 * sp.pi) == sp.Rational(5, 16), 'cos^4, cos^6 moments')
q = 2 * Fr(157, 50) * Fr(9283, 10000) * wit
check('R1g-factor2', Fr(9283, 10000)**3 < Fr(4, 5) and Fr(157, 50) < pilo and Chi < 2 * q, f'C* < 2q, q = {float(q):.12f}')

# Q1 two-orbital model
k, zt, C0 = sp.symbols('k z C0', real=True)
s1, s2, s3 = sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.Matrix([[1, 0], [0, -1]])
I2 = sp.eye(2)
Bk = sp.Matrix([[2 * C0 * sp.cos(k), 2 * sp.I * sp.Rational(3, 2) * C0 * sp.sin(k)],
                [-2 * sp.I * sp.Rational(3, 2) * C0 * sp.sin(k), -4 * C0 * sp.cos(k)]])  # beta = 0, C_s = C0, C_p = -2C0, C_sp = 3C0/2
Q = sp.cos(k) * s3 - sp.sin(k) * s2
check('Q1-B', sp.simplify(Bk - C0 * (-sp.cos(k) * I2 + 3 * Q)) == sp.zeros(2), 'B = C0(-cos k I + 3Q)')
check('Q1-Q2', sp.simplify(Q * Q - I2) == sp.zeros(2) and sp.simplify(Q.H - Q) == sp.zeros(2), 'Q^2 = I, Q Hermitian')
tauz = C0 * zt
E = sp.exp(-sp.I * tauz * sp.cos(k)) * (sp.cos(3 * tauz) * I2 + sp.I * sp.sin(3 * tauz) * Q)
check('Q1-ode', sp.simplify(-sp.I * sp.diff(E, zt) - Bk * E) == sp.zeros(2) and sp.simplify(E.subs(zt, 0) - I2) == sp.zeros(2),
      '-i dE/dz = B E, E(0) = I: E = exp(izB)')
Ewrong = sp.exp(sp.I * tauz * sp.cos(k)) * (sp.cos(3 * tauz) * I2 - sp.I * sp.sin(3 * tauz) * Q)
check('Q1-sign-control', sp.simplify(-sp.I * sp.diff(Ewrong, zt) - Bk * Ewrong) != sp.zeros(2), 'exp(-izB) rejected')
Qp, Qm = (s3 + sp.I * s2) / 2, (s3 - sp.I * s2) / 2
check('Q1-Qpm', sp.simplify(sp.exp(sp.I * k) * Qp + sp.exp(-sp.I * k) * Qm - Q).expand(complex=True).applyfunc(sp.simplify) == sp.zeros(2),
      'Q = e^{ik}Q+ + e^{-ik}Q-')
W = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
a, b = sp.symbols('a b')
check('Q1-W', sp.simplify(W.H * (a * Qp + b * Qm) * W - sp.Matrix([[0, b], [a, 0]])) == sp.zeros(2), "W*(aQ+ + bQ-)W = [[0,b],[a,0]]")
# the S/P limit with flat bands: C_s = -C_p = C_sp = C0 gives B = 2 C0 Q
Bflat = sp.Matrix([[2 * C0 * sp.cos(k), 2 * sp.I * C0 * sp.sin(k)], [-2 * sp.I * C0 * sp.sin(k), -2 * C0 * sp.cos(k)]])
check('Q1-flat', sp.simplify(Bflat - 2 * C0 * Q) == sp.zeros(2), 'flat-band control B = 2C0 Q')

# Q2 thresholds of the normalised T0E envelope b(s) = (24*2^(1/4) s^(-1/2) + 36*2^(1/6) s^(-1/3)) / (2pi)
def bLE_upper(s, r2_4, r2_6, sq, cb, pil):  # upper bound given upper bounds on 2^(1/4), 2^(1/6), lower bounds on sqrt s, cbrt s, pi
    return (24 * r2_4 / sq + 36 * r2_6 / cb) / (2 * pil)
r24u, r26u = Fr(118921, 100000), Fr(112247, 100000)
r24l, r26l = Fr(118920, 100000), Fr(112246, 100000)
ok = r24u**4 > 2 and r26u**6 > 2 and r24l**4 < 2 and r26l**6 < 2
sq519, cb519 = Fr(2278, 100), Fr(8036, 1000)
ok &= sq519**2 < 519 and cb519**3 < 519
check('Q2-519', ok and bLE_upper(519, r24u, r26u, sq519, cb519, pilo) < 1, f'b_LE(519) < {float(bLE_upper(519, r24u, r26u, sq519, cb519, pilo)):.6f}')
sq518, cb518 = Fr(22760, 1000), Fr(8034, 1000)
ok = sq518**2 > 518 and cb518**3 > 518
low518 = (24 * r24l / sq518 + 36 * r26l / cb518) / (2 * pihi)
check('Q2-518', ok and low518 > 1, f'b_LE(518) > {float(low518):.6f}')
# four-site cycle: eigenvalues of S + S* on Z_4 are 2, 0, -2, 0; exp(i tau lambda/2 * ...) at tau = 200 pi
ev = [2 * sp.cos(2 * sp.pi * j / 4) for j in range(4)]
check('Q2-cycle', all(sp.simplify(sp.exp(sp.I * 200 * sp.pi * e / 2) - 1) == 0 for e in ev), 'U = I on the 4-cycle at tau = 2 kappa t = 200 pi')

# Q3 open chain escape length by brute force: minimal walk length from m to n through a site outside [-L, L]
def min_escape(L, m, n):
    best = None
    for out in (L + 1, -(L + 1)):
        dd = abs(out - m) + abs(n - out)
        best = dd if best is None else min(best, dd)
    return best
ok = all(min_escape(L, m, n) == 2 * (L + 1) - abs(m + n) for L in range(1, 6) for m in range(-L, L + 1) for n in range(-L, L + 1))
check('Q3-escape', ok, 'd = 2(L+1) - |m+n| for all L <= 5')

# FLOAT table (labelled)
import mpmath as mp
mp.mp.dps = 30
bLE = lambda s: (24 * mp.mpf(2)**0.25 * s**-0.5 + 36 * mp.mpf(2)**(mp.mpf(1)/6) * s**(-mp.mpf(1)/3)) / (2 * mp.pi)
bC = lambda s: (8 * (1 + mp.sqrt(7)) / 3) / (2 * mp.pi) * s**(-mp.mpf(1)/3)
bL = lambda s: mp.mpf('0.7857468705') * s**(-mp.mpf(1)/3)
for s in [4, 100, 1000, 10000]:
    print(f"FLOAT tau={s}: probability bounds T0E {float(min(1, bLE(s))**2):.6g}  T0E' {float(min(1, bC(s))**2):.6g}  Landau {float(min(1, bL(s))**2):.6g}")
print(f"FLOAT T0E' amplitude coefficient C*/(2pi) = {float(bC(1)):.9f}; Landau/that = {float(bL(1)/bC(1)):.5f}")
print(f"RESULT {sum(OK)}/{len(OK)} PASS")
sys.exit(0 if all(OK) else 1)
