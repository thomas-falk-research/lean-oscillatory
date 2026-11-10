#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's independent checks of the external reviewer's 2026-11-10 results (answers: review/2026-11-10-external-results-answers.md).

Written from the mathematics, not from the reviewer's scripts. Exact (SymPy) unless marked FLOAT.
Result 1 (hand proof of S5.1'):
  P1  chain rule: with g_u = F_u(u, h(u)) (abstract smooth F, h), d^3/du^3 g_u equals the seven-term formula of the proof.
  P2  implicit derivatives at the A3 point: h_u = 0 and h_uu = -T/h0 from F_s(u, h(u)) + q = 0, so g_uuuu(0) = Q - 3T^2/h0
      (generic quartic jet, q = 0; the r = 2 case of the reduced-jet identity is check X2 of dossier_checks.py).
  P3  the quotient identity for r'' = (K/H)'' and the polynomial U = 1 + R2 + 2R1 + R0.
  P4  the fourth-order outer constant: 2 eta/lambda + 2*18 eta^(-1/3) at eta = lambda^(3/4) equals 38 lambda^(-1/4);
      38 = 5*2^3 - 2 (the S1.k constant at k = 4); 38 * 64 = 2432.
  P5  the non-stable coupled example F = u^4 + (1+u)s^2/2: reduced phase u^4 - q^2/(2(1+u)), g_uuuu = 24 - 12q^2/(1+u)^5,
      which vanishes at (0, sqrt 2): a reduced fourth-derivative bound uniform in all q is false, so the split at q0 is needed.
Result 2 (C^2-only remainder fails in two transverse dimensions):
  Q1  the transition integrals: int_{1/t}^{2/t} S(tq-1)/q dq = int_1^2 S(z-1)/z dz and int_{1/2}^1 (1-S(2q-1))/q dq =
      log 2 - int_1^2 S(z-1)/z dz, so int w_t/q = log(t/2) for t >= 4 (exact, for an abstract S).
  Q2  FLOAT: the C^2 Euclidean budget of A_t sampled on the support for t in {4, 64, 1024, 65536} stays below 16048.
Exit status 0 iff every check passes. Usage: SYMPY_GROUND_TYPES=python python3 -I numerics/review/cusp_proof_checks.py
"""
import sys

import mpmath as mp
import sympy as sp

OK = []


def check(cid, ok, detail):
    OK.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}", flush=True)


u, s, q = sp.symbols("u s q", real=True)
F = sp.Function("F")
h = sp.Function("h")(u)
Fu = sp.diff(F(u, s), u)
gu = Fu.subs(s, h)
lhs = sp.diff(gu, u, 3)


def P(nu, ns):
    return sp.diff(F(u, s), *([u] * nu + [s] * ns)).subs(s, h)


hu, huu, huuu = sp.diff(h, u), sp.diff(h, u, 2), sp.diff(h, u, 3)
rhs = (P(4, 0) + 3 * P(3, 1) * hu + 3 * P(2, 2) * hu**2 + P(1, 3) * hu**3 + 3 * P(2, 1) * huu
       + 3 * P(1, 2) * hu * huu + P(1, 1) * huuu)
check("P1", sp.simplify(sp.expand(lhs.doit() - rhs.doit())) == 0, "d^3/du^3 F_u(u,h(u)) = the proof's seven-term g_uuuu formula")

h0, T, Q, c3, c4, c5, c6, c7 = sp.symbols("h0 T Q c3 c4 c5 c6 c7", nonzero=True)
Fj = h0 * s**2 / 2 + T * u**2 * s / 2 + Q * u**4 / 24 + c3 * s**3 + c4 * u * s**2 + c5 * u**3 * s + c6 * u**2 * s**2 + c7 * s**4
A1_, A2_, A3_ = sp.symbols("A1_ A2_ A3_")
hs = A1_ * u + A2_ * u**2 + A3_ * u**3
eq = sp.expand(sp.diff(Fj, s).subs(s, hs))
sol = sp.solve([eq.coeff(u, k) for k in (1, 2, 3)], [A1_, A2_, A3_], dict=True)[0]
g = sp.expand(Fj.subs(s, hs.subs(sol)))
check("P2", sol[A1_] == 0 and sp.simplify(2 * sol[A2_] + T / h0) == 0 and sp.simplify(24 * g.coeff(u, 4) - (Q - 3 * T**2 / h0)) == 0,
      f"h_u(0) = {sol[A1_]}, h_uu(0) = {sp.simplify(2*sol[A2_])}, g_uuuu(0) = Q - 3T^2/h0 (generic quartic jet incl. s^3, u s^2, u^3 s, u^2 s^2, s^4)")

x = sp.symbols("x")
K, H = sp.Function("K")(x), sp.Function("H")(x)
r2 = sp.diff(K / H, x, 2)
form = sp.diff(K, x, 2) / H - 2 * sp.diff(K, x) * sp.diff(H, x) / H**2 - K * sp.diff(H, x, 2) / H**2 + 2 * K * sp.diff(H, x)**2 / H**3
rho = sp.symbols("rho", positive=True)
R0, R1, R2 = rho, rho / 2 + rho**2 / 2, rho / 3 + rho**2 / 2 + rho**2 / 3 + rho**3 / 2
U = sp.expand(1 + R2 + 2 * R1 + R0)
check("P3", sp.simplify(r2 - form) == 0 and sp.expand(U - (1 + sp.Rational(7, 3) * rho + sp.Rational(11, 6) * rho**2 + rho**3 / 2)) == 0,
      f"(K/H)'' = K''/H - 2K'H'/H^2 - KH''/H^2 + 2K H'^2/H^3; with |K^(j)| <= D/(j+1), |H| >= mu: U = {U}")

lam = sp.symbols("lambda", positive=True)
eta = lam ** sp.Rational(3, 4)
tot = sp.simplify(2 * eta / lam + 36 * eta ** sp.Rational(-1, 3))
check("P4", sp.simplify(tot - 38 * lam ** sp.Rational(-1, 4)) == 0 and 5 * 2**3 - 2 == 38 and 38 * 64 == 2432,
      "2 eta/lambda + 36 eta^(-1/3) = 38 lambda^(-1/4) at eta = lambda^(3/4); 38 = c_4 of S1.k; 38*64 = 2432")

Fe = u**4 + (1 + u) * s**2 / 2
hsol = sp.solve(sp.diff(Fe, s) + q, s)[0]
ge = sp.simplify(Fe.subs(s, hsol) + q * hsol)
g4 = sp.simplify(sp.diff(ge, u, 4))
check("P5", sp.simplify(ge - (u**4 - q**2 / (2 * (1 + u)))) == 0 and sp.simplify(g4 - (24 - 12 * q**2 / (1 + u)**5)) == 0
      and g4.subs({u: 0, q: sp.sqrt(2)}) == 0,
      f"F = u^4 + (1+u)s^2/2 (A3, not stable: T = 0): g = u^4 - q^2/(2(1+u)), g_uuuu = {g4}, zero at (u,q) = (0, sqrt 2)")

z, t = sp.symbols("z t", positive=True)
Sf = sp.Function("S")
# change of variables, checked by differentiating the substitution maps
qq = sp.symbols("qq", positive=True)
sub_inner = sp.simplify(sp.diff(t * qq, qq) / (t * qq) - 1 / qq) == 0   # z = t q: dz/z = dq/q
sub_outer = sp.simplify(sp.diff(2 * qq, qq) / (2 * qq) - 1 / qq) == 0   # z = 2 q: dz/z = dq/q
plateau = sp.simplify(sp.integrate(1 / qq, (qq, 2 / t, sp.Rational(1, 2))) - sp.log(t / 4))
total = sp.simplify(sp.log(t / 4) + sp.log(2) - sp.log(t / 2))
check("Q1", sub_inner and sub_outer and plateau == 0 and total == 0,
      "z = tq and z = 2q preserve dq/q; plateau [2/t, 1/2] gives log(t/4); C_S + log(t/4) + (log 2 - C_S) = log(t/2), "
      "for any S with S = 0 on (-inf, 0], 1 on [1, inf) and t >= 4 (transition intervals disjoint)")

mp.mp.dps = 30


def fS(xv):
    return mp.e ** (-1 / xv) if xv > 0 else mp.mpf(0)


def S(xv):
    if xv <= 0:
        return mp.mpf(0)
    if xv >= 1:
        return mp.mpf(1)
    return fS(xv) / (fS(xv) + fS(1 - xv))


worst = []
for tv in (4, 64, 1024, 65536):
    tv = mp.mpf(tv)

    def hfun(qv):
        w = S(tv * qv - 1) * (1 - S(2 * qv - 1))
        return mp.e ** (-1j * tv * qv / 2) * w / qv / tv**2

    m2 = mp.mpf(0)
    pts = [mp.mpf(1) / tv * (1 + k / mp.mpf(40)) for k in range(41)] + [mp.mpf(2) / tv + (mp.mpf(1) - 2 / tv) * k / 200 for k in range(201)]
    for qv in pts:
        if qv >= 1:
            continue
        d1 = mp.diff(hfun, qv, 1)
        d2 = mp.diff(hfun, qv, 2)
        m2 = max(m2, 2 * abs(d1) + 4 * qv * abs(d2))  # ||D^2 A||_E <= 2|h'| + 4 q |h''|
    worst.append((int(tv), float(m2)))
check("Q2", all(m < 16048 for _, m in worst),
      "FLOAT sampled sup of 2|h'| + 4q|h''| (bounds the Euclidean Hessian norm of A_t): "
      + ", ".join(f"t={a}: {b:.4g}" for a, b in worst) + " (proof's bound 16048)")

print(f"OVERALL {'PASS' if all(OK) else 'FAIL'} {sum(OK)}/{len(OK)}")
sys.exit(0 if all(OK) else 1)
