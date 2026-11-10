#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Independent exact checks of the external research audit of 2026-11-10 (answers: review/2026-11-10-external-audit-answers.md).

The audit's own script (not recorded, owner privacy rule) checks its polynomial identities. This script checks what
those identities imply for OscInt's dimension lift (ROADMAP I3b):
  A1  the audit's phase has full Hessian of rank 2 (corank 1) at 0, so 0 is not a corank-2 (D4-type) point of the 3D
      phase, although the restriction to z = 0 has zero Hessian and a nondegenerate cubic;
  A2  eliminating the nondegenerate direction (dPhi/dz = 0) gives the reduced phase (x - 1/2)(x + 3y^2)^2, whose
      Hessian at 0 is rank 1 (Schur complement 0 - 1*1/1 = -1 in x) and whose critical set is the curve x = -3y^2:
      the reduced phase is not D4, so the audit's example violates the corrected hypothesis, as it should;
  A3  the intrinsic criterion (full Hessian of corank exactly 2, the cubic D^3 Phi(0) restricted to ker H
      nondegenerate) is invariant: it agrees with "the reduced phase is D4" on a coupled positive control
      Phi_+ = (z + xy)^2/2 + x^3 - 3xy^2 + z x^2 (reduced cubic x^3 - 3xy^2, isolated critical point), and rejects
      the audit's phase;
  A4  the reduced cubic equals D^3 Phi restricted to ker H in general (r = 1 transverse variable, symbolic jets):
      the transverse critical curve is s(u) = O(|u|^2), so elimination changes only terms of order >= 4.
Exit status 0 iff every check passes. SymPy only; no Lean, no analytic theorem is checked here.
Usage: SYMPY_GROUND_TYPES=python python3 -I numerics/review/audit_checks.py
"""
import sys

import sympy as sp

OK = []


def check(cid, ok, detail):
    OK.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}", flush=True)


x, y, z = sp.symbols("x y z", real=True)
V = (x, y, z)
Phi = sp.Rational(1, 2) * (z + x) ** 2 + (x - sp.Rational(1, 2)) * (x + 3 * y**2) ** 2
H = sp.hessian(Phi, V).subs({x: 0, y: 0, z: 0})
ker = H.nullspace()
restr = sp.hessian(Phi.subs(z, 0), (x, y)).subs({x: 0, y: 0})
check("A1", H.rank() == 2 and len(ker) == 1 and restr == sp.zeros(2) and H[2, 2] == 1,
      f"full Hessian at 0 = {H.tolist()}, rank {H.rank()}, kernel {[list(k) for k in ker]}; restriction to z = 0 has Hessian 0: "
      "the 3D point has corank 1, not 2")

g = sp.expand(Phi.subs(z, -x))  # dPhi/dz = z + x = 0
gH = sp.hessian(g, (x, y)).subs({x: 0, y: 0})
crit = [sp.simplify(sp.diff(g, v).subs(x, -3 * y**2)) for v in (x, y)]
check("A2", sp.expand(g - (x - sp.Rational(1, 2)) * (x + 3 * y**2) ** 2) == 0 and gH == sp.diag(-1, 0) and crit == [0, 0],
      f"reduced phase g = (x - 1/2)(x + 3y^2)^2, Hessian at 0 = {gH.tolist()} (rank 1, not D4), critical on x = -3y^2")


def intrinsic_D4(F, vars_):
    """Corank of D^2F(0) is exactly 2, and D^3F(0) restricted to the 2D kernel is a binary cubic with nonzero discriminant."""
    pt = {v: 0 for v in vars_}
    Hm = sp.hessian(F, vars_).subs(pt)
    kb = Hm.nullspace()
    if len(kb) != 2:
        return False, f"corank {len(kb)}"
    a, b = sp.symbols("a b")
    dirv = a * kb[0] + b * kb[1]
    s = sp.symbols("s")
    cubic = sp.expand(sp.diff(F.subs({v: s * dirv[i] for i, v in enumerate(vars_)}), s, 3).subs(s, 0) / 6)
    P = sp.Poly(cubic, a, b)
    c = [P.coeff_monomial(a**3), P.coeff_monomial(a**2 * b), P.coeff_monomial(a * b**2), P.coeff_monomial(b**3)]
    disc = c[1]**2 * c[2]**2 - 4 * c[0] * c[2]**3 - 4 * c[1]**3 * c[3] - 27 * c[0]**2 * c[3]**2 + 18 * c[0] * c[1] * c[2] * c[3]
    return disc != 0, f"corank 2, cubic on kernel {cubic}, discriminant {disc}"


Phip = (z + x * y) ** 2 / 2 + x**3 - 3 * x * y**2 + z * x**2
zc = sp.solve(sp.diff(Phip, z), z)[0]
gp = sp.expand(Phip.subs(z, zc))
gp3 = sum(t for t in sp.Add.make_args(gp) if sp.Poly(t, x, y).total_degree() == 3)
okp, dp = intrinsic_D4(Phip, V)
oka, da = intrinsic_D4(Phi, V)
check("A3", okp and not oka and sp.hessian(gp, (x, y)).subs({x: 0, y: 0}) == sp.zeros(2) and sp.expand(gp3 - (x**3 - 3 * x * y**2)) == 0,
      f"positive control Phi_+: {dp}; reduced phase cubic {gp3} (D4). Audit phase: {da} (rejected)")

# A4: one transverse variable s, two kernel variables (u1, u2); generic symbolic jet with F_s = h s + O(2), F_su(0) = 0
s, u1, u2, h = sp.symbols("s u1 u2 h", nonzero=True)
cs = sp.symbols("k0:20")
mons3 = [u1**3, u1**2 * u2, u1 * u2**2, u2**3, s * u1**2, s * u1 * u2, s * u2**2, s**2 * u1, s**2 * u2, s**3]
mons4 = [u1**4, u1**3 * u2, u1**2 * u2**2, u1 * u2**3, u2**4, s * u1**3]
F = h * s**2 / 2 + sum(c * m for c, m in zip(cs, mons3 + mons4))
e = sp.symbols("e")
# s(u) solves F_s = 0; to the order that matters, s = O(e^2) along u -> e u
A_, B_, C_ = sp.symbols("A_ B_ C_")
sc = A_ * u1**2 + B_ * u1 * u2 + C_ * u2**2
eq = sp.expand(sp.diff(F, s).subs(s, sc))
sol = sp.solve([sp.Poly(eq, u1, u2).coeff_monomial(m) for m in (u1**2, u1 * u2, u2**2)], [A_, B_, C_], dict=True)[0]
gred = sp.expand(F.subs(s, sc.subs(sol)).subs({u1: e * u1, u2: e * u2}))
check("A4", sp.expand(gred.coeff(e, 3) - sum(c * m for c, m in zip(cs[:4], mons3[:4]))) == 0,
      "with s(u) = O(|u|^2) from F_s = 0, the cubic part of the reduced phase is exactly D^3F(0) on ker H (u-cubic terms); "
      "mixed terms s*u^2 enter only at order 4")

print(f"OVERALL {'PASS' if all(OK) else 'FAIL'} {sum(OK)}/{len(OK)}")
sys.exit(0 if all(OK) else 1)
