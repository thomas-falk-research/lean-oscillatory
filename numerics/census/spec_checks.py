#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Exact checks behind the census specification (docs/prereg/2026-11-09-CENSUS-spec.md).

Tooling, not evidence for a Lean theorem. Every check is an identity or an exact evaluation in SymPy (no floating
point decides anything): the classification formulas of spec section 2, the admissible outer functions of section 1,
the corpus models' formulas from their physical definitions and their smoothness/gap facts (section 3), and the
expected classification of the controls (section 5). It does not search the torus and classifies no corpus model
beyond the points named in section 5 (square lattice and QWZ m = 3), whose types were known before this script
(docs/prereg/2026-11-08-P1-classify.md, docs/design/vector-amplitudes.md section 6).

Usage (from the repository root, in the environment of numerics/census/requirements.txt):
  SYMPY_GROUND_TYPES=python python3 -I numerics/census/spec_checks.py
Prints one line per check, `CHECK <id> PASS|FAIL <detail>`, then `SUMMARY <passed>/<total>`, and `ALL_CHECKS_PASS`
only if every check passed. Exit status 0 iff every check passed; 2 if the environment is not the pinned one.
"""
import os
import platform
import subprocess
import sys

import mpmath
import sympy as sp

RESULTS = []


def check(cid, ok, detail=""):
    RESULTS.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}".rstrip(), flush=True)


_X = sp.Symbol("_x")


def is_zero(e):
    """Exact zero test for an algebraic number given as a SymPy expression."""
    e = sp.radsimp(sp.simplify(e))
    if e == 0:
        return True
    return sp.minimal_polynomial(e, _X) == _X


def jets(f, v):
    """Hessian, third and fourth derivative tensors of f in the variables v (lists, symmetric)."""
    H = [[sp.diff(f, a, b) for b in v] for a in v]
    T = [[[sp.diff(f, a, b, c) for c in v] for b in v] for a in v]
    Q = [[[[sp.diff(f, a, b, c, d) for d in v] for c in v] for b in v] for a in v]
    return H, T, Q


def at(J, pt):
    return [at(x, pt) for x in J] if isinstance(J, list) else sp.simplify(J.subs(pt))


def contract(t, *vs):
    if not vs:
        return t
    return sum(vs[0][i] * contract(t[i], *vs[1:]) for i in range(2))


def kernels(H):
    p, q, r = H[0][0], H[0][1], H[1][1]
    return (q, -p), (r, -q)


def rank1_invariants(H, T, Q):
    """(g3 for both kernel vectors, g4) at a rank-1 point, spec section 2.2 (w chosen with H[w,w] != 0)."""
    va, vb = kernels(H)
    v = va if not (is_zero(va[0]) and is_zero(va[1])) else vb
    w = None
    for cand in ((1, 0), (0, 1), (1, 1)):
        if not is_zero(contract(H, cand, cand)):
            w = cand
            break
    g3a, g3b = contract(T, va, va, va), contract(T, vb, vb, vb)
    g4 = contract(Q, v, v, v, v) - 3 * contract(T, v, v, w) ** 2 / contract(H, w, w)
    return sp.simplify(g3a), sp.simplify(g3b), sp.simplify(g4), v, w


def disc_cubic(T):
    """Discriminant of the binary cubic C(k) = T[k,k,k] = a k1^3 + b k1^2 k2 + c k1 k2^2 + d k2^3."""
    a, b, c, d = T[0][0][0], 3 * T[0][0][1], 3 * T[0][1][1], T[1][1][1]
    return sp.simplify(b**2 * c**2 - 4 * a * c**3 - 4 * b**3 * d - 27 * a**2 * d**2 + 18 * a * b * c * d), (a, b, c, d)


def cubic_root_structure(coeffs):
    """'zero', 'triple', 'double' or 'distinct' for the projective roots of the binary cubic."""
    a, b, c, d = coeffs
    k = sp.Symbol("_k")
    if all(is_zero(x) for x in coeffs):
        return "zero"
    # dehomogenise in a direction that is not a root: use k2 = 1 if d or c or b or a gives degree 3, else swap
    p = sp.Poly(a * k**3 + b * k**2 + c * k + d, k)
    if p.degree() < 3:  # a root at infinity (k2 = 0): swap roles
        p = sp.Poly(d * k**3 + c * k**2 + b * k + a, k)
    if p.degree() < 3:  # roots at both 0 and infinity: count directly
        return "double" if p.degree() >= 1 else "triple"
    sqf = sp.sqf_list(p)[1]
    mult = sorted(m for _, m in sqf for _ in range(sp.Poly(_, k).degree()))
    return {(1, 1, 1): "distinct", (1, 2): "double", (3,): "triple"}[tuple(mult)]


def env_record():
    print(f"# python {platform.python_version()} ({platform.python_implementation()}), sympy {sp.__version__}, "
          f"mpmath {mpmath.__version__}, SYMPY_GROUND_TYPES={os.environ.get('SYMPY_GROUND_TYPES')}, "
          f"ground types in use: {sp.polys.domains.GROUND_TYPES if hasattr(sp.polys.domains, 'GROUND_TYPES') else '?'}")
    print(f"# platform {platform.platform()}, machine {platform.machine()}")
    try:
        head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], capture_output=True,
                               text=True, check=True).stdout.strip()
        print(f"# git HEAD {head}, tracked files modified: {'yes' if dirty else 'no'}")
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"# git state unavailable: {e}")
    if sp.__version__ != "1.14.0" or mpmath.__version__ != "1.3.0":
        print("ENVIRONMENT NOT PINNED (numerics/census/requirements.txt)")
        sys.exit(2)


def main():
    env_record()
    k1, k2 = sp.symbols("k1 k2", real=True)
    K = [k1, k2]
    c1, c2, s1, s2 = sp.cos(k1), sp.cos(k2), sp.sin(k1), sp.sin(k2)

    # ---------------- Section 2: classification formulas ----------------
    u, s, h = sp.Symbol("u"), sp.Symbol("s"), sp.Symbol("h", nonzero=True)
    names = ["a30", "a21", "a12", "a03", "a40", "a31", "a22", "a13", "a04"]
    A = dict(zip(names, sp.symbols(names)))
    phi = h * s**2 / 2 + sum(A[n] * u**int(n[1]) * s**int(n[2]) / (sp.factorial(int(n[1])) * sp.factorial(int(n[2])))
                             for n in names)
    b1, b2, b3 = sp.symbols("b1 b2 b3")
    S_ = b1 * u + b2 * u**2 + b3 * u**3
    eqs = sp.expand(sp.diff(phi, s).subs(s, S_))
    sol = sp.solve([eqs.coeff(u, j) for j in (1, 2, 3)], [b1, b2, b3], dict=True)[0]
    g = sp.series(phi.subs(s, S_.subs(sol)), u, 0, 5).removeO()
    check("R1", sp.simplify(6 * g.coeff(u, 3) - A["a30"]) == 0
          and sp.simplify(24 * g.coeff(u, 4) - (A["a40"] - 3 * A["a21"] ** 2 / h)) == 0,
          "splitting lemma: reduced function g(u) = a30 u^3/6 + (a40 - 3 a21^2/h) u^4/24 + O(u^5)")

    p, q, r = sp.symbols("p q r")
    Hs = [[p, q], [q, r]]
    va, vb = kernels(Hs)
    det = p * r - q**2
    Hva = [sp.expand(contract(Hs[i], va)) for i in range(2)]
    Hvb = [sp.expand(contract(Hs[i], vb)) for i in range(2)]
    check("R2", Hva == [0, sp.expand(-det)] and Hvb == [sp.expand(det), 0]
          and sp.expand(va[0] * vb[1] - va[1] * vb[0] - det) == 0
          and sp.solve([va[0], va[1], vb[0], vb[1]], [p, q, r], dict=True) == [{p: 0, q: 0, r: 0}],
          "H(q,-p) = (0,-det H), H(r,-q) = (det H, 0), (q,-p) x (r,-q) = det H: where det H = 0 both lie in ker H "
          "and are parallel; both vanish only if H = 0, so at a rank-1 point g3 = 0 iff T[va,va,va] = T[vb,vb,vb] = 0")

    t = {(i, j, k): sp.Symbol(f"t{''.join(sorted(str(x) for x in (i, j, k)))}") for i in range(2) for j in range(2)
         for k in range(2)}
    Tsym = [[[t[(i, j, k)] for k in range(2)] for j in range(2)] for i in range(2)]
    lam = sp.Symbol("lam")
    # basis with v = e1 kernel, H[w,w] = h for w = e2 + lam e1; T[v,v,w] changes by lam T[v,v,v]
    diffT = sp.expand(contract(Tsym, (1, 0), (1, 0), (lam, 1)) - contract(Tsym, (1, 0), (1, 0), (0, 1)))
    check("R3", sp.expand(diffT - lam * Tsym[0][0][0]) == 0,
          "T[v,v,w+lam v] - T[v,v,w] = lam T[v,v,v]: g4 independent of w when g3 = 0 (H[w+lam v] = H[w])")

    # ---------------- Section 1: admissible outer functions ----------------
    x = sp.Symbol("x")
    outer = {"id": x, "sqrt": sp.sqrt(x), "arccos": sp.acos(x), "arcsin": sp.asin(x), "2asin(sqrt)": 2 * sp.asin(sp.sqrt(x))}
    for name, G in outer.items():
        G1 = sp.diff(G, x)
        R = sp.simplify(G1**2)
        ok = R.is_rational_function(x) and not is_zero(R)
        rho = sp.Integer(1)
        for m in range(2, 7):
            rho = sp.simplify(sp.diff(rho, x) + rho * sp.diff(R, x) / (2 * R))
            ok = ok and sp.simplify(sp.diff(G, x, m) - rho * G1) == 0 and rho.is_rational_function(x)
        check(f"A1[{name}]", ok, f"(G')^2 = {R}; G^(m) = rho_m G' with rho_m rational, m = 2..6")

    # ---------------- Section 3: model formulas from their definitions ----------------
    z1, z2, m_ = sp.symbols("z1 z2 m")
    C1, C2 = (z1 + 1 / z1) / 2, (z2 + 1 / z2) / 2
    S1, S2 = (z1 - 1 / z1) / (2 * sp.I), (z2 - 1 / z2) / (2 * sp.I)
    zero_rat = lambda e: sp.simplify(sp.together(sp.expand(e))) == 0

    check("M-QWZ", zero_rat(S1**2 + S2**2 + (m_ + C1 + C2) ** 2 - (2 + m_**2 + 2 * m_ * (C1 + C2) + 2 * C1 * C2)),
          "|d|^2 for d = (sin k1, sin k2, m + cos k1 + cos k2) equals 2 + m^2 + 2m(c1 + c2) + 2 c1 c2")
    sx, sy, sz = sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.Matrix([[1, 0], [0, -1]])
    Hq = S1 * sx + S2 * sy + (m_ + C1 + C2) * sz
    check("M-QWZ-H2", (Hq * Hq - (S1**2 + S2**2 + (m_ + C1 + C2) ** 2) * sp.eye(2)).applyfunc(
        lambda e: sp.simplify(sp.together(sp.expand(e)))) == sp.zeros(2), "H(k)^2 = |d(k)|^2 Id, bands +-|d|")
    al = sp.Rational(3, 5)
    Pa = 1 + al**2 + 9 + 6 * (C1 + C2) + 2 * C1 * C2 + (1 - al**2) * C2**2
    check("M-aQWZ", zero_rat(S1**2 + al**2 * S2**2 + (3 + C1 + C2) ** 2 - Pa),
          "|d|^2 for d = (sin k1, (3/5) sin k2, 3 + c1 + c2) equals 34/25 + 9 + 6(c1+c2) + 2c1c2 + (16/25) c2^2")
    stencil = sp.Rational(1, 6) * (4 * (z1 + 1 / z1 + z2 + 1 / z2) + (z1 * z2 + z1 / z2 + z2 / z1 + 1 / (z1 * z2)) - 20)
    check("M-FD9", zero_rat(stencil - sp.Rational(1, 6) * (8 * (C1 + C2) + 4 * C1 * C2 - 20)),
          "9-point stencil (1/6)[4(N+S+E+W) + (NE+NW+SE+SW) - 20] has symbol (1/6)(8(c1+c2) + 4c1c2 - 20)")
    a1_, a2_ = sp.symbols("a1 a2")
    fd9 = 20 - 8 * (C1 + C2) - 4 * C1 * C2
    check("M-FD9-NS", zero_rat(fd9 - (12 * (1 - C1) + 12 * (1 - C2) - 4 * (1 - C1) * (1 - C2)))
          and sp.expand((12 * a1_ + 12 * a2_ - 4 * a1_ * a2_) - (4 * a1_ + 12 * a2_) - 4 * a1_ * (2 - a2_)) == 0,
          "20 - 8(c1+c2) - 4c1c2 = 12a1 + 12a2 - 4a1a2 (a_i = 1 - c_i in [0,2]) = 4a1 + 12a2 + 4a1(2 - a2) "
          ">= 4a1 + 12a2 >= 0, zero only at a1 = a2 = 0, i.e. k = (0,0)")
    gam = sp.Rational(-3, 10)
    tt = sp.Symbol("t", positive=True)
    eps = -2 * tt * (C1 + C2) - 4 * gam * tt * C1 * C2
    check("M-SQNNN", zero_rat(eps / (-2 * tt) - (C1 + C2 - sp.Rational(3, 5) * C1 * C2)),
          "t-t' band -2t(c1+c2) - 4t'c1c2 with t'/t = -3/10 is -2t (c1 + c2 - (3/5) c1 c2)")
    # honeycomb: a1 = (1,0), a2 = (1/2, sqrt3/2); B site at delta1; nearest neighbours delta1, delta1-a1, delta1-a2
    a1v, a2v = sp.Matrix([1, 0]), sp.Matrix([sp.Rational(1, 2), sp.sqrt(3) / 2])
    d1 = sp.Matrix([sp.Rational(1, 2), sp.sqrt(3) / 6])
    nn = [d1, d1 - a1v, d1 - a2v]
    dist2 = sorted({sp.nsimplify(sp.simplify((d1 + i * a1v + j * a2v).dot(d1 + i * a1v + j * a2v)))
                    for i in range(-3, 4) for j in range(-3, 4)})
    nn_ok = all(sp.simplify(v.dot(v) - dist2[0]) == 0 for v in nn) and sum(
        1 for i in range(-3, 4) for j in range(-3, 4)
        if sp.simplify((d1 + i * a1v + j * a2v).dot(d1 + i * a1v + j * a2v) - dist2[0]) == 0) == 3
    f = 1 + 1 / z1 + 1 / z2  # e^{-i k.delta1} f(k), with k.a1 = k1, k.a2 = k2
    fb = 1 + z1 + z2
    check("M-GRAPHENE", nn_ok and zero_rat(f * fb - (3 + 2 * C1 + 2 * C2 + 2 * (z1 / z2 + z2 / z1) / 2)),
          f"exactly three nearest B sites at squared distance {dist2[0]}; |f|^2 = 3 + 2c1 + 2c2 + 2cos(k1 - k2)")
    # Castro Neto et al., Rev. Mod. Phys. 81 (2009), eq. (6): f = 2cos(sqrt3 ky a) + 4cos(sqrt3 ky a/2)cos(3 kx a/2),
    # lattice vectors a1 = (a/2)(3, sqrt3), a2 = (a/2)(3, -sqrt3); claim: f = 2cos(k.a1) + 2cos(k.a2) + 2cos(k.(a1-a2))
    kx, ky = sp.symbols("kx ky", real=True)
    a1c, a2c = (sp.Rational(3, 2), sp.sqrt(3) / 2), (sp.Rational(3, 2), -sp.sqrt(3) / 2)  # a = 1
    dot = lambda v: kx * v[0] + ky * v[1]
    fcn = 2 * sp.cos(sp.sqrt(3) * ky) + 4 * sp.cos(sp.sqrt(3) * ky / 2) * sp.cos(3 * kx / 2)
    fours = 2 * sp.cos(dot(a1c)) + 2 * sp.cos(dot(a2c)) + 2 * sp.cos(dot((a1c[0] - a2c[0], a1c[1] - a2c[1])))
    check("M-GRAPHENE-CN", sp.simplify(sp.expand_trig(sp.expand(fcn - fours))) == 0,
          "Castro Neto et al. eq. (6) f equals 2cos(k.a1) + 2cos(k.a2) + 2cos(k.(a1-a2)), i.e. "
          "2c1 + 2c2 + 2cos(k1 - k2) in k_i = k.a_i: E = +-t sqrt(3 + f) at t' = 0 is M05")
    Dl, tt_, fr, fi = sp.symbols("Delta t f_r f_i", real=True)
    Hs2 = sp.Matrix([[Dl, tt_ * (fr + sp.I * fi)], [tt_ * (fr - sp.I * fi), -Dl]])
    ev = Hs2.eigenvals()
    check("M-hBN", set(sp.simplify(e**2 - (Dl**2 + tt_**2 * (fr**2 + fi**2))) for e in ev) == {0} and len(ev) == 2,
          "staggered sublattice potential +-Delta: eigenvalues of [[Delta, t f], [t conj f, -Delta]] are "
          "+-sqrt(Delta^2 + t^2 |f|^2) (M06 with Delta/t = 1/2)")
    king = 8 - 2 * (C1 + C2) - 2 * ((z1 * z2 + 1 / (z1 * z2)) / 2) - 2 * ((z1 / z2 + z2 / z1) / 2)
    check("M-KING", zero_rat(king - (8 - 2 * (C1 + C2 + 2 * C1 * C2))),
          "King's graph symbol 8 - 2cos k1 - 2cos k2 - 2cos(k1+k2) - 2cos(k1-k2) = 8 - 2(c1 + c2 + 2 c1 c2): "
          "the t-t' family c1 + c2 + 2g c1 c2 at g = 1 (M18)")
    check("M-FD9-TT", zero_rat(sp.Rational(1, 6) * (20 - 8 * (C1 + C2) - 4 * C1 * C2)
                               - (sp.Rational(10, 3) - sp.Rational(4, 3) * (C1 + C2 + C1 * C2 / 2))),
          "the 9-point symbol (1/6)(20 - 8(c1+c2) - 4c1c2) = 10/3 - (4/3)(c1 + c2 + (1/2) c1 c2): the t-t' family at "
          "g = 1/4 up to an affine map (same point types)")
    Sq, vq = sp.Symbol("S", positive=True), sp.Symbol("vq", nonnegative=True)
    check("M-YEE-ARCCOS", sp.simplify(sp.cos(2 * sp.asin(sp.sqrt(vq))) - (1 - 2 * vq)) == 0
          and zero_rat((1 - 2 * Sq**2 * (2 - C1 - C2) / 2) - (1 - 2 * Sq**2 + Sq**2 * (C1 + C2))),
          "Yee: cos(Psi) = 1 - 2v = 1 - 2S^2 + S^2 (c1 + c2), i.e. Psi = arccos(1 - 2S^2 + S^2(c1 + c2)) on [0, pi]")
    w1 = sp.Symbol("w1")
    roots = sp.solve(w1**2 + w1 + 1, w1)
    check("M-GRAPHENE-NS", sorted(sp.simplify(sp.arg(rt)) for rt in roots) == [-2 * sp.pi / 3, 2 * sp.pi / 3],
          "on the unit torus 1 + w1 + w2 = 0 iff w1^2 + w1 + 1 = 0, w2 = conj(w1): Dirac points "
          "(k1, k2) = (2pi/3, -2pi/3), (-2pi/3, 2pi/3) (w = e^{-ik})")
    Cg = sp.ones(4, 4) / 2 - sp.eye(4)
    U = sp.diag(z1, 1 / z1, z2, 1 / z2) * Cg
    L = sp.Symbol("L")
    cp = sp.together((L * sp.eye(4) - U).det())
    check("M-GROVER", zero_rat(cp - (L - 1) * (L + 1) * (L**2 + (C1 + C2) * L + 1)),
          "det(L - S(k)G), G = J/2 - I, S = diag(z1, 1/z1, z2, 1/z2): (L-1)(L+1)(L^2 + (c1+c2)L + 1); "
          "dispersive bands cos w = -(c1 + c2)/2, flat bands at L = +-1")
    v_ = sp.Symbol("v", nonnegative=True)
    check("M-YEE", sp.simplify(sp.sin(k1 / 2) ** 2 - (1 - c1) / 2) == 0
          and sp.simplify(sp.sin(sp.asin(sp.sqrt(v_))) ** 2 - v_) == 0,
          "sin^2(k/2) = (1 - cos k)/2; Psi = 2 asin(sqrt v), v = S^2 (2 - c1 - c2)/2, solves sin^2(Psi/2) = v")

    # smoothness and gap facts (exact identities giving lower bounds)
    check("G-QWZ1", zero_rat((2 + 1 + 2 * (C1 + C2) + 2 * C1 * C2) - (1 + 2 * (1 + C1) * (1 + C2))),
          "m = 1: P = 1 + 2(1 + c1)(1 + c2) >= 1")
    check("G-QWZ3", zero_rat((2 + 9 + 6 * (C1 + C2) + 2 * C1 * C2) - (2 * (3 + C1) * (3 + C2) - 7)),
          "m = 3: P = 2(3 + c1)(3 + c2) - 7 >= 1")
    check("G-aQWZ", zero_rat(Pa - (S1**2 + al**2 * S2**2 + (3 + C1 + C2) ** 2)),
          "P = sin^2 k1 + (9/25) sin^2 k2 + (3 + c1 + c2)^2 >= 1")
    check("G-YEE", all(sp.Rational(2) * Sv**2 < 1 for Sv in (sp.Rational(1, 2), sp.Rational(7, 10))),
          "v = S^2 (2 - c1 - c2)/2 in [0, 2S^2] with 2S^2 = 1/2, 49/50 < 1 for S = 1/2, 7/10: "
          "branch point only at v = 0, i.e. k = (0,0)")
    check("G-ARCCOS", sp.Rational(1, 2) + sp.Rational(3, 10) < 1, "|c1/2 + 3c2/10| <= 4/5 < 1: arccos analytic")

    # ---------------- Section 5: controls and known answers ----------------
    # K-SQ: u = c1 + c2
    Hs_, Ts_, Qs_ = jets(c1 + c2, K)
    ok = True
    for a in (sp.pi / 2, -sp.pi / 2):
        for b in (sp.pi / 2, -sp.pi / 2):
            pt = {k1: a, k2: b}
            Hp, Tp = at(Hs_, pt), at(Ts_, pt)
            dsc, co = disc_cubic(Tp)
            ok = ok and all(is_zero(Hp[i][j]) for i in range(2) for j in range(2)) and not is_zero(dsc) \
                and cubic_root_structure(co) == "distinct"
            if a == b == sp.pi / 2:
                ok = ok and is_zero(dsc + 27) and list(co) == [1, 0, 0, 1]
    detS = sp.simplify(Hs_[0][0] * Hs_[1][1] - Hs_[0][1] ** 2)
    for a in (sp.pi / 2, -sp.pi / 2):
        Hl, Tl = at(Hs_, {k1: a}), at(Ts_, {k1: a})
        _, vbl = kernels(Hl)  # (q, -p) vanishes on this line; (r, -q) = (-c2, 0)
        g3l = sp.simplify(contract(Tl, vbl, vbl, vbl))
        ok = ok and sp.simplify(g3l - (-c2**3 * sp.sin(a))) == 0
    check("K-SQ", ok and sp.simplify(detS - c1 * c2) == 0,
          "u = c1 + c2: det H = c1 c2; at (+-pi/2, +-pi/2) H = 0 and the cubic has three distinct roots (D4; at "
          "(pi/2, pi/2) C = k1^3 + k2^3, Disc = -27); "
          "on k1 = +-pi/2 the kernel is (r,-q) = (-c2, 0) and g3 = -c2^3 sin k1 != 0 for c2 != 0 (fold); "
          "the lines k2 = +-pi/2 by the symmetry k1 <-> k2: no A3 point")

    P3 = 11 + 6 * (c1 + c2) + 2 * c1 * c2
    Hq_, Tq_, Qq_ = jets(sp.sqrt(P3), K)
    aa = sp.acos(sp.Rational(-1, 3))
    ok = True
    for sa in (1, -1):
        for sb in (1, -1):
            pt = {k1: sa * aa, k2: sb * aa}
            Hp, Tp, Qp = at(Hq_, pt), at(Tq_, pt), at(Qq_, pt)
            detp = Hp[0][0] * Hp[1][1] - Hp[0][1] ** 2
            nonzeroH = not all(is_zero(Hp[i][j]) for i in range(2) for j in range(2))
            g3a, g3b, g4, _, _ = rank1_invariants(Hp, Tp, Qp)
            ok = ok and is_zero(detp) and nonzeroH and is_zero(g3a) and is_zero(g3b) and not is_zero(g4)
    # value with v = (1,-1), w = (1,1) at (a,a), i.e. coordinates k = (a+s+u, a+s-u)
    pt = {k1: aa, k2: aa}
    Hp, Tp, Qp = at(Hq_, pt), at(Tq_, pt), at(Qq_, pt)
    g4n = contract(Qp, (1, -1), (1, -1), (1, -1), (1, -1)) - 3 * contract(Tp, (1, -1), (1, -1), (1, 1)) ** 2 / contract(
        Hp, (1, 1), (1, 1))
    ok = ok and is_zero(contract(Hp, (1, 1), (1, 1)) - 32 / (195 * sp.sqrt(65))) \
        and is_zero(contract(Tp, (1, -1), (1, -1), (1, 1)) - 12 * sp.sqrt(130) / 65) \
        and is_zero(contract(Qp, (1, -1), (1, -1), (1, -1), (1, -1)) - 18 / sp.sqrt(65))
    check("K-QWZ3", ok and is_zero(g4n + sp.Rational(5247) / sp.sqrt(65)),
          "QWZ m = 3 at (+-a, +-a), a = arccos(-1/3): det H = 0, H != 0, g3 = 0 (both kernel vectors), g4 != 0 (A3); "
          "with v = (1,-1), w = (1,1) at (a,a): H[w,w] = 32/(195 sqrt65), T[v,v,w] = 12 sqrt130/65, "
          "Q[v,v,v,v] = 18/sqrt65, g4 = -5247/sqrt(65)")

    # K-DKG: discrete Klein-Gordon, mass 1 (M17); Cuenin-Ikromov (Nonlinearity 34 (2021), Prop. 9) state A3 exactly at
    # cos k1 = cos k2 = 0. Re-derived here at the four points (the "exactly" part is the paper's, not checked here).
    Hd_, Td_, Qd_ = jets(sp.sqrt(5 - 2 * c1 - 2 * c2), K)
    ok = True
    for a in (sp.pi / 2, -sp.pi / 2):
        for b in (sp.pi / 2, -sp.pi / 2):
            pt = {k1: a, k2: b}
            Hp, Tp, Qp = at(Hd_, pt), at(Td_, pt), at(Qd_, pt)
            nonzeroH = not all(is_zero(Hp[i][j]) for i in range(2) for j in range(2))
            g3a, g3b, g4, _, _ = rank1_invariants(Hp, Tp, Qp)
            ok = ok and is_zero(Hp[0][0] * Hp[1][1] - Hp[0][1] ** 2) and nonzeroH and is_zero(g3a) and is_zero(g3b) \
                and not is_zero(g4)
    check("K-DKG", ok, "M17 sqrt(5 - 2c1 - 2c2) at (+-pi/2, +-pi/2): det H = 0, H != 0, g3 = 0, g4 != 0 (A3), "
                       "agreeing with Cuenin-Ikromov Prop. 9 at these points")

    xx, yy = sp.symbols("x y", real=True)
    V2 = [xx, yy]

    def poly_control(phi):
        return jets(phi, V2)

    # K1: rotated, shifted cusp X^2 Y + Y^2
    Rm = sp.Matrix([[sp.Rational(3, 5), -sp.Rational(4, 5)], [sp.Rational(4, 5), sp.Rational(3, 5)]])
    rr = sp.Matrix([sp.Rational(1, 7), -sp.Rational(2, 9)])
    XY = Rm * (sp.Matrix([xx, yy]) - rr)
    phi1 = sp.expand(XY[0] ** 2 * XY[1] + XY[1] ** 2)
    H1, T1, Q1 = poly_control(phi1)
    Hp, Tp, Qp = at(H1, {xx: rr[0], yy: rr[1]}), at(T1, {xx: rr[0], yy: rr[1]}), at(Q1, {xx: rr[0], yy: rr[1]})
    g3a, g3b, g4, _, _ = rank1_invariants(Hp, Tp, Qp)
    tau = sp.Symbol("tau", real=True)
    ptc = rr + Rm.T * sp.Matrix([tau, tau**2])
    Hc, Tc = at(H1, {xx: ptc[0], yy: ptc[1]}), at(T1, {xx: ptc[0], yy: ptc[1]})
    detc = sp.simplify(Hc[0][0] * Hc[1][1] - Hc[0][1] ** 2)
    vac, vbc = kernels(Hc)
    g3c_a = sp.factor(sp.simplify(contract(Tc, vac, vac, vac)))
    g3c = sp.factor(sp.simplify(contract(Tc, vbc, vbc, vbc)))
    frob = sp.expand(sum(H1[i][j] ** 2 for i in range(2) for j in range(2)))
    XYs = sp.symbols("X Y")
    frob_rot = sp.expand(frob.subs({xx: (rr + Rm.T * sp.Matrix(XYs))[0], yy: (rr + Rm.T * sp.Matrix(XYs))[1]}))
    common = sp.solve([sp.numer(sp.together(g3c_a)), sp.numer(sp.together(g3c))], tau, dict=True)
    check("K1", is_zero(Hp[0][0] * Hp[1][1] - Hp[0][1] ** 2) and is_zero(g3a) and is_zero(g3b) and not is_zero(g4)
          and detc == 0 and [d[tau] for d in common if d[tau].is_real] == [0]
          and sp.simplify(frob_rot - (4 * XYs[1] ** 2 + 8 * XYs[0] ** 2 + 4)) == 0,
          f"K1 = X^2 Y + Y^2, (X,Y) = R((x,y) - r), R = [[3/5,-4/5],[4/5,3/5]], r = (1/7,-2/9): at r rank 1, g3 = 0, "
          f"g4 = {sp.simplify(g4)} != 0 (A3); det H = 0 on r + R^T(tau, tau^2), where T[va^3] = {g3c_a} and "
          f"T[vb^3] = {g3c} vanish together only at tau = 0 (at tau = 3/4 the vector (r,-q) is zero, not g3); "
          f"|H|_F^2 = 4Y^2 + 8X^2 + 4 >= 4 (no rank-0 point)")

    # K2: shifted D5 normal form X^2 Y + Y^4
    r2 = (sp.Rational(-1, 5), sp.Rational(1, 3))
    phi2 = sp.expand((xx - r2[0]) ** 2 * (yy - r2[1]) + (yy - r2[1]) ** 4)
    H2, T2, Q2 = poly_control(phi2)
    pt2 = {xx: r2[0], yy: r2[1]}
    Hp, Tp = at(H2, pt2), at(T2, pt2)
    dsc, co = disc_cubic(Tp)
    ptc2 = {xx: r2[0] + sp.sqrt(6) * tau**3, yy: r2[1] + tau**2}
    Hc, Tc = at(H2, ptc2), at(T2, ptc2)
    vac, _ = kernels(Hc)
    g3c2 = sp.factor(sp.simplify(contract(Tc, vac, vac, vac)))
    det2 = sp.factor(sp.simplify(H2[0][0] * H2[1][1] - H2[0][1] ** 2))
    check("K2", all(is_zero(Hp[i][j]) for i in range(2) for j in range(2)) and is_zero(dsc)
          and cubic_root_structure(co) == "double" and sp.simplify(Hc[0][0] * Hc[1][1] - Hc[0][1] ** 2) == 0,
          f"K2 = X^2 Y + Y^4, (X,Y) = (x,y) - (-1/5, 1/3): at r H = 0, cubic {co} has a double root (class D>=5); "
          f"det H = {det2}; on X = +-sqrt6 tau^3, Y = tau^2 (shown for +): g3 = {g3c2} != 0 for tau != 0 (folds); "
          f"H = 0 only at r (H11 = 2Y, H12 = 2X)")

    # K3: shifted X^3 + Y^4: E/J point, non-isolated A3 segment, folds
    r3 = (sp.Rational(2, 7), sp.Rational(-1, 11))
    phi3 = sp.expand((xx - r3[0]) ** 3 + (yy - r3[1]) ** 4)
    H3, T3, Q3 = poly_control(phi3)
    Hp, Tp = at(H3, {xx: r3[0], yy: r3[1]}), at(T3, {xx: r3[0], yy: r3[1]})
    _, co = disc_cubic(Tp)
    X0 = sp.Symbol("X0", real=True, nonzero=True)
    ptl = {xx: r3[0] + X0, yy: r3[1]}
    Hl, Tl, Ql = at(H3, ptl), at(T3, ptl), at(Q3, ptl)
    g3l_a, g3l_b, g4l, _, _ = rank1_invariants(Hl, Tl, Ql)
    Y0 = sp.Symbol("Y0", real=True, nonzero=True)
    ptf = {xx: r3[0], yy: r3[1] + Y0}
    Hf, Tf = at(H3, ptf), at(T3, ptf)
    vaf, vbf = kernels(Hf)  # (q,-p) = (0,0) on this line; (r,-q) = (12 Y0^2, 0) spans the kernel
    g3f = sp.simplify(contract(Tf, vbf, vbf, vbf))
    check("K3", all(is_zero(Hp[i][j]) for i in range(2) for j in range(2)) and cubic_root_structure(co) == "triple"
          and sp.simplify(g3l_a) == 0 and sp.simplify(g3l_b) == 0 and sp.simplify(g4l) != 0 and sp.simplify(g3f) != 0,
          f"K3 = X^3 + Y^4, (X,Y) = (x,y) - (2/7, -1/11): at r H = 0, cubic {co} triple (class E/J); on Y = 0, X = X0 != 0: "
          f"rank 1, g3 = 0, g4 = {sp.simplify(g4l)} (a non-isolated A3 segment); on X = 0, Y = Y0 != 0: g3 = {g3f} (fold)")

    # K5: separable trap sqrt((c1+c2)^2 + 1/4)
    Pt = (c1 + c2) ** 2 + sp.Rational(1, 4)
    Ht, Tt, Qt = jets(sp.sqrt(Pt), K)
    pt = {k1: sp.pi / 3, k2: 2 * sp.pi / 3}
    grad = [sp.simplify(sp.diff(sp.sqrt(Pt), kk).subs(pt)) for kk in K]
    Hp, Tp, Qp = at(Ht, pt), at(Tt, pt), at(Qt, pt)
    g3a, g3b, g4, _, _ = rank1_invariants(Hp, Tp, Qp)
    const_line = sp.simplify(sp.sqrt(Pt).subs(k2, sp.pi - k1))
    pt0 = {k1: 0, k2: sp.pi}
    H0, T0 = at(Ht, pt0), at(Tt, pt0)
    _, co0 = disc_cubic(T0)
    check("K5", grad == [0, 0] and is_zero(Hp[0][0] * Hp[1][1] - Hp[0][1] ** 2)
          and not all(is_zero(Hp[i][j]) for i in range(2) for j in range(2)) and is_zero(g3a) and is_zero(g3b)
          and is_zero(g4) and const_line == sp.Rational(1, 2)
          and all(is_zero(H0[i][j]) for i in range(2) for j in range(2)) and cubic_root_structure(co0) == "zero",
          "K5 = sqrt((c1+c2)^2 + 1/4): constant 1/2 on k1 + k2 = pi; at (pi/3, 2pi/3) grad = 0, rank 1, g3 = g4 = 0 "
          "(non-isolated A>=4 curve); at (0, pi) H = 0 and the cubic is zero (class E/J)")

    n_ok = sum(RESULTS)
    print(f"SUMMARY {n_ok}/{len(RESULTS)}")
    if n_ok == len(RESULTS):
        print("ALL_CHECKS_PASS")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
