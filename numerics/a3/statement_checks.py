#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Checks behind the batch-A3 statements (docs/statements.md, "Batch A3"), run before the statements are frozen.

Part 1 (exact, SymPy): the algebra the statements and their sanity data rely on.
  E1  stable-cusp model P = h s^2/2 + (T/2) u^2 s + (Q/24) u^4: away from the origin every point is nondegenerate or
      a fold iff g4 = hQ - 3T^2 != 0 and T != 0 (on the degenerate curve g3 = h^2 u g4); this is what makes the
      dyadic route of S5.1 (fold bound S3 on annuli) possible.
  E2  non-versal model (T = 0): g3 vanishes on the whole line u = 0, so S3 does not apply on annuli (S5.1' needs
      another route).
  E3  the sanity data of OscInt/Front/CuspSanity.lean: the generic stable datum, and each bite datum fails the
      condition it is meant to fail.
  E4  the van der Corput constants c_k = 5 * 2^(k-1) - 2 satisfy c_2 = 8, c_3 = 18 and c_{k+1} = 2 c_k + 2.
Part 2 (EXPLORATORY numerics, mpmath, not rigorous, not evidence for a Lean theorem):
  N1  sup over a grid of linear terms y of t^(3/4) |int e^{i(t phi + y.k)} A| for phi = x^2 y + y^2 (stable cusp) and
      phi = x^4 + y^2 (non-versal), Gaussian amplitude A = exp(-(x^2 + y^2)), t in {10, 100, 1000, 10000}: bounded if
      S5.1 / S5.1' hold; t^(3/4)|I(t, 0)| tends to a nonzero limit (the exponent cannot be improved).
  N2  t^(1/k) sup_b |int_0^b e^{i t x^k / k!} dx| against c_k for k = 4, 5 (the S1.k constant is not violated).
Usage: SYMPY_GROUND_TYPES=python python3 -I numerics/a3/statement_checks.py  (env: numerics/census/requirements.txt)
Exit status 0 iff every Part-1 check passes (Part 2 prints numbers only).
"""
import platform
import subprocess
import sys

import mpmath as mp
import sympy as sp

OK = []


def check(cid, ok, detail):
    OK.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}", flush=True)


def jet(f, X):
    x, y = X
    H = sp.Matrix([[sp.diff(f, a, b) for b in X] for a in X])
    T = lambda a, b, c: sum(sp.diff(f, X[i], X[j], X[l]) * a[i] * b[j] * c[l]
                            for i in range(2) for j in range(2) for l in range(2))
    Q = lambda a: sum(sp.diff(f, X[i], X[j], X[l], X[m]) * a[i] * a[j] * a[l] * a[m]
                      for i in range(2) for j in range(2) for l in range(2) for m in range(2))
    return H, T, Q


def a3_invariants_at0(f, X, v, w):
    """(H v, H[w,w], g3, T[v,v,w], g4 = H[w,w] Q[v^4] - 3 T[v,v,w]^2) at the origin."""
    H, T, Q = jet(f, X)
    at0 = {X[0]: 0, X[1]: 0}
    Hv = [sp.simplify((H * sp.Matrix(v))[i].subs(at0)) for i in range(2)]
    hww = sp.simplify((sp.Matrix(w).T * H * sp.Matrix(w))[0].subs(at0))
    g3 = sp.simplify(T(v, v, v).subs(at0))
    tvvw = sp.simplify(T(v, v, w).subs(at0))
    g4 = sp.simplify(hww * Q(v).subs(at0) - 3 * tvvw**2)
    return Hv, hww, g3, tvvw, g4


def main():
    print(f"# python {platform.python_version()}, sympy {sp.__version__}, mpmath {mp.__version__}")
    try:
        head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], capture_output=True,
                               text=True, check=True).stdout.strip()
        print(f"# git HEAD {head}, tracked files modified: {'yes' if dirty else 'no'}")
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"# git state unavailable: {e}")

    u, s = sp.symbols("u s", real=True)
    h, T, Q = sp.symbols("h T Q", real=True, nonzero=True)
    P = h * s**2 / 2 + T * u**2 * s / 2 + Q * u**4 / 24
    HP, TP, _ = jet(P, [u, s])
    detP = sp.expand(HP.det())
    s_curve = sp.solve(detP, s)
    ok = len(s_curve) == 1
    sc = s_curve[0]
    Hc = HP.subs(s, sc)
    p, q, r = Hc[0, 0], Hc[0, 1], Hc[1, 1]
    va, vb = (q, -p), (r, -q)
    g3b = sp.factor(sp.simplify(TP(vb, vb, vb).subs(s, sc)))
    g3a = sp.factor(sp.simplify(TP(va, va, va).subs(s, sc)))
    g4 = h * Q - 3 * T**2
    ok = ok and sp.simplify(g3b - h**2 * u * g4) == 0 and sp.simplify(vb[0] - h) == 0
    check("E1", ok, f"P = h s^2/2 + (T/2) u^2 s + (Q/24) u^4: det D^2P = {sp.factor(detP)} vanishes on s = {sc}; there "
                    f"the kernel vector (r,-q) = (h, -T u) is nonzero and T[v,v,v] = {g3b} = h^2 u (hQ - 3T^2); "
                    f"T[(q,-p)^3] = {g3a}. So off the origin every degenerate point is a fold iff g4 = hQ - 3T^2 != 0; "
                    f"the formula s(u) needs T != 0 (solved for s)")
    P0 = h * s**2 / 2 + Q * u**4 / 24
    H0, T0, _ = jet(P0, [u, s])
    ok = sp.simplify(H0.det() - h * Q * u**2 / 2) == 0
    g3_line = sp.simplify(T0((1, 0), (1, 0), (1, 0)).subs(u, 0))
    check("E2", ok and g3_line == 0, f"T = 0: det D^2P = h Q u^2/2 vanishes on u = 0, kernel e_u, T[e_u^3] = Q u = 0 "
                                     f"there: every point (0, s) is degenerate with g3 = 0 (A3 along a line); the "
                                     f"fold bound S3 does not apply on annuli")

    x, y = sp.symbols("x y", real=True)
    X = [x, y]
    e1, e2 = (1, 0), (0, 1)
    gen = x**2 * y + 2 * y**2 + 3 * x**4 + 5 * x * y**2
    Hv, hww, g3, tvvw, g4v = a3_invariants_at0(gen, X, e1, e2)
    check("E3-gen", Hv == [0, 0] and hww != 0 and g3 == 0 and tvvw != 0 and g4v != 0,
          f"generic stable datum x^2y + 2y^2 + 3x^4 + 5xy^2 at 0, v = e1, w = e2: H v = {Hv}, H[w,w] = {hww}, "
          f"g3 = {g3}, T[v,v,w] = {tvvw}, g4 = {g4v} (stable A3)")
    trap = sp.expand((y + x**2 / 2) ** 2)
    Hv, hww, g3, tvvw, g4v = a3_invariants_at0(trap, X, e1, e2)
    _, _, Qt = jet(trap, X)
    check("E3-trap", Hv == [0, 0] and hww != 0 and g3 == 0 and g4v == 0 and Qt(e1).subs({x: 0, y: 0}) != 0,
          f"(y + x^2/2)^2 = {trap}: H v = 0, H[w,w] = {hww}, g3 = 0, Q[v^4] = {Qt(e1).subs({x: 0, y: 0})} != 0 but "
          f"g4 = {g4v}: not A3 (a test using Q[v^4] alone would accept it)")
    fold = x**3 + y**2
    Hv, hww, g3, _, _ = a3_invariants_at0(fold, X, e1, e2)
    check("E3-fold", Hv == [0, 0] and hww != 0 and g3 != 0, f"x^3 + y^2: g3 = {g3} != 0 (fold, not A3)")
    nonv = x**4 + y**2
    Hv, hww, g3, tvvw, g4v = a3_invariants_at0(nonv, X, e1, e2)
    check("E3-nonversal", Hv == [0, 0] and hww != 0 and g3 == 0 and tvvw == 0 and g4v != 0,
          f"x^4 + y^2: g3 = 0, g4 = {g4v} != 0 (A3) but T[v,v,w] = 0 (not stable)")
    for name, f in (("rank0", x**3 + y**3), ("nondeg", x**2 + y**2)):
        H, _, _ = jet(f, X)
        H0m = H.subs({x: 0, y: 0})
        rank = H0m.rank()
        check(f"E3-{name}", rank != 1, f"{f}: Hessian rank at 0 = {rank} (not 1): no (v, w) as in IsA3Point")
    ck = [5 * 2 ** (k - 1) - 2 for k in range(2, 9)]
    check("E4", ck[0] == 8 and ck[1] == 18 and all(ck[i + 1] == 2 * ck[i] + 2 for i in range(len(ck) - 1)),
          f"c_k = 5 * 2^(k-1) - 2 for k = 2..8: {ck}; c_2 = 8 (S1.2), c_3 = 18 (S1.3), c_(k+1) = 2 c_k + 2")

    print("# Part 2: EXPLORATORY numerics (mpmath, not rigorous)")
    mp.mp.dps = 30

    def rays(g, th_pos, th_neg):
        # int_R g(x) dx for an entire g that decays in the sectors between the real axis and the rays
        # x = r e^{i th_pos} (r > 0) and x = r e^{i th_neg} (r > 0, th_neg near pi): Cauchy's theorem moves each
        # half-line onto its steepest-descent ray, where e^{+-i t x^4} becomes e^{-t r^4} (no oscillation).
        zp, zn = mp.expjpi(th_pos / mp.pi), mp.expjpi(th_neg / mp.pi)
        R = mp.linspace(0, 8, 33)
        return mp.quad(lambda r: g(r * zp) * zp, R) - mp.quad(lambda r: g(r * zn) * zn, R)

    def I_stable(t, y1, y2):
        # int e^{i(t(x^2 y + y^2) + y1 x + y2 y)} e^{-(x^2+y^2)} dx dy; y-integral in closed form:
        # int e^{-(1 - i t) y^2 + i (t x^2 + y2) y} dy = sqrt(pi/(1 - i t)) exp(-(t x^2 + y2)^2 / (4 (1 - i t))),
        # whose x-dependence oscillates like e^{-i t x^4/4}: rays at -pi/8 and 7pi/8 (there Re of the exponent
        # -(t^2/(4(1+t^2))) r^4 (cos 4th - t sin 4th) <= 0 on the swept sectors).
        a = 1 - 1j * t
        g = lambda xx: mp.exp(-xx**2 + 1j * y1 * xx) * mp.sqrt(mp.pi / a) * mp.exp(-(t * xx**2 + y2)**2 / (4 * a))
        return rays(g, -mp.pi / 8, 7 * mp.pi / 8)

    def I_nonv(t, y1, y2):
        # product: closed-form y-integral times int e^{i t x^4 - x^2 + i y1 x} dx (rays at pi/8 and 9pi/8)
        a = 1 - 1j * t
        Iy = mp.sqrt(mp.pi / a) * mp.exp(-(y2)**2 / (4 * a))
        g = lambda xx: mp.exp(1j * t * xx**4 - xx**2 + 1j * y1 * xx)
        return Iy * rays(g, mp.pi / 8, 9 * mp.pi / 8)

    lim_nonv = mp.sqrt(mp.pi) * 2 * mp.gamma(mp.mpf(5) / 4)
    print(f"N0 reference: t^(3/4)|I(t,0)| for x^4 + y^2 tends to sqrt(pi) * 2 Gamma(5/4) = {mp.nstr(lim_nonv, 10)} "
          f"(|int e^(i t x^4) dx| t^(1/4) -> 2 Gamma(5/4), |int e^(i t y^2) dy| t^(1/2) -> sqrt(pi))")

    for name, I in (("stable x^2y + y^2", I_stable), ("non-versal x^4 + y^2", I_nonv)):
        for t in (10, 100, 1000, 10000):
            vals = []
            for y1 in (0, 0.3 * t ** 0.25, -0.7 * t ** 0.25):
                for y2 in (0, 0.5 * t ** 0.5, -1.1 * t ** 0.5):
                    vals.append(abs(I(t, y1, y2)) * t ** 0.75)
            print(f"N1 {name}: t = {t:>5}: t^(3/4)|I(t,0)| = {mp.nstr(vals[0], 8)}, "
                  f"max over 9 linear terms = {mp.nstr(max(vals), 8)}")
    for k in (4, 5):
        ckk = 5 * 2 ** (k - 1) - 2
        best = 0
        for t in (10, 1000):
            f = lambda xx: mp.exp(1j * t * xx**k / mp.factorial(k))
            # mu = t (k-th derivative of t x^k/k! is t); sup over b on a grid
            for b in mp.linspace(0.05, 6, 120):
                val = abs(mp.quad(f, mp.linspace(0, b, 30))) * t ** (mp.mpf(1) / k)
                best = max(best, val)
        print(f"N2 k = {k}: max t^(1/k) |int_0^b e^(i t x^k/k!)| over t in {{10, 1000}}, b in [0.05, 6] = "
              f"{mp.nstr(best, 8)} (c_k = {ckk})")

    n = sum(OK)
    print(f"SUMMARY {n}/{len(OK)}")
    if n == len(OK):
        print("ALL_CHECKS_PASS")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
