#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Independent re-derivation of the claims in the external reviewer dossier of 2026-11-10
(answers: review/2026-11-10-external-dossier-answers.md), written without the dossier's own scripts (they were not supplied).

Part 1 (exact, SymPy): X1-X8.  Part 2 (FLOAT TEST, NumPy/SciPy/mpmath, not rigorous): F1-F8.
Every check prints CHECK <id> PASS|FAIL <detail>. Exit status 0 iff every check passes.
A FLOAT TEST is evidence about the sampled case only; none of it is a certified enclosure.
Usage: SYMPY_GROUND_TYPES=python python3 -I numerics/review/dossier_checks.py
Needs sympy 1.14.0, mpmath 1.3.0 (numerics/census/requirements.txt) plus numpy and scipy.
"""
import platform
import subprocess
import sys

import mpmath as mp
import numpy as np
import scipy
import sympy as sp
from scipy.linalg import expm

OK = []


def check(cid, ok, detail):
    OK.append(bool(ok))
    print(f"CHECK {cid} {'PASS' if ok else 'FAIL'} {detail}", flush=True)


def is_zero(e):
    return sp.simplify(sp.expand(e)) == 0


# ---------------------------------------------------------------- Part 1: exact
m = sp.symbols("m", positive=True)
s, u = sp.symbols("s u", real=True)
ca, sa = sp.symbols("c_a s_a", real=True)

# X1. QWZ upper band at the diagonal point (a, a), cos a = -1/m, sin a = sqrt(m^2-1)/m, for symbolic m > 2.
# k = (a+s+u, a+s-u). P = m^2 + 2 + 2m(cos k1 + cos k2) + 2 cos k1 cos k2, expanded with cos(a+x) = ca cos x - sa sin x.
def cosA(x):
    return ca * sp.cos(x) - sa * sp.sin(x)


k1, k2 = s + u, s - u  # offsets from a
P = m**2 + 2 + 2 * m * (cosA(k1) + cosA(k2)) + 2 * cosA(k1) * cosA(k2)
omega = sp.sqrt(P)
sub_pt = {s: 0, u: 0}
sub_a = {ca: -1 / m, sa: sp.sqrt(m**2 - 1) / m}


def d_at(expr, *vars_):
    e = sp.diff(expr, *vars_).subs(sub_pt)
    return sp.simplify(sp.expand(e.subs(sub_a)))


D = m**4 - 2 * m**2 + 2
P0 = sp.simplify(P.subs(sub_pt).subs(sub_a))
check("X1a", is_zero(P0 - D / m**2), f"P(a,a) = D_m/m^2, got {P0}")
w_ss = d_at(omega, s, s)
w_su = d_at(omega, s, u)
w_uu = d_at(omega, u, u)
w_uuu = d_at(omega, u, u, u)
w_suu = d_at(omega, s, u, u)
w_uuuu = d_at(omega, u, u, u, u)
check("X1b", w_su == 0 and w_uu == 0 and w_uuu == 0, f"omega_su = {w_su}, omega_uu = {w_uu}, omega_uuu = {w_uuu}")
exp_ss = 4 * (m**2 - 1) / (m * D ** sp.Rational(3, 2))
exp_suu = 2 * m * sp.sqrt(m**2 - 1) / sp.sqrt(D)
exp_uuuu = 6 * m / sp.sqrt(D)
check("X1c", is_zero(w_ss - exp_ss) and is_zero(w_suu - exp_suu) and is_zero(w_uuuu - exp_uuuu),
      "omega_ss = 4(m^2-1)/(m D^(3/2)), omega_suu = 2m sqrt(m^2-1)/sqrt(D), omega_uuuu = 6m/sqrt(D) (dossier A1.3)")
Gam = sp.simplify(w_uuuu - 3 * w_suu**2 / w_ss)
exp_G = -3 * m * (m**6 - 2 * m**4 + 2 * m**2 - 2) / sp.sqrt(D)
check("X1d", is_zero(Gam - exp_G), f"Gamma_m = {sp.factor(Gam)} (dossier A1.4)")
z = sp.symbols("z", real=True)
pz = z**3 - 2 * z**2 + 2 * z - 2
dp = sp.diff(pz, z)
check("X1e", sp.discriminant(dp, z) == -8 and pz.subs(z, 4) == 38 and sp.Poly(dp, z).LC() > 0,
      "p(z) = z^3-2z^2+2z-2: p' has discriminant -8 and positive leading coefficient, p(4) = 38, so p > 0 on z > 4")
# Lean form of the invariant (IsA3Point with v = (1,-1) = dk/du, w = (1,1) = dk/ds): g4 = H[w,w] Q[v^4] - 3 T[v,v,w]^2.
g4 = sp.simplify(w_ss * w_uuuu - 3 * w_suu**2)
check("X1f", is_zero(g4 - w_ss * Gam),
      f"g4 (Lean IsA3Point quantity) = omega_ss * Gamma_m; at m = 3: g4 = {sp.nsimplify(sp.simplify(g4.subs(m, 3)))}")
vals3 = [sp.simplify(e.subs(m, 3)) for e in (w_ss, w_suu, w_uuuu, Gam, g4)]
check("X1g", is_zero(vals3[0] - 32 / (195 * sp.sqrt(65))) and is_zero(vals3[1] - 12 * sp.sqrt(130) / 65)
      and is_zero(vals3[2] - 18 / sp.sqrt(65)) and is_zero(vals3[3] + 5247 / sp.sqrt(65)),
      f"m = 3 agrees with CENSUS spec section 7 (omega_ss, omega_suu, omega_uuuu, Gamma) = {vals3[:4]};"
      f" note g4 at m=3 = {vals3[4]} = {sp.N(vals3[4], 12)}")
# Two normalisations of the same invariant: Lean IsA3Point uses H[w,w]Q - 3T^2; CENSUS spec 2.2 uses Q - 3T^2/H[w,w].
check("X1h", is_zero(vals3[4] - vals3[0] * vals3[3]) and not is_zero(vals3[4] - vals3[3]),
      f"Lean form H[w,w]Q - 3T^2 = {vals3[4]} (m=3) equals omega_ss * (spec g4 = Gamma); same sign and nonvanishing; "
      "anyone comparing numbers across the two must rescale by H[w,w]")
# Only diagonal degenerate points: on k1 = k2 = b, omega_uu = P_uu/(2 omega) and P_uu = -4m cos b - 4.
b = sp.symbols("b", real=True)
Pdiag = (m**2 + 2 + 2 * m * (sp.cos(b + u) + sp.cos(b - u)) + 2 * sp.cos(b + u) * sp.cos(b - u))
Puu = sp.simplify(sp.diff(Pdiag, u, 2).subs(u, 0))
check("X1i", is_zero(Puu - (-4 * m * sp.cos(b) - 4)),
      f"on the diagonal P_uu = {sp.factor(Puu)}: omega_uu = 0 iff cos b = -1/m, i.e. b = +-a_m (and the four points (+-a,+-a) by evenness)")
# group velocity at (a,a)
grad1 = sp.simplify((sp.diff(omega, s) + sp.diff(omega, u)).subs(sub_pt).subs(sub_a) / 2)
vm = (m**2 - 1) ** sp.Rational(3, 2) / (m * sp.sqrt(D))
check("X1j", is_zero(grad1 + vm) and is_zero(sp.expand(m**2 * D - (m**2 - 1) ** 3) - (m**4 - m**2 + 1)),
      "d omega/dk1 at (a,a) = -v_m, v_m = (m^2-1)^(3/2)/(m sqrt D); m^2 D - (m^2-1)^3 = m^4 - m^2 + 1 > 0 so 0 < v_m < 1 (C2.4)")

# X2. Reduced fourth jet, r = 2 transverse variables, fully symbolic generic coefficients.
s1, s2 = sp.symbols("s1 s2", real=True)
h11, h12, h22, v1, v2, Q = sp.symbols("h11 h12 h22 v1 v2 Q", real=True)
c = sp.symbols("c0:12", real=True)  # other jet terms that cannot affect u^4 (cubic in s, s*u^3 forbidden? no: F_su=0 only at 0)
# F = 1/2 s^T H s + 1/2 u^2 (v.s) + Q u^4/24 + terms of order >= 3 in s, or s^2 u, or s u^3 (all O(u^5) or higher after s=O(u^2))
F = (sp.Rational(1, 2) * (h11 * s1**2 + 2 * h12 * s1 * s2 + h22 * s2**2) + sp.Rational(1, 2) * u**2 * (v1 * s1 + v2 * s2)
     + Q * u**4 / 24 + c[0] * s1**3 + c[1] * s1**2 * s2 + c[2] * s1**2 * u + c[3] * s1 * s2 * u + c[4] * s2**2 * u
     + c[5] * s1 * u**3 + c[6] * s2 * u**3 + c[7] * u**5)
# critical curve s(u) = A u^2 + B u^3 + ...: solve order by order
A1, A2, B1, B2 = sp.symbols("A1 A2 B1 B2")
sc = {s1: A1 * u**2 + B1 * u**3, s2: A2 * u**2 + B2 * u**3}
eqs = [sp.expand(sp.diff(F, v).subs(sc)) for v in (s1, s2)]
sol2 = sp.solve([e.coeff(u, 2) for e in eqs], [A1, A2], dict=True)[0]
g = sp.expand(F.subs(sc).subs(sol2))
g4coef = sp.simplify(24 * g.coeff(u, 4))
Hm = sp.Matrix([[h11, h12], [h12, h22]])
vv = sp.Matrix([v1, v2])
check("X2", is_zero(g4coef - (Q - 3 * (vv.T * Hm.inv() * vv)[0])),
      "r = 2, generic symbolic jet including s^2 u, s u^3, s^3 terms: g''''(0) = Q - 3 v^T H^-1 v (dossier A2; r=2 symbolic, not all r)")

# X3. Negative control N2: F = s^2/2 + s u^2/2 + u^4/8 has raw F_uuuu = 3 but reduced phase identically 0.
Fn = s**2 / 2 + s * u**2 / 2 + u**4 / 8
scrit = sp.solve(sp.diff(Fn, s), s)[0]
check("X3", sp.diff(Fn, u, 4) == 3 and sp.expand(Fn.subs(s, scrit)) == 0 and is_zero(Fn - (s + u**2 / 2) ** 2 / 2),
      "F = (s + u^2/2)^2/2: raw quartic 3, reduced phase 0, H[w,w]Q - 3T^2 = 1*3 - 3*1 = 0 (not IsA3Point)")

# X4. IsA3Point: v = 0 is impossible, and the invariant does not depend on the choice of w modulo v.
# With H v = 0 and T[v,v,v] = 0: H[w+cv, w+cv] = H[w,w], T[v,v,w+cv] = T[v,v,w] + c T[v,v,v].
cc, hww, Tvvw, Tvvv, Q4 = sp.symbols("cc hww Tvvw Tvvv Q4")
inv = hww * Q4 - 3 * Tvvw**2
inv_shift = hww * Q4 - 3 * (Tvvw + cc * Tvvv) ** 2
check("X4", is_zero(inv_shift.subs(Tvvv, 0) - inv) and inv.subs({Q4: 0, Tvvw: 0}) == 0,
      "v = 0 gives Q[v^4] = T[v,v,w] = 0, so the invariant is 0 (v != 0 is forced); w -> w + c v leaves it unchanged")

# X5. C2 squares identity: P - sin^2 k1 (m + cos k2)^2 = (1 + (m + cos k2) cos k1)^2 + sin^2 k2.
x1, x2, M_ = sp.symbols("x1 x2 M", real=True)
Pq = (M_ + sp.cos(x1) + sp.cos(x2)) ** 2 + sp.sin(x1) ** 2 + sp.sin(x2) ** 2
lhs = Pq - sp.sin(x1) ** 2 * (M_ + sp.cos(x2)) ** 2
rhs = (1 + (M_ + sp.cos(x2)) * sp.cos(x1)) ** 2 + sp.sin(x2) ** 2
d1 = sp.diff(Pq, x1)
check("X5", sp.simplify(sp.expand_trig(lhs - rhs)) == 0 and sp.simplify(d1 + 2 * sp.sin(x1) * (M_ + sp.cos(x2))) == 0,
      "squares identity and dP/dk1 = -2 sin k1 (m + cos k2): |d omega/dk_j| <= 1 wherever omega > 0, any real m (C2)")

# X6. C5: imaginary part of H_m(k + i theta). For real b, ||b.sigma|| = |b|.
th1, th2 = sp.symbols("theta1 theta2", real=True)
bx = sp.cos(x1) * sp.sinh(th1)
by = sp.cos(x2) * sp.sinh(th2)
bz = -(sp.sin(x1) * sp.sinh(th1) + sp.sin(x2) * sp.sinh(th2))
Hc = [sp.sin(x1 + sp.I * th1), sp.sin(x2 + sp.I * th2), M_ + sp.cos(x1 + sp.I * th1) + sp.cos(x2 + sp.I * th2)]
ims = [sp.simplify(sp.im(sp.expand_complex(e))) for e in Hc]
nb2 = sp.expand(bx**2 + by**2 + bz**2)
target = sp.sinh(th1) ** 2 + sp.sinh(th2) ** 2 + 2 * sp.sin(x1) * sp.sin(x2) * sp.sinh(th1) * sp.sinh(th2)
check("X6", all(is_zero(a - b_) for a, b_ in zip(ims, (bx, by, bz))) and is_zero(sp.trigsimp(nb2 - target)),
      "Im H_m(k+i theta) = b.sigma with |b|^2 = sh1^2 + sh2^2 + 2 sin k1 sin k2 sh1 sh2 <= (|sh1|+|sh2|)^2, mass-free; "
      "the dossier's term-by-term triangle inequality (C5.3) only gives 2(|sh1|+|sh2|): the conclusion holds, the stated reason does not reach it")

# X7. C3: projector distance in C^2, ||P+ - P0||^2 = (1 - a/omega)/2, and omega - a <= r^2/(2a).
aa, rr = sp.symbols("a r", positive=True)
om = sp.sqrt(aa**2 + rr**2)
nz = aa / om
proj2 = ((1 - nz) ** 2 + (rr / om) ** 2) / 4  # |n - z|^2 / 4 with n = (r_x, r_y, a)/omega
check("X7", is_zero(proj2 - (1 - aa / om) / 2) and is_zero(sp.simplify(om - aa - rr**2 / (om + aa))),
      "||P+ - P0||^2 = |n - e_z|^2/4 = (1 - a/omega)/2; omega - a = r^2/(omega + a) (C3.2-3)")

# X8. Schur shear (B2) on the dossier's rational data R18.
Hs = sp.Matrix([[3, 1, 0], [1, 4, 1], [0, 1, 2]])
Bs = sp.Matrix([[1, 2], [0, 1], [-1, 1]])
zz = sp.Matrix(sp.symbols("z1:4"))
yy = sp.Matrix(sp.symbols("y1:3"))
Cs = Bs.T * Hs.inv() * Bs
lhs8 = (zz.T * Hs * zz / 2 + zz.T * Bs * yy + yy.T * Cs * yy / 2)[0]
sh = zz + Hs.inv() * Bs * yy
rhs8 = (sh.T * Hs * sh / 2)[0]
check("X8", sp.expand(lhs8 - rhs8) == 0, "Schur completion identity residual 0 on R18 data (B2)")

# ---------------------------------------------------------------- Part 2: FLOAT TEST
sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
sz = np.array([[1, 0], [0, -1]], complex)


def Hq(mm, q1, q2):
    return np.sin(q1) * sx + np.sin(q2) * sy + (mm + np.cos(q1) + np.cos(q2)) * sz


# F1. C3 / C4 bounds on random momenta.
rng = np.random.default_rng(20261110)
worst = []
for mm, t in [(2.5, 1.0), (3.0, 5.0), (10.0, 20.0), (30.0, 20.0), (100.0, 100.0), (100.0, 400.0)]:
    r3 = r4 = 0.0
    for _ in range(400):
        q1, q2 = rng.uniform(-np.pi, np.pi, 2)
        H = Hq(mm, q1, q2)
        a_ = mm + np.cos(q1) + np.cos(q2)
        at = a_ + (np.sin(q1) ** 2 + np.sin(q2) ** 2) / (2 * mm)
        U = expm(-1j * t * H)
        r3 = max(r3, np.linalg.norm(U - expm(-1j * t * a_ * sz), 2))
        r4 = max(r4, np.linalg.norm(U - expm(-1j * t * at * sz), 2))
    b3 = min(2, (t + np.sqrt(2)) / (mm - 2))
    b4 = min(2, np.sqrt(2) / (mm - 2) + t * (2 / (mm * (mm - 2)) + 1 / (2 * (mm - 2) ** 3)))
    worst.append((mm, t, r3, b3, r4, b4))
check("F1", all(r3 <= b3 + 1e-12 and r4 <= b4 + 1e-12 for (_, _, r3, b3, r4, b4) in worst),
      "C3/C4 (m,t,sampled C3,bound C3,sampled C4,bound C4): " + "; ".join(f"({a:g},{b:g},{c:.4g},{d:.4g},{e:.4g},{f:.4g})" for a, b, c, d, e, f in worst))


# F2/F3. Kernel by trapezoid sums on an N x N grid k_j = -pi + 2 pi j / N (the dossier's convention).
def kernel_grid(mm, t, N):
    kk = -np.pi + 2 * np.pi * np.arange(N) / N
    Q1, Q2 = np.meshgrid(kk, kk, indexing="ij")
    d1, d2, d3 = np.sin(Q1), np.sin(Q2), mm + np.cos(Q1) + np.cos(Q2)
    w = np.sqrt(d1**2 + d2**2 + d3**2)
    cw, sw = np.cos(t * w), np.where(w > 0, np.sin(t * w) / np.where(w > 0, w, 1), t)
    # U = cos(tw) I - i sin(tw)/w (d.sigma)
    U = np.empty((N, N, 2, 2), complex)
    U[..., 0, 0] = cw - 1j * sw * d3
    U[..., 1, 1] = cw + 1j * sw * d3
    U[..., 0, 1] = -1j * sw * (d1 - 1j * d2)
    U[..., 1, 0] = -1j * sw * (d1 + 1j * d2)
    return kk, U


def kernel_at(kk, U, xs):
    N = len(kk)
    E = np.exp(1j * np.outer(xs, kk))  # (len xs, N)
    return np.einsum("ai,bj,ijpq->abpq", E, E, U) / N**2


def opnorm(A):
    return np.linalg.norm(A, 2)


# F2: C5 locality bound F_t(r) = r arcosh(r/t) - sqrt(r^2 - t^2) for r > t, at m = 3 (gapped) and m = 2 (gapless).
def Ft(r, t):
    r = abs(r)
    return 0.0 if r <= t else r * np.arccosh(r / t) - np.sqrt(r * r - t * t)


ok2, rows2 = True, []
for mm, t in [(3.0, 5.0), (2.0, 5.0), (3.0, 20.0)]:
    kk, U = kernel_grid(mm, t, 512)
    xs = np.arange(-60, 61)
    K = kernel_at(kk, U, xs)
    ratio = 0.0
    for ia, xa in enumerate(xs):
        for ib, xb in enumerate(xs):
            bnd = np.exp(-Ft(xa, t) - Ft(xb, t))
            nrm = opnorm(K[ia, ib])
            if bnd > 1e-12:  # below this the reference grid's own error dominates
                ratio = max(ratio, nrm / bnd)
    ok2 &= ratio <= 1 + 1e-9
    rows2.append((mm, t, ratio))
check("F2", ok2, "C5: max ||K(t,x)|| / exp(-F_t(|x1|)-F_t(|x2|)) over |x|_inf <= 60 where the bound > 1e-12, N = 512: "
      + "; ".join(f"m={a:g},t={b:g}: {c:.4g}" for a, b, c in rows2) + " (m = 2 is gapless: the bound is mass-free)")

# F3: aliasing identity sign for odd N on the -pi-offset grid, and the C6 bound.
mm, t, R = 3.0, 20.0, 20
kk65, U65 = kernel_grid(mm, t, 65)
kkr, Ur = kernel_grid(mm, t, 512)
xs = np.arange(-R, R + 1)
K65 = kernel_at(kk65, U65, xs)
Kref = kernel_at(kkr, Ur, xs)
disc = max(opnorm(K65[i, j] - Kref[i, j]) for i in range(len(xs)) for j in range(len(xs)))
eta, dlt, N, L = 1.5, 0.05, 65, 65 - R
bound6 = 4 * (1 + np.exp(-dlt)) / ((1 - np.exp(-eta)) * (1 - np.exp(-dlt))) * np.exp(t * (np.sinh(eta) + np.sinh(dlt)) - eta * L)
# alias identity sign: needs aliases of order one, so a small odd grid N = 5 at t = 3, x = (-1, 0), reference K from N = 512


def kernel_pt(kk, U, xa, xb):
    Nn = len(kk)
    return np.einsum("i,j,ijpq->pq", np.exp(1j * xa * kk), np.exp(1j * xb * kk), U) / Nn**2


kk5, U5 = kernel_grid(3.0, 3.0, 5)
kkR, UR = kernel_grid(3.0, 3.0, 512)
Lr = range(-8, 9)
terms = {(l1, l2): kernel_pt(kkR, UR, -1 + 5 * l1, 5 * l2) for l1 in Lr for l2 in Lr}
signed = sum(((-1) ** (5 * (l1 + l2))) * K for (l1, l2), K in terms.items())
unsigned = sum(terms.values())
K5 = kernel_pt(kk5, U5, -1, 0)
e_signed, e_unsigned = opnorm(K5 - signed), opnorm(K5 - unsigned)
check("F3", disc <= bound6 and abs(bound6 - 8.4751320538e-9) < 1e-18,
      f"C6: bound {bound6:.10e} (dossier 8.4751320538e-9); observed max ||K_65 - K_512|| over |x|<=20, m=3, t=20: {disc:.4e} "
      f"(dossier 2.4317e-13)")
check("F3b", e_signed < 1e-10 and e_unsigned > 1e-2,
      f"alias sign, N = 5, m = 3, t = 3, x = (-1,0), grid k_j = -pi + 2 pi j/N: |K_5 - sum (-1)^(N(l1+l2)) K(x+Nl)| = {e_signed:.2e}, "
      f"|K_5 - unsigned sum| = {e_unsigned:.3f}. The dossier's unsigned identity (C6) holds on the grid starting at 0 "
      "(or for even N); on the -pi grid with odd N the terms carry (-1)^(N l). The norm bound is unaffected")

# F4. D1 / D3 weak-link chain: closed-form bounds (seed-independent) and a sampled amplitude.
J, j, t, n, src, dst = 0.55, 0.01, 3.0, 16, 3, 13
eta = np.arccosh((dst - src) / (2 * J * t))
ordinary = np.exp(-eta * (dst - src) + t * 2 * J * np.sinh(eta))
beta = np.arcsinh((J / j) * np.sinh(eta)) - eta
tailored = ordinary * np.exp(-beta)
rng = np.random.default_rng(20261110)
onsite = rng.uniform(-0.7, 0.7, n)
Hc_ = np.diag(onsite).astype(complex)
for i in range(n - 1):
    Hc_[i, i + 1] = Hc_[i + 1, i] = (j if i == 7 else J)
amp = abs(expm(-1j * t * Hc_)[dst, src])
# row sums under the tailored weight: phi(v) = eta v for v <= 7, eta v + beta for v >= 8
phi = np.array([eta * v + (beta if v >= 8 else 0.0) for v in range(n)])
rows = [sum(abs(Hc_[v, w]) * np.sinh(abs(phi[v] - phi[w])) for w in range(n) if w != v) for v in range(n)]
check("F4", abs(ordinary - 2.499634380e-4) < 1e-12 and abs(tailored - 4.679594231e-6) < 1e-14
      and max(rows) <= 2 * J * np.sinh(eta) * (1 + 1e-12) and amp <= tailored,
      f"D3: eta = {eta:.9f}, beta = {beta:.9f}, ordinary {ordinary:.10e}, tailored {tailored:.10e} (dossier values reproduced); "
      f"max row sum {max(rows):.6f} <= 2J sinh eta = {2 * J * np.sinh(eta):.6f}; sampled |U_13,3| = {amp:.4e} "
      f"(dossier 5.680852681e-7; agreement depends on the chain construction, which the dossier does not fully specify)")

# F5. D4 truncation inequality on an own seeded instance (the dossier's construction is not fully specified).
rng = np.random.default_rng(20261111)
n, J, t, lo, hi, src = 31, 0.55, 3.0, 6, 24, 15
Hf = np.diag(rng.uniform(-0.7, 0.7, n)).astype(complex)
for i in range(n - 1):
    Hf[i, i + 1] = Hf[i + 1, i] = J
psi0 = np.zeros(n, complex)
psi0[src] = 1
full = expm(-1j * t * Hf) @ psi0
idx = np.arange(lo, hi + 1)
trunc = np.zeros(n, complex)
trunc[idx] = expm(-1j * t * Hf[np.ix_(idx, idx)]) @ psi0[idx]
err = np.linalg.norm(full - trunc)
Rd = min(src - lo, hi - src)
j_d = J  # two boundary edges, onto distinct outside sites: ||J_d|| = J
best = min(j_d * np.exp(-e * Rd) * (np.exp(2 * J * np.sinh(e) * t) - 1) / (2 * J * np.sinh(e)) for e in np.linspace(0.01, 5, 2000))
check("F5", err <= best, f"D4 own instance (seed 20261111, onsite U(-0.7,0.7), R = {Rd}): error {err:.4e} <= bound {best:.4e}")

# F6. D5 premise: QWZ m = 1 band range (the contour needs omega in [1, 3]).
kk = np.linspace(-np.pi, np.pi, 1201)
Q1, Q2 = np.meshgrid(kk, kk)
w1 = np.sqrt(np.sin(Q1) ** 2 + np.sin(Q2) ** 2 + (1 + np.cos(Q1) + np.cos(Q2)) ** 2)
check("F6", w1.min() >= 1 - 1e-12 and abs(w1.max() - 3) < 1e-12,
      f"QWZ m = 1 positive band on a 1201^2 grid: min {w1.min():.12f}, max {w1.max():.12f} "
      "(exact: P - 1 = (1 + c1 + c2)^2 + s1^2 + s2^2 - 1 >= 0 needs proof; grid only)")
# exact: P_1 - 1 = 2 + 2(c1+c2) + 2c1c2 = 2(1+c1)(1+c2) >= 0
check("F6x", sp.expand(sp.expand_trig((1 + sp.cos(x1) + sp.cos(x2)) ** 2 + sp.sin(x1) ** 2 + sp.sin(x2) ** 2 - 1
                                      - 2 * (1 + sp.cos(x1)) * (1 + sp.cos(x2))).rewrite(sp.cos)).simplify() == 0,
      "exact: P_1 - 1 = 2(1 + cos k1)(1 + cos k2) >= 0, so omega >= 1 for m = 1 (D5's clearance delta = 1/2 holds)")

# F7. One-site Kerr negative control N10.
g, t, e = 100.0, 1.0, 1e-3
p1, p2 = 1.0, 1.0 + e
ratio = abs(p1 * np.exp(-1j * g * t * p1**2) - p2 * np.exp(-1j * g * t * p2**2)) / e
check("F7", abs(ratio - 199.8686933) < 1e-4, f"|psi(1) - psi(1.001)| / 0.001 at g = 100, t = 1: {ratio:.7f} (dossier 199.8686933)")

# F8. LE constant versus Landau (C1), mpmath 30 digits, not rigorous.
mp.mp.dps = 30
AB = (24 * mp.mpf(2) ** (mp.mpf(1) / 4) + 36 * mp.mpf(2) ** (mp.mpf(1) / 6)) ** 2
cL = mp.findroot(lambda x: mp.diff(lambda y: y ** (mp.mpf(1) / 3) * mp.besselj(0, y), x), 0.78)
cval = cL ** (mp.mpf(1) / 3) * mp.besselj(0, cL)
check("F8", abs(AB - mp.mpf("4754.047960596477752")) < 1e-12 and abs(cval - mp.mpf("0.7857468704985")) < 1e-12,
      f"(A+B)^2 = {mp.nstr(AB, 19)}; c = sup x^(1/3) J_0 = {mp.nstr(cval, 16)} at x0 = {mp.nstr(cL, 15)}; "
      f"ratio (A+B)^2/(2 pi c)^2 = {mp.nstr(AB / (2 * mp.pi * cval) ** 2, 12)} (0.7857 < c: a truncation, never an upper bound)")

# ---------------------------------------------------------------- record
try:
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
except OSError:
    commit = "unknown"
print(f"RUNTIME python {platform.python_version()} sympy {sp.__version__} mpmath {mp.__version__} numpy {np.__version__} "
      f"scipy {scipy.__version__} platform {platform.platform()} commit {commit}")
print(f"OVERALL {'PASS' if all(OK) else 'FAIL'} {sum(OK)}/{len(OK)}")
sys.exit(0 if all(OK) else 1)
