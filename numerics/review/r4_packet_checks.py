#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's checks of the external R4 research packet (2026-11-14): the W2 quadratic bound (Q), its benchmark
coefficient and observation ratios, (Q) on an exact Gaussian with a non-diagonal Hessian and a linear term, the W2
threshold arithmetic, the L1 bound on a datum, and the W1 operator datum.

Answers file: review/2026-11-14-external-R4-answers.md. The lead's own computations, independent of the packet's
scripts (which were run separately in a network-less sandbox). The saddle integrals are evaluated by a third method,
different from both of the packet's: exact reduction to incomplete gamma functions (mpmath gammainc, 50 digits).
Norms are exact (SymPy). Run: python3 -I numerics/review/r4_packet_checks.py  (mpmath, sympy; versions printed).
"""
import sys, platform
from fractions import Fraction as Fr
import mpmath as mp, sympy as sy
print("runtime", sys.version.split()[0], platform.platform(), "mpmath", mp.__version__, "sympy", sy.__version__)
mp.mp.dps = 50
res = {}
def rep(name, ok, **kw):
    res[name] = bool(ok); print(("PASS " if ok else "FAIL ") + name, kw)

# ---- the packet's benchmark amplitude (Archive 2, W2/PACKET.md "Numerics") ----
t = sy.symbols('t', real=True)
w = (1 - t**2)**3
a = w*(1 + t/5 + t**2/7 + sy.I*(sy.Rational(1, 11) + t/13 + t**2/17))
b = w*(1 + t/3 + t**2/19 + sy.I*(sy.Rational(1, 23) + t/29 + t**2/31))
def l2sq(f):  # exact ∫_{-1}^{1} |f|^2
    return sy.integrate(sy.expand(f*sy.conjugate(f)), (t, -1, 1))
# A(x, y) = a(X) b(Y) with (X, Y) a rotation plus a shift of (x, y): Euclidean L2 norms and the Laplacian are invariant,
# so ||A||^2 = ||a||^2 ||b||^2 and ||ΔA||^2 = ∫∫ |a'' b + a b''|^2 = |a''|^2|b|^2 + |a|^2|b''|^2 + 2 Re(<a'',a><b,b''>)
a2, b2 = sy.diff(a, t, 2), sy.diff(b, t, 2)
ip = lambda f, g: sy.integrate(sy.expand(f*sy.conjugate(g)), (t, -1, 1))
U2 = sy.nsimplify(l2sq(a)*l2sq(b))
V2 = sy.simplify(l2sq(a2)*l2sq(b) + l2sq(a)*l2sq(b2) + 2*sy.re(ip(a2, a)*ip(b, b2)))
U, V = mp.sqrt(mp.mpf(sy.Rational(U2))), mp.sqrt(mp.mpf(sy.Rational(V2)))
eta = 15  # saddle (3X^2 - 5Y^2)/2: H = diag(3, -5) in the rotated frame, |det H| = 15
B = mp.pi/mp.sqrt(eta)*mp.sqrt(U*V)
rep("Q1 benchmark coefficient B = pi/sqrt(15) sqrt(||A||_2 ||ΔA||_2) lies in the packet's [1.858998723437, 1.858998723438]",
    mp.mpf("1.858998723437") <= B <= mp.mpf("1.858998723438"), B=mp.nstr(B, 15))

# ---- saddle integral by incomplete gamma: ∫_{-1}^{1} t^k e^{i α t^2} dt ----
def moment(k, al):
    if k % 2: return mp.mpc(0)
    s = mp.mpf(k + 1)/2  # 2∫_0^1 t^k e^{iαt^2} dt = ∫_0^1 u^{s-1} e^{iαu} du = (-iα)^{-s} γ(s, -iα)
    z = -1j*al
    return z**(-s)*mp.gammainc(s, 0, z)
def coeffs(f):
    p = sy.Poly(sy.expand(f), t)
    return {m[0]: complex(c) for m, c in zip(p.monoms(), p.coeffs())}
ca, cb = coeffs(a), coeffs(b)
def I_saddle(m):
    ia = sum(mp.mpc(c.real, c.imag)*moment(k, mp.mpf(3)*m/2) for k, c in ca.items())
    ib = sum(mp.mpc(c.real, c.imag)*moment(k, -mp.mpf(5)*m/2) for k, c in cb.items())
    return ia*ib  # Jacobian of the rotation is 1; the shift moves the integration domain, not the integral
# cross-check the moment formula against direct quadrature at small α
mx = max(abs(moment(k, al) - mp.quad(lambda x: x**k*mp.expjpi(al*x**2/mp.pi), [-1, 0, 1])) for k in (0, 2, 6) for al in (0.7, -4))
rep("Q2 incomplete-gamma moments agree with direct quadrature (k = 0, 2, 6)", mx < mp.mpf(10)**-30, max_err=float(mx))
ratios = {}
for m in (8, 32, 128, 512, 2048, 8192):
    Im = abs(I_saddle(m))
    ratios[m] = B/(m*Im)
rlo, rhi = min(ratios.values()), max(ratios.values())
rep("Q3 bound/|I| on the saddle at m = 8 ... 8192 lies in the packet's [1.140113304341, 1.151319433660] and is >= 1",
    abs(rlo - mp.mpf("1.140113304341")) < 1e-11 and abs(rhi - mp.mpf("1.151319433660")) < 1e-11 and rlo >= 1,
    ratios={k: mp.nstr(v, 13) for k, v in ratios.items()})

# ---- (Q) on an exact Gaussian, non-diagonal H, linear term p (outside the compact-support class: a check of the
# constant only; the Plancherel argument covers Schwartz amplitudes) ----
# A = e^{-|z|^2/2}: ||A||^2 = π, ΔA = (|z|^2 - 2)A, ||ΔA||^2 = π ∫_0^∞ (u - 2)^2 e^{-u} du = 2π
UG, VG = mp.sqrt(mp.pi), mp.sqrt(2*mp.pi)
worst = mp.mpf(0)
for H, p in (([[2, 3], [3, -1]], [0.3, -1.1]), ([[0.5, 0.2], [0.2, 0.9]], [0, 0]), ([[-4, 1], [1, 3]], [2, 2])):
    Hm, pv = mp.matrix(H), mp.matrix(p)
    for m in (1, 5, 40, 300):
        Mq = mp.eye(2) - 1j*m*Hm  # ∫ e^{-z^T M z / 2 + i m p·z} dz = 2π det(M)^{-1/2} e^{-m^2 p^T M^{-1} p / 2}
        val = 2*mp.pi/mp.sqrt(mp.det(Mq))*mp.exp(-(m**2)*(pv.T*mp.inverse(Mq)*pv)[0]/2)
        bound = mp.pi/(m*mp.sqrt(abs(mp.det(Hm))))*mp.sqrt(UG*VG)
        worst = max(worst, abs(val)/bound)
rep("Q4 (Q) holds on exact Gaussians with non-diagonal H and linear terms (max |I|/bound < 1)", worst < 1, max_ratio=mp.nstr(worst, 8))

# ---- threshold arithmetic: first integer m with B m^{-α} < T1 ----
T1 = Fr(574721155072, 586519735725)
rows = {"Q saddle": ("1.858998723438", 1, 2), "L6 saddle": ("89.548394742", 1, 92), "L6 fold": ("219.843832648", Fr(5, 6), 663),
        "L1": ("19.009474378", 1, 20), "G saddle": ("75456477926.594003", 1, 77005541038)}
ok = True
for name, (Bs, al, first) in rows.items():
    thr = (mp.mpf(Bs)/mp.mpf(T1.numerator)*T1.denominator)**(mp.mpf(al.denominator)/al.numerator if isinstance(al, Fr) else mp.mpf(1)/al)
    ok &= int(mp.floor(thr)) + 1 == first
rep("Q5 the packet's first integers (2, 92, 663, 20, 77005541038) follow from its B values and T1", ok)

# ---- L1 on a datum: Q(z) = 2 z1 + z1^2/2 + z2^3 on the support of A = w(z1) w(z2), e = (1, 0) ----
# DQ e = 2 + z1 >= c = 1 and D^2 Q[e, e] = 1 = L2 on [-1,1]^2; U1 = ∫ |∂1 A| + ... use the max-norm operator norm
# ||DA|| = |∂1 A| + |∂2 A| (dual of the max norm is l1)
mp.mp.dps = 20
wf = lambda s: (1 - s*s)**3 if abs(s) < 1 else 0
dw = lambda s: -6*s*(1 - s*s)**2 if abs(s) < 1 else 0
U0 = mp.quad(lambda s: wf(s), [-1, 1])**2
U1 = 2*mp.quad(lambda s: abs(dw(s)), [-1, 0, 1])*mp.quad(lambda s: wf(s), [-1, 1])
viol = 0
for m in (3, 10, 40):
    I = mp.quad(lambda x: wf(x)*mp.expj(m*(2*x + x*x/2)), [-1, 0, 1])*mp.quad(lambda y: wf(y)*mp.expj(m*y**3), [-1, 0, 1])
    viol = max(viol, abs(I)/((U1/1 + 1*U0/1)/m))
rep("Q6 (L1) holds on a datum with c = 1, L2 = 1 (max |I|/bound < 1)", viol < 1, max_ratio=mp.nstr(viol, 6))

# ---- referee MINOR-1: the coordinate L6 rows used 2||a'||_2 ||b'||_2 (Cauchy-Schwarz) for ||A_XY||_1 ----
mp.mp.dps = 30
fa = sy.lambdify(t, sy.diff(a, t), "mpmath"); fb = sy.lambdify(t, sy.diff(b, t), "mpmath")
l1a = mp.quad(lambda x: abs(fa(x)), mp.linspace(-1, 1, 41)); l1b = mp.quad(lambda x: abs(fb(x)), mp.linspace(-1, 1, 41))
l2a = mp.sqrt(mp.mpf(sy.Rational(l2sq(sy.diff(a, t))))); l2b = mp.sqrt(mp.mpf(sy.Rational(l2sq(sy.diff(b, t)))))
exact, cs = l1a*l1b, 2*l2a*l2b
rep("MINOR-1 exact ||A_XY||_1 = ||a'||_1 ||b'||_1 = 4.0797 is below the Cauchy-Schwarz input 5.4191 the packet used "
    "(so the L6 rows are valid but loose by a factor 1.33)", abs(exact - mp.mpf("4.0797")) < 1e-3 and abs(cs - mp.mpf("5.4191")) < 1e-3,
    exact=mp.nstr(exact, 8), cauchy_schwarz=mp.nstr(cs, 8), factor=mp.nstr(cs/exact, 6))
mp.mp.dps = 50

# ---- W1 operator datum: f(-1) = 2+i, f(0) = -3+4i, f(1) = 5-6i on Z ----
f = {-1: complex(2, 1), 0: complex(-3, 4), 1: complex(5, -6)}
g = lambda x: f.get(x, 0)
lap = {x: g(x + 1) + g(x - 1) - 2*g(x) for x in range(-3, 4)}
rep("W1 ||f||^2 = 91 and ||Δf||^2 = 882 (direct)", round(sum(abs(v)**2 for v in f.values())) == 91
    and round(sum(abs(v)**2 for v in lap.values())) == 882)

print("RESULT", "PASS" if all(res.values()) else "FAIL", f"{sum(res.values())}/{len(res)}")
