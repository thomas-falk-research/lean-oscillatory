#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified checks of the chains in docs/design/unlock-map.md, section 2. Tooling, not evidence for a Lean theorem.

Every comparison is made on rigorous enclosures: a check passes only if the inequality or the equality holds for
every point of the enclosures (Arb balls from python-flint, or exact rationals from the standard library). A check
that cannot be decided at the working precision is reported UNRESOLVED and counts as a failure of the run.

Two methods that share no code are used for the lattice kernel I(t, n) = int_{-pi}^{pi} e^{i(t cos k + n k)} dk:
  A  exact rationals: the power series J_n(x) = sum_m (-1)^m (x/2)^{2m+n} / (m! (m+n)!), with the alternating-series
     remainder (valid once the terms decrease), in fractions.Fraction; then I = 2 pi i^n J_n (a paper step);
  B  Arb's rigorous integration (acb.integral) of the integrand of the Lean definition `latticeKernel1`.

K1  T0E' on a grid: |I(t, n)| <= (8 (1 + sqrt 7) / 3) t^{-1/3}; and the value C*/(2 pi).
K2  methods A and B agree (their enclosures intersect and both are narrower than 1e-25).
K3  light cone (proposed N1): |I(t, n)| <= 2 pi exp(|t| sinh eta - |n| eta).
K4  ring (proposed N2): the propagator of i v' + Delta_N v = 0 on Z/N, computed three ways: the matrix exponential,
    the finite Fourier sum, and the sum of the lattice kernel over the coset n + N Z with the tail bounded by K3.
K5  open chain (proposed N3): the Dirichlet chain of M sites against the image formula on the ring of 2(M+1) sites.
K6  ballistic identity (proposed N4): sum_n n^2 |G(t, n)|^2 = 2 t^2, tail bounded by K3.
K7  partition bound (proposed N5) for omega = cos with the five-piece partition of T0E: the bound is the T0E
    formula, and it dominates |I| at the grid points.
Negative controls C1-C5: each must fail.

Usage: python3 -I numerics/review/unlock_chain_checks.py   (python-flint; versions printed at run time)
"""
import platform
import sys
from fractions import Fraction
from math import factorial

import flint
from flint import acb, acb_mat, arb, ctx

ctx.prec = 240
results = []


def record(name, status, detail):
    results.append((name, status))
    print(f"{name}: {status}  {detail}")


def le(x, y):
    """Certified x <= y for arb x, y: True, False, or None when the balls overlap."""
    d = y - x
    if d >= 0:
        return True
    if d < 0:
        return False
    return None


def verdict(flags):
    if all(f is True for f in flags):
        return "PASS"
    if any(f is False for f in flags):
        return "FAIL"
    return "UNRESOLVED"


# ---- method A: exact rationals -------------------------------------------------------------------------------------
def bessel_rational(n, x, tol=Fraction(1, 10**40)):
    """Exact rational enclosure (lo, hi) of J_n(x) for an integer n >= 0 and a rational x."""
    assert n >= 0
    h = Fraction(x) / 2
    term = h**n / factorial(n)
    s = Fraction(0)
    m = 0
    while True:
        s += term if m % 2 == 0 else -term
        nxt = term * h * h / ((m + 1) * (m + 1 + n))
        # the terms decrease from here on iff h^2 <= (m+1)(m+1+n); then |remainder| <= next term
        if h * h <= (m + 1) * (m + 1 + n) and nxt <= tol:
            return s - nxt, s + nxt
        term = nxt
        m += 1


def frac_to_arb(q):
    return arb(q.numerator) / arb(q.denominator)


def kernel_A(t, n):
    """Enclosure of I(t, n) = 2 pi i^|n| J_|n|(t) from method A, as an acb. The kernel is even in n (substitute
    k -> -k); equivalently 2 pi i^n J_n with J_{-n} = (-1)^n J_n. A first version of this script flipped the sign for
    odd negative n; check K2 (against method B) caught it."""
    lo, hi = bessel_rational(abs(n), t)
    mid = frac_to_arb((lo + hi) / 2)
    rad = frac_to_arb((hi - lo) / 2)
    j = mid + arb(0, 1) * rad  # ball of radius rad around mid
    return 2 * arb.pi() * acb(0, 1) ** (abs(n) % 4) * acb(j)


# ---- method B: rigorous integration of the Lean integrand ----------------------------------------------------------
def kernel_B(t, n):
    tt = frac_to_arb(Fraction(t))

    def f(k, _analytic):
        return (acb(0, 1) * (tt * k.cos() + n * k)).exp()

    return acb.integral(f, -arb.pi(), arb.pi())


def G(t, n):
    """Schrodinger kernel G_1(t, n) = (2 pi)^{-1} e^{-2it} I(2t, n) (schrodingerKernel 1 in the Lean statements)."""
    tt = frac_to_arb(Fraction(t))
    return (acb(0, -2) * tt).exp() * kernel_A(2 * Fraction(t), n) / (2 * arb.pi())


CSTAR = 8 * (1 + arb(7).sqrt()) / 3
TS = [Fraction(1, 10), Fraction(1, 2), Fraction(783662818503470, 10**15), Fraction(37, 10), 5, Fraction(25, 2), 40]
NS = [0, 1, 2, 3, 7, 12, 13, 40, 41, -1, -5]

# K1
flags = []
worst = arb(0)
for t in TS:
    bound = CSTAR * frac_to_arb(Fraction(t)) ** (arb(-1) / 3)
    for n in NS:
        v = abs(kernel_A(t, n))
        flags.append(le(v, bound))
        r = v / bound
        if r.mid() > worst.mid():
            worst = r
record("K1", verdict(flags), f"|I| <= C* t^(-1/3) at {len(flags)} points; C*/(2 pi) = {(CSTAR / (2 * arb.pi())).str(20)}; "
       f"largest ratio |I|/bound = {worst.str(8)}")

# K2
flags = []
maxw = 0.0
for t in TS[:6]:
    for n in [0, 1, 3, 7, -5]:
        a, b = kernel_A(t, n), kernel_B(t, n)
        flags.append(True if a.overlaps(b) else False)
        w = max(float(a.rad()), float(b.rad()))
        flags.append(True if w < 1e-25 else None)
        maxw = max(maxw, w)
record("K2", verdict(flags), f"series (exact rationals) and rigorous quadrature overlap at {len(flags) // 2} points; "
       f"widest enclosure radius {maxw:.2e}")

# K3
flags = []
for t in TS:
    tt = frac_to_arb(Fraction(t))
    for n in NS:
        for eta in [Fraction(0), Fraction(1, 10), Fraction(1, 2), 1, 2, 4]:
            e = frac_to_arb(Fraction(eta))
            flags.append(le(abs(kernel_A(t, n)), 2 * arb.pi() * (tt * e.sinh() - abs(n) * e).exp()))
record("K3", verdict(flags), f"|I(t, n)| <= 2 pi exp(|t| sinh eta - |n| eta) at {len(flags)} points")


def ring_laplacian(N):
    L = [[acb(0) for _ in range(N)] for _ in range(N)]
    for y in range(N):
        L[y][y] += -2
        L[y][(y + 1) % N] += 1
        L[y][(y - 1) % N] += 1
    return acb_mat(L)


def lightcone_tail(t, N, eta=2):
    """Certified bound for sum over |m| >= mmax+1 of |G(t, y + mN)|, |y| < N, from K3 at 2t (geometric series)."""
    e = arb(eta)
    tt = frac_to_arb(abs(Fraction(t)))
    return lambda mmax: 2 * (2 * tt * e.sinh() - e * (mmax * N)).exp() / (1 - (-e * N).exp())


# K4
flags = []
count = 0
for N in [1, 2, 3, 5, 8, 12]:
    for t in [Fraction(1, 3), 2, Fraction(11, 2)]:
        tt = frac_to_arb(Fraction(t))
        U = (ring_laplacian(N) * (acb(0, 1) * tt)).exp()
        for y in range(N):
            four = acb(0)
            for j in range(N):
                th = 2 * arb.pi() * j / N
                four += (acb(0, 1) * tt * (2 * th.cos() - 2)).exp() * (acb(0, 1) * th * y).exp()
            four /= N
            mmax = int((2 * 2 * float(t) * 3.63 + 60) / (2 * N)) + 2  # eta * mmax * N >= 2 * 2t sinh(eta) + 60, eta = 2
            alias = acb(0)
            for m in range(-mmax, mmax + 1):
                alias += G(t, y + m * N)
            tail = lightcone_tail(t, N)(mmax)
            alias_ball = alias + acb(arb(0, 1), arb(0, 1)) * tail
            mat = U[y, 0]
            flags.append(True if mat.overlaps(four) else False)
            flags.append(True if alias_ball.overlaps(mat) else False)
            flags.append(True if float(abs(alias_ball - mat).upper()) < 1e-20 else None)
            count += 1
record("K4", verdict(flags), f"ring propagator: matrix exponential = Fourier sum = coset sum of the lattice kernel "
       f"at {count} entries (N in 1, 2, 3, 5, 8, 12)")

# K5
flags = []
count = 0
for M in [1, 2, 5, 9]:
    N = 2 * (M + 1)
    P = [[acb(0) for _ in range(M)] for _ in range(M)]
    for a in range(M):
        P[a][a] += -2
        if a + 1 < M:
            P[a][a + 1] += 1
            P[a + 1][a] += 1
    for t in [Fraction(1, 3), 2, Fraction(11, 2)]:
        tt = frac_to_arb(Fraction(t))
        U = (acb_mat(P) * (acb(0, 1) * tt)).exp()
        R = (ring_laplacian(N) * (acb(0, 1) * tt)).exp()
        for a in range(1, M + 1):
            for b in range(1, M + 1):
                img = R[(a - b) % N, 0] - R[(a + b) % N, 0]
                flags.append(True if img.overlaps(U[a - 1, b - 1]) else False)
                flags.append(True if float(abs(img - U[a - 1, b - 1]).upper()) < 1e-20 else None)
                count += 1
record("K5", verdict(flags), f"open chain of M identical sites = odd part of the ring of 2(M+1) sites at {count} entries "
       f"(M in 1, 2, 5, 9)")

# K6
flags = []
for t in [Fraction(1, 3), 2, Fraction(11, 2)]:
    tt = frac_to_arb(Fraction(t))
    nmax = 120
    s = arb(0)
    for n in range(-nmax, nmax + 1):
        g = abs(G(t, n))
        s += n * n * g * g
    # tail: |G(t, n)| <= exp(2|t| sinh 1 - |n|), so sum_{|n| > nmax} n^2 |G|^2 <= 2 e^{4 t sinh 1} sum_{n > nmax} n^2 e^{-2n}
    tail = 2 * (4 * tt * arb(1).sinh()).exp() * arb(nmax + 1) ** 2 * (arb(-2) * (nmax + 1)).exp() * 4
    ball = s + arb(0, 1) * tail
    flags.append(True if ball.overlaps(2 * tt * tt) else False)
    flags.append(True if float(ball.rad()) < 1e-20 else None)
record("K6", verdict(flags), "sum n^2 |G(t, n)|^2 = 2 t^2 at t = 1/3, 2, 11/2 (enclosure radius below 1e-20)")

# K7
flags = []
for t in TS:
    tt = frac_to_arb(Fraction(t))
    mu = 1 / arb(2).sqrt()
    part = 3 * 8 * (tt * mu) ** (arb(-1) / 2) + 2 * 18 * (tt * mu) ** (arb(-1) / 3)
    t0e = 24 * arb(2) ** (arb(1) / 4) * tt ** (arb(-1) / 2) + 36 * arb(2) ** (arb(1) / 6) * tt ** (arb(-1) / 3)
    flags.append(True if part.overlaps(t0e) and float((part - t0e).rad()) < 1e-40 else None)
    for n in NS:
        flags.append(le(abs(kernel_A(t, n)), part))
record("K7", verdict(flags), "five-piece partition of cos: sum of S1.k bounds = the T0E formula, and it dominates |I|")

# ---- negative controls: each must FAIL -----------------------------------------------------------------------------
ctl = []
# C1: half the light-cone bound is false at t = 0, n = 0, eta = 0
ctl.append(("C1 half light cone", le(abs(kernel_A(Fraction(0), 0)), arb.pi())))
# C2: the coset sum with the wrong period (N + 1) does not give the ring of N sites
N, t = 5, Fraction(2)
U = (ring_laplacian(N) * (acb(0, 1) * frac_to_arb(t))).exp()
wrong = sum((G(t, 1 + m * (N + 1)) for m in range(-20, 21)), acb(0))
wrong_ball = wrong + acb(arb(0, 1), arb(0, 1)) * lightcone_tail(t, N + 1)(20)
ctl.append(("C2 wrong period", True if wrong_ball.overlaps(U[1, 0]) else False))
# C3: the chain with free ends (diagonal = minus the degree) is not the odd part of the ring
M = 5
P = [[acb(0) for _ in range(M)] for _ in range(M)]
for a in range(M):
    if a + 1 < M:
        P[a][a + 1] += 1
        P[a + 1][a] += 1
        P[a][a] += -1
        P[a + 1][a + 1] += -1
UP = (acb_mat(P) * (acb(0, 1) * frac_to_arb(t))).exp()
R = (ring_laplacian(2 * (M + 1)) * (acb(0, 1) * frac_to_arb(t))).exp()
ctl.append(("C3 free-end chain", True if (R[0, 0] - R[2, 0]).overlaps(UP[0, 0]) else False))
# C4: diffusive scaling sum n^2 |G|^2 = 2 t is false at t = 2
s = sum((n * n * abs(G(t, n)) ** 2 for n in range(-120, 121)), arb(0))
ctl.append(("C4 diffusive moment", True if (s + arb(0, 1) * arb("1e-30")).overlaps(2 * frac_to_arb(t)) else False))
# C5: a constant that is too small must be seen by the grid: C*/2 - 1/10 = 4.76 is below the kernel's value
#     t^{1/3} |I(t, 0)| = 4.937 at t = 0.7837 (the maximiser behind Landau's constant)
t0 = Fraction(783662818503470, 10**15)
ctl.append(("C5 constant too small", le(abs(kernel_A(t0, 0)), (CSTAR / 2 - arb(1) / 10) * frac_to_arb(t0) ** (arb(-1) / 3))))
for name, flag in ctl:
    status = "fails as required" if flag is False else "NOT REJECTED"
    results.append((name, "PASS" if flag is False else "FAIL"))
    print(f"{name}: {status}")

npass = sum(1 for _, s in results if s == "PASS")
print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, "
      f"working precision {ctx.prec} bits")
print(f"RESULT: {npass} of {len(results)} checks pass" + ("" if npass == len(results) else "  (NOT ALL)"))
sys.exit(0 if npass == len(results) else 1)
