#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified truth checks of the batch-FR statements (OscInt/Statements/FiniteRing.lean) on samples, run by the lead
before the freeze. Tooling, not evidence for a Lean theorem. Arb balls throughout: an equality passes only if the
two enclosures overlap and are narrower than 1e-25; an inequality only if it holds for the whole enclosures.

Two methods that share no formula: the kernels as written in the Lean definitions (a discrete Fourier sum for the
ring; its odd reflection for the chain; the Bessel form e^{-2it} i^n J_n(2t) for the line, itself checked against
the integral of the definition), and the matrix exponential exp(itL) of the graph Laplacian L (ring: circulant with
-2 on the diagonal; chain: tridiagonal with -2 on the diagonal).

FR-K  derivative in t against i (R(r+1) + R(r-1) - 2R(r)) (the derivative from the Fourier sum, term by term, and
      a central difference as a coarse second opinion); the value at t = 0; the period.
FR-U  the ring kernel against exp(itL): U[x, y] = R_N(t, x - y); so the kernel sum is the unique solution.
FR-S  the coset sum over |m| <= K against the ring kernel, with the certified tail from LC-1.
FR-P  the finite-size inequality 2 e^{2|t| sinh eta} cosh(r eta) / (e^{eta N} - 1) on a grid, and how sharp it is
      (a first draft had e^{|r| eta} in place of cosh(r eta): true, but its control "without the factor 2" did not
      fail, which showed the draft was a factor 2 from sharp; the statement was sharpened before the freeze).
FC-K  walls, unit datum; FC-U: the chain kernel against exp(itL_chain); FC-P: the inequality on a grid.
Controls (each must fail): FR-P without the factor 2; FR-P with e^{|t| sinh} in place of e^{2|t| sinh}; FC-P
without the wall term e^{-(x+y) eta}; the chain kernel with an even reflection (free ends) against exp(itL_chain);
the ring kernel of N sites against the matrix exponential of the open chain of N sites.

Usage: python3 -I numerics/review/fr_statement_checks.py
"""
import platform
import random

import flint
from flint import acb, acb_mat, arb, ctx

ctx.prec = 700
I = acb(0, 1)
PI = arb.pi()
TOL = arb(10) ** (-25)
rng = random.Random(20261116)
results = []


def same(x, y):
    d = acb(x) - acb(y)
    return d.contains(0) and bool(abs(d).upper() < TOL)


def le(x, y):
    return bool(y - x >= 0)


def report(name, ok, detail):
    results.append((name, ok))
    print(f"{name}: {'PASS' if ok else 'FAIL'}  {detail}")


def ring(N, t, r):
    return sum(((I * (2 * t * ((2 * PI * j / N).cos() - 1) + r * 2 * PI * j / N)).exp() for j in range(N)), acb(0)) / N


def dring(N, t, r):
    """d/dt of the Fourier sum, term by term."""
    return sum((I * 2 * ((2 * PI * j / N).cos() - 1) * (I * (2 * t * ((2 * PI * j / N).cos() - 1) + r * 2 * PI * j / N)).exp()
                for j in range(N)), acb(0)) / N


def line(t, n):
    return (-2 * I * t).exp() * I ** (n % 4) * acb(2 * t).bessel_j(n)


def line_from_definition(t, n):
    k1 = acb.integral(lambda k, _: (I * (2 * t * k.cos() + n * k)).exp(), -PI, PI)
    return (-2 * I * t).exp() * k1 / (2 * PI)


def chain(M, t, x, y):
    return ring(2 * (M + 1), t, x - y) - ring(2 * (M + 1), t, x + y)


def expm(L, t):
    return (acb_mat(L) * (I * t)).exp()


def ring_laplacian(N):
    L = [[acb(0)] * N for _ in range(N)]
    for a in range(N):
        L[a][a] += -2
        L[a][(a + 1) % N] += 1
        L[a][(a - 1) % N] += 1
    return L


def chain_laplacian(M):
    L = [[acb(0)] * M for _ in range(M)]
    for a in range(M):
        L[a][a] += -2
        if a + 1 < M:
            L[a][a + 1] += 1
            L[a + 1][a] += 1
    return L


TS = [arb(0), arb("0.5"), arb(1), arb(2), arb("-1.5"), arb("3.7")]

# the line kernel: Bessel form against the definition
n = bad = 0
for t in TS:
    for k in (-7, -2, 0, 1, 3, 8):
        n += 1
        bad += not same(line(t, k), line_from_definition(t, k))
report("line kernel: Bessel form against the integral of the definition", bad == 0, f"{n} points, {bad} failures")

# FR-K
n = bad = 0
worst_fd = 0.0
for N in (1, 2, 3, 4, 5, 8, 13):
    for t in TS:
        for r in range(-N - 2, N + 3):
            rhs = I * (ring(N, t, r + 1) + ring(N, t, r - 1) - 2 * ring(N, t, r))
            n += 1
            bad += not same(dring(N, t, r), rhs)
            h = arb(10) ** (-12)
            fd = (ring(N, t + h, r) - ring(N, t - h, r)) / (2 * h)
            worst_fd = max(worst_fd, float(abs(fd - rhs).upper()))
            bad += not same(ring(N, arb(0), r), 1 if r % N == 0 else 0)
            bad += not same(ring(N, t, r + N), ring(N, t, r))
report("FR-K equation, unit datum, period", bad == 0 and worst_fd < 1e-15, f"{n} points, {bad} failures; central difference agrees within {worst_fd:.1e}")

# FR-U
n = bad = 0
for N in (1, 2, 3, 5, 8, 13):
    for t in TS[1:]:
        U = expm(ring_laplacian(N), t)
        for x in range(N):
            for y in range(N):
                n += 1
                bad += not same(U[x, y], ring(N, t, x - y))
report("FR-U ring kernel against exp(itL) of the ring", bad == 0, f"{n} entries, {bad} failures")
U = expm(chain_laplacian(5), arb(1))
ctrl = all(same(U[x, y], ring(5, arb(1), x - y)) for x in range(5) for y in range(5))
report("FR-U control (ring kernel against the open chain must differ)", not ctrl, f"all entries equal: {ctrl}")

# FR-S
n = bad = 0
for N in (1, 2, 3, 5, 8):
    for t in TS:
        for r in (-3, 0, 1, 4):
            K = 60
            s = sum((line(t, r + m * N) for m in range(-K, K + 1)), acb(0))
            eta = arb(2)
            # tail: |G(t, n)| <= e^{2|t| sinh eta - |n| eta}; |r + mN| >= |m|N - |r|
            tail = 2 * (2 * abs(t) * eta.sinh() + abs(r) * eta).exp() * (-eta * N * (K + 1)).exp() / (1 - (-eta * N).exp())
            n += 1
            bad += not le(abs(s - ring(N, t, r)), tail + TOL)
report("FR-S coset sum (|m| <= 60) against the ring kernel, within the certified tail", bad == 0, f"{n} points, {bad} failures")

# FR-P
n = bad = 0
worst = 0.0
fail_no2 = fail_half = 0
for N in (1, 2, 3, 5, 8, 13, 21):
    for t in TS:
        for r in range(-N, N + 1, max(1, N // 3)):
            lhs = abs(ring(N, t, r) - line(t, r))
            for es in ("0.05", "0.3", "1", "2", "4", "12"):
                eta = arb(es)
                rhs = 2 * (2 * abs(t) * eta.sinh()).exp() * (r * eta).cosh() / ((eta * N).exp() - 1)
                n += 1
                bad += not le(lhs, rhs)
                worst = max(worst, float((lhs / rhs).mid()))
                fail_no2 += bool(lhs > rhs / 2)
                fail_half += bool(lhs > 2 * (abs(t) * eta.sinh()).exp() * (r * eta).cosh() / ((eta * N).exp() - 1))
report("FR-P finite-size inequality", bad == 0, f"{n} comparisons, {bad} violations, largest ratio {worst:.6f}")
report("FR-P control (without the factor 2 must fail somewhere)", fail_no2 > 0, f"{fail_no2} certified violations")
report("FR-P control (e^{|t| sinh} must fail somewhere)", fail_half > 0, f"{fail_half} certified violations")

# FC-K, FC-U
n = bad = 0
ctrl_even = True
for M in (1, 2, 3, 5, 9):
    for t in TS:
        for y in range(1, M + 1):
            n += 1
            bad += not (same(chain(M, t, 0, y), 0) and same(chain(M, t, M + 1, y), 0))
            for x in range(1, M + 1):
                bad += not same(chain(M, arb(0), x, y), 1 if x == y else 0)
        if not bool(t == 0):
            U = expm(chain_laplacian(M), t)
            for x in range(1, M + 1):
                for y in range(1, M + 1):
                    n += 1
                    bad += not same(U[x - 1, y - 1], chain(M, t, x, y))
                    even = ring(2 * (M + 1), t, x - y) + ring(2 * (M + 1), t, x + y)
                    ctrl_even = ctrl_even and same(U[x - 1, y - 1], even)
report("FC-K walls and unit datum; FC-U chain kernel against exp(itL) of the open chain", bad == 0, f"{n} checks, {bad} failures")
report("FC-U control (even reflection must differ)", not ctrl_even, f"all entries equal: {ctrl_even}")

# FC-P
n = bad = 0
worst = 0.0
fail_nowall = 0
for M in (1, 2, 5, 9, 16):
    N = 2 * (M + 1)
    for t in TS:
        for x in range(1, M + 1, max(1, M // 4)):
            for y in range(1, M + 1, max(1, M // 4)):
                lhs = abs(chain(M, t, x, y) - line(t, x - y))
                for es in ("0.05", "0.3", "1", "2", "4"):
                    eta = arb(es)
                    E = (2 * abs(t) * eta.sinh()).exp()
                    img = 2 * (((x - y) * eta).cosh() + ((x + y) * eta).cosh()) / ((eta * N).exp() - 1)
                    rhs = E * ((-(x + y) * eta).exp() + img)
                    n += 1
                    bad += not le(lhs, rhs)
                    worst = max(worst, float((lhs / rhs).mid()))
                    fail_nowall += bool(lhs > E * img)
report("FC-P finite-size inequality", bad == 0, f"{n} comparisons, {bad} violations, largest ratio {worst:.6f}")
report("FC-P control (without the wall term must fail somewhere)", fail_nowall > 0, f"{fail_nowall} certified violations")

# the numbers a device user would quote: M = 9, centre, best eta on a grid
for M, x, y, ts in ((9, 5, 5, "1"), (9, 5, 5, "2"), (5, 3, 3, "1"), (5, 3, 3, "2")):
    t = arb(ts)
    N = 2 * (M + 1)
    best = None
    for e10 in range(1, 60):
        eta = arb(e10) / 10
        rhs = (2 * abs(t) * eta.sinh()).exp() * ((-(x + y) * eta).exp() + 2 * (((x - y) * eta).cosh() + ((x + y) * eta).cosh()) / ((eta * N).exp() - 1))
        if best is None or bool(rhs < best[1]):
            best = (eta, rhs)
    true = abs(chain(M, t, x, y) - line(t, x - y))
    print(f"  chain M = {M}, x = y = {x}, t = {ts}: |C - G| = {true.str(6)}; FC-P bound {best[1].str(6)} at eta = {best[0].str(3)}")

npass = sum(ok for _, ok in results)
print(f"summary: {npass} of {len(results)} checks pass")
print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, "
      f"working precision {ctx.prec} bits, seed 20261116")
