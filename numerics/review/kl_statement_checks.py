#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified truth checks of the batch-KL statements (OscInt/Statements/KusminLandau.lean), run by the lead before
the freeze. Tooling, not evidence for a Lean theorem. Sequences have exact rational terms; sums are Arb balls.

T1  KL-D on 4000 random sequences: N in 0..12, lam = p/q with q <= 12, an integer shift k in -2..2, differences
    drawn in [k + lam, k + 1 - lam] and sorted up or down: |sum e(c_n)| <= cot(pi lam / 2). The test is "no
    certified violation"; the output counts the comparisons proved on the whole enclosures and those the
    enclosures do not decide (exact equality occurs at lam = 1/2). Until 2026-11-19 this line said "(certified)"
    for all 4000 (external review of batch KL).
T2  KL-C on the same sequences: <= 2 / (pi lam).
T3  Landau's extremal sequences (Arias de Reyna, arXiv:2002.05982, Lemma 2(b)): for theta = (2M+1)/(2N+1) < 1/2,
    c_j = j theta (j < N), c_j = N theta + (j - N)(1 - theta) (N <= j <= 2N): |sum| = cot(pi theta / 2) (the
    enclosures of the two sides overlap and are narrower than 1e-40), for (M, N) in (0,1), (0,2), (1,3), (0,3), (2,6).
T4  KL-F on f(x) = alpha x + beta x^2 over [0, L] with f' in [lam, 1 - lam] (20 parameter sets, exact rationals).
Controls (each must fail): C1 the bound 1/(pi theta) + 1 of Cheng-Graham's Lemma 2 at theta = 1/5 (Landau's
sequence 0, 1/5, 2/5, 6/5, 2); C2 KL-C with 1/pi at c = (0, 1/4); C3 KL-D without monotonicity at
c = (0, 1/4, 1, 5/4, 2), lam = 1/4; C4 KL-D with lam = 1 allowed (N = 0); C5 any constant below cot at theta = 1/3.
The random generator is Python's Mersenne Twister with seed 20261116.

Usage: python3 -I numerics/review/kl_statement_checks.py
"""
import platform
import random
import sys
from fractions import Fraction as F

import flint
from flint import acb, arb, ctx

ctx.prec = 200
PI = arb.pi()


def A(q):
    return arb(q.numerator) / arb(q.denominator)


def S(c):
    return abs(sum(((acb(0, 2) * PI * A(x)).exp() for x in c), acb(0)))


def cot(lam):
    x = PI * A(lam) / 2
    return x.cos() / x.sin()


def le(x, y):
    d = y - x
    return True if d >= 0 else (False if d < 0 else None)


ok = True
rng = random.Random(20261116)
bad1 = bad2 = 0
pr1 = pr2 = 0
worst = 0.0
for _ in range(4000):
    q = rng.randint(2, 12)
    p = rng.randint(1, q // 2)
    lam = F(p, q)
    N = rng.randint(0, 12)
    k = rng.randint(-2, 2)
    den = rng.choice([1, 2, 3, 5, 7, 60])
    diffs = []
    for _ in range(N):
        lo, hi = k + lam, k + 1 - lam
        steps = rng.randint(0, den * 4)
        diffs.append(lo + (hi - lo) * F(steps, den * 4))
    diffs.sort(reverse=rng.random() < 0.5)
    c = [F(rng.randint(-5, 5), 7)]
    for d in diffs:
        c.append(c[-1] + d)
    s = S(c)
    r1, r2 = le(s, cot(lam)), le(s, 2 / (PI * A(lam)))
    if r1 is False:
        bad1 += 1
    if r2 is False:
        bad2 += 1
    pr1 += r1 is True
    pr2 += r2 is True
    worst = max(worst, float((s / cot(lam)).mid()))
print(f"T1 KL-D: 4000 sequences, proved {pr1}, undecided {4000 - pr1 - bad1}, certified violations {bad1}, "
      f"largest ratio |S|/cot {worst:.6f} "
      "(a ratio of exactly 1 is an attained bound; undecidable comparisons at equality are not violations)")
print(f"T2 KL-C: proved {pr2}, undecided {4000 - pr2 - bad2}, certified violations {bad2}")
ok = ok and bad1 == 0 and bad2 == 0

t3 = True
for (M, N) in [(0, 1), (0, 2), (1, 3), (0, 3), (2, 6)]:
    th = F(2 * M + 1, 2 * N + 1)
    c = [j * th for j in range(N)] + [N * th + (j - N) * (1 - th) for j in range(N, 2 * N + 1)]
    s, b = S(c), cot(th)
    good = s.overlaps(b) and float(s.rad()) < 1e-40 and float(b.rad()) < 1e-40
    t3 = t3 and good
    print(f"T3 theta = {th}: |S| = {s.str(15)}, cot = {b.str(15)}: {'equal to 40 digits' if good else 'MISMATCH'}")
ok = ok and t3

bad4 = 0
for i in range(20):
    lam = F(rng.randint(1, 5), 12)
    L = rng.randint(1, 8)
    alpha = lam + (1 - 2 * lam) * F(rng.randint(0, 5), 10)
    beta = ((1 - lam) - alpha) / (2 * L) * F(rng.randint(0, 10), 10)
    f = lambda x: alpha * x + beta * x * x
    if le(S([f(F(n)) for n in range(0, L + 1)]), cot(lam)) is False:
        bad4 += 1
print(f"T4 KL-F: 20 quadratic phases, certified violations {bad4}")
ok = ok and bad4 == 0

th = F(1, 5)
c5 = [F(0), F(1, 5), F(2, 5), F(6, 5), F(2)]
ctl = [
    ("C1 Cheng-Graham 1/(pi theta) + 1 at theta = 1/5", le(S(c5), 1 / (PI * A(th)) + 1)),
    ("C2 1/(pi lam) at (0, 1/4)", le(S([F(0), F(1, 4)]), 1 / (PI * A(F(1, 4))))),
    ("C3 no monotonicity", le(S([F(0), F(1, 4), F(1), F(5, 4), F(2)]), cot(F(1, 4)))),
    ("C4 lam = 1, N = 0", le(S([F(0)]), cot(F(1)))),
    ("C5 cot - 1/1000 at theta = 1/3", le(S([F(0), F(1, 3), F(1)]), cot(F(1, 3)) - arb("0.001"))),
]
for name, flag in ctl:
    print(f"{name}: {'fails as required' if flag is False else 'NOT REJECTED'}")
    ok = ok and flag is False
print(f"C1 detail: |S| = {S(c5).str(10)}, 1/(pi theta) + 1 = {(1 / (PI * A(th)) + 1).str(10)}, cot(pi/10) = {cot(th).str(10)}")
print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, {ctx.prec} bits")
print("RESULT:", "PASS" if ok else "NOT PASS")
sys.exit(0 if ok else 1)
