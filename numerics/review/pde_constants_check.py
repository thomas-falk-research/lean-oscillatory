#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Independent check of the constants of the packet's PDE work package (P1, P3) and of HOP's H2 tail bound.

P1: k(t) = min(1, C|t|^(-s)), ||k||_2^2 = 2 C^(1/s) (1 + 1/(2s-1)), A = ||k||_2^(1/2).
P3: Lipschitz constant 80 A^4 R^4 |lam| of the Duhamel map, threshold eps0 = (1/(2560 |lam| A^4))^(1/4).
H2: sum_{k>=b} R^k/k! <= R^b / (b! (1 - R/(b+1))) for R < b+1.
mpmath quadrature at 50 digits; exact rational arithmetic where possible. Scoping check only, not a registered test and
never evidence for a Lean theorem (docs/design/2026-11-28-HOP-PDE-scoping.md).
"""
import itertools
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 50
worst = 0
for s, C in itertools.product([mp.mpf(2) / 3, mp.mpf(3) / 4, mp.mpf("0.55"), mp.mpf(1)], [1, 2, mp.mpf("7.5"), 100]):
    k2 = lambda t: min(1, C * abs(t) ** (-s)) ** 2 if t != 0 else 1
    t0 = C ** (1 / s)
    # tail by t = t0 e^x (smooth, exponentially decaying integrand), so slow decay (s near 1/2) is integrated accurately
    tail = mp.quad(lambda x: k2(t0 * mp.e ** x) * t0 * mp.e ** x, [0, 10, 100, mp.inf])
    num = 2 * (mp.quad(k2, [0, t0]) + tail)
    formula = 2 * C ** (1 / s) * (1 + 1 / (2 * s - 1))
    worst = max(worst, abs(num / formula - 1))
print("P1 ||k||_2^2 formula, worst relative error over 16 (s, C):", mp.nstr(worst, 5))

# P3 algebra: with R = 2 eps and 160 |lam| A^4 R^4 <= 1, the map is a 1/2-contraction into the ball of radius R.
for lam, A in [(Fraction(1), Fraction(1)), (Fraction(-3, 7), Fraction(5, 2)), (Fraction(10), Fraction(13, 10))]:
    # largest eps allowed: eps^4 = 1/(2560 |lam| A^4); check the two inequalities at that eps symbolically via eps^4
    eps4 = 1 / (2560 * abs(lam) * A ** 4)
    R4 = 16 * eps4
    lip = 80 * abs(lam) * A ** 4 * R4
    # self-map: eps + |lam| A^4 R^5 <= R  <=>  1/2 + |lam| A^4 R^4 <= 1 (divide by R = 2 eps)
    selfmap = Fraction(1, 2) + abs(lam) * A ** 4 * R4
    print(f"P3 lam={lam} A={A}: Lipschitz {lip} (want <= 1/2), self-map ratio {selfmap} (want < 1)")
    assert lip <= Fraction(1, 2) and selfmap < 1

# Pointwise quintic difference: ||u|^4 u - |v|^4 v| <= 5 max(|u|,|v|)^4 |u - v|, sampled on complex pairs.
mp.mp.dps = 30
bad = 0
import random
rnd = random.Random(20261128)
for _ in range(200000):
    u = complex(rnd.uniform(-2, 2), rnd.uniform(-2, 2)); v = complex(rnd.uniform(-2, 2), rnd.uniform(-2, 2))
    lhs = abs(abs(u) ** 4 * u - abs(v) ** 4 * v); rhs = 5 * max(abs(u), abs(v)) ** 4 * abs(u - v)
    bad += lhs > rhs * (1 + 1e-12)
print("P3 pointwise quintic difference bound, violations in 200000 seeded samples:", bad)

# H2 tail bound, exact rationals.
viol = 0
for b in range(1, 25):
    for R in [Fraction(n, 4) for n in range(1, 4 * (b + 1))]:
        if R >= b + 1:
            continue
        fact = 1
        for i in range(2, b + 1):
            fact *= i
        bound = R ** b / (fact * (1 - R / (b + 1)))
        tail = Fraction(0); term = R ** b / fact; k = b
        for _ in range(400):
            tail += term; k += 1; term = term * R / k
        viol += tail > bound
print("H2 tail bound, violations (truncated tails, 400 terms) over b = 1..24, R on a 1/4 grid below b+1:", viol)
