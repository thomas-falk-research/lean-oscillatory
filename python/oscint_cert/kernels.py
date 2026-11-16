# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Rigorous rational enclosures of the quantities that OscInt's lattice statements bound or identify."""
from fractions import Fraction as F
from math import factorial

from . import rational as R

MAX_ORDER = 10000
MAX_ARG = 400  # |x| above this is reported UNRESOLVED (the exact series becomes expensive), never approximated


def bessel_j(n: int, x: F, digits: int = 30):
    """Enclosure of J_n(x), integer n, rational x, from the power series
    J_n(x) = sum_m (-1)^m (x/2)^(2m+n) / (m! (m+n)!) with the alternating-series remainder."""
    if abs(x) > MAX_ARG or abs(n) > MAX_ORDER:
        raise R.Unresolved(f"Bessel argument or order outside the supported range (|x| <= {MAX_ARG}, |n| <= {MAX_ORDER})")
    sign = 1
    if n < 0:
        n, sign = -n, (-1) ** (n % 2)
    if x < 0:
        x, sign = -x, sign * (-1) ** (n % 2)
    h = x / 2
    tol = F(1, 10**digits)
    term = h**n / factorial(n)
    s = F(0)
    m = 0
    while True:
        s += term if m % 2 == 0 else -term
        nxt = term * h * h / ((m + 1) * (m + 1 + n))
        if h * h <= (m + 1) * (m + 1 + n) and nxt <= tol:
            lo, hi = (s - nxt, s) if m % 2 == 0 else (s, s + nxt)
            return (lo * sign, hi * sign) if sign > 0 else (-hi, -lo)
        term = nxt
        m += 1


def population(n: int, t: F, digits: int = 30):
    """Enclosure of J_n(2t)^2: the probability at site n, time t, of the lattice Schrodinger group on Z started at
    site 0 (statement LS-K with the Bessel identification, a paper step)."""
    j = bessel_j(n, 2 * t, digits)
    a = R.iabs(j)
    return (a[0] * a[0], a[1] * a[1])


def cstar_over_two_pi(digits: int = 30):
    """Enclosure of C*/(2 pi), C* = 8 (1 + sqrt 7) / 3 (statements T0E', LS-D)."""
    s7 = R.sqrt(R.iv(7), digits + 2)
    cstar = R.mul(R.iv(F(8, 3)), R.add(R.iv(1), s7))
    return R.div(cstar, R.mul(R.iv(2), R.pi(digits + 2)))


def ls_d_envelope(d: int, t: F, digits: int = 30):
    """Enclosure of min{1, (C*/(2 pi))^d (2|t|)^(-d/3)}, the bound of statement LS-D for a datum of l^1 norm 1."""
    if d < 0:
        raise ValueError("the dimension is a natural number")
    if d > 64:
        raise R.Unresolved("dimension above 64")
    if t == 0:
        raise ValueError("LS-D excludes t = 0")
    c = R.ipow(cstar_over_two_pi(digits), d)
    rt = R.root(R.iv((2 * abs(t)) ** d), 3, digits + 2)  # ((2|t|)^d)^(1/3)
    e = R.div(c, rt)
    return (min(e[0], F(1)), min(e[1], F(1)))
