# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Exact-rational interval arithmetic: the only arithmetic the certificate checker uses.

An interval is a pair (lo, hi) of fractions.Fraction with lo <= hi. Every function returns an interval that contains
the exact real value for every point of its input intervals. No floating point is used anywhere in this module.
"""
from fractions import Fraction as F
from math import isqrt

Interval = tuple


class Unresolved(Exception):
    """The computation is outside the supported range or budget; the caller reports UNRESOLVED, never a number."""


_NUM = None


def parse_rational(s) -> F:
    """Parse an exact rational written as "-?D+", "-?D+/D+" (nonzero denominator) or "-?D+.D+", ASCII digits only
    (contract section 2). No leading "+", no spaces, no exponent, no sign on the denominator. A JSON integer is
    accepted where the caller passes one. Anything else raises ValueError."""
    global _NUM
    if isinstance(s, bool) or not isinstance(s, (str, int)):
        raise ValueError(f"expected a string or integer, got {type(s).__name__}")
    if isinstance(s, int):
        return F(s)
    if len(s) > 4000:
        raise Unresolved("numeral longer than 4000 characters")
    if _NUM is None:
        import re
        _NUM = re.compile(r"-?[0-9]+(?:/[0-9]+|\.[0-9]+)?", re.ASCII)
    if not _NUM.fullmatch(s):
        raise ValueError(f"not an exact rational: {s!r}")
    if "/" in s:
        num, _, den = s.partition("/")
        d = int(den)
        if d == 0:
            raise ValueError("zero denominator")
        return F(int(num), d)
    return F(s)


def fmt(q: F) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def round_out(a, digits: int):
    """The interval rounded outward to multiples of 10^-digits (bounded size for printing)."""
    s = 10**digits
    lo = F((a[0].numerator * s) // a[0].denominator, s)
    hi = F(-((-a[1].numerator * s) // a[1].denominator), s)
    return (lo, hi)


def iv(q) -> Interval:
    q = F(q)
    return (q, q)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def mul(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(ps), max(ps))


def inv(a):
    if a[0] <= 0 <= a[1]:
        raise Unresolved("division by an interval containing zero")
    return (1 / a[1], 1 / a[0])


def div(a, b):
    return mul(a, inv(b))


def ipow(a, n: int):
    if n < 0:
        return inv(ipow(a, -n))
    r = iv(1)
    for _ in range(n):
        r = mul(r, a)
    return r


def iabs(a):
    if a[0] >= 0:
        return a
    if a[1] <= 0:
        return (-a[1], -a[0])
    return (F(0), max(-a[0], a[1]))


def contains(outer, inner) -> bool:
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def disjoint(a, b) -> bool:
    return a[1] < b[0] or b[1] < a[0]


def _iroot(n: int, k: int) -> int:
    """floor(n ** (1/k)) for integers n >= 0, k >= 1."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x**k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


def root(a, k: int, digits: int):
    """Enclosure of the k-th root of a non-negative interval, to about `digits` decimal digits."""
    if a[0] < 0:
        raise Unresolved("root of a negative number")
    s = 10**digits

    def lo(q):
        return F(_iroot((q.numerator * s**k) // q.denominator, k), s)

    def hi(q):
        n = -((-q.numerator * s**k) // q.denominator)  # ceiling
        r = _iroot(n, k)
        return F(r if r**k == n else r + 1, s)

    return (lo(a[0]), hi(a[1]))


def sqrt(a, digits: int):
    if a[0] < 0:
        raise Unresolved("square root of a negative number")
    s = 10**digits
    lo = F(isqrt((a[0].numerator * s * s) // a[0].denominator), s)
    n = -((-a[1].numerator * s * s) // a[1].denominator)  # ceiling
    r = isqrt(n)
    return (lo, F(r if r * r == n else r + 1, s))


def _arctan_inv(m: int, terms: int):
    """Enclosure of arctan(1/m), m >= 2, from the alternating series: consecutive partial sums bracket the value."""
    s = F(0)
    for j in range(terms):
        s += F((-1) ** j, (2 * j + 1) * m ** (2 * j + 1))
    nxt = F((-1) ** terms, (2 * terms + 1) * m ** (2 * terms + 1))
    return (min(s, s + nxt), max(s, s + nxt))


def pi(digits: int):
    """Enclosure of pi by Machin's formula pi = 16 arctan(1/5) - 4 arctan(1/239)."""
    t5 = digits * 10 // 14 + 3  # 5^(-2j) gains about 1.4 digits per term
    t239 = digits * 10 // 47 + 3
    a, b = _arctan_inv(5, t5), _arctan_inv(239, t239)
    return sub(mul(iv(16), a), mul(iv(4), b))


def _sincos_point(x: F, digits: int):
    """Enclosures of sin x and cos x at a rational x with |x| <= 2, by Taylor series with the alternating remainder."""
    if abs(x) > 2:
        raise Unresolved("internal: argument reduction failed")
    tol = F(1, 10 ** (digits + 2))
    x2 = x * x
    # terms decrease in modulus from the start when |x| <= 2 for cos beyond j = 1 and for sin beyond j = 1; we sum
    # until the next term is below tol and at least 4 terms were taken, then bracket by one further term.
    s, c = F(0), F(0)
    ts, tc = x, F(1)
    j = 0
    while True:
        s += ts
        c += tc
        nts = -ts * x2 / ((2 * j + 2) * (2 * j + 3))
        ntc = -tc * x2 / ((2 * j + 1) * (2 * j + 2))
        j += 1
        if j >= 4 and abs(nts) <= tol and abs(ntc) <= tol:
            break
        ts, tc = nts, ntc
    return ((min(s, s + nts), max(s, s + nts)), (min(c, c + ntc), max(c, c + ntc)))


def sincos(x: F, digits: int):
    """Enclosures (sin x, cos x) at a rational point x with |x| <= 64, by halving the argument and doubling."""
    if abs(x) > 64:
        raise Unresolved("trigonometric argument above 64 in modulus")
    k = 0
    y = x
    while abs(y) > 1:
        y /= 2
        k += 1
    s, c = _sincos_point(y, digits + 2 * k + 2)
    for _ in range(k):
        s, c = mul(mul(iv(2), s), c), sub(mul(c, c), mul(s, s))
        s = (max(s[0], F(-1)), min(s[1], F(1)))
        c = (max(c[0], F(-1)), min(c[1], F(1)))
    return s, c
