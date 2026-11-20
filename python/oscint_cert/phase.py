# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Hypothesis checker for one-dimensional trigonometric-polynomial phases.

A phase is omega(k) = sum_j amp_j * fn_j(freq_j * k), fn in {cos, sin}, amp rational, freq integer. The checker
decides, with exact rational interval arithmetic only, whether |omega^(order)(k)| >= mu on [a, b], the hypothesis of
the k-th derivative van der Corput statement S1.k:
  PASS        every point of [a, b] satisfies it (a finite subdivision, each piece certified);
  FAIL        a rational point k0 in [a, b] with |omega^(order)(k0)| < mu is exhibited (certified);
  UNRESOLVED  neither was established within the subdivision budget.
"""
from fractions import Fraction as F

from . import rational as R


def parse_phase(terms):
    out = []
    if not isinstance(terms, list) or not terms:
        raise ValueError("phase: a non-empty list of terms is required")
    if len(terms) > 64:
        raise R.Unresolved("phase: more than 64 terms")
    for t in terms:
        if not isinstance(t, dict) or set(t) != {"amp", "freq", "fn"} or t.get("fn") not in ("cos", "sin"):
            raise ValueError("phase term: exactly amp, freq, fn; fn must be 'cos' or 'sin'")
        f = t.get("freq")
        if isinstance(f, bool) or not isinstance(f, int):
            raise ValueError("phase term: freq must be an integer")
        if abs(f) > 1000:
            raise R.Unresolved("phase term: |freq| above 1000")
        if isinstance(t.get("amp"), int):
            raise ValueError("phase term: amp must be a string")
        out.append((R.parse_rational(t.get("amp")), f, t["fn"]))
    return out


def derivative(terms, order: int):
    """The terms of the order-th derivative (exact)."""
    out = []
    for amp, f, fn in terms:
        a, g = amp, fn
        for _ in range(order):
            if g == "cos":
                a, g = -a * f, "sin"
            else:
                a, g = a * f, "cos"
        if a != 0:
            out.append((a, f, g))
    return out


def eval_point(terms, k: F, digits: int):
    acc = R.iv(0)
    for amp, f, fn in terms:
        s, c = R.sincos(f * k, digits)
        acc = R.add(acc, R.mul(R.iv(amp), c if fn == "cos" else s))
    return acc


def lipschitz(terms) -> F:
    """A bound for the modulus of the derivative of the trigonometric polynomial, valid everywhere."""
    return sum((abs(amp) * abs(f) for amp, f, _ in terms), F(0))


def check_lower_bound(terms, order: int, a: F, b: F, mu: F, digits: int = 20, max_pieces: int = 4096):
    """Decide |omega^(order)| >= mu on [a, b]. Returns (status, detail)."""
    if not (a <= b) or mu <= 0 or order < 0 or order > 16:
        raise ValueError("need a <= b, mu > 0, 0 <= order <= 16")
    if max(abs(a), abs(b)) * max((abs(f) for _, f, _ in terms), default=1) > 64:
        return "UNRESOLVED", {"reason": "frequency times interval end above 64"}
    if len(terms) > 8:
        max_pieces = max(64, max_pieces * 8 // len(terms))  # the work per piece grows with the number of terms
    d = derivative(terms, order)
    L = lipschitz(d)
    stack = [(a, b)]
    pieces = []
    while stack:
        u, v = stack.pop()
        m = (u + v) / 2
        val = eval_point(d, m, digits)
        av = R.iabs(val)
        if av[1] < mu:
            shown = R.round_out(val, 30)  # bounded size for printing; still an enclosure
            return "FAIL", {"point": R.fmt(m), "value_enclosure": [R.fmt(shown[0]), R.fmt(shown[1])]}
        lower = av[0] - L * (v - u) / 2  # mean value inequality around the midpoint
        if lower >= mu:
            pieces.append((u, v))
            continue
        if len(pieces) + len(stack) + 2 > max_pieces or v - u < F(1, 10 ** (digits - 2)):
            return "UNRESOLVED", {"reason": "subdivision budget exhausted", "near": R.fmt(m)}
        stack.append((u, m))
        stack.append((m, v))
    pieces.sort()
    return "PASS", {"pieces": len(pieces), "lipschitz": R.fmt(L)}


def vdc_constant(order: int) -> F:
    """The constant of S1.k: 5 * 2^(k-1) - 2 for k >= 2."""
    if order < 2:
        raise ValueError("S1.k needs k >= 2")
    return F(5 * 2 ** (order - 1) - 2)


def vdc_bound(order: int, mu: F, t: F, digits: int = 20):
    """Enclosure of c_k (t mu)^(-1/k): the S1.k bound for the phase t*omega + (any linear term), amplitude 1 on the
    interval (ampNorm = 1), when |omega^(k)| >= mu there and t > 0."""
    if t <= 0:
        raise ValueError("t must be positive")
    r = R.root(R.iv(t * mu), order, digits + 2)
    return R.div(R.iv(vdc_constant(order)), r)
