#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Exact maximum of the Hadamard walk from a point state, t <= 3000 (batch HW, clarification of 2026-11-19).
Tooling, not evidence for a Lean theorem. Written after an external review found that the recorded "1.6208 at most"
was the maximum rounded down.

The walk of OscInt/Statements/HadamardWalk.lean from the state (1, 0) at the site 0:
    (U psi)(x) = ((psi_1(x+1) + psi_2(x+1))/sqrt 2, (psi_1(x-1) - psi_2(x-1))/sqrt 2),
so psi_t(x) = n_t(x) / 2^(t/2) with integer pairs n_t(x), computed here in Python integers (no rounding).
For a rational c the comparison  t^(1/3) |n| / 2^(t/2) > c  is decided exactly as  n^6 t^2 c_den^6 > c_num^6 2^(3t).
Reported: for c in 1.6208, 1.62084, 1.62085 the times t <= 3000 at which the largest component exceeds c t^(-1/3),
and the maximiser (ranked in floating point; its bracket is certified by the exact comparisons).
Checks (the process fails if one fails): some t exceeds 1.6208 and 1.62084; no t exceeds 1.62085.

Usage: python3 -I numerics/review/hw_exact_max_checks.py
"""
import math
import platform
import sys
from fractions import Fraction

T = 3000
CS = [Fraction(16208, 10000), Fraction(162084, 100000), Fraction(162085, 100000)]
off = T + 2
a = [0] * (2 * off + 1)
b = [0] * (2 * off + 1)
a[off] = 1
over = {c: [] for c in CS}
best = (0.0, None)
for t in range(1, T + 1):
    na = [0] * (2 * off + 1)
    nb = [0] * (2 * off + 1)
    for i in range(off - t, off + t + 1):
        na[i] = a[i + 1] + b[i + 1]
        nb[i] = a[i - 1] - b[i - 1]
    a, b = na, nb
    m, where = 0, None
    for i in range(off - t, off + t + 1):
        if abs(a[i]) > m:
            m, where = abs(a[i]), (i - off, 1)
        if abs(b[i]) > m:
            m, where = abs(b[i]), (i - off, 2)
    for c in CS:
        if m**6 * t**2 * c.denominator**6 > c.numerator**6 * 2 ** (3 * t):
            over[c].append((t, where))
    val = math.exp(math.log(m) - t / 2 * math.log(2) + math.log(t) / 3)
    if val > best[0]:
        best = (val, (t, where))
# conservation of the l^2 norm, exactly: sum of squares of the numerators is 2^T
norm_ok = sum(x * x for x in a) + sum(x * x for x in b) == 2**T
print(f"exact walk to t = {T}; sum of |n|^2 at t = {T} equals 2^{T}: {norm_ok}")
for c in CS:
    print(f"times t <= {T} with t^(1/3) max|psi_t| > {float(c)} (exact test): {len(over[c])}  {over[c][:6]}")
print(f"maximiser (floating-point ranking): {best[0]:.12f} at t = {best[1][0]}, x = {best[1][1][0]}, component {best[1][1][1]}")
ok = norm_ok and len(over[CS[0]]) > 0 and len(over[CS[1]]) > 0 and len(over[CS[2]]) == 0
print(f"python {platform.python_version()}")
print("RESULT:", "PASS" if ok else "NOT PASS")
sys.exit(0 if ok else 1)
