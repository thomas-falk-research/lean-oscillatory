#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified truth checks of the batch-PA statements (OscInt/Statements/PeriodicAnalytic.lean) on sample functions,
run by the lead before the freeze. Tooling, not evidence for a Lean theorem. Arb balls throughout; a comparison
passes only if it holds for the whole enclosures, and a comparison the enclosures do not decide counts as not passed.
(Until 2026-11-19 an undecided PA-C comparison with midpoints closer than 1e-30 was accepted, against this
description; the recorded run of 2026-11-16 printed no such line. Removed after the external review of batch PA.)

Functions, each with the strip half-width a and a bound M valid on |Im z| < a:
  f1  7 cos(3z),            M = 7 cosh(3a)                       (entire; the extremal shape for PA-T)
  f2  (2+3i) e^{iz} + 5,    M = sqrt(13) e^a + 5                 (entire, one-sided spectrum)
  f3  1 / (2 - e^{iz}),     M = 1 / (2 - e^a),        a < log 2  (pole at z = -i log 2)
  f4  1 / (5/4 - cos z),    M = 1 / (5/4 - cosh a),   a < log 2  (poles at z = +- i log 2)
  f5  e^{i t cos z},        M = e^{|t| sinh a},       t = 3      (the lattice-kernel integrand)
PA-C: |int_0^{2pi} v e^{-ik theta}| <= 2 pi M e^{-a|k|};   PA-T: |I_N - I| <= 4 pi M / (e^{aN} - 1).
LC-1 is check K3 of numerics/review/unlock_chain_checks.py.
Controls (each must be certified false on the whole enclosures): PA-T with 2 pi for f1 (N = 3, a = 1/2); PA-T with e^{2aN} for f1; PA-C with pi for f2
(k = 1, a = 5); PA-C with e^{-2a|k|} for f1 (k = 3, a = 1/2).

Usage: python3 -I numerics/review/pa_statement_checks.py
"""
import platform
import sys

import flint
from flint import acb, arb, ctx

ctx.prec = 200
I = acb(0, 1)
PI = arb.pi()
LOG2 = arb(2).log()

FUNCS = {
    "f1": (lambda z: 7 * (3 * z).cos(), lambda a: 7 * (3 * a).cosh(), [arb("0.5"), arb(1), arb(3)]),
    "f2": (lambda z: acb(2, 3) * (I * z).exp() + 5, lambda a: arb(13).sqrt() * a.exp() + 5, [arb("0.5"), arb(1), arb(5)]),
    "f3": (lambda z: 1 / (2 - (I * z).exp()), lambda a: 1 / (2 - a.exp()), [arb("0.1"), arb("0.4"), arb("0.69")]),
    "f4": (lambda z: 1 / (arb("1.25") - z.cos()), lambda a: 1 / (arb("1.25") - a.cosh()), [arb("0.1"), arb("0.4"), arb("0.69")]),
    "f5": (lambda z: (I * 3 * z.cos()).exp(), lambda a: (3 * a.sinh()).exp(), [arb("0.5"), arb(1), arb(2)]),
}


def integral(f, k=0):
    return acb.integral(lambda th, _: f(th) * (-I * k * th).exp(), arb(0), 2 * PI)


def trap(f, N):
    return 2 * PI / N * sum((f(acb(2 * PI * j / N)) for j in range(N)), acb(0))


def certainly_le(x, y):
    d = y - x
    return True if d >= 0 else (False if d < 0 else None)


ok = True
worstC = worstT = 0.0
nC = nT = 0
for name, (f, M, As) in FUNCS.items():
    I0 = integral(f)
    for a in As:
        assert a < LOG2 or name in ("f1", "f2", "f5")
        for k in range(-6, 7):
            lhs = abs(integral(f, k))
            rhs = 2 * PI * M(a) * (-a * abs(k)).exp()
            r = certainly_le(lhs, rhs)
            nC += 1
            if r is not True:
                print(f"PA-C {name} a={a} k={k}: {'FALSE' if r is False else 'UNRESOLVED'} lhs={lhs.str(10)} rhs={rhs.str(10)}")
                ok = False
            worstC = max(worstC, float((lhs / rhs).mid()))
        for N in [1, 2, 3, 4, 5, 8, 16]:
            lhs = abs(trap(f, N) - I0)
            rhs = 4 * PI * M(a) / ((a * N).exp() - 1)
            r = certainly_le(lhs, rhs)
            nT += 1
            if r is not True:
                print(f"PA-T {name} a={a} N={N}: {'FALSE' if r is False else 'UNRESOLVED'} lhs={lhs.str(10)} rhs={rhs.str(10)}")
                ok = False
            worstT = max(worstT, float((lhs / rhs).mid()))
print(f"PA-C: {nC} comparisons, largest ratio lhs/rhs {worstC:.6f}")
print(f"PA-T: {nT} comparisons, largest ratio lhs/rhs {worstT:.6f}")

f1, M1, _ = FUNCS["f1"]
f2, M2, _ = FUNCS["f2"]
a = arb("0.5")
ctl = [
    ("C1 PA-T with 2 pi", certainly_le(abs(trap(f1, 3) - integral(f1)), 2 * PI * M1(a) / ((a * 3).exp() - 1))),
    ("C2 PA-T with e^{2aN}", certainly_le(abs(trap(f1, 3) - integral(f1)), 4 * PI * M1(a) / ((2 * a * 3).exp() - 1))),
    ("C3 PA-C with pi", certainly_le(abs(integral(f2, 1)), PI * M2(arb(5)) * (-arb(5)).exp())),
    ("C4 PA-C with e^{-2a|k|}", certainly_le(abs(integral(f1, 3)), 2 * PI * M1(a) * (-2 * a * 3).exp())),
]
for name, flag in ctl:
    print(f"{name}: {'fails as required' if flag is False else 'NOT REJECTED'}")
    ok = ok and flag is False
print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, {ctx.prec} bits")
print("RESULT:", "PASS" if ok else "NOT PASS")
sys.exit(0 if ok else 1)
