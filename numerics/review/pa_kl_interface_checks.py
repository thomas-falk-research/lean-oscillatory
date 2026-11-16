#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Interface checks for the blueprints of batches PA and KL (Blueprint/PeriodicAnalytic.lean,
Blueprint/KusminLandau.lean; routes docs/proof-PA.md, docs/proof-KL.md), run by the lead before the route referees.
Tooling, not evidence for a Lean theorem: each intermediate proposition is tested on samples in the shape the
blueprint states it. Arb balls throughout; an equality passes only if the two enclosures overlap and are narrower
than 1e-25; an inequality passes only if it holds for the whole enclosures.

PA  I1  ContourShiftFacts: the Fourier integral on the real line against the one at height b, b = +-a/2 and
        +-0.95a, for the five functions of pa_statement_checks.py and k = -4..4.
    I2  FourierSeriesFacts: |v(x) - sum_{|k| <= K} c_k e^{ikx}| is at most the geometric tail
        sum_{|k| > K} M e^{-a|k|} = 2 M e^{-a(K+1)}/(1 - e^{-a}), at 5 real points x, K = 40.
    I3  AliasBoundFacts on random sequences (|c_k| <= M e^{-a|k|}, finitely many nonzero, f_j computed from the
        finite sum) and on the extremal sequence c_k = M e^{-a|k|} truncated at |k| <= K: the ratio of the two
        sides must be below 1 and tend to 1.
    I4  KernelIntegrandFacts: |e^{it cos z}| <= e^{|t| sinh eta} at random points of the strip, and the kernel
        over [-pi, pi] against the Fourier integral over [0, 2 pi] of index -n, 20 points (t, n).
KL  J1  the weights zeta(x) = 1/(e(x) - 1): |zeta| = |1 + zeta| = 1/(2 sin pi x) and
        zeta(x) - zeta(y) = (i/2)(cot pi y - cot pi x), 50 rational points.
    J2  the summation-by-parts identity for random unit vectors E_n with E_n = zeta_n (E_{n+1} - E_n).
    J3  the half-angle identities 1/sin x + cot x = cot(x/2), 1/sin x - cot x = tan(x/2), and cot x <= 1/x.
    J4  KLCoreFacts (k = 0) on 300 random monotone difference sequences.
Controls (each must fail): I1 with a height outside the strip of f3 (b = -0.8 > log 2 in modulus); I3 with the
bound M/(e^{aN} - 1) on the extremal sequence; J4 with cot(pi lam) in place of cot(pi lam/2) on the extremal
sequence of lam = 1/3.

Usage: python3 -I numerics/review/pa_kl_interface_checks.py
"""
import platform
import random

import flint
from flint import acb, arb, ctx

ctx.prec = 200
I = acb(0, 1)
PI = arb.pi()
rng = random.Random(20261116)
TOL = arb(10) ** (-25)

FUNCS = {
    "f1": (lambda z: 7 * (3 * z).cos(), lambda a: 7 * (3 * a).cosh(), [arb("0.5"), arb(1)]),
    "f2": (lambda z: acb(2, 3) * (I * z).exp() + 5, lambda a: arb(13).sqrt() * a.exp() + 5, [arb("0.5"), arb(1)]),
    "f3": (lambda z: 1 / (2 - (I * z).exp()), lambda a: 1 / (2 - a.exp()), [arb("0.4"), arb("0.69")]),
    "f4": (lambda z: 1 / (arb("1.25") - z.cos()), lambda a: 1 / (arb("1.25") - a.cosh()), [arb("0.4"), arb("0.69")]),
    "f5": (lambda z: (I * 3 * z.cos()).exp(), lambda a: (3 * a.sinh()).exp(), [arb("0.5"), arb(2)]),
}
results = []


def same(x, y):
    d = acb(x) - acb(y)
    return d.contains(0) and bool(abs(d).upper() < TOL)


def le(x, y):
    return bool(y - x >= 0)


def report(name, ok, detail):
    results.append((name, ok))
    print(f"{name}: {'PASS' if ok else 'FAIL'}  {detail}")


def shifted(f, k, b):
    return acb.integral(lambda th, _: f(th + I * b) * (-I * k * (th + I * b)).exp(), arb(0), 2 * PI)


# I1
n = bad = 0
for name, (f, M, As) in FUNCS.items():
    for a in As:
        for k in range(-4, 5):
            base = shifted(f, k, arb(0))
            for frac in ("0.5", "-0.5", "0.95", "-0.95"):
                n += 1
                bad += not same(base, shifted(f, k, a * arb(frac)))
report("I1 contour shift", bad == 0, f"{n} comparisons, {bad} not equal")
f3 = FUNCS["f3"][0]
ctrl = same(shifted(f3, 1, arb(0)), shifted(f3, 1, arb("-0.8")))
report("I1 control (height beyond the pole must differ)", not ctrl, f"equal: {ctrl}")

# I2
n = bad = 0
for name, (f, M, As) in FUNCS.items():
    a = As[-1]
    K = 40
    c = {k: shifted(f, k, arb(0)) / (2 * PI) for k in range(-K, K + 1)}
    tail = 2 * M(a) * (-a * (K + 1)).exp() / (1 - (-a).exp())
    for xs in ("0", "0.7", "2.5", "-1.3", "6.1"):
        x = arb(xs)
        s = sum((c[k] * (I * k * x).exp() for k in range(-K, K + 1)), acb(0))
        n += 1
        bad += not le(abs(f(acb(x)) - s), tail + TOL)
report("I2 Fourier series at real points", bad == 0, f"{n} comparisons (K = 40), {bad} outside the tail bound")

# I3
n = bad = 0
worst = 0.0
for _ in range(200):
    a = arb(rng.randint(1, 30)) / 10
    M = arb(rng.randint(1, 50)) / 10
    N = rng.randint(1, 9)
    K = rng.randint(0, 40)
    c = {k: acb(rng.uniform(-1, 1), rng.uniform(-1, 1)) for k in range(-K, K + 1)}
    c = {k: v / max(abs(v).upper(), arb(1)) * M * (-a * abs(k)).exp() * arb(rng.choice(["1", "0.5", "0.999"])) for k, v in c.items()}
    fj = [sum((c[k] * (I * k * 2 * PI * j / N).exp() for k in c), acb(0)) for j in range(N)]
    lhs = abs(sum(fj, acb(0)) / N - c[0])
    rhs = 2 * M / ((a * N).exp() - 1)
    n += 1
    bad += not le(lhs, rhs)
    worst = max(worst, float((lhs / rhs).mid()))
report("I3 alias bound, random sequences", bad == 0, f"{n} sequences, {bad} violations, largest ratio {worst:.6f}")
ratios = []
for K in (3, 12, 60, 240):
    a, M, N = arb("0.3"), arb(2), 3
    c = {k: acb(M * (-a * abs(k)).exp()) for k in range(-K, K + 1)}
    fj = [sum((c[k] * (I * k * 2 * PI * j / N).exp() for k in c), acb(0)) for j in range(N)]
    lhs = abs(sum(fj, acb(0)) / N - c[0])
    ratios.append((K, lhs / (2 * M / ((a * N).exp() - 1)), lhs / (M / ((a * N).exp() - 1))))
ok = all(bool(r < 1) for _, r, _ in ratios) and bool(ratios[-1][1] > arb("0.999999"))
report("I3 extremal sequence (ratio below 1, tending to 1)", ok, "; ".join(f"K={K}: {r.str(8)}" for K, r, _ in ratios))
report("I3 control (half the bound must fail on the extremal sequence)", not bool(ratios[-1][2] <= 1), f"ratio to M/(e^(aN)-1): {ratios[-1][2].str(8)}")

# I4
n = bad = 0
for _ in range(300):
    t = arb(rng.randint(-80, 80)) / 10
    eta = arb(rng.randint(1, 30)) / 10
    z = acb(arb(rng.randint(-700, 700)) / 100, eta * arb(rng.randint(-999, 999)) / 1000)
    n += 1
    bad += not le(abs((I * t * z.cos()).exp()), (abs(t) * eta.sinh()).exp())
    bad += not same((I * t * (z + 2 * PI).cos()).exp(), (I * t * z.cos()).exp())
report("I4 kernel integrand: bound and period on the strip", bad == 0, f"{n} points, {bad} failures")
n = bad = 0
for _ in range(20):
    t = arb(rng.randint(-60, 60)) / 10
    nn = rng.randint(-9, 9)
    lhs = acb.integral(lambda k, _: (I * (t * k.cos() + nn * k)).exp(), -PI, PI)
    rhs = acb.integral(lambda th, _: (I * t * th.cos()).exp() * (-I * (-nn) * th).exp(), arb(0), 2 * PI)
    bessel = 2 * PI * I ** (nn % 4) * acb(t).bessel_j(nn)
    n += 1
    bad += not (same(lhs, rhs) and same(lhs, bessel))
report("I4 kernel as a Fourier integral of index -n (and against 2 pi i^n J_n(t))", bad == 0, f"{n} points, {bad} failures")


# KL
def e(x):
    return (2 * PI * I * x).exp()


def zeta(x):
    return 1 / (e(x) - 1)


def cot(x):
    return x.cos() / x.sin()


n = bad = 0
pts = [arb(rng.randint(1, 999)) / 1000 for _ in range(50)]
for x, y in zip(pts, pts[1:] + pts[:1]):
    n += 1
    h = 1 / (2 * (PI * x).sin())
    bad += not (same(abs(zeta(x)), h) and same(abs(1 + zeta(x)), h)
                and same(zeta(x) - zeta(y), I / 2 * (cot(PI * y) - cot(PI * x))))
report("J1 weights", bad == 0, f"{n} points, {bad} failures")
n = bad = 0
for _ in range(100):
    N = rng.randint(1, 12)
    d = [arb(rng.randint(1, 999)) / 1000 for _ in range(N)]
    c = [arb(0)]
    for x in d:
        c.append(c[-1] + x)
    E = [e(x) for x in c]
    z = [zeta(x) for x in d]
    lhs = sum(E, acb(0))
    rhs = (1 + z[N - 1]) * E[N] - z[0] * E[0] - sum(((z[m] - z[m - 1]) * E[m] for m in range(1, N)), acb(0))
    n += 1
    bad += not same(lhs, rhs)
report("J2 summation by parts", bad == 0, f"{n} sequences, {bad} failures")
n = bad = 0
for _ in range(100):
    x = PI * arb(rng.randint(1, 999)) / 1000
    n += 1
    bad += not (same(1 / x.sin() + cot(x), cot(x / 2)) and same(1 / x.sin() - cot(x), (x / 2).tan()))
    y = x / 2
    bad += not le(cot(y), 1 / y)
report("J3 half-angle identities and cot x <= 1/x", bad == 0, f"{n} points, {bad} failures")
n = bad = 0
worst = 0.0
for _ in range(300):
    lam = arb(rng.randint(1, 500)) / 1000
    N = rng.randint(0, 30)
    ds = sorted(rng.uniform(float(lam.upper()) + 1e-9, 1 - float(lam.upper()) - 1e-9) for _ in range(N)) if bool(lam < arb("0.5")) else [0.5] * N
    if rng.random() < 0.5:
        ds.reverse()
    c = [arb(0)]
    for x in ds:
        c.append(c[-1] + arb(x))
    lhs = abs(sum((e(x) for x in c), acb(0)))
    rhs = cot(PI * lam / 2)
    n += 1
    bad += not le(lhs, rhs + TOL)
    worst = max(worst, float((lhs / rhs).mid()))
report("J4 core inequality, k = 0", bad == 0, f"{n} sequences, {bad} violations, largest ratio {worst:.6f}")
lam = arb(1) / 3
lhs = abs(sum((e(lam * j) for j in range(2)), acb(0)))  # c = (0, 1/3): |1 + e(1/3)| = 1
report("J4 control (cot(pi lam) must fail at lam = 1/3)", not bool(lhs <= cot(PI * lam)), f"|S| = {lhs.str(8)}, cot(pi/3) = {cot(PI * lam).str(8)}, cot(pi/6) = {cot(PI * lam / 2).str(8)}")

npass = sum(ok for _, ok in results)
print(f"summary: {npass} of {len(results)} checks pass")
print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, "
      f"working precision {ctx.prec} bits, seed 20261116")
