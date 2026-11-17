#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Numerical checks of the blueprint propositions of batch HW (Blueprint/HadamardWalk.lean), transcribed from the
Lean text, run by the lead before the parts are proved. Tooling, not evidence for a Lean theorem. mpmath, 30 digits;
the kernel by the trapezoidal rule, which is exact for trigonometric polynomials. HadamardLinearFacts is checked on
random finite states by the step itself."""
import random, math
import numpy as np
from mpmath import mp, mpf, sin, cos, asin, sqrt, pi, diff, quad, fabs
mp.dps = 30
ok = True
def report(name, cond, detail=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
om = lambda k: asin(sin(k) / sqrt(2))
D1 = lambda k: cos(k) / sqrt(1 + cos(k) ** 2)
D2 = lambda k: -sin(k) / ((1 + cos(k) ** 2) * sqrt(1 + cos(k) ** 2))
D3 = lambda k: -(cos(k) * (4 - 2 * cos(k) ** 2)) / ((1 + cos(k) ** 2) ** 2 * sqrt(1 + cos(k) ** 2))
g = lambda k: 1 / sqrt(2 * (1 + cos(k) ** 2))
gp = lambda k: sin(k) * cos(k) / (sqrt(2) * ((1 + cos(k) ** 2) * sqrt(1 + cos(k) ** 2)))
# HadamardPhaseFacts
pts = [mpf(j) / 211 * 4 * pi - 2 * pi for j in range(1, 211)]
m = max(max(fabs(diff(om, k) - D1(k)), fabs(diff(D1, k) - D2(k)), fabs(diff(D2, k) - D3(k))) for k in pts)
report("HadamardPhaseFacts: derivative chain hwD1, hwD2, hwD3 (numerical differentiation, 210 points)", m < mpf(10) ** -18, f"max diff {mp.nstr(m, 3)}")
grid = [mpf(j) / 20000 * 2 * pi for j in range(20000)]
lo2 = min(fabs(D2(k)) for k in grid if fabs(sin(k)) >= 1 / sqrt(2)); lo3 = min(fabs(D3(k)) for k in grid if fabs(cos(k)) >= 1 / sqrt(2))
report("|hwD2| >= 2/(3 sqrt 3) where |sin k| >= 1/sqrt 2 (20000 points of a period)", lo2 >= 2 / (3 * sqrt(3)) - mpf(10) ** -25, f"min {mp.nstr(lo2, 15)} bound {mp.nstr(2/(3*sqrt(3)), 15)}")
report("|hwD3| >= 1/(2 sqrt 2) where |cos k| >= 1/sqrt 2", lo3 >= 1 / (2 * sqrt(2)) - mpf(10) ** -25, f"min {mp.nstr(lo3, 15)} bound {mp.nstr(1/(2*sqrt(2)), 15)}")
# HadamardAmplitudeFacts
m = max(fabs(diff(g, k) - gp(k)) for k in pts)
report("HadamardAmplitudeFacts: hwAmp' is the derivative of hwAmp", m < mpf(10) ** -18, f"max diff {mp.nstr(m, 3)}")
amp = lambda a, b: fabs(g(b)) + quad(lambda k: fabs(gp(k)), [a, (a + b) / 2, b])
arcs = [(-pi / 4, pi / 4, sqrt(3) - 1), (pi / 4, 3 * pi / 4, sqrt(2) - 1 / sqrt(3)), (3 * pi / 4, 5 * pi / 4, sqrt(3) - 1), (5 * pi / 4, 7 * pi / 4, sqrt(2) - 1 / sqrt(3))]
worst = max(amp(a, b) - c for a, b, c in arcs)
report("ampNorm on the four arcs <= the stated bounds (they are equalities)", worst <= mpf(10) ** -20, f"largest ampNorm - bound {mp.nstr(worst, 3)}")
# HadamardDecayArithFacts
def arith(t):
    T = mpf(t + 1); t = mpf(t)
    return ((7 * T ** (-mpf(1) / 2) + 12 * T ** (-mpf(1) / 3)) / sqrt(2) + 7 * t ** (-mpf(1) / 2) + 12 * t ** (-mpf(1) / 3)) / (39 * T ** (-mpf(1) / 3))
ts = list(range(1, 3000)) + [10 ** j for j in range(4, 16)]
r = max(arith(t) for t in ts)
report("HadamardDecayArithFacts: left/right <= 1 for t = 1..2999 and 10^4..10^15", r <= 1, f"largest ratio {mp.nstr(r, 8)} (t = 1: {mp.nstr(arith(1), 8)})")
# HadamardKernelRecFacts
def kernel(t, x):
    N = 4 * (t + abs(x)) + 64
    k = -math.pi + 2 * math.pi * np.arange(N) / N
    w = np.arcsin(np.sin(k) / math.sqrt(2))
    return ((np.exp(-1j * t * w) - (-1) ** t * np.exp(1j * t * w)) / np.sqrt(2 * (1 + np.cos(k) ** 2)) * np.exp(-1j * x * k)).sum() / N
m = 0
for t in range(0, 14):
    for x in range(-t - 4, t + 5):
        m = max(m, abs(kernel(t + 2, x) - ((kernel(t + 1, x + 1) - kernel(t + 1, x - 1)) / math.sqrt(2) + kernel(t, x))))
m0 = max(abs(kernel(0, x)) for x in range(-5, 6)); m1 = max(abs(kernel(1, x) - (1 if x == 0 else 0)) for x in range(-5, 6))
report("HadamardKernelRecFacts: K(0,.) = 0, K(1,.) = delta, recursion for t <= 13", max(m, m0, m1) < 1e-12, f"max diff {max(m, m0, m1):.2e}")
# HadamardLinearFacts
def step(psi):
    out = {}; s = math.sqrt(2)
    for x in set(z + d for z in psi for d in (-1, 1)):
        p = psi.get(x + 1, (0, 0)); q = psi.get(x - 1, (0, 0))
        out[x] = ((p[0] + p[1]) / s, (q[0] - q[1]) / s)
    return out
def walk(psi, t):
    for _ in range(t): psi = step(psi)
    return psi
rng = random.Random(20261117); m = 0
for trial in range(6):
    S = rng.sample(range(-6, 7), 4)
    psi0 = {y: (complex(rng.gauss(0, 1), rng.gauss(0, 1)), complex(rng.gauss(0, 1), rng.gauss(0, 1))) for y in S}
    for t in (0, 1, 2, 7):
        full = walk(dict(psi0), t)
        parts = {y: walk({0: psi0[y]}, t) for y in S}
        for x in range(-16, 17):
            tot = [0, 0]
            for y in S:
                v = parts[y].get(x - y, (0, 0)) if t > 0 else ((psi0[y] if x - y == 0 else (0, 0)))
                tot[0] += v[0]; tot[1] += v[1]
            f = full.get(x, (0, 0)) if t > 0 else psi0.get(x, (0, 0))
            m = max(m, abs(f[0] - tot[0]), abs(f[1] - tot[1]))
report("HadamardLinearFacts: walk of a 4-site state = sum of translated point-state walks (t = 0, 1, 2, 7)", m < 1e-12, f"max diff {m:.2e}")
print("ALL PASS" if ok else "SOME FAIL")
