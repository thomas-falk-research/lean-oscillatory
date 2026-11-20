# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
# SPDX-License-Identifier: Apache-2.0
"""Numeric checks of the interfaces of Blueprint/StationaryLeading.lean (batch SPL), floating point (mpmath, 30 digits).

Not a registered test and not evidence for a statement: it checks that each blueprint proposition is plausible as
written before parts are assigned (CONTRIBUTING.md, step 6). Exit code 0 iff every check passes.
"""
import sys
import mpmath as mp

mp.mp.dps = 30
I = mp.mpc(0, 1)
L = mp.sqrt(mp.pi) * (1 + I) / 2
SQPI = mp.sqrt(mp.pi)


def e(u):
    return mp.exp(I * u * u / 2)


def F(x):
    t = x / SQPI
    return SQPI * (mp.fresnelc(t) + I * mp.fresnels(t))


def E1(u):
    return F(u) - L


def E2(u):
    return u * (F(u) - L) + I * e(u)


def kpos(u):
    return F(u) / 2 + u * e(u) / 2 + I * u * u / 2 * (L - F(u))


def kappa(u):
    return kpos(u) if u >= 0 else -kpos(-u)


results = []


def check(name, ok, detail):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name + ": " + detail)


grid_pos = [mp.mpf(j) / 100 for j in range(1, 2001)] + [mp.mpf(20 + j) for j in range(1, 181)]
grid_all = [mp.mpf(0)] + grid_pos

# P-fresnel
m = max(abs(F(x) - L) * x for x in grid_pos)
check("P-fresnel |F(x)-L| x <= 2", m <= 2, f"max over grid = {mp.nstr(m, 8)}")
m = max(abs(F(-x) + F(x)) for x in grid_pos[::50])
check("P-fresnel oddness", m < mp.mpf(10) ** -25, f"max defect = {mp.nstr(m, 3)}")
m = max(abs(mp.diff(F, x) - e(x)) for x in [mp.mpf(-3), mp.mpf(-0.5), mp.mpf(0), mp.mpf(1.3), mp.mpf(7)])
check("P-fresnel F' = e", m < mp.mpf(10) ** -15, f"max defect = {mp.nstr(m, 3)}")

# P-bound
m = max(abs(F(x)) for x in grid_all)
check("P-bound |F| <= 7/4", m <= mp.mpf(7) / 4, f"max over grid = {mp.nstr(m, 8)}")

# P-kernel
pts = [mp.mpf(-4), mp.mpf(-1.1), mp.mpf(0), mp.mpf(0.4), mp.mpf(1.6246), mp.mpf(5.5)]
m = max(abs(mp.diff(E1, u) - e(u)) for u in pts)
check("P-kernel E1' = e", m < mp.mpf(10) ** -15, f"max defect = {mp.nstr(m, 3)}")
m = max(abs(mp.diff(E2, u) - E1(u)) for u in pts)
check("P-kernel E2' = E1", m < mp.mpf(10) ** -15, f"max defect = {mp.nstr(m, 3)}")
m = max(abs(mp.diff(lambda v: I * kpos(v), u) - E2(u)) for u in pts)
check("P-kernel (i kpos)' = E2 (also at negative arguments)", m < mp.mpf(10) ** -15, f"max defect = {mp.nstr(m, 3)}")
m = max(abs(E1(u)) for u in grid_all)
check("P-kernel |E1| <= 4 on [0, inf)", m <= 4, f"max over grid = {mp.nstr(m, 8)}")
m = max(abs(E2(u)) for u in grid_all)
check("P-kernel |E2| <= 3 on [0, inf)", m <= 3, f"max over grid = {mp.nstr(m, 8)}")
m = max(abs(kappa(u)) for u in grid_all)
check("P-kernel |kappa| <= 7/8", m <= mp.mpf(7) / 8, f"max over grid = {mp.nstr(m, 10)}")
m = abs(kappa(mp.mpf(10) ** -12))
check("P-kernel continuity at 0", m < mp.mpf(10) ** -11, f"|kappa(1e-12)| = {mp.nstr(m, 3)}")


# P-line, on amplitudes that are neither even nor odd nor real
def line_defect(g, cuts):
    g3 = lambda t: mp.diff(g, t, 3)
    lhs = mp.quad(lambda u: g(u) * e(u), cuts)
    rhs = 2 * L * g(0) - I * mp.quad(lambda t: g3(t) * kappa(t), cuts)
    return abs(lhs - rhs), abs(lhs)


cuts = [mp.mpf(c) for c in range(-12, 13)]
amps = {
    "gaussian": lambda u: mp.exp(-u * u / 2),
    "(1+u) gaussian, shifted": lambda u: (1 + u) * mp.exp(-(u - mp.mpf(3) / 10) ** 2 / 2),
    "complex, modulated": lambda u: mp.exp(I * mp.mpf(7) / 10 * u) * (2 - I * u) * mp.exp(-(u + mp.mpf(1) / 5) ** 2),
}
for name, g in amps.items():
    d, size = line_defect(g, cuts)
    check(f"P-line identity [{name}]", d < mp.mpf(10) ** -12, f"defect = {mp.nstr(d, 3)}, |lhs| = {mp.nstr(size, 8)}")

# assembly of SPL-I from P-line (scaling), one case
lam = mp.mpf(4)
g = amps["(1+u) gaussian, shifted"]
g3 = lambda t: mp.diff(g, t, 3)
R = mp.quad(lambda u: g(u) * mp.exp(I * lam * u * u / 2), cuts) - g(0) * mp.sqrt(2 * mp.pi / lam) * mp.exp(I * mp.pi / 4)
rhs = -I * lam ** (-mp.mpf(3) / 2) * mp.quad(lambda t: g3(t) * kappa(mp.sqrt(lam) * t), cuts)
check("assembly SPL-I from P-line at lam = 4", abs(R - rhs) < mp.mpf(10) ** -12, f"defect = {mp.nstr(abs(R - rhs), 3)}, |R| = {mp.nstr(abs(R), 8)}")


# P-bump: g''' = m, four mollified point masses; only int |g'''| and int g''' k enter the proposition
def bump_case(k, M, tau, eps, label):
    T = max(4 * M * tau / eps, 2 * tau)          # 2 M tau / T <= eps / 2
    # delta: modulus of continuity of k at +-tau over |s| <= w, measured
    w = min(tau / 2, eps / 100)
    c = mp.quad(lambda t: mp.cos(mp.pi * t / (2 * w)) ** 2, [-w, w])
    psi = lambda t: mp.cos(mp.pi * t / (2 * w)) ** 2 / c if abs(t) < w else mp.mpf(0)

    def mol(a, f):
        return mp.quad(lambda t: psi(t - a) * f(t), [a - w, a, a + w])

    intk = (mol(tau, k) - mol(-tau, k)) / 2 - tau / (2 * T) * (mol(T, k) - mol(-T, k))
    norm1 = 1 + tau / T                           # the four bumps are disjoint (2 w <= tau <= T - tau)
    lhs = (abs(k(tau)) - eps) * norm1
    check(f"P-bump [{label}] tau = {mp.nstr(tau, 5)}, eps = {mp.nstr(eps, 3)}", lhs <= abs(intk),
          f"(|k(tau)|-eps) N = {mp.nstr(lhs, 8)} <= |int g''' k| = {mp.nstr(abs(intk), 8)}; T = {mp.nstr(T, 6)}, w = {mp.nstr(w, 3)}")
    # moments of m of order 0, 1, 2 vanish (compact support of g): order 1 in closed form
    m1 = (tau + tau) / 2 - tau / (2 * T) * (T + T)
    check(f"P-bump [{label}] first moment of g'''", m1 == 0, f"= {m1}")


bump_case(kappa, mp.mpf(7) / 8, mp.mpf("1.6246"), mp.mpf(1) / 10, "k = kappa")
bump_case(kappa, mp.mpf(7) / 8, mp.mpf("0.3"), mp.mpf(1) / 50, "k = kappa")
k2 = lambda t: mp.sin(3 * t) + I * t / (1 + t * t)
bump_case(k2, mp.mpf(3) / 2, mp.mpf(2), mp.mpf(1) / 20, "k = sin 3t + i t/(1+t^2), M = 3/2")

print(f"{sum(results)} of {len(results)} checks pass")
sys.exit(0 if all(results) else 1)
