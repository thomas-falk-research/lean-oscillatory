#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Registered numeric test of the draft statements of batch SPL (docs/prereg/2026-11-19-SPL-quadratic-remainder.md).
Tooling, not evidence for a Lean theorem. Protocol, cases, criteria and controls are fixed in that file; this
program implements them and prints PASS/FAIL per criterion and an overall line.

    R(g, lam) = int g(u) e^{i lam u^2/2} du - g(0) sqrt(2 pi/lam) e^{i pi/4}
    claim     |R(g, lam)| <= K ||g'''||_1 lam^{-3/2},  K = 0.7219740
    identity  R(g, lam) = -(i/lam^{3/2}) int g'''(t) kappa(sqrt(lam) t) dt

Arithmetic: IEEE-754 binary64, round to nearest, NumPy/SciPy; composite Gauss-Legendre quadrature with 12 nodes per
panel, panels summed in increasing order of the abscissa; mpmath at 30 digits for the maximum of |kappa| only. No
random numbers. Every quadrature is run at two panel widths and the difference is printed as its error estimate.
"""
import hashlib
import sys
import datetime
import numpy as np
import scipy
from scipy.special import fresnel
import mpmath as mp

K = 0.7219740
SQ2PI = np.sqrt(2 * np.pi)
FINF = np.sqrt(np.pi) * (0.5 + 0.5j)
GLX, GLW = np.polynomial.legendre.leggauss(12)


def F(x):
    s, c = fresnel(np.asarray(x, dtype=float) / np.sqrt(np.pi))
    return np.sqrt(np.pi) * (c + 1j * s)


def kappa(t, odd=True):
    t = np.asarray(t, dtype=float)
    a = np.abs(t)
    v = F(a) / 2 + a * np.exp(1j * a * a / 2) / 2 + 1j * a * a / 2 * (FINF - F(a))
    return np.where(t < 0, -v, v) if odd else v


def quad(f, breaks, width):
    """Composite 12-point Gauss-Legendre on [breaks[0], breaks[-1]], panels of at most `width`, split at breaks."""
    total = 0.0 + 0.0j
    for a, b in zip(breaks[:-1], breaks[1:]):
        n = max(1, int(np.ceil((b - a) / width)))
        edges = np.linspace(a, b, n + 1)
        mid = (edges[:-1] + edges[1:]) / 2
        half = (edges[1:] - edges[:-1]) / 2
        x = mid[:, None] + half[:, None] * GLX[None, :]
        total += np.sum(f(x) * GLW[None, :] * half[:, None])
    return total


def quad2(f, breaks, width):
    a = quad(f, breaks, width)
    b = quad(f, breaks, width / 2)
    return b, abs(a - b)


# ---- the cases: g, g''(0), g''' and breakpoints (zeros of g''' and ends of the support) -----------------------
def gauss_family(p):
    """g = p(u) e^{-u^2/2}, p a numpy poly1d. Returns g, g''', g(0), g''(0), real zeros of g''' ."""
    D = lambda q: q.deriv() - np.poly1d([1.0, 0.0]) * q
    p1 = D(p); p2 = D(p1); p3 = D(p2)
    g = lambda u: p(u) * np.exp(-u * u / 2)
    g3 = lambda u: p3(u) * np.exp(-u * u / 2)
    z = sorted(r.real for r in p3.roots if abs(r.imag) < 1e-12)
    return g, g3, p(0.0), p2(0.0), z


def shifted_gauss(c):
    """g = u e^{-(u-c)^2} = q(v) e^{-v^2}, v = u - c, q = v + c."""
    D = lambda q: q.deriv() - np.poly1d([2.0, 0.0]) * q
    q = np.poly1d([1.0, c]); q1 = D(q); q2 = D(q1); q3 = D(q2)
    g = lambda u: q(u - c) * np.exp(-(u - c) ** 2)
    g3 = lambda u: q3(u - c) * np.exp(-(u - c) ** 2)
    z = sorted(r.real + c for r in q3.roots if abs(r.imag) < 1e-12)
    return g, g3, 0.0, q2(-c) * np.exp(-c * c), z


def poly_bump():
    """g = (1 - (u/3)^2)^4 (1 + u/2) on [-3, 3], 0 outside: C^3 on the line."""
    base = np.poly1d([-1.0 / 9, 0.0, 1.0]) ** 4 * np.poly1d([0.5, 1.0])
    p2 = base.deriv(2); p3 = base.deriv(3)
    ins = lambda u: (np.abs(u) <= 3.0)
    g = lambda u: np.where(ins(u), base(u), 0.0)
    g3 = lambda u: np.where(ins(u), p3(u), 0.0)
    z = sorted(r.real for r in p3.roots if abs(r.imag) < 1e-12 and abs(r.real) < 3.0)
    return g, g3, base(0.0), p2(0.0), z


def exact_R(case, lam):
    """Closed forms for G1, G2, G3 (principal branches)."""
    lead = SQ2PI / np.sqrt(lam) * np.exp(1j * np.pi / 4)
    if case == "G1":
        s = 1 - 1j * lam
        return SQ2PI * s ** -0.5 - lead
    if case == "G2":
        s = 1 - 1j * lam
        return SQ2PI * (s ** -0.5 + 0.4 * s ** -1.5) - lead
    if case == "G3":
        c = 0.6; A = 1 - 1j * lam / 2; B = 2 * c
        return np.exp(-c * c) * (B / (2 * A)) * np.sqrt(np.pi / A) * np.exp(B * B / (4 * A))
    raise ValueError(case)


def l1(g3, zeros, lo, hi):
    br = [lo] + [z for z in zeros if lo < z < hi] + [hi]
    v, e = quad2(lambda u: np.abs(g3(u)), br, 0.05)
    return v.real, e


def kernel_R(g3, zeros, lo, hi, lam, odd=True):
    br = [lo] + sorted(set([z for z in zeros if lo < z < hi] + [0.0])) + [hi]
    w = min(0.02, 1.0 / (lam * max(abs(lo), abs(hi))))
    v, e = quad2(lambda t: g3(t) * kappa(np.sqrt(lam) * t, odd), br, w)
    return -1j * v / lam ** 1.5, e / lam ** 1.5


def direct_R(g, g0, lo, hi, lam, breaks=()):
    br = sorted(set([lo, hi, 0.0] + list(breaks)))
    w = min(0.02, 1.0 / (lam * max(abs(lo), abs(hi))))
    v, e = quad2(lambda u: g(u) * np.exp(1j * lam * u * u / 2), br, w)
    return v - g0 * SQ2PI / np.sqrt(lam) * np.exp(1j * np.pi / 4), e


# ---- G5: the near-extremal amplitude ---------------------------------------------------------------------------
def Phi3(t, w):
    """Third antiderivative from -infinity of phi_w(t) = (1 + cos(pi t/w))/(2w) on |t| <= w (unit mass)."""
    t = np.asarray(t, dtype=float)
    mid = (t + w) ** 3 / (12 * w) - (w / (2 * np.pi ** 2)) * ((w / np.pi) * np.sin(np.pi * t / w) + (t + w))
    top = 2 * w * w / 3 - w * w / np.pi ** 2 + (t * t - w * w) / 2
    return np.where(t < -w, 0.0, np.where(t > w, top, mid))


def g5(tau, T, w):
    g = lambda t: 0.5 * (Phi3(t - tau, w) - Phi3(t + tau, w)) - (tau / (2 * T)) * (Phi3(t - T, w) - Phi3(t + T, w))
    phi = lambda t: np.where(np.abs(t) <= w, (1 + np.cos(np.pi * t / w)) / (2 * w), 0.0)
    g3 = lambda t: 0.5 * (phi(t - tau) - phi(t + tau)) - (tau / (2 * T)) * (phi(t - T) - phi(t + T))
    br = sorted([s * (c + d) for s in (-1, 1) for c in (tau, T) for d in (-w, w)])
    return g, g3, br


def main():
    results = []

    def report(name, ok, detail):
        results.append((name, ok))
        print(("PASS " if ok else "FAIL ") + name + ": " + detail)

    print(f"# numerics/review/spl_remainder_checks.py, run {datetime.datetime.now(datetime.timezone.utc):%Y-%m-%dT%H:%M:%SZ}")
    print(f"# sha256 of the script: {hashlib.sha256(open(__file__, 'rb').read()).hexdigest()}")
    print(f"# python {sys.version.split()[0]}, numpy {np.__version__}, scipy {scipy.__version__}, mpmath {mp.__version__}; binary64; no random numbers")
    print(f"# claim constant K = {K}")

    # (e) the maximum of |kappa| in two ways
    mp.mp.dps = 30
    mF = lambda x: mp.sqrt(mp.pi) * (mp.fresnelc(x / mp.sqrt(mp.pi)) + 1j * mp.fresnels(x / mp.sqrt(mp.pi)))
    mFinf = mp.sqrt(mp.pi) * (mp.mpf(1) / 2 + 1j / 2)
    mk = lambda t: mF(t) / 2 + t * mp.e ** (1j * t * t / 2) / 2 + 1j * t * t / 2 * (mFinf - mF(t))
    grid = np.arange(1, 40001) / 1000.0
    vals = np.abs(kappa(grid))
    i = int(np.argmax(vals))
    tstar = mp.findroot(lambda t: mp.diff(lambda x: abs(mk(x)) ** 2, t), mp.mpf(grid[i]))
    kstar = abs(mk(tstar))
    print(f"e1 closed form: grid maximum of |kappa| on (0, 40], step 0.001: {vals[i]:.10f} at tau = {grid[i]:.3f}; refined tau* = {mp.nstr(tstar, 12)}, K* = {mp.nstr(kstar, 12)}")
    X = 1000.0
    defv, deferr = quad2(lambda x: F(x) * x ** -3.0, [float(tstar), 2.0, 5.0, 20.0, 100.0, X], 0.01)
    kdef = float(tstar) ** 2 * (defv + FINF / (2 * X * X))
    tail = float(tstar) ** 2 / X ** 3
    print(f"e2 definition tau^2 int_tau^inf F(x) x^-3 dx at tau*: |kappa| = {abs(kdef):.10f} (quadrature difference {deferr:.1e}, tail bound {tail:.1e})")
    report("(e) K* by two methods", abs(abs(kdef) - float(kstar)) < 1e-7 and float(kstar) <= K and K - float(kstar) < 1e-7,
           f"difference {abs(abs(kdef) - float(kstar)):.2e}; K - K* = {K - float(kstar):.2e}")
    tail_max = float(np.max(vals[grid > 2.6]))
    report("(e') the maximum is the first local maximum", tail_max < float(kstar) - 0.05, f"largest |kappa| on (2.6, 40]: {tail_max:.6f}")

    # cases G1..G4
    cases = {}
    g, g3, g0, g2, z = gauss_family(np.poly1d([1.0])); cases["G1"] = (g, g3, g0, g2, z, -12.0, 12.0)
    g, g3, g0, g2, z = gauss_family(np.poly1d([0.4, 0.7, 1.0])); cases["G2"] = (g, g3, g0, g2, z, -12.0, 12.0)
    g, g3, g0, g2, z = shifted_gauss(0.6); cases["G3"] = (g, g3, g0, g2, z, -8.0, 9.0)
    g, g3, g0, g2, z = poly_bump(); cases["G4"] = (g, g3, g0, g2, z, -3.0, 3.0)
    lams = [1.0, 4.0, 16.0, 64.0, 256.0]
    worst_a = 0.0; ok_a = True; ok_id = True; worst_id = 0.0; ok_x = True; worst_x = 0.0
    rho_store = {}
    for name, (g, g3, g0, g2, z, lo, hi) in cases.items():
        n1, e1 = l1(g3, z, lo, hi)
        print(f"{name}: g(0) = {g0:.6f}, g''(0) = {g2:.6f}, ||g'''||_1 = {n1:.10f} (quadrature difference {e1:.1e})")
        for lam in lams:
            Rd, ed = direct_R(g, g0, lo, hi, lam)
            Rk, ek = kernel_R(g3, z, lo, hi, lam)
            rho = lam ** 1.5 * abs(Rd) / n1
            rho_store[(name, lam)] = rho
            line = f"  lam = {lam:6.0f}: rho = {rho:.8f}; direct R = {Rd:.10f} (diff {ed:.1e}); kernel R = {Rk:.10f} (diff {ek:.1e}); |direct - kernel| lam^1.5 = {lam ** 1.5 * abs(Rd - Rk):.2e}"
            if name in ("G1", "G2", "G3"):
                Rx = exact_R(name, lam)
                dx = lam ** 1.5 * abs(Rd - Rx)
                worst_x = max(worst_x, dx); ok_x &= dx < 1e-6
                line += f"; |direct - closed form| lam^1.5 = {dx:.2e}"
            print(line)
            worst_a = max(worst_a, rho); ok_a &= rho <= K + 1e-9
            d = lam ** 1.5 * abs(Rd - Rk)
            worst_id = max(worst_id, d); ok_id &= d < 1e-6
    report("(a) bound on G1-G4, five values of lam", ok_a, f"largest rho = {worst_a:.8f} against K = {K}")
    report("(c2) identity on G1-G4", ok_id, f"largest |direct - kernel| lam^1.5 = {worst_id:.2e} (tolerance 1e-6)")
    report("(x) direct quadrature against closed forms, G1-G3", ok_x, f"largest scaled difference {worst_x:.2e} (tolerance 1e-6)")

    # (b) the next term of the expansion
    ok_b = True; det = []
    for name in ("G1", "G2", "G3"):
        g, g3, g0, g2, z, lo, hi = cases[name]
        lam = 4096.0
        r = lam ** 1.5 * abs(exact_R(name, lam)) / (SQ2PI * abs(g2) / 2)
        det.append(f"{name} {r:.5f}"); ok_b &= abs(r - 1) < 0.05
    g, g3, g0, g2, z, lo, hi = cases["G4"]
    Rd, ed = direct_R(g, g0, lo, hi, 256.0)
    r = 256.0 ** 1.5 * abs(Rd) / (SQ2PI * abs(g2) / 2)
    det.append(f"G4 (lam 256) {r:.5f}"); ok_b &= abs(r - 1) < 0.05
    report("(b) lam^1.5 |R| against sqrt(2 pi) |g''(0)|/2", ok_b, "ratios " + ", ".join(det))

    # (c) the near-extremal amplitude
    tau = float(tstar); T = 400.0; w = 0.01
    g, g3, br = g5(tau, T, w)
    g0 = float(g(np.array(0.0)))
    Rd, ed = direct_R(g, g0, -T - w, T + w, 1.0, br)
    n1 = 1 + tau / T
    n1q, e1 = quad2(lambda t: np.abs(g3(t)), br, 0.001)
    Rk, ek = quad2(lambda t: g3(t) * kappa(t), br, 0.001)
    Rk = -1j * Rk
    rho5 = abs(Rd) / n1
    print(f"G5: tau = {tau:.6f}, T = {T}, w = {w}; g(0) = {g0:.6f}; ||g'''||_1 = {n1:.8f} (quadrature {n1q.real:.8f}); direct R = {Rd:.8f} (diff {ed:.1e}); kernel R = {Rk:.8f} (diff {ek:.1e})")
    report("(c) near-extremal amplitude", K >= rho5 >= 0.985 * K and ed < 1e-5, f"rho = {rho5:.8f}; 0.985 K = {0.985 * K:.8f}; K = {K}")
    report("(c2) identity on G5", abs(Rd - Rk) < 1e-4, f"|direct - kernel| = {abs(Rd - Rk):.2e} (tolerance 1e-4)")

    # controls: each must come out as stated
    g, g3, g0, g2, z, lo, hi = cases["G1"]
    n1, _ = l1(g3, z, lo, hi)
    lam = 256.0
    wrong = SQ2PI * (1 - 1j * lam) ** -0.5 - SQ2PI / np.sqrt(lam)
    rho_c1 = lam ** 1.5 * abs(wrong) / n1
    report("control C1 (phase factor e^{i pi/4} replaced by 1) violates the bound", rho_c1 > K, f"rho = {rho_c1:.4f}")
    report("control C2 (constant sqrt(2 pi)/4 in the place of K) is violated by G5", rho5 > SQ2PI / 4, f"rho = {rho5:.8f} against {SQ2PI / 4:.8f}")
    dmax = 0.0
    for name in ("G2", "G3"):
        g, g3, g0, g2, z, lo, hi = cases[name]
        Rd, _ = direct_R(g, g0, lo, hi, 1.0)
        Rk, _ = kernel_R(g3, z, lo, hi, 1.0, odd=False)
        dmax = max(dmax, abs(Rd - Rk))
    report("control C3 (kappa extended as an even function) breaks the identity", dmax > 1e-3, f"largest |direct - kernel| at lam = 1 on G2, G3: {dmax:.4f}")
    r3 = (256.0 ** 2 * rho_store[("G1", 256.0)] / 256.0 ** 1.5) / (16.0 ** 2 * rho_store[("G1", 16.0)] / 16.0 ** 1.5)
    report("control C4 (remainder of order lam^-2) is refuted", r3 > 3.0, f"lam^2 |R| grows by the factor {r3:.3f} from lam = 16 to 256 on G1")

    n_ok = sum(1 for _, ok in results if ok)
    print(f"OVERALL: {'PASS' if n_ok == len(results) else 'FAIL'} ({n_ok} of {len(results)} lines PASS)")
    return 0 if n_ok == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
