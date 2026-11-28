#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Registered numeric test of batch K2 (docs/prereg/2026-11-28-K2.md). Floating-point falsification only: no
enclosure, no interval arithmetic; tooling, never evidence for a Lean theorem.

Criteria (each prints one PASS/FAIL line; OVERALL PASS iff every criterion and every control comes out as required):
  MA  K2-MA remainder: |I_b(t) - t^(-1/m) C| <= 4/(m t r^(m-1)), C the closed-form improper integral.
  MC  K2-MA constant: Re C >= 1/(12 m) for m = 2..40, and the symmetric partial integrals approach C within
      the one-sided tail bounds 2 * 2/(m R^(m-1)).
  ML  K2-ML: |I_b(t)| >= t^(-1/m)/(24 m) at and beyond the threshold t^(1-1/m) = 96 r^(1-m).
  F   K2-F: the localised integral equals sum_j c_j K(t, n + j) (floor offsets), and |L| <= (sum |c_j|) max |K|.
  L   K2-L: on three model phases (m = 3, 4, 6), t^(1/2 + 1/m) sup_y |I(t, y)| does not grow: its maximum over
      t = 320, 640 is at most twice its maximum over t = 20, 40, 80.
  G   K2-U / K2-D: for eight couplings, t^beta sup_n |K| stays in a band [lo, hi] with lo > 0 and hi/lo <= 2.5 over
      t in [20, 160] (this cannot separate 2/3 from 3/4).
Controls (each must FAIL as stated): CMA (remainder constant 4 -> 1/20), CML (threshold 96 -> 1e-6, at t = 1e-8),
  CL (the A3 model claimed with m = 2), CG (no decay, exponent 0), CF (index n - j instead of n + j).
"""
import math, sys, time
import numpy as np
import mpmath as mp

RESULTS = []
def line(name, ok, detail):
    RESULTS.append((name, ok))
    print(f"{name}: {'PASS' if ok else 'FAIL'}  {detail}", flush=True)

# ---------------------------------------------------------------------------------------------------- monomials
GL_X, GL_W = np.polynomial.legendre.leggauss(20)

def smooth_step(z):
    """C-infinity, 1 for z <= 0, 0 for z >= 1, nonincreasing (vectorised)."""
    z = np.asarray(z, dtype=float)
    def f(x):
        out = np.zeros_like(x); m = x > 0; out[m] = np.exp(-1 / x[m]); return out
    a, b = f(1 - z), f(z)
    return np.where(z <= 0, 1.0, np.where(z >= 1, 0.0, a / np.where(a + b > 0, a + b, 1.0)))

def C_closed(m, sg):
    g = 2 / mp.mpf(m) * mp.gamma(mp.mpf(1) / m)
    v = g * mp.e ** (1j * sg * mp.pi / (2 * m)) if m % 2 == 0 else g * mp.cos(mp.pi / (2 * m))
    return complex(v)

def quad_composite(f, lo, hi, nsub):
    e = np.linspace(lo, hi, nsub + 1)
    mid = (e[:-1] + e[1:]) / 2; half = (e[1:] - e[:-1]) / 2
    x = (mid[:, None] + half[:, None] * GL_X[None, :]).ravel()
    w = (half[:, None] * GL_W[None, :]).ravel()
    return np.sum(w * f(x))

def I_b(m, sg, t, r, R, nsub):
    f = lambda x: smooth_step((np.abs(x) - r) / (R - r)) * np.exp(1j * sg * t * x ** m)
    return quad_composite(f, -R, R, nsub)

def nsub_for(t, R, m):
    # resolution: about 8 subintervals (20 Gauss points each) per oscillation of t x^m on [0, R]
    return int(16 + 8 * t * R ** m / (2 * math.pi)) + 1

def check_MA(const=4, label="MA"):
    worst = 0.0; worst_q = 0.0; n = 0
    for m in (2, 3, 4, 6, 7):
        for (r, R) in ((0.5, 1.0), (1.0, 1.6)):
            for sg in (1, -1):
                C = C_closed(m, sg)
                for t in (0.5, 3.0, 17.5, 60.0):
                    ns = nsub_for(t, R, m)
                    v1 = I_b(m, sg, t, r, R, ns)
                    v2 = I_b(m, sg, t, r, R, 2 * ns)  # a-posteriori quadrature check
                    worst_q = max(worst_q, abs(v1 - v2))
                    err = abs(v2 - t ** (-1.0 / m) * C)
                    worst = max(worst, err / (const / (m * t * r ** (m - 1))))
                    n += 1
    ok = worst <= 1 and worst_q < 1e-9
    return ok, f"{n} cases; max error/bound {worst:.4f}; max quadrature change {worst_q:.2e}"

def check_MC():
    mp.mp.dps = 25
    okc = all(C_closed(m, 1).real > 1 / (12 * m) for m in range(2, 41))
    worst = 0.0; worst_q = 0.0
    for m in (2, 3, 4, 6):
        for sg in (1, -1):
            C = C_closed(m, sg)
            for Rr in (6.0, 12.0):
                ns = nsub_for(1.0, Rr, m)
                f = lambda x: np.exp(1j * sg * x ** m)
                v1 = quad_composite(f, -Rr, Rr, ns); v = quad_composite(f, -Rr, Rr, 2 * ns)
                worst_q = max(worst_q, abs(v - v1))
                worst = max(worst, abs(v - C) / (4 / (m * Rr ** (m - 1))))
    ok = okc and worst <= 1 and worst_q < 1e-8
    return ok, f"Re C > 1/(12m) for m = 2..40: {okc}; partial integrals: max |S_R - C|/tail {worst:.4f}; quadrature change {worst_q:.2e}"

def check_ML(thr=96, label="ML", small_t=None):
    worst = math.inf; n = 0; skipped = 0
    for m in (2, 3, 4, 6):
        for (r, R) in ((0.5, 1.0), (1.0, 1.6)):
            for sg in (1, -1):
                t0 = (thr * r ** (1 - m)) ** (m / (m - 1))
                ts = [small_t] if small_t is not None else [t0 * (1 + 1e-9), 2 * t0]
                for t in ts:
                    if t ** (1 - 1 / m) < thr * r ** (1 - m): continue  # the statement's hypothesis fails here
                    if t * R ** m > 2e5: skipped += 1; continue  # resolution cap, counted
                    v = I_b(m, sg, t, r, R, nsub_for(t, R, m))
                    worst = min(worst, abs(v) / (t ** (-1.0 / m) / (24 * m)))
                    n += 1
    return worst >= 1, f"{n} cases ({skipped} beyond the resolution cap, not run); min |I_b| / (t^(-1/m)/(24m)) = {worst:.4f}"

# ---------------------------------------------------------------------------------------------- lattice kernels
ASTAR = 1 / (2 * math.sqrt(2))

def choose_N(t, a):
    # alias bound for the coefficients of exp(i t p): sum_{|j| >= d} |c_j| <= 2 x^d / d!, x = t (2 + |a|), d = N/2
    x = t * (2 + abs(a)); N = 64
    while True:
        d = N // 2
        lg = d * math.log(x) - math.lgamma(d + 1) + math.log(2) if x > 0 else -1e9
        if lg < math.log(1e-12): return N
        N *= 2
        if N > 4096: return None

def kernel_grid(a, t, N):
    """Normalised kernel (2 pi)^-2 int exp(i(t p + n.k)) dk at all n in the FFT box: ifft2 of exp(i t p)."""
    x = 2 * np.pi * np.arange(N) / N
    X, Y = np.meshgrid(x, x, indexing="ij")
    return np.fft.ifft2(np.exp(1j * t * (np.cos(X) + np.cos(Y) + a * np.cos(X + Y))))

def check_G(couplings, ts, beta_of):
    """K2-U / K2-D content at reachable times: t^beta sup_n |K| in a band [lo, hi] with lo > 0 and hi/lo <= 2.5.
    Over t in [20, 160] this cannot separate the exponents 2/3 and 3/4 (a factor 8^(1/12) = 1.19); it can detect
    a missing decay (control CG, exponent 0)."""
    ok = True; details = []
    for a in couplings:
        beta = beta_of(a); vals = []
        for t in ts:
            N = choose_N(t, a)
            if N is None: return False, f"resolution cap reached at a={a}, t={t}"
            vals.append(float(np.abs(kernel_grid(a, t, N)).max()) * t ** beta)
        lo, hi = min(vals), max(vals)
        ok = ok and lo > 0 and hi / lo <= 2.5
        details.append(f"a={a:+.4f} beta={beta:.4f} band=[{lo:.4f},{hi:.4f}]")
    return ok, "; ".join(details)

def triRate(a):
    return 2 / 3 if (a == 0 or abs(abs(a) - ASTAR) < 1e-15) else 3 / 4

def check_F(sign=+1):
    """Localised integral vs sum_j c_j K(t, n + sign*j). Grid M on [-pi, pi)^2 (periodic trapezoid; the integrands
    are smooth, and compactly supported or periodic, so the rule converges spectrally)."""
    worst_id = 0.0; worst_bd = 0.0; worst_res = 0.0
    def chi(X, Y):
        # nonsymmetric smooth bump, support in the open box (centre (0.4, -0.3), radii 1.1 and 0.9)
        u = ((X - 0.4) / 1.1) ** 2 + ((Y + 0.3) / 0.9) ** 2
        out = np.zeros_like(X); m = u < 1
        out[m] = np.exp(-1 / (1 - u[m])) * (1 + 0.3 * X[m])
        return out
    for (a, t, p) in ((0.3, 23.7, (0.37, -1.21)), (-1.0, 41.3, (-0.83, 0.52)), (ASTAR, 17.9, (1.13, -0.07))):
        for M in (512, 1024):
            x = -np.pi + 2 * np.pi * np.arange(M) / M
            X, Y = np.meshgrid(x, x, indexing="ij")
            P = np.cos(X) + np.cos(Y) + a * np.cos(X + Y)
            ch = chi(X, Y)
            L = (ch * np.exp(1j * t * (P + p[0] * X + p[1] * Y))).sum() / M ** 2  # normalised (2pi)^-2 int
            n1, n2 = math.floor(t * p[0]), math.floor(t * p[1])
            d1, d2 = t * p[0] - n1, t * p[1] - n2
            adel = ch * np.exp(1j * (d1 * X + d2 * Y))
            # c_j = (2pi)^-2 int adel e^{-ij.k}; grid starts at -pi: phase factor e^{i j pi}
            c = np.fft.fft2(adel) / M ** 2
            jj = np.fft.fftfreq(M, 1 / M).astype(int)
            J1, J2 = np.meshgrid(jj, jj, indexing="ij")
            c = c * np.exp(1j * np.pi * (J1 + J2))
            # K(t, m) = (2pi)^-2 int e^{i(tP + m.k)} = mean of e^{itP} e^{i m.k} over the grid starting at -pi
            E = np.exp(1j * t * P)
            Kall = np.fft.ifft2(E)  # = mean E e^{+i m.(2 pi idx/M)}; shift for the -pi origin: e^{-i m pi}
            mm = np.fft.fftfreq(M, 1 / M).astype(int)
            M1, M2 = np.meshgrid(mm, mm, indexing="ij")
            Kall = Kall * np.exp(-1j * np.pi * (M1 + M2))
            Kdict_idx = lambda q1, q2: Kall[q1 % M, q2 % M]
            # full discrete sum over the grid's frequencies: tests the index sign and the normalisations exactly;
            # the change from M = 512 to M = 1024 (L and the l1 norm) tests the discretisation
            S = np.sum(c * Kall[(n1 + sign * J1) % M, (n2 + sign * J2) % M])
            l1 = np.abs(c).sum()
            res = (L, S, l1, np.abs(Kall).max())
            if M == 512: prev = res
        worst_res = max(worst_res, abs(prev[0] - res[0]), abs(prev[2] - res[2]))
        worst_id = max(worst_id, abs(res[0] - res[1]) / max(abs(res[0]), 1e-300))
        worst_bd = max(worst_bd, abs(res[0]) / (res[2] * res[3]))
    ok = worst_id < 1e-9 and worst_bd <= 1 and worst_res < 1e-5
    return ok, f"max relative |L - sum c_j K| {worst_id:.2e}; max |L|/(l1 * max|K|) {worst_bd:.4f}; grid change of L and of the l1 norm {worst_res:.2e}"

def check_L(models, ratio_max=2.0):
    """sup over linear terms y of |int exp(i(t Psi + y.k)) A| on a grid, via FFT. Upper-bound content of K2-L:
    the scaled values t^(1/2 + 1/m) sup_y |I| at t = 320, 640 are at most ratio_max times their maximum over
    t = 20, 40, 80 (no growth). Exponent fits are not used: at a cusp the approach to t^(-3/4) is slow (relative
    correction of order t^(-1/4)), which a smoke test of this program showed before registration."""
    ok = True; details = []
    ts = np.array([20.0, 40.0, 80.0, 320.0, 640.0])
    Lbox = 8.0; N = 4096
    x = -Lbox / 2 + Lbox * np.arange(N) / N
    X, Y = np.meshgrid(x, x, indexing="ij")
    rr = X ** 2 + Y ** 2
    A = np.zeros_like(X); msk = rr < 0.36
    A[msk] = np.exp(-1 / (1 - rr[msk] / 0.36)) * (1 + 0.5 * X[msk] - 0.2 * Y[msk])  # smooth, support radius 0.6
    for name, Psi, m in models:
        P = Psi(X, Y); sc = []
        for t in ts:
            F = np.fft.fft2(A * np.exp(1j * t * P)) * (Lbox / N) ** 2
            sc.append(np.abs(F).max() * t ** (0.5 + 1.0 / m))
        ratio = max(sc[3:]) / max(sc[:3])
        ok = ok and ratio <= ratio_max
        details.append(f"{name}: m={m} scaled=" + ",".join(f"{v:.4f}" for v in sc) + f" ratio={ratio:.4f}")
    return ok, "; ".join(details)

def main():
    t0 = time.time()
    print("k2_checks: numpy", np.__version__, "mpmath", mp.__version__, "python", sys.version.split()[0], flush=True)
    ok, d = check_MC(); line("MC", ok, d)
    ok, d = check_MA(); line("MA", ok, d)
    ok, d = check_ML(); line("ML", ok, d)
    ok, d = check_F(+1); line("F", ok, d)
    models = [("fold y^2/2 + x^3", lambda X, Y: Y ** 2 / 2 + X ** 3, 3),
              ("sheared A3 y^2/2 + y x^2 + x^4", lambda X, Y: Y ** 2 / 2 + Y * X ** 2 + X ** 4, 4),
              ("A5 y^2/2 + x^6 + x^2 y^3", lambda X, Y: Y ** 2 / 2 + X ** 6 + X ** 2 * Y ** 3, 6)]
    ok, d = check_L(models); line("L", ok, d)
    couplings = [0.0, ASTAR, -ASTAR, -0.8, 1.0, 1.5, 0.25, 2.0]
    ts = np.linspace(20.0, 160.0, 15)
    ok, d = check_G(couplings, ts, triRate); line("G", ok, d)
    # controls: each must FAIL
    ok, d = check_MA(const=0.05); line("CMA (must FAIL)", not ok, d)
    ok, d = check_ML(thr=1e-6, small_t=1e-8); line("CML (must FAIL)", not ok, d)
    ok, d = check_L([("sheared A3 claimed as m=2", lambda X, Y: Y ** 2 / 2 + Y * X ** 2 + X ** 4, 2)]); line("CL (must FAIL)", not ok, d)
    ok, d = check_G([1.0, -0.8], ts, lambda a: 0.0); line("CG (must FAIL)", not ok, d)
    ok, d = check_F(-1); line("CF (must FAIL)", not ok, d)
    allok = all(o for _, o in RESULTS)
    print(f"elapsed {time.time() - t0:.0f} s", flush=True)
    print("OVERALL:", "PASS" if allok else "FAIL", flush=True)
    return 0 if allok else 1

if __name__ == "__main__":
    sys.exit(main())
