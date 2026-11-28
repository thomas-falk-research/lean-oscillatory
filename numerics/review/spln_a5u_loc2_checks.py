#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Registered numeric test of batches SPL-N, A5U and LOC2 (docs/prereg/2026-11-28-SPLN-A5U-LOC2.md).
Floating-point falsification only: no enclosure, no interval arithmetic; tooling, never evidence for a Lean theorem.
Python with numpy, scipy and mpmath only; deterministic (the one random sample has a fixed seed).

Notation: kappa = splKernel (frozen, OscInt/Statements/StationaryLeading.lean), F = fresnelPrim, Lf = fresnelLimit
= sqrt(pi)(1 + i)/2, E(v) = exp(i v^2/2); K(alpha, t, n) = triKernel (unnormalised, OscInt/Statements/TriangularDecay.lean),
a* = triExceptional = 1/(2 sqrt 2); locConstC2 chi = 4((3/2)|chi| + |d1 chi| + |d2 chi| + |Lap chi|), normalised L2 norms
on [-pi, pi]^2 (draft OscInt/Statements/TorusLocalizationC2.lean).

Criteria (each prints one PASS/FAIL line):
  SPLN-A  kappa by method (i), the frozen formula kappa_+ = F/2 + tau E/2 + (i tau^2/2)(Lf - F) with
          F(x) = sqrt(pi)(C(x/sqrt(pi)) + i S(x/sqrt(pi))) (mpmath.fresnelc/fresnels, 40 digits), and by method (ii),
          kappa(x) = x + i Lf x^2/2 - i int_0^x (x - v)^2 E(v)/2 dv (mpmath.quad on x^2/4 + 4 pieces, 40 digits),
          agree to |difference| <= 1e-25 at 200 points (12 (i + 1)/200, i = 0..198, and 8123/5000).
  SPLN-U  the maximum of |kappa| on the grid tau = j/1000 of [0, 12], refined by mpmath.findroot on
          d|kappa|^2/dtau = 2 Re(conj(kappa) kappa'), kappa' = E + i tau (Lf - F), started at the grid maximiser,
          lies in (72197399/10^8, 360987/500000]: both comparisons are decided only if their margin exceeds
          max(difference of the two methods at the refined point, 1e-35) (the floor is the 40-digit working precision for
          values of size 1; the printed count says how many were decided); the refined value is >= the grid maximum, and the
          numerical derivative of |kappa|^2 there (mpmath.diff) is below 1e-20.
  SPLN-G  |kappa| <= 360987/500000 on [0, 50], from the grid of step 1e-3 with the interpolation pad
          (|Lf - F(a)| + h) h^2/8 on each cell [a, a + h] (|kappa''| = |Lf - F| and |F'| = 1); a cell whose endpoint
          maximum plus pad exceeds the cap is split into 10, down to h = 1e-8 (a cell still failing there is a FAIL);
          plus the large-tau part, checked in exact rational arithmetic: |Lf|/2 + 4/50^3 <= cap via pi < 22/7, with the
          tail bound 4/x^3 (paper, lead's record section 3; tested numerically by SPLN-T only on [2, 200]). Negative tau
          is |kappa(-tau)| = |kappa_+(tau)| by the definition and is not computed.
  SPLN-L  |kappa(8123/5000)| - 72197399/10^8 > 0 by both methods, the margin larger than max(their difference, 1e-35);
          the value printed to 15 digits.
  SPLN-T  |kappa(x) - Lf/2| <= 4/x^3 at 10001 log-spaced points of [2, 200] (method (i) at 40 digits; the change from
          40 to 60 digits at the worst point is printed and must be below 1e-25; about 10 digits cancel at x = 200).
  A5U-Q   orientation and normalisation of the lattice evolution: (2 pi)^-2 K(alpha, t, n) = (exp(i t H) delta_0)(n),
          H hopping 1/2 to (+-1, 0), (0, +-1) and alpha/2 to +-(1, 1), checked at alpha = a* + 1e-2, t = 0.9, 2.3, 4.1,
          sites (3, 1), (-2, 5), (4, -1) against the periodic trapezoid sum of exp(i(t P + n.k)) on 256^2 points
          (change from 128^2 below 1e-13): |4 pi^2 psi(n) - K| <= 1e-10. Plus the large-t check: at alpha = a*,
          t = T_MAX, the evolved box equals the FFT kernel (4096^2, alias bound printed) within 1e-9 at every box site.
          The sign of n.k is not testable: P(-k) = P(k) makes K(alpha, t, n) = K(alpha, t, -n), and both quadratures
          are printed.
  A5U-Y   the exact symmetry K(-alpha, t, n) = (-1)^(n1 + n2) conj K(alpha, t, n) (shift k -> k + (pi, pi), and
          P(-k) = P(k)) holds for the evolved boxes of alpha and -alpha at every t of every pair within 1e-10
          (unnormalised). Each coupling a* + s eps is evolved together with its partner -a* - s eps (9 pairs, 18
          couplings). The two evolutions are related by sign flips in every floating operation, so this line checks the
          indexing and the pairing of the couplings, not the accuracy of the evolution (A5U-Q does that).
  A5U-S   for a0 = +-a*, eps in {0, 1e-3, 3e-3, 1e-2, 3e-2} and both signs of alpha - a0 (18 couplings), t on 25
          log-spaced points of [1, 200]: S(alpha, t) = sup_n |K| / (t^(-2/3) crossEnvelope(eps t^(1/3))), sup over the
          box (sites outside it are below 1e-12 (2 pi)^2 by the Combes-Thomas bound). PASS iff
          max S / median S <= BAND over all 450 values, BAND = 2.0 (fixed from a smoke run of the one coupling a*,
          eps = 0, on this grid: ratio 1.386; its partner -a* has the same moduli). Box radius R: the least R with
          (2 + |alpha|) sqrt(8R) exp(-mu R + T c sinh mu)/(c sinh mu) < 1e-12 for some mu in a grid of (0, 8], c = 1 + |alpha|
          (Duhamel plus the Combes-Thomas bound |(exp(i s H_R) delta_0)(m)| <= exp(-mu |m|_inf + s c sinh mu)).
          With eps <= 3e-2 and t <= 200, eps t^(1/3) <= 0.18 < 1, so crossEnvelope = 1 at every point of this line.
  FQ-D    the closed-form derivatives of the three cutoffs agree with central differences (h = 1e-6 first, 1e-4 second)
          at 200 seeded random points each: max |closed form - difference| <= 1e-4 max |closed form|.
  FQ-I    the identity int chi e^{it(Psi + p.k)} = sum_n h^(n) c(n + j), j = floor(t p), h = chi e^{i (t p - j).k},
          h^(n) = (2 pi)^-2 int h e^{-i n.k}, c(m) = int e^{i(t Psi + m.k)}, as the full discrete sum on the 2048^2 grid:
          |L - S| <= 1e-9 |L| + 1e-14 T in all 81 cases, T = sum_n |h^(n) c(n + j)| + 4 pi^2 mean|chi| (the size of the
          terms of the two sums, the scale of their rounding). The second term is for the cases where |L| is tiny
          (|L|/T down to about 1e-12); the output counts the cases it decided and prints min |L|/T.
  FQ-B    |L| <= locConstC2(chi) B in all 81 cases (3 cutoffs x 3 phases x t in {0, 0.7, 13.3} x 3 velocities), on grids
          M = 1024 and 2M = 2048; e_X = |X_M - X_2M| is used as the error bound of the 2M value X_2M (a-posteriori
          estimate, not a proof); B_N = max |c(n)| over |n|_inf <= N = 511, a lower bound of B = sup_n |c(n)| up to
          e_B. A case is decided TRUE if |L| + e_L <= (D - e_D)(B_N - e_B), decided FALSE if
          |L| - e_L > (D + e_D) B_up with B_up = max(B_N + e_B, T_N), T_N the stated tail bound for |n|_inf > N.
          PASS iff all 81 are decided TRUE. Counts of TRUE, FALSE and undecided are printed.
Controls (each must FAIL its criterion as stated; a control counts only on a decided violation):
  CU   SPLN-U with cap 0.7219739: the refined maximum exceeds it by more than the methods' difference.
  CL   SPLN-L with target 0.721974: |kappa(8123/5000)| is below it by more than the methods' difference.
  CT   SPLN-T with 4 replaced by 1/2: some point has |kappa - Lf/2| > (1/2)/x^3 by more than the precision change.
  CQt  A5U-Q with exp(-i t H): some site differs by more than 1e-6.
  CQd  A5U-Q with the diagonal hopping on +-(1, -1): some site differs by more than 1e-6.
  CA5  A5U-S at eps = 0 with crossEnvelope = 1 and the rate 3/4: S' = sup_n |K| t^(3/4) must GROW: at both a0,
       G = mean of S' over the t >= T_MAX/4 / mean of S' over T_MAX/32 <= t <= T_MAX/8 is >= 1.05 (an exact t^(-2/3)
       law gives about 8^(1/12) = 1.19). The band criterion itself does not reject the rate 3/4 at these times; its
       value for S' is printed.
  CFQ  FQ-B with the constant 4 replaced by 1/20: at least one case decided FALSE.
  CFI  FQ-I with the index n - j: |L - S| > 1e-3 |L| + 1e-14 T in at least one case.
Information only, not part of OVERALL: A5U-W, the ratio of A5U-S for eps in {0.1, 0.2} at both a0 and both signs, where
  eps t^(1/3) reaches 1.17 and the envelope's second branch is used; r is existential, so no value there can contradict A5U.
OVERALL: PASS iff every criterion line PASSes and every control comes out as required; the exit code is 1 otherwise.
"""
import fractions, math, sys, time
import numpy as np
import scipy, scipy.sparse as sp
from scipy.sparse.linalg import expm_multiply
import mpmath as mp

RESULTS = []
def line(name, ok, detail):
    RESULTS.append((name, ok))
    print(f"{name}: {'PASS' if ok else 'FAIL'}  {detail}", flush=True)

def ctrl(name, came_out_as_required, detail):
    RESULTS.append((name, came_out_as_required))
    print(f"{name} (must FAIL): {'FAILS as required' if came_out_as_required else 'DOES NOT FAIL (defect of the test)'}  "
          f"{detail}", flush=True)

def info(name, detail):
    print(f"{name} (information, not part of OVERALL): {detail}", flush=True)

# ================================================================================================== SPL-N
DPS = 40
CAP = mp.mpf(360987) / 500000
LOW = mp.mpf(72197399) / 100000000
LPT = mp.mpf(8123) / 5000
PREC_FLOOR = mp.mpf("1e-35")  # decision threshold floor: 40 working digits, values of size 1

def _consts():
    sp_ = mp.sqrt(mp.pi)
    return sp_, sp_ * (1 + 1j) / 2

def fresnel_F(x):
    sp_, _ = _consts()
    z = x / sp_
    return sp_ * (mp.fresnelc(z) + 1j * mp.fresnels(z))

def kappa_i(x):
    """Method (i): the frozen formula of splKernelPos with mpmath Fresnel integrals. Returns (kappa, F)."""
    _, Lf = _consts()
    x = mp.mpf(x); f = fresnel_F(x); E = mp.expj(x ** 2 / 2)
    return f / 2 + x * E / 2 + 1j * x ** 2 / 2 * (Lf - f), f

def kappa_ii(x):
    """Method (ii): x + i Lf x^2/2 - i int_0^x (x - v)^2 E(v)/2 dv by mpmath.quad on x^2/4 + 4 equal pieces."""
    _, Lf = _consts()
    x = mp.mpf(x)
    if x == 0: return mp.mpc(0)
    g = lambda v: (x - v) ** 2 * mp.expj(v ** 2 / 2) / 2
    n = max(4, int(x * x / 4) + 4)
    return x + 1j * Lf * x ** 2 / 2 - 1j * mp.quad(g, [x * i / n for i in range(n + 1)])

def dkappa(x):
    _, Lf = _consts()
    x = mp.mpf(x)
    return mp.expj(x ** 2 / 2) + 1j * x * (Lf - fresnel_F(x))

def check_SPLN_A():
    mp.mp.dps = DPS
    pts = [mp.mpf(12) * (i + 1) / 200 for i in range(199)] + [LPT]
    worst = mp.mpf(0); nz = 0
    for x in pts:
        d = abs(kappa_i(x)[0] - kappa_ii(x))
        worst = max(worst, d); nz += (abs(kappa_i(x)[0]) > 0)
    ok = worst <= mp.mpf("1e-25")
    return ok, f"{len(pts)} points ({nz} with nonzero kappa); max |method (i) - method (ii)| = {mp.nstr(worst, 3)}"

def spl_grid(hi=50, step_den=1000):
    """|kappa| and F on tau = j/step_den, j = 0..hi*step_den (method (i), 40 digits)."""
    mp.mp.dps = DPS
    taus, vals, Fs = [], [], []
    for j in range(hi * step_den + 1):
        t = mp.mpf(j) / step_den
        k, f = kappa_i(t)
        taus.append(t); vals.append(abs(k)); Fs.append(f)
    return taus, vals, Fs

def check_SPLN_U(grid, cap=CAP, low=LOW):
    mp.mp.dps = DPS
    taus, vals, _ = grid
    n12 = 12000
    jmax = max(range(n12 + 1), key=lambda j: vals[j])
    gmax = vals[jmax]
    g = lambda x: 2 * mp.re(mp.conj(kappa_i(x)[0]) * dkappa(x))
    xs = mp.findroot(g, taus[jmax])
    v1 = abs(kappa_i(xs)[0]); v2 = abs(kappa_ii(xs)); raw = abs(v1 - v2); dis = max(raw, PREC_FLOOR)
    nd = abs(mp.diff(lambda y: abs(kappa_i(y)[0]) ** 2, xs))
    m_up = cap - v1; m_lo = v1 - low
    dec_up = abs(m_up) > dis; dec_lo = abs(m_lo) > dis
    ok = dec_up and dec_lo and m_up >= 0 and m_lo > 0 and v1 >= gmax and nd < mp.mpf("1e-20")
    det = (f"grid max {mp.nstr(gmax, 15)} at tau = {mp.nstr(taus[jmax], 6)}; refined tau* = {mp.nstr(xs, 15)}, "
           f"|kappa(tau*)| = {mp.nstr(v1, 18)} (i), {mp.nstr(v2, 18)} (ii), difference {mp.nstr(raw, 3)} (decision threshold "
           f"{mp.nstr(dis, 3)}); "
           f"cap - max = {mp.nstr(m_up, 6)}, max - lower = {mp.nstr(m_lo, 6)}; comparisons decided: "
           f"{int(dec_up) + int(dec_lo)} of 2; |d|kappa|^2/dtau| at tau* = {mp.nstr(nd, 3)}")
    return ok, det, (v1, dis)

def check_SPLN_G(grid, cap=CAP):
    mp.mp.dps = DPS
    taus, vals, Fs = grid
    _, Lf = _consts()
    h0 = taus[1] - taus[0]
    refined = 0; failed = 0; worst_margin = mp.inf; hmin_used = h0
    stack = []
    for i in range(len(taus) - 1):
        stack.append((taus[i], vals[i], Fs[i], taus[i + 1], vals[i + 1], h0))
    while stack:
        a, va, Fa, b, vb, h = stack.pop()
        pad = (abs(Lf - Fa) + h) * h ** 2 / 8
        marg = cap - (max(va, vb) + pad)
        if marg >= 0:
            worst_margin = min(worst_margin, marg); continue
        if h <= mp.mpf("1e-8") * 1.0000001:
            failed += 1; worst_margin = min(worst_margin, marg); continue
        refined += 1; hn = h / 10; hmin_used = min(hmin_used, hn)
        pts = [a + hn * k for k in range(11)]
        ks = [(va, Fa)] + [(lambda r: (abs(r[0]), r[1]))(kappa_i(p)) for p in pts[1:10]] + [(vb, None)]
        for k in range(10):
            stack.append((pts[k], ks[k][0], ks[k][1], pts[k + 1], ks[k + 1][0], hn))
    # large tau: |Lf|/2 + 4/50^3 <= cap, in rationals with pi < 22/7: |Lf|/2 = sqrt(pi/2)/2
    Fr = fractions.Fraction
    capr = Fr(360987, 500000); rest = capr - Fr(4, 50 ** 3)
    asym_ok = rest > 0 and Fr(22, 7) / 2 / 4 < rest ** 2
    ok = failed == 0 and asym_ok
    return ok, (f"{len(taus) - 1} cells of step 1e-3 on [0, {mp.nstr(taus[-1], 4)}]; {refined} cells split (smallest step {mp.nstr(hmin_used, 2)}); "
                f"{failed} cells failing at step 1e-8; smallest margin cap - (endpoint max + pad) = {mp.nstr(worst_margin, 4)}; "
                f"large tau: sqrt(22/14)/2 + 4/50^3 < cap in exact rationals: {asym_ok}")

def check_SPLN_L(pt=LPT, target=LOW, sense=+1):
    mp.mp.dps = DPS
    v1 = abs(kappa_i(pt)[0]); v2 = abs(kappa_ii(pt)); raw = abs(v1 - v2); dis = max(raw, PREC_FLOOR)
    m1 = sense * (v1 - target); m2 = sense * (v2 - target)
    decided = abs(m1) > dis and abs(m2) > dis
    ok = decided and m1 > 0 and m2 > 0
    return ok, (f"|kappa({mp.nstr(pt, 8)})| = {mp.nstr(v1, 15)} (i), {mp.nstr(v2, 15)} (ii), difference {mp.nstr(raw, 3)} "
                f"(decision threshold {mp.nstr(dis, 3)}); value - target = {mp.nstr(v1 - target, 6)} (i), {mp.nstr(v2 - target, 6)} (ii); decided: {decided}"), (v1, v2, dis)

def check_SPLN_T(const=4, npts=10001):
    mp.mp.dps = DPS
    _, Lf = _consts()
    worst = mp.mpf(0); wx = None; nviol = 0
    for i in range(npts):
        x = mp.mpf(2) * mp.power(100, mp.mpf(i) / (npts - 1))
        r = abs(kappa_i(x)[0] - Lf / 2) * x ** 3
        if r > worst: worst, wx = r, x
        if r > const: nviol += 1
    mp.mp.dps = 60
    _, Lf60 = _consts()
    r60 = abs(kappa_i(wx)[0] - Lf60 / 2) * wx ** 3
    mp.mp.dps = DPS
    chg = abs(r60 - worst)
    ok = worst <= const and chg < mp.mpf("1e-25")
    return ok, (f"{npts} points; max |kappa - Lf/2| x^3 = {mp.nstr(worst, 12)} at x = {mp.nstr(wx, 8)} (bound {const}); "
                f"points above the bound: {nviol}; 40 -> 60 digit change at the worst point {mp.nstr(chg, 3)}"), (worst, chg, nviol)

# ================================================================================================== A5U
ASTAR = 1 / (2 * math.sqrt(2))
T_MAX = 200.0
TS = np.geomspace(1.0, T_MAX, 25)
BAND = 2.0
GROW = 1.05
TOL_BOX = 1e-12
MUS = np.linspace(0.01, 8.0, 4000)

def box_bound(R, T, a):
    c = 1 + abs(a); h = 2 + abs(a)
    e = np.log(h * np.sqrt(8 * R) / (c * np.sinh(MUS))) - MUS * R + T * c * np.sinh(MUS)
    return float(np.exp(e.min()))

def box_radius(T, a, tol=TOL_BOX):
    R = int((1 + abs(a)) * T) + 1
    while box_bound(R, T, a) >= tol: R += 1
    return R

def hamiltonian(R, a, diag=(1, 1)):
    n = 2 * R + 1
    I = sp.identity(n, format="csr")
    S = sp.diags([np.ones(n - 1)], [1], format="csr")  # (S psi)(m) = psi(m + 1)
    X = sp.kron(S, I, format="csr"); Y = sp.kron(I, S, format="csr")  # index (m1 + R) * n + (m2 + R)
    D = X @ Y if diag == (1, 1) else X @ Y.T
    return (0.5 * (X + X.T + Y + Y.T) + 0.5 * a * (D + D.T)).tocsr()

def evolve(a, ts, R, sgn=1, diag=(1, 1)):
    """exp(i sgn t H_R) delta_0 on the box [-R, R]^2 at the times ts (increasing), as (2R+1, 2R+1) arrays."""
    n = 2 * R + 1
    A = (1j * sgn) * hamiltonian(R, a, diag)
    psi = np.zeros(n * n, complex); psi[R * n + R] = 1.0
    tp = 0.0
    for t in ts:
        if t > tp: psi = expm_multiply(A * (t - tp), psi)
        tp = t
        yield t, psi.reshape(n, n)

def quad_kernel(a, t, sites, M, sign_nk=+1):
    """Periodic trapezoid sum for int_{[-pi,pi]^2} exp(i(t P(k) + sign_nk n.k)) dk (direct sum, no FFT)."""
    x = -np.pi + 2 * np.pi * np.arange(M) / M
    X, Y = np.meshgrid(x, x, indexing="ij")
    E = np.exp(1j * t * (np.cos(X) + np.cos(Y) + a * np.cos(X + Y)))
    w = (2 * np.pi / M) ** 2
    return [w * np.sum(E * np.exp(1j * sign_nk * (n1 * X + n2 * Y))) for (n1, n2) in sites]

QSITES = [(3, 1), (-2, 5), (4, -1)]
QTS = [0.9, 2.3, 4.1]
QALPHA = ASTAR + 1e-2

def a5u_q_diffs(sgn=1, diag=(1, 1)):
    R = box_radius(max(QTS), QALPHA)
    worst = 0.0; worst_q = 0.0; worst_nk = 0.0; nz = 0
    for t, psi in evolve(QALPHA, QTS, R, sgn, diag):
        q1 = quad_kernel(QALPHA, t, QSITES, 128); q2 = quad_kernel(QALPHA, t, QSITES, 256)
        qm = quad_kernel(QALPHA, t, QSITES, 256, sign_nk=-1)
        for (n1, n2), a1, a2, am in zip(QSITES, q1, q2, qm):
            ev = 4 * np.pi ** 2 * psi[n1 + R, n2 + R]
            worst = max(worst, abs(ev - a2)); worst_q = max(worst_q, abs(a1 - a2)); worst_nk = max(worst_nk, abs(a2 - am))
            nz += abs(a2) > 1e-3
    return worst, worst_q, worst_nk, nz, R

def fft_kernel_box(a, t, R, N=4096):
    x = 2 * np.pi * np.arange(N) / N
    X, Y = np.meshgrid(x, x, indexing="ij")
    K = np.fft.ifft2(np.exp(1j * t * (np.cos(X) + np.cos(Y) + a * np.cos(X + Y))))  # (2 pi)^-2 int e^{i(tP + m.k)}
    del X, Y
    idx = np.arange(-R, R + 1) % N
    return K[np.ix_(idx, idx)]

def fft_alias_bound(a, t, R, N):
    # aliases of box sites lie at sup-distance >= N - R; Combes-Thomas: |kernel(m)| <= exp(-mu |m| + t c sinh mu),
    # summed over the at most 8 d sites at distance d >= N - R
    c = 1 + abs(a); d0 = N - R
    e = -MUS * d0 + t * c * np.sinh(MUS) + np.log(8.0 * d0 / (1 - np.exp(-MUS)) ** 2)
    return float(np.exp(e.min()))

def check_A5U_Q():
    w, wq, wnk, nz, R = a5u_q_diffs()
    ok_small = w <= 1e-10 and wq < 1e-13
    # large-t check at alpha = a*, t = T_MAX
    Rb = box_radius(T_MAX, ASTAR)
    psi = None
    for t, p in evolve(ASTAR, [T_MAX], Rb): psi = p.copy()
    Kf = fft_kernel_box(ASTAR, T_MAX, Rb)
    big = float(np.abs(psi - Kf).max()) * 4 * np.pi ** 2
    alias = fft_alias_bound(ASTAR, T_MAX, Rb, 4096)
    ok = ok_small and big <= 1e-9
    return ok, (f"small t: {len(QTS) * len(QSITES)} comparisons ({nz} with |K| > 1e-3), box R = {R}: max |4 pi^2 psi(n) - K| "
                f"= {w:.2e}, quadrature change 128 -> 256: {wq:.2e}; |K(+n.k) - K(-n.k)| = {wnk:.2e} (equal by P(-k) = P(k), "
                f"sign of n.k untestable); large t: alpha = a*, t = {T_MAX:g}, box R = {Rb} ({(2 * Rb + 1) ** 2} sites), "
                f"max over the box |evolution - FFT 4096^2| = {big:.2e} (unnormalised), FFT alias bound {alias:.1e} (0 means below the floating range)")

def a5u_pairs(epss=(0.0, 1e-3, 3e-3, 1e-2, 3e-2)):
    """The 18 couplings a0 + sg*eps (a0 = +-a*) as 9 pairs (alpha, -alpha): alpha = a* + sg*eps is the coupling
    (a0 = +a*, sign sg) and -alpha the coupling (a0 = -a*, sign -sg)."""
    return [(eps, sg) for eps in epss for sg in ((1,) if eps == 0 else (1, -1))]

def env(s):
    return 1.0 if s <= 1 else s ** (-0.25)

def run_pair(a, ts=TS):
    """Evolve alpha = a and -alpha on one box; sups (unnormalised) per t for both, and the symmetry defect."""
    R = box_radius(ts[-1], a)
    m = np.arange(-R, R + 1)
    par = np.where(((m[:, None] + m[None, :]) % 2) == 0, 1.0, -1.0)
    sp_, sq_ = [], []; sym = 0.0; unit = 0.0
    for (t, p), (_, q) in zip(evolve(a, ts, R), evolve(-a, ts, R)):
        sp_.append(4 * np.pi ** 2 * float(np.abs(p).max())); sq_.append(4 * np.pi ** 2 * float(np.abs(q).max()))
        sym = max(sym, 4 * np.pi ** 2 * float(np.abs(q - par * np.conj(p)).max()))
        unit = max(unit, abs(np.linalg.norm(p) - 1), abs(np.linalg.norm(q) - 1))
    return R, np.array(sp_), np.array(sq_), sym, unit

def check_A5U(pairs=None, ts=TS):
    """Band statistic of A5U-S, symmetry defect of A5U-Y and the growth statistic of control CA5."""
    if pairs is None: pairs = a5u_pairs()
    allS = []; rows = []; symw = 0.0; unitw = 0.0; Rmax = 0; ctl = []
    for (eps, sg) in pairs:
        R, sups_p, sups_q, sym, unit = run_pair(ASTAR + sg * eps, ts)
        symw = max(symw, sym); unitw = max(unitw, unit); Rmax = max(Rmax, R)
        envv = np.array([env(eps * t ** (1 / 3)) for t in ts])
        for a0, sgn, sups in ((ASTAR, sg, sups_p), (-ASTAR, -sg, sups_q)):
            S = sups * ts ** (2 / 3) / envv
            allS.extend(S.tolist())
            rows.append(f"a0={a0:+.4f} alpha-a0={sgn * eps:+.0e} R={R} S in [{S.min():.3f},{S.max():.3f}]")
            if eps == 0:
                S34 = sups * ts ** 0.75
                hi = ts >= ts[-1] / 4; lo = (ts >= ts[-1] / 32) & (ts <= ts[-1] / 8)
                ctl.append((a0, S34[hi].mean() / S34[lo].mean(), S34.max() / np.median(S34)))
    allS = np.array(allS)
    return allS.max() / np.median(allS), len(allS), rows, symw, unitw, Rmax, ctl

# ================================================================================================== LOC2 (K2-FQ)
M1, M2 = 1024, 2048
NB = M1 // 2 - 1
FQ_TS = (0.0, 0.7, 13.3)
FQ_PS = ((0.37, -1.21), (-2.83, 0.52), (1.13, 3.07))

class Bump:
    """chi1: C-infinity, complex: g(u) q(k), g(u) = exp(-1/(1 - u)) for u < 1, u = ((k1-a1)/w1)^2 + ((k2-a2)/w2)^2,
    q = 1 + 0.3 k1 + 0.2 i k2; support k1 in [-1.8, 2.6], k2 in [-2.2, 1.6]."""
    name = "chi1 (C-inf bump, complex)"
    a = (0.4, -0.3); w = (2.2, 1.9)
    def parts(self, X, Y):
        a, w = self.a, self.w
        u = ((X - a[0]) / w[0]) ** 2 + ((Y - a[1]) / w[1]) ** 2
        inside = u < 1
        g = np.zeros_like(X); g1 = np.zeros_like(X); g2 = np.zeros_like(X)
        ui = u[inside]; gi = np.exp(-1 / (1 - ui))
        g[inside] = gi; g1[inside] = -gi / (1 - ui) ** 2; g2[inside] = gi * (2 * ui - 1) / (1 - ui) ** 4
        u1 = 2 * (X - a[0]) / w[0] ** 2; u2 = 2 * (Y - a[1]) / w[1] ** 2
        u11 = 2 / w[0] ** 2; u22 = 2 / w[1] ** 2
        q = 1 + 0.3 * X + 0.2j * Y; q1 = 0.3; q2 = 0.2j
        chi = g * q
        d1 = g1 * u1 * q + g * q1
        d2 = g1 * u2 * q + g * q2
        d11 = g2 * u1 ** 2 * q + g1 * u11 * q + 2 * g1 * u1 * q1
        d22 = g2 * u2 ** 2 * q + g1 * u22 * q + 2 * g1 * u2 * q2
        return chi, d1, d2, d11 + d22

class Poly:
    """chi2: exactly C^2: (1 - |k - c|^2/rho^2)^3 for |k - c| < rho, c = (-0.5, 0.7), rho = 2; support inside the box."""
    name = "chi2 (C^2 radial (1-r^2/rho^2)^3_+)"
    c = (-0.5, 0.7); rho = 2.0
    def parts(self, X, Y):
        c, r2 = self.c, self.rho ** 2
        u = ((X - c[0]) ** 2 + (Y - c[1]) ** 2) / r2
        v = np.where(u < 1, 1 - u, 0.0)
        f = v ** 3; f1 = -3 * v ** 2; f2 = 6 * v
        u1 = 2 * (X - c[0]) / r2; u2 = 2 * (Y - c[1]) / r2; uu = 2 / r2
        return f, f1 * u1, f1 * u2, f2 * (u1 ** 2 + u2 ** 2) + 2 * f1 * uu

class Prod:
    """chi3: non-radial product b(k1; 0.2, 2.6) b(k2; -0.1, 3.0), b(x; c, w) = (1 - ((x-c)/w)^2)^3_+ (C^2);
    support [-2.4, 2.8] x [-3.1, 2.9]."""
    name = "chi3 (C^2 product, rectangle support)"
    @staticmethod
    def b(x, c, w):
        v = (x - c) / w; s = np.where(np.abs(v) < 1, 1 - v ** 2, 0.0)
        return s ** 3, -6 * v * s ** 2 / w, (24 * v ** 2 * s - 6 * s ** 2) / w ** 2
    def parts(self, X, Y):
        b0, b1, b2 = self.b(X, 0.2, 2.6); c0, c1, c2 = self.b(Y, -0.1, 3.0)
        return b0 * c0, b1 * c0, b0 * c1, b2 * c0 + b0 * c2

CUTOFFS = (Bump(), Poly(), Prod())

def psi_tri(X, Y): return np.cos(X) + np.cos(Y) + 0.3 * np.cos(X + Y)
def psi_kink(X, Y): return np.cos(X) + np.cos(Y) + 0.3 * np.cos(X + Y) + 0.8 * np.abs(np.sin(X))
def psi_zero(X, Y): return np.zeros_like(X)
PHASES = (("triPhase 0.3", psi_tri), ("triPhase 0.3 + 0.8|sin k1|", psi_kink), ("zero", psi_zero))

def tail_bound(phase_name, t, N):
    """Upper bound for sup_{|n|_inf > N} |c(n)|, c(n) = int e^{i(t Psi + n.k)} (unnormalised).
    Analytic directions: shifting k_j -> k_j + i mu sign(n_j) gives |c(n)| <= 4 pi^2 exp(-mu |n_j| + t s_j sinh mu), s_j the
    sum of the moduli of the coefficients of the cosines containing k_j (1.3 for both directions of triPhase 0.3).
    Kink direction (k1 of the second phase): two integrations by parts in k1 on (-pi, 0) and (0, pi):
    |c(n)| <= (2 pi/n1^2)(3.2 t + 2 pi (2.1 t + 2.1^2 t^2)) (jumps 1.6 t of d1 e^{it Psi} at k1 = 0 and pi;
    |Psi_1|, |Psi_11| <= 2.1)."""
    if phase_name == "zero" or t == 0: return 0.0
    ct = float(np.exp((-MUS * (N + 1) + t * 1.3 * np.sinh(MUS)).min())) * 4 * np.pi ** 2
    if phase_name.startswith("triPhase 0.3 +"):
        kink = 2 * np.pi / (N + 1) ** 2 * (3.2 * t + 2 * np.pi * (2.1 * t + 2.1 ** 2 * t ** 2))
        return max(ct, kink)
    return ct

def fq_grid(M):
    x = -np.pi + 2 * np.pi * np.arange(M) / M
    X, Y = np.meshgrid(x, x, indexing="ij")
    jj = np.fft.fftfreq(M, 1 / M).astype(int)
    J1, J2 = np.meshgrid(jj, jj, indexing="ij")
    return X, Y, J1, J2

def fq_compute(M, constant=4.0, index_sign=+1):
    """For grid M: per cutoff the four norms and D; per phase and t the coefficient array; per case L and the identity."""
    X, Y, J1, J2 = fq_grid(M)
    sh = np.exp(-1j * np.pi * (J1 + J2))  # e^{i m.x_0}, x_0 = (-pi, -pi)
    out = {"D": [], "norms": [], "B": {}, "L": {}, "id": {}}
    parts = []
    for ch in CUTOFFS:
        chi, d1, d2, lap = ch.parts(X, Y)
        nrm = [float(np.sqrt(np.mean(np.abs(f) ** 2))) for f in (chi, d1, d2, lap)]
        out["norms"].append(nrm)
        out["D"].append(constant * (1.5 * nrm[0] + nrm[1] + nrm[2] + nrm[3]))
        parts.append(chi)
    for pname, P in PHASES:
        Pv = P(X, Y)
        for t in FQ_TS:
            E = np.exp(1j * t * Pv)
            c = 4 * np.pi ** 2 * np.fft.ifft2(E) * sh  # c(m) at index m mod M
            sel = (np.abs(J1) <= NB) & (np.abs(J2) <= NB)
            out["B"][(pname, t)] = (float(np.abs(c[sel]).max()), c[sel].copy() if M == M1 else None)
            for ci, chi in enumerate(parts):
                for p in FQ_PS:
                    L = 4 * np.pi ** 2 * np.mean(chi * E * np.exp(1j * t * (p[0] * X + p[1] * Y)))
                    out["L"][(ci, pname, t, p)] = L
                    if M == M2:
                        j1, j2 = math.floor(t * p[0]), math.floor(t * p[1])
                        d1_, d2_ = t * p[0] - j1, t * p[1] - j2
                        hh = np.fft.fft2(chi * np.exp(1j * (d1_ * X + d2_ * Y))) / M ** 2 * np.conj(sh)  # h^(n)
                        terms = hh * c[(index_sign * J1 + j1) % M, (index_sign * J2 + j2) % M]
                        S = np.sum(terms)
                        T = float(np.abs(terms).sum()) + 4 * np.pi ** 2 * float(np.mean(np.abs(chi)))
                        out["id"][(ci, pname, t, p)] = (abs(L - S), abs(L), T)
                        del terms, hh
            if M == M2:
                out["B"][(pname, t)] = (out["B"][(pname, t)][0], c[sel].copy())
            del E, c
    return out

ID_REL, ID_ABS = 1e-9, 1e-14

def identity_verdict(ids):
    """FQ-I: |L - S| <= 1e-9 |L| + 1e-14 T, T = sum_n |h^(n) c(n + j)| + 4 pi^2 mean |chi| (the moduli of the terms of
    the two discrete sums, the scale of their rounding errors). The count of cases decided only by the second term,
    and the smallest |L|/T (an error comparable to |L| hides under the second term only if |L|/T < 1e-14) are printed."""
    bad = sum(1 for (e, L, T) in ids.values() if e > ID_REL * L + ID_ABS * T)
    by_abs = sum(1 for (e, L, T) in ids.values() if ID_REL * L < e <= ID_REL * L + ID_ABS * T)
    wr = max(e / L for (e, L, T) in ids.values()); wt = max(e / T for (e, L, T) in ids.values())
    lmin = min(L / T for (e, L, T) in ids.values())
    return bad == 0, (f"{len(ids)} cases; max |L - S|/|L| = {wr:.2e}; max |L - S|/T = {wt:.2e}; cases failing "
                      f"{ID_REL:g}|L| + {ID_ABS:g}T: {bad}; cases passing only through the term {ID_ABS:g}T: {by_abs}; "
                      f"min |L|/T = {lmin:.2e} (an error of relative size 1e-2 of |L| is detected wherever |L|/T > 1e-12)")

def check_FQ(r1, r2, factor=1.0):
    """FQ-B with D multiplied by `factor` (1 for the criterion, 1/80 for control CFQ: constant 4 -> 1/20)."""
    ntrue = nfalse = nund = 0; worst = 0.0; worst_case = None
    eD_max = eL_max = eB_max = 0.0
    for ci in range(3):
        D = r2["D"][ci] * factor; eD = abs(r1["D"][ci] - r2["D"][ci]) * factor
        eD_max = max(eD_max, eD)
        for pname, _ in PHASES:
            for t in FQ_TS:
                B = r2["B"][(pname, t)][0]
                eB = float(np.abs(r1["B"][(pname, t)][1] - r2["B"][(pname, t)][1]).max())
                eB_max = max(eB_max, eB)
                Bup = max(B + eB, tail_bound(pname, t, NB))
                for p in FQ_PS:
                    L = abs(r2["L"][(ci, pname, t, p)]); eL = abs(r1["L"][(ci, pname, t, p)] - r2["L"][(ci, pname, t, p)])
                    eL_max = max(eL_max, eL)
                    if L + eL <= (D - eD) * (B - eB): ntrue += 1
                    elif L - eL > (D + eD) * Bup: nfalse += 1
                    else: nund += 1
                    rr = L / (D * B)
                    if rr > worst: worst, worst_case = rr, (CUTOFFS[ci].name, pname, t, p)
    return ntrue, nfalse, nund, worst, worst_case, (eD_max, eL_max, eB_max)

def check_FQ_D(npts=200, seed=20261128):
    rng = np.random.default_rng(seed)
    worst = 0.0
    for ch in CUTOFFS:
        X = rng.uniform(-np.pi, np.pi, npts); Y = rng.uniform(-np.pi, np.pi, npts)
        f = lambda x, y: ch.parts(np.asarray(x, float), np.asarray(y, float))[0]
        _, d1, d2, lap = ch.parts(X, Y)
        h1, h2 = 1e-6, 1e-4
        fd1 = (f(X + h1, Y) - f(X - h1, Y)) / (2 * h1)
        fd2 = (f(X, Y + h1) - f(X, Y - h1)) / (2 * h1)
        fdl = (f(X + h2, Y) + f(X - h2, Y) + f(X, Y + h2) + f(X, Y - h2) - 4 * f(X, Y)) / h2 ** 2
        for a_, b_ in ((d1, fd1), (d2, fd2), (lap, fdl)):
            sc = max(float(np.abs(a_).max()), 1e-300)
            worst = max(worst, float(np.abs(a_ - b_).max()) / sc)
    return worst <= 1e-4, f"{3 * npts} points, 3 derivatives each; max |closed form - difference| / max|closed form| = {worst:.2e}"

# ================================================================================================== main
def main():
    t0 = time.time()
    print(f"spln_a5u_loc2_checks: python {sys.version.split()[0]}, numpy {np.__version__}, scipy {scipy.__version__}, "
          f"mpmath {mp.__version__}", flush=True)
    # ---- SPL-N
    ok, d = check_SPLN_A(); line("SPLN-A", ok, d)
    ts_ = time.time(); grid = spl_grid(); print(f"  (grid: {time.time() - ts_:.0f} s)", flush=True)
    ok, d, (vmax, dis) = check_SPLN_U(grid); line("SPLN-U", ok, d)
    ok, d = check_SPLN_G(grid); line("SPLN-G", ok, d)
    ok, d, _ = check_SPLN_L(); line("SPLN-L", ok, d)
    ok, d, _ = check_SPLN_T(); line("SPLN-T", ok, d)
    print(f"  (SPL-N done at {time.time() - t0:.0f} s)", flush=True)
    # ---- A5U
    ok, d = check_A5U_Q(); line("A5U-Q", ok, d)
    ratio, nS, rows, symw, unitw, Rmax, ctl = check_A5U()
    line("A5U-Y", symw <= 1e-10, f"max |K(-alpha) - (-1)^(n1+n2) conj K(alpha)| over all boxes and times = {symw:.2e}; "
                                 f"max | |psi|_2 - 1 | = {unitw:.1e}")
    line("A5U-S", ratio <= BAND, f"{nS} values, max S / median S = {ratio:.4f} (band {BAND}); largest box R = {Rmax}; "
                                 + "; ".join(rows))
    print(f"  (A5U done at {time.time() - t0:.0f} s)", flush=True)
    # ---- LOC2
    ok, d = check_FQ_D(); line("FQ-D", ok, d)
    r1 = fq_compute(M1); r2 = fq_compute(M2)
    ok, d = identity_verdict(r2["id"]); line("FQ-I", ok, d)
    nt, nf, nu, worst, wc, errs = check_FQ(r1, r2)
    dstr = ", ".join(f"{CUTOFFS[i].name}: D = {r2['D'][i]:.6f} (norms " + ", ".join(f"{v:.6f}" for v in r2["norms"][i]) + ")"
                     for i in range(3))
    line("FQ-B", nt == 81 and nf == 0 and nu == 0,
         f"81 cases: decided TRUE {nt}, decided FALSE {nf}, undecided {nu}; max |L|/(D B_N) = {worst:.4e} at {wc}; "
         f"max errors e_D {errs[0]:.1e}, e_L {errs[1]:.1e}, e_B {errs[2]:.1e}; {dstr}; tail bounds T_N (N = {NB}) up to "
         f"{max(tail_bound(pn, t, NB) for pn, _ in PHASES for t in FQ_TS):.3e}")
    print(f"  (LOC2 done at {time.time() - t0:.0f} s)", flush=True)
    # ---- controls
    _, d, _ = check_SPLN_U(grid, cap=mp.mpf("0.7219739"))
    ctrl("CU", vmax - mp.mpf("0.7219739") > dis, d)
    _, d, (v1, v2, dl) = check_SPLN_L(target=mp.mpf("0.721974"))
    ctrl("CL", mp.mpf("0.721974") - max(v1, v2) > dl, d)
    _, d, (wT, chT, nvT) = check_SPLN_T(const=mp.mpf(1) / 2)
    ctrl("CT", wT - mp.mpf(1) / 2 > chT, d)
    w, _, _, _, _ = a5u_q_diffs(sgn=-1); ctrl("CQt", w > 1e-6, f"max site difference with exp(-itH): {w:.3e}")
    w, _, _, _, _ = a5u_q_diffs(diag=(1, -1)); ctrl("CQd", w > 1e-6, f"max site difference with hopping on +-(1,-1): {w:.3e}")
    ctrl("CA5", all(G >= GROW for _, G, _ in ctl),
         "; ".join(f"a0={a0:+.4f}: G = {G:.4f} (required >= {GROW}), band ratio of S' = {br:.4f}" for a0, G, br in ctl))
    nt, nf, nu, worst, wc, _ = check_FQ(r1, r2, factor=1 / 80)
    ctrl("CFQ", nf >= 1, f"constant 1/20: decided TRUE {nt}, decided FALSE {nf}, undecided {nu}; max |L|/(D' B_N) = {worst:.4f}")
    rbad = fq_compute(M2, index_sign=-1)
    nbad = sum(1 for (e, L, T) in rbad["id"].values() if e > 1e-3 * L + ID_ABS * T)
    ctrl("CFI", nbad >= 1, f"index n - j: {nbad} of {len(rbad['id'])} cases with |L - S| > 1e-3 |L| + {ID_ABS:g} T; "
                          f"max relative error {max(e / L for (e, L, T) in rbad['id'].values()):.3e}")
    del rbad
    # ---- information only
    ratioW, nW, rowsW, _, _, _, _ = check_A5U(pairs=a5u_pairs(epss=(0.1, 0.2)))
    info("A5U-W", f"{nW} values (eps = 0.1, 0.2, both a0, both signs), max S / median S = {ratioW:.4f}; " + "; ".join(rowsW))
    allok = all(o for _, o in RESULTS)
    print(f"elapsed {time.time() - t0:.0f} s", flush=True)
    print("OVERALL:", "PASS" if allok else "FAIL", flush=True)
    return 0 if allok else 1

if __name__ == "__main__":
    sys.exit(main())
