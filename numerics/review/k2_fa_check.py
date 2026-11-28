#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's numeric check of the paper refutation of plant F-a of batch K2 (K2-F with the support condition
tsupport chi ⊆ (−π, π)² dropped; docs/replay/plants/2026-11-28-K2/plant-F-a.lean.txt), answered in
review/2026-11-28-K2-pr26-external-review-answers.md. NOT registered; floating point (except criterion A, integer
arithmetic); tooling, never evidence for a Lean theorem. Deterministic, no random numbers.

Construction (chi = 1, t = 1, p = (1/2, 0)): f_N(x) = (1/(2N)) Σ_{k≤N} (−1)^k sin kx; h(y) the 2M-cell step function
with values e_0..e_{M−1}, −e_0..−e_{M−1} (e the coefficients of the Rudin–Shapiro polynomial P_r, M = 2^r ≥ 32N²);
Ψ(x, y) = s(y) arccos f_N(x), s a continuous piecewise-linear version of h (ramps of total measure ≤ 1/(8N)).
Normalised measure dμ = dx/(2π) per variable in A and B; the box integrals of the plant (unnormalised) in C and D.
  A  Rudin–Shapiro: aperiodic autocorrelations of P_r and Q_r sum to 2M at lag 0 and 0 elsewhere, M = 1..2048.
  B  step version G0 = f + i√(1−f²) h: sup |hat f| = 1/(4N); sup_l |hat h(l)| ≤ √(2/M) ≤ 1/(4N) (scanned |l| ≤ 64M,
     tail bounded analytically); hence every integer coefficient of G0 is ≤ 1/(4N); and the ratio of the fractional
     integral to that sup is (2/π) Σ_{k≤N} k/(k²−1/4) ≥ H_N/π − 1/2, N = 2..32.
  C  continuous phase on the box, N = 4, 8: max over lattice coefficients (2D FFT) ≤ 4π²/(2N); ratio ≥ H_N/π − 1/2.
  D  the fractional box integral by the trapezoidal rule at Nx = 512 and 2048 agrees to 1e-3 relative.
"""
import sys
import numpy as np
from math import pi

ok = True
def crit(name, cond, msg):
    global ok
    ok &= bool(cond)
    print(f"{'PASS' if cond else 'FAIL'}  {name}  {msg}")

def rs(r):
    P = np.array([1]); Q = np.array([1])
    for _ in range(r):
        P, Q = np.concatenate([P, Q]), np.concatenate([P, -Q])
    return P, Q

def H(N): return (1/np.arange(1, N+1)).sum()

# A
good = True
for r in range(0, 12):
    P, Q = rs(r); M = len(P)
    a = np.correlate(P, P, 'full') + np.correlate(Q, Q, 'full')
    good &= a[M-1] == 2*M and bool(np.all(np.delete(a, M-1) == 0))
crit("A", good, "Rudin-Shapiro |P|^2+|Q|^2 = 2M (autocorrelations), M = 1..2048")

# B
def ghat_max(N, K=4096):
    x = -pi + 2*pi*np.arange(K)/K
    f = sum((-1)**k*np.sin(k*x) for k in range(1, N+1))/(2*N)
    return np.abs(np.fft.fft(np.sqrt(1-f**2))/K).max(), np.abs(f).max()
def hhat_sup(r):
    P, _ = rs(r); M = len(P); e = np.concatenate([P, -P]); L = 64*M
    l = np.arange(-L, L+1); l = l[l != 0]
    cell = (1-np.exp(-1j*l*pi/M))/(1j*l*2*pi)        # (1/2π) ∫_0^{π/M} e^{−ilu} du
    S = np.fft.fft(e)[l % (2*M)]                       # Σ_j e_j z^j, z = e^{−iπl/M}, depends on l mod 2M
    tail = 2*np.sqrt(2*M)/(pi*L)                       # |cell| ≤ 1/(π|l|), |S| ≤ 2√(2M) for |l| > L
    return max(np.abs(cell*S).max(), tail), np.sqrt(2/M)
for N in [2, 4, 8, 16, 32]:
    r = int(np.ceil(np.log2(32*N*N))); M = 2**r
    gm, fm = ghat_max(N); hs, hb = hhat_sup(r)
    sup = max(1/(4*N), gm*hs)
    k = np.arange(1, N+1); fr = (k/(k**2-0.25)).sum()/(2*pi*N)
    crit(f"B N={N}", fm <= 0.5 + 1e-12 and hs <= hb + 1e-12 and hb <= 1/(4*N) + 1e-15 and sup <= 1/(4*N) + 1e-15
         and fr/sup >= H(N)/pi - 0.5,
         f"M={M}: sup|hhat| = {hs:.6f} <= sqrt(2/M) = {hb:.6f}; sup|G0hat| = {sup:.6f}; frac = {fr:.6f}; "
         f"ratio = {fr/sup:.4f} >= H_N/pi - 1/2 = {H(N)/pi-0.5:.4f}")

# C and D
def phase_s(N):
    r = int(np.ceil(np.log2(32*N*N))); M = 2**r; P, _ = rs(r); e = np.concatenate([P, -P]).astype(float)
    Ny = 2*M*16; y = -pi + 2*pi*np.arange(Ny)/Ny; cellw = pi/M; w = min(cellw/8, (2*pi)/(8*N)/(2*M))
    c = np.floor((y+pi)/cellw).astype(int) % (2*M); u = (y+pi) - c*cellw
    s = e[c].copy(); nxt = e[(c+1) % (2*M)]; m = u > cellw - w
    s[m] = e[c[m]] + (nxt[m]-e[c[m]])*(u[m]-(cellw-w))/w
    return M, Ny, s
def fN(N, x): return sum((-1)**k*np.sin(k*x) for k in range(1, N+1))/(2*N)
for N in [4, 8]:
    M, Ny, s = phase_s(N); Nx = 128
    x = -pi + 2*pi*np.arange(Nx)/Nx
    G = np.exp(1j*np.outer(np.arccos(fN(N, x)), s))
    B = (np.abs(np.fft.fft2(G))/(Nx*Ny)*(4*pi**2)).max()
    vals = []
    for Nxt in [512, 2048]:
        xt = np.linspace(-pi, pi, Nxt+1); wt = np.full(Nxt+1, 2*pi/Nxt); wt[0] = wt[-1] = pi/Nxt
        vals.append(abs(((wt*np.exp(0.5j*xt))[:, None]*np.exp(1j*np.outer(np.arccos(fN(N, xt)), s))).sum()*(2*pi/Ny)))
    crit(f"C N={N}", B <= 4*pi**2/(2*N) and vals[-1]/B >= H(N)/pi - 0.5,
         f"M={M}, grid {Nx}x{Ny}: max lattice coeff B = {B:.5f} <= 4pi^2/(2N) = {4*pi**2/(2*N):.5f}; "
         f"|box integral at p=(1/2,0)| = {vals[-1]:.5f}; ratio = {vals[-1]/B:.4f} >= {H(N)/pi-0.5:.4f}")
    crit(f"D N={N}", abs(vals[0]-vals[1]) <= 1e-3*vals[1], f"trapezoid Nx=512: {vals[0]:.6f}, Nx=2048: {vals[1]:.6f}")

print("OVERALL:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
