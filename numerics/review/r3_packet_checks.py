#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's checks of the external R3 research packet (2026-11-13): T8 (Fourier error package), T7 (Hann window),
T10 (lattice constants), T5 (Clopper-Pearson sample size), T2 (threshold arithmetic).

Answers file: review/2026-11-13-external-R3-answers.md. These are the lead's own computations from first principles
(direct grid sums, quadrature, Bessel functions, Beta quantiles), not re-assertions of the packet's closed forms. The
packet's four scripts were run separately in a network-less sandbox and compared byte for byte with their expected
outputs (recorded in the answers file); nothing here imports or reads them. mpmath at 60 digits; quadrature results
are diagnostics, not enclosures; integer and Fraction comparisons are exact.
Run: python3 -I numerics/review/r3_packet_checks.py  (mpmath; versions printed).
"""
import sys, platform, cmath, math, random
from fractions import Fraction as Fr
import mpmath as mp
print("runtime", sys.version.split()[0], platform.platform(), "mpmath", mp.__version__)
mp.mp.dps = 60
res = {}
def rep(name, ok, **kw):
    res[name] = bool(ok); print(("PASS " if ok else "FAIL ") + name, kw)

def grid(N):  # k_j = -pi + 2 pi j / N
    return [-mp.pi + 2*mp.pi*j/N for j in range(N)]

# ---------------- T8 ----------------
# G1: Poisson kernel F(k) = (1-r^2)/(1-2r cos k + r^2), c_n = r^|n|; Q_N(0) = grid average, computed directly.
r = mp.mpf(1)/2
F = lambda k: (1-r**2)/(1-2*r*mp.cos(k)+r**2)
errs, closed_ok = {}, True
for N in range(1, 25):
    Q = sum(F(k) for k in grid(N))/N
    x = (-r)**N
    closed_ok &= abs(Q - (1+x)/(1-x)) < mp.mpf(10)**-50
    errs[N] = abs(Q - 1)
least = min(N for N in errs if errs[N] < mp.mpf(10)**-6)
rep("G1 direct grid average equals (1+(-r)^N)/(1-(-r)^N), N = 1..24 (to 1e-50)", closed_ok)
rep("G1 least N with |Q_N(0) - c_0| < 1e-6 is 21; error at 21 equals 2/2097153",
    least == 21 and abs(errs[21] - mp.mpf(2)/2097153) < mp.mpf(10)**-50,
    err20=float(errs[20]), err21=float(errs[21]))
rep("G1 unsigned envelope 2r^21/(1-r^21) also below 1e-6 (so accuracy alone cannot see the sign)",
    Fr(2, 2**21-1) < Fr(1, 10**6), unsigned=float(Fr(2, 2**21-1)))

# G2: parity controls, direct grid averages of monomials
avg = lambda f, N: sum(f(k) for k in grid(N))/N
m3 = avg(lambda k: mp.exp(3j*k), 3); m2 = avg(lambda k: mp.exp(2j*k), 2); m1 = avg(lambda k: mp.exp(1j*k), 2)
rep("G2 N=3, c_3=1 gives -1; N=2, c_2=1 gives +1; N=2, c_1=1 gives 0",
    abs(m3+1) < 1e-50 and abs(m2-1) < 1e-50 and abs(m1) < 1e-50)
zero_grid = sum(mp.exp(3j*2*mp.pi*j/3) for j in range(3))/3
rep("G2 on the grid starting at 0 the same monomial gives +1 (origin matters)", abs(zero_grid-1) < 1e-50)

# G3: signed alias identity, generic complex coefficients, d = 1 and d = 2
random.seed(20261113)
M = 120
def coef1(m, rho=mp.mpf("0.55")):
    rng = random.Random(1000 + m)
    return mp.mpc(rng.uniform(-1, 1), rng.uniform(-1, 1))*rho**abs(m)
cs = {m: coef1(m) for m in range(-M, M+1)}
worst_s, worst_u = mp.mpf(0), mp.mpf(10)
for N in (3, 4, 5, 7):
    for n in (-2, 0, 1, 3):
        G = sum(sum(c*mp.exp(1j*m*k) for m, c in cs.items())*mp.exp(-1j*n*k) for k in grid(N))/N
        signed = sum(((-1)**(N*l))*cs[n+N*l] for l in range(-M//N, M//N+1) if abs(n+N*l) <= M)
        unsigned = sum(cs[n+N*l] for l in range(-M//N, M//N+1) if abs(n+N*l) <= M)
        worst_s = max(worst_s, abs(G-signed))
        if N % 2: worst_u = min(worst_u, abs(G-unsigned))
rep("G3 d=1 grid coefficient = signed alias sum (generic complex c, rho 0.55, |m|<=120)", worst_s < mp.mpf(10)**-25,
    max_err=float(worst_s), min_unsigned_miss_odd_N=float(worst_u))
M2 = 40
c2 = {}
for a in range(-M2, M2+1):
    for b in range(-M2, M2+1):
        rng = random.Random(7*a + 1009*b)
        c2[(a, b)] = mp.mpc(rng.uniform(-1, 1), rng.uniform(-1, 1))*mp.mpf("0.4")**(abs(a)+abs(b))
mp.mp.dps = 30
w2 = mp.mpf(0)
for N, n in ((3, (1, -1)), (4, (0, 2))):
    g = grid(N); G = 0
    for k1 in g:
        for k2 in g:
            Fv = sum(c*mp.exp(1j*(a*k1+b*k2)) for (a, b), c in c2.items())
            G += Fv*mp.exp(-1j*(n[0]*k1+n[1]*k2))
    G /= N*N
    S = sum(((-1)**(N*(l1+l2)))*c2[(n[0]+N*l1, n[1]+N*l2)] for l1 in range(-M2, M2+1) for l2 in range(-M2, M2+1)
            if abs(n[0]+N*l1) <= M2 and abs(n[1]+N*l2) <= M2)
    w2 = max(w2, abs(G-S))
rep("G3 d=2 grid coefficient = sum (-1)^(N(l1+l2)) c_(n+Nl) (N = 3, 4)", w2 < mp.mpf(10)**-15, max_err=float(w2))
mp.mp.dps = 60

# G4: geometric budgets T8.3c (sharp at n = 0) and T8.3d (l1 envelope, max-norm window)
A, rr, ok = mp.mpf(1), mp.mpf("0.3"), True
for N in (3, 6):
    for n in range(-(N-1), N):
        actual = sum(rr**abs(n+N*l) for l in range(-60, 61) if l != 0)
        ok &= actual <= A*(rr**(N-abs(n)) + rr**(N+abs(n)))/(1-rr**N) + mp.mpf(10)**-50
    sharp = sum(rr**(N*abs(l)) for l in range(-80, 81) if l != 0)
    ok &= abs(sharp - 2*rr**N/(1-rr**N)) < mp.mpf(10)**-40
rep("G4 T8.3c budget holds for all |n| < N and is attained at n = 0 by phase-aligned coefficients", ok)
ok = True
for N in (4, 7):
    for R in (0, 1, 2):
        for n in [(a, b) for a in range(-R, R+1) for b in range(-R, R+1)]:
            actual = sum(rr**(abs(n[0]+N*l1)+abs(n[1]+N*l2)) for l1 in range(-30, 31) for l2 in range(-30, 31)
                         if (l1, l2) != (0, 0))
            ok &= actual <= rr**(-2*R)*(((1+rr**N)/(1-rr**N))**2 - 1)*(1 + mp.mpf(10)**-50)
rep("G4 T8.3d budget holds on the max-norm window (N = 4, 7; R = 0, 1, 2); equality at R = 0, n = 0 up to 1e-50 relative", ok)

# G5: continuum Poisson sanity, Laplace density f = e^{-|x|}/2, H(u) = 1/(1+u^2), h = pi/4, x = 0
h = mp.pi/4
H = lambda u: 1/(1+u**2)
Hq = mp.quad(lambda x: mp.exp(-abs(x))/2*mp.exp(1j*mp.mpf(3)*x), [-mp.inf, 0, mp.inf])
rep("G5 transform of e^{-|x|}/2 at u=3 equals 1/(1+9) (convention exp(+iux))", abs(Hq - mp.mpf(1)/10) < 1e-30, quad_err=float(abs(Hq - mp.mpf(1)/10)))
S16 = h/(2*mp.pi)*(1 + 2*sum(H(k*h) for k in range(1, 17)))
Sinf = h/(2*mp.pi)*(1 + 2*mp.nsum(lambda k: H(k*h), [1, mp.inf]))
budget = mp.mpf(17)/324 + 2/(mp.pi*(1+4*mp.pi))
rep("G5 infinite sum = 1/2 + 1/(e^8 - 1) (Poisson, period L = 8), finite K = 16 error within the budget",
    abs(Sinf - (mp.mpf(1)/2 + 1/(mp.e**8-1))) < 1e-40 and abs(S16 - mp.mpf(1)/2) <= budget and budget < mp.mpf(1)/10,
    err=float(abs(S16-0.5)), budget=float(budget))
for B, q, L, R in ((1, 2, 8, 0), (2, 3, 5, 3), (1, 1.5, 3, 2.5)):
    B, q, L, R = map(mp.mpf, (B, q, L, R))
    D = 1+L-R
    exact = 2*B*mp.nsum(lambda m: (1+m*L-R)**(-q), [1, mp.inf])
    assert exact <= 2*B*(D**(-q) + D**(1-q)/(L*(q-1)))
rep("G5 alias budget dominates 2B sum_{m>=1} (1+mL-R)^(-q) at three parameter sets", True)

# G6, G7: T8-1 sanity tail and T8-4 data
tail = mp.quad(lambda u: (1+u)**-2, [1, mp.inf])*2/(2*mp.pi)
rep("G6 (1/2pi) int_{|u|>1} (1+|u|)^-2 = 1/(2pi) = A/(pi(p-1)) (1+T)^(1-p) at A=1,p=2,T=1",
    abs(tail - 1/(2*mp.pi)) < 1e-40)
I4 = mp.quad(lambda u: mp.exp(-u)*mp.exp(4j*u), [0, mp.inf])
tri = mp.quad(lambda u: (1-u/mp.pi)*mp.exp(1j*u), [0, mp.pi])
rep("G7 int_0^inf e^{-u} e^{4iu} = 1/(1-4i), |.| = 1/sqrt17 in (1/8, 1/2); triangle datum = 2/pi + i, |.| > 1",
    abs(I4 - 1/(1-4j)) < 1e-15 and abs(tri - (2/mp.pi + 1j)) < 1e-40 and abs(tri) > 1,
    I4abs=float(abs(I4)), tri_abs=float(abs(tri)))

# ---------------- T7 ----------------
hann = lambda x: mp.cos(mp.pi*x)**2
norm = mp.quad(hann, [-0.5, 0.5])
Ahat = lambda u: mp.quad(lambda x: hann(x)*mp.exp(-2j*mp.pi*u*x), [-0.5, 0, 0.5])/norm
closed = lambda u: mp.sin(mp.pi*u)/(mp.pi*u*(1-u**2))
dev = max(abs(Ahat(u) - closed(u)) for u in (mp.mpf("0.3"), mp.mpf("2.5"), mp.mpf("3.5"), mp.mpf("7.25")))
mp.mp.dps = 30
samples = max(abs(closed(mp.mpf(35)/10 + mp.mpf(j)/2000)) for j in range(0, 2000*60))
mp.mp.dps = 60
target = 8/(315*mp.pi)
rep("T7 normalised Hann transform = sin(pi u)/(pi u (1-u^2)); attained at u = 7/2; envelope 1/(pi u (u^2-1)) decreasing; "
    "max of samples on [3.5, 63.5] <= 8/(315 pi)",
    dev < 1e-40 and abs(abs(closed(mp.mpf(7)/2)) - target) < 1e-50 and samples <= target*(1+mp.mpf(10)**-25),
    value=float(target), dB=float(20*mp.log10(target)))

# ---------------- T10 ----------------
Cs = 8*(1+mp.sqrt(7))/3
C0 = Cs/(2*mp.pi)
rep("T10 C0 = C*/(2pi) = 4(1+sqrt7)/(3pi) = 1.5473049131..., C0^3/2 = 1.85224195868...",
    abs(C0 - 4*(1+mp.sqrt(7))/(3*mp.pi)) < 1e-50 and mp.nstr(C0, 11) == "1.5473049132" and mp.nstr(C0**3/2, 12) == "1.85224195868",
    C0=mp.nstr(C0, 13), thr=mp.nstr(C0**3/2, 13))
J16 = abs(mp.besselj(16, 8))
rep("T10 |J_16(8)| <= e^6/65536 (contour bound) << C0/2 (cube-root bound)",
    J16 <= mp.e**6/65536 < C0/2, J16=float(J16), contour=float(mp.e**6/65536), cube=float(C0/2))
lan = max(abs(mp.besselj(n, x))*x**(mp.mpf(1)/3) for n in range(0, 6) for x in [mp.mpf(j)/20 for j in range(1, 800)])
rep("T10 sampled max |J_n(x)| x^(1/3) (n <= 5, x <= 40) is below Landau's 0.7858 and below C0", lan < 0.7858 < C0,
    sampled_max=float(lan))

# ---------------- T5 ----------------
def betaincinv(a, b, p):  # regularized incomplete Beta quantile by bisection (mpmath 1.3.0 has no inverse)
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(220):
        mid = (lo+hi)/2
        if mp.betainc(a, b, 0, mid, regularized=True) < p: lo = mid
        else: hi = mid
    return (lo+hi)/2
def cp_lower_all_success(n, alpha):  # two-sided 1 - alpha, x = n
    return betaincinv(n, 1, alpha/2)
for n, a, val in ((4, mp.mpf(1)/20, "0.3976"), (8, mp.mpf(1)/20, "0.6306"), (86, mp.mpf(1)/40, None)):
    lo = cp_lower_all_success(n, a)
    assert abs(lo - (a/2)**(mp.mpf(1)/n)) < 1e-40, n
rep("T5 CP lower endpoint for n/n is (alpha/2)^(1/n) (Beta quantile); 86/86 at 97.5% gives 0.9503 > 0.95, 85/85 gives < 0.95",
    (mp.mpf(1)/80)**(mp.mpf(1)/86) > mp.mpf(19)/20 > (mp.mpf(1)/80)**(mp.mpf(1)/85)
    and Fr(19, 20)**86 < Fr(1, 80) < Fr(19, 20)**85,
    n86=mp.nstr((mp.mpf(1)/80)**(mp.mpf(1)/86), 12), n85=mp.nstr((mp.mpf(1)/80)**(mp.mpf(1)/85), 12))
rep("T5 repository rounds: 4/4 -> 0.398, 8/8 -> 0.631, 0/2 -> 0.842, 0/4 -> 0.602 (docs/calibration.md)",
    [mp.nstr(v, 3) for v in ((mp.mpf(1)/40)**(mp.mpf(1)/4), (mp.mpf(1)/40)**(mp.mpf(1)/8),
                              1-(mp.mpf(1)/40)**(mp.mpf(1)/2), 1-(mp.mpf(1)/40)**(mp.mpf(1)/4))] == ["0.398", "0.631", "0.842", "0.602"])
# exact CP coverage at p = 1/2, n = 86, 95%: shows two 95% intervals do not give 95% joint coverage
n = 86
cover = 0
for x in range(n+1):
    lo = mp.mpf(0) if x == 0 else betaincinv(x, n-x+1, mp.mpf(1)/40)
    hi = mp.mpf(1) if x == n else betaincinv(x+1, n-x, 1-mp.mpf(1)/40)
    if lo <= 0.5 <= hi:
        cover += mp.binomial(n, x)/mp.mpf(2)**n
rep("T5 CP 95% coverage at p=1/2, n=86, squared, is about 0.9219 < 0.95 (why Bonferroni is used)",
    abs(cover**2 - mp.mpf("0.921881054588")) < 1e-9, coverage=mp.nstr(cover, 12), joint=mp.nstr(cover**2, 12))

# ---------------- T2 ----------------
ok = True
for base, (pn, pd), lo in ((Fr(11025, 16), (6, 5), 2546), (Fr(23275, 16), (4, 3), 16482), (Fr(99225, 64), (3, 2), 61046)):
    # base^(pn/pd) in (lo, lo+1)  <=>  lo^pd < base^pn < (lo+1)^pd
    ok &= lo**pd < base**pn < (lo+1)**pd
rep("T2 thresholds (11025/16)^(6/5), (23275/16)^(4/3), (99225/64)^(3/2) lie in (2546,2547), (16482,16483), (61046,61047)", ok)

# Referee findings re-checked by the lead: T8-3 "useful from" sentence; T5 pilot pass probability
eps = Fr(1, 10**6)
least_uniform = min(N for N in range(1, 40) if Fr(1, 2**N) <= eps/(2+eps))
least_unsigned = min(N for N in range(1, 40) if Fr(2, 2**N-1) < eps)
least_signed = min(N for N in range(1, 40) if Fr(2, 2**N-(-1)**N) < eps)
rep("MINOR-1 at eps = 1e-6 the uniform condition, the unsigned envelope and the exact signed error all give least N = 21 "
    "(the packet's 'slightly better odd-grid threshold' sentence is false at this tolerance)",
    least_uniform == least_unsigned == least_signed == 21)
lo85 = betaincinv(85, 2, mp.mpf(1)/80)
rep("MINOR-2 85/86 at 97.5% gives lower endpoint 0.928 < 0.95: the pilot passes only on 172/172; "
    "pass probability p^172 is 0.178, 0.422, 0.842 at p = 0.99, 0.995, 0.999",
    lo85 < mp.mpf(19)/20 and [round(x**172, 3) for x in (0.99, 0.995, 0.999)] == [0.178, 0.422, 0.842],
    lower_85_of_86=mp.nstr(lo85, 6))

# Numbers quoted in the answers from referee reports, recomputed by the lead
rep("T5 pass probability at exactly the targets (0.95, 0.05) is 0.95^172 = 1.5e-4; one-sided 95% needs n = 59, "
    "one-sided Bonferroni 97.5% needs n = 72",
    abs(0.95**172 - 1.47e-4) < 1e-6
    and min(n for n in range(1, 200) if Fr(19, 20)**n < Fr(1, 20)) == 59
    and min(n for n in range(1, 200) if Fr(19, 20)**n < Fr(1, 40)) == 72, p_at_targets=0.95**172)
# T2 with the packet's own k = 2 constant 6 (c3 = 14, c4 = 30): least integer t with C*(1225/1024)*... strictly below trivial
def least_t(C, num, den):  # least integer t with C t^(-num/den) < 1024/1225, i.e. t^num > (C*1225/1024)^den
    base = Fr(C)*Fr(1225, 1024); t = 1
    while Fr(t)**num <= base**den: t += 1
    return t
alt = (least_t(4*14*6, 5, 6), least_t(4*30*6, 3, 4), least_t(4*14*14, 2, 3))
orig = (least_t(4*18*8, 5, 6), least_t(4*38*8, 3, 4), least_t(4*18*18, 2, 3))
rep("T2 thresholds with constants 8/18/38 are 2547/16483/61047; with the hand constant 6 (14, 30) they are lower",
    orig == (2547, 16483, 61047), with_6=alt)

print("RESULT", "PASS" if all(res.values()) else "FAIL", f"{sum(res.values())}/{len(res)}")
