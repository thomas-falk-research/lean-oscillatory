"""Checks of the batch VC2 statements as written (docs/statements.md, "Batch VC2"). Floating point and mpmath
quadrature: searches and consistency checks, not certificates. Two methods for the oscillatory integrals: Fresnel
closed forms piece by piece (scipy.special.fresnel) and adaptive quadrature (scipy.integrate.quad).
Run: python vc2_statement_checks.py   (numpy, scipy, mpmath; versions in numerics/review/requirements-review.txt)"""
import math, cmath, numpy as np
from scipy.special import fresnel
from scipy.integrate import quad
from mpmath import mp, mpf, quad as mquad, sin as msin, sqrt as msqrt, exp as mexp, pi as mpi, findroot
ok = True
def report(name, cond, detail=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))

mp.dps = 30
def A(w):   # vdc2Profile, literal
    w = mpf(w)
    return 2 * mquad(lambda u: msin(w - u * u / 2), [0, msqrt(2 * w)])
def Fq(c):  # int_{-c}^{c} e^{i x^2/2} dx by quadrature
    c = mpf(c)
    return mquad(lambda x: mexp(1j * x * x / 2), [-c, 0, c])

# 1. the profile: maximum on [0, pi], value at pi, identity with the quadratic integral
grid = [mpi * j / 2000 for j in range(2001)]
vals = [A(w) for w in grid]
mx = max(vals); wmx = grid[vals.index(mx)]
wstar = findroot(lambda w: (A(w + mpf(10) ** -12) - A(w - mpf(10) ** -12)), wmx)
m = A(wstar)
report("VC2-N: max of A on [0, pi] (2001 points) below 7/2", mx < mpf(7) / 2, f"max {mp.nstr(mx, 12)} at w = {mp.nstr(wmx, 6)}; refined {mp.nstr(m, 15)} at {mp.nstr(wstar, 10)}")
report("control: A exceeds 33/10 somewhere (so 33/10 is not a bound)", mx > mpf(33) / 10)
worst = max(A(w) - abs(Fq(msqrt(2 * w))) for w in [mpf(j) / 10 for j in range(0, 80)])
report("VC2-A: A(w) <= |int_{-sqrt(2w)}^{sqrt(2w)} e^{i x^2/2}| for w = 0, 0.1, ..., 7.9", worst <= mpf(10) ** -20, f"largest A - |F| = {mp.nstr(worst, 5)}")
gap = abs(Fq(msqrt(2 * wstar))) - m
report("VC2-A is tight at the maximiser (|F(w*)| - A(w*) small)", abs(gap) < mpf(10) ** -15, mp.nstr(gap, 5))
big = max(A(mpf(j) / 50) for j in range(158, 2001))
report("A stays below its maximum on [pi, 40] (step 1/50)", big < m, f"largest {mp.nstr(big, 10)}")
M = float(m)

# 2. VC2-S on random phases with f' continuous, piecewise linear with slopes >= lam (corners in f')
def piecewise_integral(lengths, curv, d0):
    """int e^{if} over consecutive pieces; on piece j: f = f_j + d_j s + curv_j s^2/2. Fresnel closed form."""
    tot = 0j; f = 0.0; d = d0
    for L, k in zip(lengths, curv):
        al = d / k
        sc = math.sqrt(k / math.pi)
        S1, C1 = fresnel((L + al) * sc); S0, C0 = fresnel(al * sc)
        piece = cmath.exp(1j * (f - d * d / (2 * k))) * ((C1 - C0) + 1j * (S1 - S0)) / sc
        tot += piece
        f += d * L + k * L * L / 2; d += k * L
    return tot
def piecewise_quad(lengths, curv, d0):
    tot = 0j; f = 0.0; d = d0
    for L, k in zip(lengths, curv):
        g = lambda s, f=f, d=d, k=k: f + d * s + k * s * s / 2
        re = quad(lambda s: math.cos(g(s)), 0, L, limit=400)[0]; im = quad(lambda s: math.sin(g(s)), 0, L, limit=400)[0]
        tot += re + 1j * im
        f += d * L + k * L * L / 2; d += k * L
    return tot
rng = np.random.default_rng(20261116)
worst = 0.0; n = 0; dmax = 0.0
for trial in range(60000):
    lam = 10 ** rng.uniform(-2, 2)
    npieces = int(rng.integers(1, 6))
    curv = lam * (1 + rng.exponential(1.0, npieces) * rng.integers(0, 2, npieces))
    lengths = rng.exponential(1.5, npieces) / math.sqrt(lam)
    total_len = lengths.sum()
    d0 = -rng.uniform(0, 1) * lam * total_len * rng.uniform(0, 1.5)
    I = piecewise_integral(lengths, curv, d0)
    r = abs(I) * math.sqrt(lam)
    worst = max(worst, r); n += 1
    if trial % 2000 == 0:
        dmax = max(dmax, abs(I - piecewise_quad(lengths, curv, d0)))
report("VC2-S with the constant max A: sqrt(lam) |int e^{if}| <= max A, random piecewise-quadratic phases", worst <= M + 1e-9, f"{n} phases, largest {worst:.9f}, max A = {M:.9f}")
report("Fresnel closed form against adaptive quadrature (30 phases)", dmax < 1e-7, f"max diff {dmax:.2e}")
sym = abs(piecewise_integral([2 * math.sqrt(2 * float(wstar))], [1.0], -math.sqrt(2 * float(wstar))))
report("the symmetric quadratic at w* reaches the constant", abs(sym - M) < 1e-9, f"{sym:.12f}")
# controls: without curvature bounded below by lam the bound fails; with a constant 33/10 it fails
flat = abs(piecewise_integral([6.0], [1e-9], 0.0))
report("control: nearly zero curvature on [0, 6] with lam = 1 exceeds the bound", flat > M, f"{flat:.6f}")
report("control: constant 33/10 is exceeded by the symmetric quadratic", sym > 3.3)

# 3. VC2-K: amplitude and a linear term, constant 7/2 (so also both signs of the curvature)
worst = 0.0; n = 0
for trial in range(1500):
    mu = 10 ** rng.uniform(-1.5, 1.5); sign = rng.choice([-1.0, 1.0]); p = rng.normal() * 3
    a = rng.uniform(-3, 0) / math.sqrt(mu); b = a + rng.exponential(3.0) / math.sqrt(mu)
    kap = mu * (1 + rng.exponential(0.5)); c3 = rng.uniform(0, 0.2) * mu / max(b - a, 1e-9)
    # phi'' = sign (kap + c3 (x - a)) >= mu in modulus on [a, b]
    phi = lambda x: sign * (kap * x * x / 2 + c3 * (x - a) ** 3 / 6)
    c0, c1, om, ph = rng.normal(), rng.normal(), rng.uniform(0, 4) / max(b - a, 1e-9), rng.uniform(0, 6.28)
    psi = lambda x: c0 + c1 * math.cos(om * (x - a) + ph) + 0.5j * math.sin(om * (x - a))
    dpsi = lambda x: -c1 * om * math.sin(om * (x - a) + ph) + 0.5j * om * math.cos(om * (x - a))
    re = quad(lambda x: (cmath.exp(1j * (phi(x) + p * x)) * psi(x)).real, a, b, limit=800)[0]
    im = quad(lambda x: (cmath.exp(1j * (phi(x) + p * x)) * psi(x)).imag, a, b, limit=800)[0]
    amp = abs(psi(b)) + quad(lambda x: abs(dpsi(x)), a, b, limit=800)[0]
    if amp > 1e-12:
        worst = max(worst, abs(re + 1j * im) * math.sqrt(mu) / amp); n += 1
report("VC2-K: sqrt(mu) |int e^{i(phi + p x)} psi| / ampNorm <= 7/2, random data", worst <= 3.5, f"{n} cases, largest ratio {worst:.6f}")
print("ALL PASS" if ok else "SOME FAIL")
