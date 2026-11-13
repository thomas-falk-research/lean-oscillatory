"""Lead's checks of the external application-chains dossier (2026-11-12/13) and two repository checks.

Answers file: review/2026-11-13-application-chains-answers.md. These are the lead's own computations, independent of the
dossier's scripts (not run). Floating-point and quadrature results are diagnostics, not enclosures; SymPy identities and
integer computations are exact. Sections:
  P1-P6, Wave  the dossier's hand propositions and imaging-block constants (re-derived numerically / symbolically);
  I3-alias     exact size of the periodic-image contribution in numerics/review/ls_interface_checks.py, I3;
  Order        empirical convergence of the trapezoid Volterra scheme behind the dossier's plasma table.
Run: python3 -I numerics/review/application_chains_checks.py  (numpy, scipy, sympy, mpmath; versions printed).
"""
import math, sys, platform
import numpy as np, scipy, scipy.linalg as la, scipy.special as sp, scipy.integrate as si
import mpmath as mp, sympy as sy
print("runtime", sys.version.split()[0], platform.platform(), "numpy", np.__version__, "scipy", scipy.__version__,
      "sympy", sy.__version__, "mpmath", mp.__version__)
mp.mp.dps = 30
CS = 8*(1+math.sqrt(7))/3
res = {}
def rep(name, ok, **kw):
    res[name] = ok; print(("PASS " if ok else "FAIL ") + name, kw)

# P2: M_eps(t) = g^2 (1/2pi) int (1-cos(2k+eps)) e^{iz cos k} dk  ==  g^2 [J0 + cos(eps) J2]
mx = 0
for z in [0.3, 2.0, 9.5, 40.0]:
    for eps in [0, 0.4, math.pi/2, math.pi]:
        q = mp.quad(lambda k: (1-mp.cos(2*k+eps))*mp.exp(1j*z*mp.cos(k)), [-mp.pi, 0, mp.pi])/(2*mp.pi)
        target = mp.besselj(0, z) + mp.cos(eps)*mp.besselj(2, z)
        mx = max(mx, abs(q-target))
        if eps == 0: mx = max(mx, abs(target - 2*mp.besselj(1, z)/z))
rep("P2 memory identity (mpmath quad, my form J0+cos(eps)J2)", mx < 1e-20, max_err=float(mx))
# repository kernel: I(z,1)=int e^{i(z cos k + k)} = 2 pi i J1(z)
mx = max(abs(mp.quad(lambda k: mp.exp(1j*(z*mp.cos(k)+k)), [-mp.pi, mp.pi]) - 2j*mp.pi*mp.besselj(1, z)) for z in [0.5, 3, 17])
rep("I(z,1) = 2 pi i J1(z)", mx < 1e-20, max_err=float(mx))
# envelope integral 4 t_m
tm = (CS/math.pi)**0.75/2
val = si.quad(lambda t: min(1, CS/math.pi*(2*t)**(-4/3)) if t > 0 else 1, 0, tm)[0] + si.quad(lambda t: CS/math.pi*(2*t)**(-4/3), tm, np.inf)[0]
rep("int min(1,(C*/pi)(2t)^-4/3) = 4 t_m (J=1)", abs(val-4*tm) < 1e-8, val=val, four_tm=4*tm)

# P3: Q_H bounds, and my own emitter computation
def Q(H, T, g):
    f = lambda tau: (H-tau)*g*g*min(1.0, CS/math.pi*(2*tau)**(-4/3))
    return si.quad(f, T, H, points=[tm] if T < tm < H else None, epsabs=1e-13, epsrel=1e-13, limit=200)[0]
claimed = {2: 0.567220, 4: 0.164236, 8: 0.0207251}
ok = True; out = {}
for T, c in claimed.items():
    q = Q(12, T, 0.2); b = q/(1-q); out[T] = b; ok &= abs(b-c) < 5e-6
rep("P3 conditional bounds Q/(1-Q) at J=1,g=.2,H=12", ok, bounds=out)
# reference: long OPEN chain (no wrap), emitter coupled to sites +1 (+g/sqrt2) and -1 (-g/sqrt2), Omega=0, hopping -1
def emitter_exact(ts, N=601, g=0.2):
    n = 2*N+1; Hm = np.zeros((n+1, n+1))
    for i in range(1, n): Hm[i, i+1] = Hm[i+1, i] = -1.0
    mid = N+1  # site 0
    Hm[0, mid+1] = Hm[mid+1, 0] = g/math.sqrt(2); Hm[0, mid-1] = Hm[mid-1, 0] = -g/math.sqrt(2)
    w, U = la.eigh(Hm)
    return np.exp(-1j*np.outer(ts, w)) @ (U[0, :]**2)
def mem(t, g=0.2):
    z = 2*np.asarray(t, float); o = np.ones_like(z); nz = z != 0; o[nz] = 2*sp.j1(z[nz])/z[nz]; return g*g*o
def solve_trunc(H, h, T, g=0.2):
    # c' = -int_0^{min(t,T)} M(tau) c(t-tau) dtau ; trapezoid in tau, implicit trapezoid in t (my own scheme, RK-free)
    n = round(H/h); t = np.arange(n+1)*h; m = mem(t, g); c = np.zeros(n+1, complex); c[0] = 1
    L = n if T is None else round(T/h)
    def F(k, ck):  # memory integral at step k given c[0..k-1] and candidate ck
        j = min(k, L)
        w = np.ones(j+1); w[0] = w[-1] = 0.5
        vals = m[:j+1]*np.concatenate(([ck], c[k-1::-1][:j] if k > 0 else []))
        return h*np.dot(w, vals) if j > 0 else 0.0
    Fprev = 0.0
    for k in range(1, n+1):
        # F(k, ck) = a*ck + b  with a = h*0.5*m[0]
        b = F(k, 0.0); a = 0.5*h*m[0] if min(k, L) > 0 else 0.0
        ck = (c[k-1] - 0.5*h*(Fprev + b))/(1 + 0.5*h*a)
        c[k] = ck; Fprev = a*ck + b
    return t, c
claimed_err = {2: 0.0244562, 4: 0.00608525, 8: 0.00124881}
h = 0.0025; t, cfull = solve_trunc(12, h, None); ref = emitter_exact(t)
errs = {}
for T in claimed_err:
    _, cT = solve_trunc(12, h, T); errs[T] = float(np.max(np.abs(ref-cT)))
fe = float(np.max(np.abs(ref-cfull)))
rep("P3 emitter errors (my solver h=.0025 vs open chain 1203 sites) within 1e-4 of claims and below bounds",
    all(abs(errs[T]-claimed_err[T]) < 1e-4 and errs[T] < out[T] for T in errs), errs=errs, full_vs_exact=fe)

# P4 plasma
def solve_plasma(H, h, T, w=0.25):
    n = round(H/h); t = np.arange(n+1)*h; q = w*t*np.exp(-t*t/2); S = np.exp(-t*t/2); r = np.zeros(n+1); r[0] = S[0]
    L = n if T is None else round(T/h)
    for k in range(1, n+1):
        j = min(k, L); wts = np.ones(j+1); wts[0] = wts[-1] = 0.5
        r[k] = S[k] - h*np.dot(wts[1:], q[1:j+1]*r[k-1::-1][:j])  # q[0]=0 so the implicit term vanishes
    return r
claimed_p = {1: (0.0885400, 0.269569), 2: (0.0233012, 0.0601490), 3: (0.00210549, 0.00493733)}
full = solve_plasma(12, 0.0025, None); ok = True; pe = {}
for T, (e, b) in claimed_p.items():
    err = float(np.max(np.abs(full-solve_plasma(12, 0.0025, T)))); bd = 0.25*math.exp(-T*T/2)/0.75**2
    pe[T] = (err, bd); ok &= abs(err-e) < 1e-5 and abs(bd-b) < 5e-6 and err < bd
rep("P4 plasma table", ok, values=pe)
lam = sy.symbols('s', positive=True); tt = sy.symbols('t', positive=True)
r1 = sy.inverse_laplace_transform((lam+1)/(lam*(lam-1)), lam, tt); r2 = sy.inverse_laplace_transform((lam+1)/(lam*(lam+3)), lam, tt)
rep("P4 controls", sy.simplify(r1-(2*sy.exp(tt)-1)) == 0 and sy.simplify(r2-(sy.Rational(1,3)+sy.Rational(2,3)*sy.exp(-3*tt))) == 0, r1=str(r1), r2=str(r2))
# Vlasov kernel sign: rho_hat(t) = S - int q(t-s) rho(s), q(s) = s|k|^2 W mu_hat(ks); 1D Gaussian check via direct v-integral
k0, W, sig, sv = 0.7, 0.3, 1.1, 1.9
mu_hat = lambda xi: math.exp(-sig**2*xi**2/2)
dmu = lambda v: -v/sig**2*math.exp(-v*v/(2*sig**2))/math.sqrt(2*math.pi*sig**2)
lhs = complex(*[si.quad(lambda v, f=f: f(np.exp(-1j*sv*k0*v)*k0*dmu(v)), -40, 40)[0] for f in (np.real, np.imag)])
rep("P4 IBP: int e^{-i s k v} k mu'(v) dv = i s k^2 mu_hat(ks)", abs(lhs - 1j*sv*k0**2*mu_hat(k0*sv)) < 1e-10, lhs=lhs)

# P5
G = lambda z: 1/(np.sqrt(z-2+0j)*np.sqrt(z+2+0j))
rep("P5 limits", abs(abs(G(1e-8j))-0.5) < 1e-6 and abs(math.sqrt(1e-8)*abs(G(2+1e-8j))-0.5) < 1e-4)

# P6
th = lambda t: mp.besselj(1, 2*t)/t if t != 0 else mp.mpf(1)
Om = 3*mp.pi/2
hh = 2*mp.quad(lambda t: th(t)*mp.cos(Om*t), [0, 1])
spec = max(abs(mp.quad(lambda w: mp.exp(1j*w*t)*mp.sqrt(4-w*w)/(2*mp.pi), [-2, 2]) - th(t)) for t in [0.3, 1.7, 5])
rep("P6 spectral rep and h_hat(3pi/2) < -1/Om + 2/Om^2 < 0", spec < 1e-20 and hh < -1/Om+2/Om**2 < 0 and mp.besselj(1, 2) > 0.5,
    h_hat=float(hh), bound=float(-1/Om+2/Om**2))
t0 = (CS/math.pi)**0.75/2
tail = lambda T: 4.5*t0**(4/3)*T**(-1/3) - t0**2/T
b = lambda t: min(1, (t0/t)**(4/3)) if t > 0 else 1
num = lambda T: si.quad(lambda t: t/T*b(t), 0, T, points=[t0])[0] + si.quad(b, T, np.inf)[0]
Tt = mp.findroot(lambda T: tail(float(T)) - 0.1, 168000)
rep("P6 taper tail formula and T(0.1)", all(abs(tail(T)-num(T)) < 1e-8 for T in [2, 10, 1000]), T_for_0_1=float(Tt))

# P1 gains
tau = (CS/(2*math.pi))**3/2
rep("P1 input-to-peak gains", abs(math.sqrt(tau*4)-2.72194) < 1e-5 and abs(math.sqrt(tau*2)-1.92470) < 1e-5)

# Wave block: exact constants and delay gap
u = sy.symbols('u'); beta = (1-u**2)**3
I0 = sy.integrate(beta, (u, -1, 1)); d2 = sy.diff(beta, u, 2); r = 1/sy.sqrt(5)
L1 = 2*(sy.integrate(-d2, (u, 0, r)) + sy.integrate(d2, (u, r, 1)))
diag = I0*I0/2; ratio = sy.nsimplify(I0*2*L1/diag)
rep("Wave diag 512/1225 and ratio 336/(5 sqrt5)", sy.simplify(diag-sy.Rational(512,1225)) == 0 and sy.simplify(ratio-sy.Rational(336,5)/sy.sqrt(5)) == 0,
    diag=str(diag), ratio=str(sy.simplify(ratio)))
gap = 1e9
for s in np.linspace(-1, 1, 201):
    for a in np.linspace(0, 2*math.pi, 73):
        for bb in np.linspace(0, 2*math.pi, 73):
            x = np.array([0.05*math.cos(a), 2+0.05*math.sin(a), 0]); zz = np.array([0.05*math.cos(bb), 1+0.05*math.sin(bb), 0])
            gm = np.array([s, 0, 1]); gap = min(gap, 2*np.linalg.norm(gm-x) - 2*np.linalg.norm(gm-zz))
rep("Wave delay gap >= 1 on the boundary circles (sampled; triangle inequality gives >= 1.434-0.2)", gap >= 1, min_gap=gap)
def Kt(t, xc, zc, n=1024):
    s, ws = np.polynomial.legendre.leggauss(n); rho = 1.5 + 0.5*s; wr = 0.5*ws
    bs = (1-s**2)**3; br = (1-(2*rho-3)**2)**3
    tx = 2*np.sqrt((s-xc[0])**2 + xc[1]**2 + 1); tz = 2*np.sqrt((s-zc[0])**2 + zc[1]**2 + 1)
    return np.sum(ws[:, None]*bs[:, None]*wr[None, :]*br[None, :]*np.exp(1j*t*rho[None, :]*(tx-tz)[:, None]))
for t in [155, 179]:
    v = abs(Kt(t, (0, 2), (0, 1)))/(512/1225); print("  normalized |K_t| at block centres, t =", t, ":", v, " bound 32/t^2 =", 32/t**2)
rep("Wave mirror pair", abs(abs(Kt(155, (0, 1), (0, -1)))/(512/1225) - 1) < 1e-12)

# I3-alias: periodic images in ls_interface_checks.py I3 (R = 24, orders <= 60), exact integers
def stencil_list(d, size, nmax=60):
    shape = (2*size+1,)*d; L = np.zeros(shape, dtype=object); L[(size,)*d] = 1; out = [L]
    for _ in range(nmax):
        new = np.zeros(shape, dtype=object)
        for ax in range(d):
            new += np.roll(L, 1, ax) + np.roll(L, -1, ax) - 2*L
        L = new; out.append(L)
    return out
worst = {}
for d in (1, 2):
    small = stencil_list(d, 24); big = stencil_list(d, 62); w = 0.0
    for tt in (-1.3, 0.4, 2.0):
        for s in ([(0,), (1,), (-3,)] if d == 1 else [(0, 0), (1, -2)]):
            w = max(w, sum(abs(tt)**n/math.factorial(n)*abs(int(small[n][tuple(24+x for x in s)] - big[n][tuple(62+x for x in s)]))
                           for n in range(61)))
    worst[d] = w
rep("I3-alias: periodic-image contribution below 1e-40 at the I3 times and sites", all(v < 1e-40 for v in worst.values()), worst=worst)

# Order: trapezoid scheme of the plasma table (cutoff T on a grid point); ratio of successive sup differences
ratios = []
for T in (None, 1, 2, 3):
    sols = [solve_plasma(12, h, T) for h in (.02, .01, .005, .0025)]
    dd = [np.max(np.abs(sols[i] - sols[i+1][::2])) for i in range(3)]
    ratios += [dd[0]/dd[1], dd[1]/dd[2]]
rep("Order: successive differences shrink by about 4 (second order) with T on the grid", all(3.9 < r < 4.1 for r in ratios),
    ratios=[round(r, 3) for r in ratios])
print("RESULT", "PASS" if all(res.values()) else "FAIL")
