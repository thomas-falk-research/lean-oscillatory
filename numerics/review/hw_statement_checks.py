#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
# Checks of the DRAFT batch HW statements, transcribed from the Lean text. Two methods for the walk:
# (W) the step recursion in complex floats, with a floating sqrt 2 at every step. Nothing in this script is exact
#     arithmetic (until 2026-11-19 this header announced an exact integer-pair path that was never written; the exact
#     walk is numerics/review/hw_exact_max_checks.py),
# (K) the kernel integral of the definition by the trapezoidal rule, which is exact for trigonometric polynomials.
import numpy as np, math, cmath, itertools, sys
from mpmath import mp, mpf, quad, asin, sin, cos, sqrt, exp, pi, diff
ok=True
def report(name,cond,detail=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ")+name+("  "+detail if detail else ""))

def hadamard_step(psi):
    # psi: dict x -> (c1,c2);  (U psi)(x) = ((psi(x+1).1+psi(x+1).2)/sqrt2, (psi(x-1).1-psi(x-1).2)/sqrt2)
    out={}
    s=math.sqrt(2)
    xs=set()
    for x in psi: xs.add(x-1); xs.add(x+1)
    for x in xs:
        p=psi.get(x+1,(0,0)); m=psi.get(x-1,(0,0))
        out[x]=((p[0]+p[1])/s,(m[0]-m[1])/s)
    return out
def walk(psi0,t):
    psi=dict(psi0)
    for _ in range(t): psi=hadamard_step(psi)
    return psi
def omega(k): return np.arcsin(np.sin(k)/math.sqrt(2))
def kernel(t,x,N=None):
    # literal: (2pi)^-1 int_{-pi}^{pi} (e^{-i t w} - (-1)^t e^{i t w})/sqrt(2(1+cos^2 k)) e^{-i x k} dk ; trapezoid N nodes
    if N is None: N=4*(t+abs(x))+64
    k=-math.pi+2*math.pi*np.arange(N)/N
    w=omega(k)
    f=(np.exp(-1j*t*w)-(-1)**t*np.exp(1j*t*w))/np.sqrt(2*(1+np.cos(k)**2))*np.exp(-1j*x*k)
    return f.sum()/N
# 0. kernel by trapezoid vs adaptive quadrature of the same integrand (mpmath), a few points
mp.dps=30
def kernel_mp(t,x):
    f=lambda k:(exp(-1j*t*asin(sin(k)/sqrt(2)))-(-1)**t*exp(1j*t*asin(sin(k)/sqrt(2))))/sqrt(2*(1+cos(k)**2))*exp(-1j*x*k)
    return quad(f,[-pi,-pi/2,0,pi/2,pi])/(2*pi)
m=0
# K(t, x) = 0 unless t + x is odd: of the first ten points only (1,0) has a nonzero value, so six points with
# t + x odd were added on 2026-11-19 (external review of batch HW); the number of nonzero values is reported.
nz=0
for (t,x) in [(0,0),(1,0),(1,1),(2,0),(2,2),(3,1),(3,-1),(5,-3),(8,4),(13,-7),(2,1),(3,2),(4,-1),(5,-2),(8,3),(13,-6)]:
    v=complex(kernel_mp(t,x))
    nz+=abs(v)>1e-3
    m=max(m,abs(v-kernel(t,x)))
report("kernel: trapezoid against adaptive quadrature, 16 points", m<1e-12 and nz>=7, f"max diff {m:.2e}; {nz} of the 16 values exceed 1e-3 in modulus")
report("K(0,x)=0, K(1,x)=delta", abs(kernel(0,0))<1e-14 and abs(kernel(0,3))<1e-14 and abs(kernel(1,0)-1)<1e-13 and abs(kernel(1,1))<1e-14 and abs(kernel(1,-1))<1e-14)
# 1. HW-R as written, all x in range, several (a,b), t+1 = 1..40
rng=np.random.default_rng(20261116)
worst=0; cases=0
for (a,b) in [(1,0),(0,1),(1,1j),(0.3-0.2j,-1.1+0.7j)]+[tuple(rng.normal(size=2)+1j*rng.normal(size=2)) for _ in range(3)]:
    for t in list(range(0,12))+[20,39]:
        psi=walk({0:(a,b)},t+1)
        for x in range(-(t+4),t+5):
            lhs=psi.get(x,(0,0))
            r1=(a+b)/math.sqrt(2)*kernel(t+1,x+1)+a*kernel(t,x)
            r2=(a-b)/math.sqrt(2)*kernel(t+1,x-1)+b*kernel(t,x)
            worst=max(worst,abs(lhs[0]-r1),abs(lhs[1]-r2)); cases+=1
report("HW-R as written (walk recursion against kernel integral)", worst<1e-11, f"{cases} cases, max diff {worst:.2e}")
# 1b. controls: wrong shift / wrong sign must fail
def hwR_variant(shift1,shift2,sgn):
    a,b=0.3-0.2j,-1.1+0.7j; w=0
    for t in range(0,6):
        psi=walk({0:(a,b)},t+1)
        for x in range(-(t+4),t+5):
            lhs=psi.get(x,(0,0))
            r1=(a+b)/math.sqrt(2)*kernel(t+1,x+shift1)+a*kernel(t,x)
            r2=(a+sgn*b)/math.sqrt(2)*kernel(t+1,x+shift2)+b*kernel(t,x)
            w=max(w,abs(lhs[0]-r1),abs(lhs[1]-r2))
    return w
report("control: shifts exchanged fails", hwR_variant(-1,1,-1)>1e-3)
report("control: (a+b) in the second component fails", hwR_variant(1,-1,1)>1e-3)
# 2. norm conservation (the step is unitary)
psi=walk({0:(0.6,0.8j)},50)
report("norm conserved over 50 steps", abs(sum(abs(v[0])**2+abs(v[1])**2 for v in psi.values())-1)<1e-12)
# 3. HW-K: sup_x |K(t,x)| against the bound, t = 1..600 by the recursion K(t+1,x) = (K(t,x+1)-K(t,x-1))/sqrt2 + K(t-1,x) (checked against the integral)
T=600; n=2*T+9; c=T+4
K0=np.zeros(n,complex); K1=np.zeros(n,complex); K1[c]=1
Ks=[K0,K1]
for t in range(1,T):
    nxt=np.zeros(n,complex); nxt[1:-1]=(Ks[-1][2:]-Ks[-1][:-2])/math.sqrt(2); nxt+=Ks[-2]; Ks.append(nxt)
m=0
for t in [2,3,7,20,61]:
    for x in range(-t-2,t+3): m=max(m,abs(Ks[t][c+x]-kernel(t,x)))
report("kernel recursion against the integral", m<1e-11, f"max diff {m:.2e}")
worst=0
for t in range(1,T+1):
    s=abs(Ks[t]).max(); worst=max(worst,s/(7*t**-0.5+12*t**(-1/3)))
report("HW-K: sup_x |K| / bound, t <= 600", worst<1, f"largest ratio {worst:.4f}")
supK=max(abs(Ks[t]).max()*t**(1/3) for t in range(1,T+1))
print(f"     sup over t<=600 of sup_x|K| t^(1/3) = {supK:.4f}")
# 4. HW-D and HW-L: components against 39 (|a|+|b|) t^(-1/3)
worst=0
for (a,b) in [(1,0),(0,1),(1,1),(1,-1),(1,1j),(1,-1j)]:
    psi={0:(a,b)}
    for t in range(1,301):
        psi=hadamard_step(psi)
        s=max(max(abs(v[0]),abs(v[1])) for v in psi.values())
        worst=max(worst,s/(39*(abs(a)+abs(b))*t**(-1/3)))
report("HW-D: largest ratio, t <= 300, six point states", worst<1, f"{worst:.4f}")
psi0={x:(complex(*rng.normal(size=2)),complex(*rng.normal(size=2))) for x in [-5,-1,0,2,9]}
l1=sum(abs(v[0])+abs(v[1]) for v in psi0.values()); psi=dict(psi0); worst=0
for t in range(1,201):
    psi=hadamard_step(psi); s=max(max(abs(v[0]),abs(v[1])) for v in psi.values()); worst=max(worst,s/(39*l1*t**(-1/3)))
report("HW-L: largest ratio, one random 5-site state, t <= 200", worst<1, f"{worst:.4f}")
# 5. constants of the route (mpmath)
w=lambda k: asin(sin(k)/sqrt(2))
D1=lambda k: cos(k)/sqrt(1+cos(k)**2)
D2=lambda k: -sin(k)*(1+cos(k)**2)**mpf(-1.5)
D3=lambda k: -cos(k)*(4-2*cos(k)**2)*(1+cos(k)**2)**mpf(-2.5)
g=lambda k: 1/sqrt(2*(1+cos(k)**2))
gp=lambda k: sin(k)*cos(k)/(sqrt(2)*(1+cos(k)**2)**mpf(1.5))
m=0
for k in [mpf(j)/97*2*pi-pi for j in range(1,97)]:
    m=max(m,abs(diff(w,k)-D1(k)),abs(diff(D1,k)-D2(k)),abs(diff(D2,k)-D3(k)),abs(diff(g,k)-gp(k)))
report("derivative chain of omega and derivative of the amplitude (numerical differentiation)", m<1e-15, f"max diff {mp.nstr(m,3)}")
grid=[mpf(j)/4000 for j in range(0,4001)]
mu2=min(abs(D2(pi/4+s*pi/2)) for s in grid); mu3=min(abs(D3(-pi/4+s*pi/2)) for s in grid)
mu2b=min(abs(D2(-3*pi/4+s*pi/2)) for s in grid); mu3b=min(abs(D3(3*pi/4+s*pi/2)) for s in grid)
report("|omega''| >= 2/(3 sqrt 3) on [pi/4,3pi/4] and [-3pi/4,-pi/4]", min(mu2,mu2b)>=2/(3*sqrt(3))-mpf(10)**-25, f"min {mp.nstr(min(mu2,mu2b),12)} target {mp.nstr(2/(3*sqrt(3)),12)}")
report("|omega'''| >= 2^(-3/2) on [-pi/4,pi/4] and [3pi/4,5pi/4]", min(mu3,mu3b)>=mpf(2)**mpf(-1.5)-mpf(10)**-25, f"min {mp.nstr(min(mu3,mu3b),12)} target {mp.nstr(mpf(2)**mpf(-1.5),12)}")
amp=lambda a,b: abs(g(b))+quad(lambda k: abs(gp(k)),[a,(a+b)/2,b])
A1=amp(-pi/4,pi/4); A2=amp(pi/4,3*pi/4); A3=amp(3*pi/4,5*pi/4); A4=amp(-3*pi/4,-pi/4)
report("ampNorm on the cos-arcs = sqrt3 - 1", abs(A1-(sqrt(3)-1))<1e-20 and abs(A3-(sqrt(3)-1))<1e-20, mp.nstr(A1,12))
report("ampNorm on the sin-arcs = sqrt2 - 1/sqrt3", abs(A2-(sqrt(2)-1/sqrt(3)))<1e-20 and abs(A4-(sqrt(2)-1/sqrt(3)))<1e-20, mp.nstr(A2,12))
c2=8*(2/(3*sqrt(3)))**mpf(-0.5)*(sqrt(2)-1/sqrt(3)); c3=18*(mpf(2)**mpf(-1.5))**(-mpf(1)/3)*(sqrt(3)-1)
a_half=2*2*c2/(2*pi); a_third=2*2*c3/(2*pi)   # two arcs, two exponentials, divided by 2 pi
report("route constant of t^(-1/2) <= 7", a_half<=7, mp.nstr(a_half,10))
report("route constant of t^(-1/3) <= 12", a_third<=12, mp.nstr(a_third,10))
cD=(7+12)/sqrt(2)+7*sqrt(2)+12*mpf(2)**(mpf(1)/3)
report("route constant of HW-D <= 39 (t >= 2: (7+12)/sqrt2 + 7 sqrt2 + 12 2^(1/3)); t = 1: 1/sqrt2", cD<=39, mp.nstr(cD,10))
print("ALL PASS" if ok else "SOME FAIL")
sys.exit(0 if ok else 1)   # a failed check must fail the process (external review of VC2, 2026-11-19)
