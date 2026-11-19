#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Exploration for batch SPL (docs/design/batch-SPL-opening.md, section 5). Not a registered test and not evidence:
it located the maximum of |kappa| before the registration of docs/prereg/2026-11-19-SPL-quadratic-remainder.md."""
import mpmath as mp
mp.mp.dps = 30
def F(x):  # int_0^x e^{i v^2/2} dv = sqrt(pi) (C(x/sqrt(pi)) + i S(x/sqrt(pi)))
    r = mp.sqrt(mp.pi); return r*(mp.fresnelc(x/r) + 1j*mp.fresnels(x/r))
Finf = mp.sqrt(mp.pi)*(0.5+0.5j)
def kappa_closed(t):
    return F(t)/2 + t*mp.e**(1j*t*t/2)/2 + 1j*t*t/2*(Finf - F(t))
def kappa_def(t):   # independent of the closed form: quadrature of the definition
    return mp.quad(lambda s: s*F(t/s), mp.linspace(0, 1, 41))
for t in [0.3, 1, 1.7, 2.5, 4]:
    a, b = kappa_closed(mp.mpf(t)), kappa_def(mp.mpf(t))
    print("tau", t, "closed", mp.nstr(a, 12), "def", mp.nstr(b, 12), "diff", mp.nstr(abs(a-b), 3))
best = (0, 0)
ts = [mp.mpf(k)/1000 for k in range(1, 30001)]
for t in ts:
    v = abs(kappa_closed(t))
    if v > best[0]: best = (v, t)
print("grid max |kappa| on (0,30]:", mp.nstr(best[0], 15), "at tau =", mp.nstr(best[1], 8))
f = lambda t: -abs(kappa_closed(t))
t0 = mp.findroot(lambda t: mp.diff(lambda x: abs(kappa_closed(x))**2, t), best[1])
print("refined: tau* =", mp.nstr(t0, 20), " K* =", mp.nstr(abs(kappa_closed(t0)), 20))
print("limit |F(inf)|/2 = sqrt(2 pi)/4 =", mp.nstr(mp.sqrt(2*mp.pi)/4, 15), "; supA/4 bound =", mp.nstr(abs(F(mp.findroot(lambda x: mp.cos(x*x/2)*mp.re(F(x)) + mp.sin(x*x/2)*mp.im(F(x)), 2.2)))/2, 15))
# local maxima list
prev = None; vals = [abs(kappa_closed(t)) for t in ts[::10]]
loc = [(ts[::10][i], vals[i]) for i in range(1, len(vals)-1) if vals[i] > vals[i-1] and vals[i] > vals[i+1]]
print("first local maxima:", [(mp.nstr(a, 5), mp.nstr(b, 8)) for a, b in loc[:5]])
