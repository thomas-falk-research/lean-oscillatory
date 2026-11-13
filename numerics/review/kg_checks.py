#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Lead's independent checks of the external R2 packet (discrete Klein-Gordon kernel; review/2026-11-12-R2-KG-answers.md).

Written by the lead without reading or reusing the packet's scripts.
J_m(t, xi) = int_{-pi}^{pi} exp(i(t sqrt(m^2 + 2 - 2 cos k) + xi k)) dk, a_m = (sqrt(m^2+4) - m)/2, C* = 8(1 + sqrt 7)/3.
K1 EXACT (sympy, polynomial identities in c = cos k, s = sin k with s^2 = 1 - c^2, q symbolic): a^2(m^2 + 2) = 1 + a^4
   (so omega'/a = sin k / sqrt(1 + q^2 - 2q cos k) with q = a^2); the numerator of h'; 1 - h^2 = (c - q)^2/Dn; the two
   level-set roots of the quadratic in cos k. omega'''(arccos q) = -a by 40-digit numerical differentiation (FLOAT).
K2 FLOAT: the level-set length |{k in [-pi, pi] : h(k) > r}| = 2 arccos r, by direct sampling, for several (m, r).
K3 FLOAT: max of (a_m |t|)^(1/3) |J_m(t, xi)| / C* over m in {0, 1e-6, 0.01, 0.1, 0.5, 1, 2, 5, 20}, normalised times
   T = a_m t in [0.1, 2000] and v = xi/T in [0, 1.6] (refined near the caustic v = 1); Gauss-Legendre on the pieces
   split at k = 0, +-arccos(q) and +-pi, with node doubling at three times per mass. Must be < 1. Also prints the
   empirical max T^(1/3)|J_m| per m (as m grows it should approach the cosine kernel's value, about 5.05).
K4 FLOAT: the lower bound |J_m(1/(2 a_m), 0)| >= 7 pi/4, and |J_m - J_0| <= 2 pi |t| m.
Controls (must be rejected): the bound without the mass factor (C* |t|^(-1/3)) at m = 20; the faster rate T^(-1/2).
Usage: python3 -I numerics/review/kg_checks.py (needs numpy, sympy, mpmath; versions printed at run time)
"""
import platform
import sys

import mpmath as mpm
import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss

ok = True
CS = 8 * (1 + np.sqrt(7)) / 3


def report(line):
    print(line, flush=True)


# K1 exact
m = sp.symbols('m', positive=True)
a = (sp.sqrt(m**2 + 4) - m) / 2
q, c, s, r, Q = sp.symbols('q c s r Q', real=True)
Dn = 1 + q**2 - 2*q*c
checks = [
    ('a^2 (m^2 + 2) = 1 + a^4', sp.expand(a**2 * (m**2 + 2) - (1 + a**4))),
    # d/dk [s Dn^(-1/2)] = (c Dn - q s^2) / Dn^(3/2); claimed numerator (c - q)(1 - q c)
    ("h' numerator = (c - q)(1 - q c)", sp.expand((c*Dn - q*s**2 - (c - q)*(1 - q*c)).subs(s**2, 1 - c**2))),
    ('Dn - s^2 = (c - q)^2', sp.expand((Dn - s**2 - (c - q)**2).subs(s**2, 1 - c**2))),
]
for e in (1, -1):
    uu = Q*r**2 + e*sp.sqrt(1 - r**2)*sp.sqrt(1 - Q**2*r**2)
    checks.append(('level root (sign %+d) solves 1 - u^2 = r^2 (1 + Q^2 - 2 Q u)' % e,
                   sp.expand((1 - uu**2) - r**2*(1 + Q**2 - 2*Q*uu))))
for name, e in checks:
    z = (e == 0)
    ok &= bool(z)
    report(f"K1 {name}: {'PASS' if z else 'FAIL'}")
mpm.mp.dps = 40
for mv in ['0.3', '2', '9']:
    mm = mpm.mpf(mv)
    am = (mpm.sqrt(mm**2 + 4) - mm) / 2
    d3 = mpm.diff(lambda kk: mpm.sqrt(mm**2 + 2 - 2*mpm.cos(kk)), mpm.acos(am**2), 3)
    good = abs(d3 + am) < mpm.mpf('1e-25')
    ok &= good
    report(f"K1 third derivative at arccos q equals -a, m = {mv}: residual {mpm.nstr(d3 + am, 3)} "
           f"{'PASS' if good else 'FAIL'} (40-digit numeric)")


def a_of(mm):
    return 2 / (np.sqrt(mm**2 + 4) + mm)


# K2 level-set lengths
for mm in [0.05, 1.0, 7.0]:
    qq = a_of(mm)**2
    kk = np.linspace(-np.pi, np.pi, 2_000_001)
    hh = np.sin(kk) / np.sqrt(1 + qq**2 - 2*qq*np.cos(kk))
    for rr in [-0.9, -0.3, 0.0, 0.4, 0.95]:
        L = np.mean(hh > rr) * 2 * np.pi
        good = abs(L - 2*np.arccos(rr)) < 1e-4
        ok &= good
        report(f"K2 m={mm} r={rr:+.2f}: length {L:.6f} vs 2 arccos r {2*np.arccos(rr):.6f} {'PASS' if good else 'FAIL'}")


def J(mm, t, xis, n):
    """Gauss-Legendre with n nodes on each piece between -pi, -c, 0, c, pi (c = arccos q)."""
    cc = np.arccos(min(a_of(mm)**2, 1.0))
    br = sorted(set([-np.pi, -cc, 0.0, cc, np.pi]))
    x, w = leggauss(n)
    tot = np.zeros(len(xis), complex)
    for lo, hi in zip(br[:-1], br[1:]):
        if hi - lo < 1e-15:
            continue
        kk = (hi - lo) / 2 * x + (hi + lo) / 2
        ww = (hi - lo) / 2 * w
        om = np.sqrt(mm**2 + 2 - 2*np.cos(kk))
        tot += np.exp(1j * (t*om[None, :] + np.outer(xis, kk))) @ ww
    return tot


# K3 the bound
masses = [0.0, 1e-6, 0.01, 0.1, 0.5, 1.0, 2.0, 5.0, 20.0]
Ts = np.geomspace(0.1, 2000, 45)
vs = np.unique(np.concatenate([np.linspace(0, 1.6, 321), np.linspace(0.95, 1.05, 201)]))
worst, worst_at, disc_max = 0.0, None, 0.0
best_norm = {}
for mm in masses:
    am = a_of(mm)
    bmax = 0.0
    for iT, T in enumerate(Ts):
        t = T / am
        n = int(max(48, 1.2 * T * 1.6 + 40))
        A = J(mm, t, T * vs, n)
        if iT in (0, 22, len(Ts) - 1):
            disc_max = max(disc_max, float(np.max(np.abs(A - J(mm, t, T * vs, 2 * n)))))
        val = T**(1/3) * np.abs(A)
        i = int(np.argmax(val))
        bmax = max(bmax, float(val[i]))
        if val[i] / CS > worst:
            worst, worst_at = float(val[i] / CS), (mm, T, vs[i])
    best_norm[mm] = bmax
    report(f"K3 m={mm:g}: max T^(1/3)|J| = {bmax:.4f}")
good = worst < 1 and disc_max < 1e-8
ok &= good
report(f"K3 max (a|t|)^(1/3)|J|/C* = {worst:.4f} at (m, T, v) = ({worst_at[0]:g}, {worst_at[1]:.3f}, {worst_at[2]:.4f}); "
       f"node-doubling discrepancy {disc_max:.1e}; {'PASS' if good else 'FAIL'}")

# K4 lower bound and Lipschitz-in-m bound
for mm in [0.0, 0.3, 1.5, 10.0]:
    am = a_of(mm)
    v = abs(J(mm, 1/(2*am), np.array([0.0]), 200)[0])
    good = v >= 7*np.pi/4
    ok &= good
    report(f"K4 m={mm}: |J(1/(2a), 0)| = {v:.5f} >= 7pi/4 = {7*np.pi/4:.5f} {'PASS' if good else 'FAIL'}")
xis = np.linspace(-7.3, 7.3, 59)
lip = max(float(np.max(np.abs(J(mm, t, xis, 2000) - J(0.0, t, xis, 2000)))) / (2*np.pi*abs(t)*mm)
          for mm in [1e-3, 0.05, 0.4] for t in [-3.0, 0.7, 25.0])
ok &= lip <= 1
report(f"K4 max |J_m - J_0| / (2 pi |t| m) = {lip:.4f} (<= 1) {'PASS' if lip <= 1 else 'FAIL'}")

# Controls
mm = 20.0
t = 1 / (2 * a_of(mm))
c1 = abs(J(mm, t, np.array([0.0]), 200)[0]) > CS * t**(-1/3)
c2 = max(T**0.5 * float(np.max(np.abs(J(1.0, T / a_of(1.0), T*vs, int(2*T + 60))))) for T in [500.0, 2000.0]) > CS
ok &= c1 and c2
report(f"Control no-mass-factor at m = 20 rejected: {c1}; control rate T^(-1/2) rejected: {c2}")
report(f"RUNTIME python {platform.python_version()} numpy {np.__version__} sympy {sp.__version__} mpmath {mpm.__version__}")
report("RESULT " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
