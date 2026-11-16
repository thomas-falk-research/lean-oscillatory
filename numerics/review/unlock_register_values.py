#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified values quoted in docs/design/unlock-map.md, section 6 (hardware and lab register). Tooling, not evidence
for a Lean theorem. Every number printed is an Arb ball (python-flint); "[m +/- r]" is a rigorous enclosure.

A  Waveguide arrays at the published Bessel arguments x = 2 kappa z (4.64, 7.8, 11.0): the peak single-site
   probability max_n J_n(x)^2, the machine-checked LS-D envelope min{1, (C*/(2 pi))^2 x^{-2/3}}, the envelope with
   Landau's constant, and the probability outside a 21-guide array with centre input, sum_{|n| >= 11} J_n(x)^2.
B  An open chain of M = 9 identical sites, excitation at the centre, times t = 1 and 2 (hopping 1; the Bessel
   argument is 2t): site populations from the certified matrix exponential, the largest difference from the infinite
   line, and the second moment against 2 t^2.
C  Trotter error of the brickwork circuit on that chain (single-excitation sector, exact): first and second order,
   steps 1/4 and 1/8: the largest population error.

Usage: python3 -I numerics/review/unlock_register_values.py   (python-flint; versions printed at run time)
"""
import platform

import flint
from flint import acb, acb_mat, arb, ctx

ctx.prec = 200


def show(x, digits=6):
    return x.str(digits)


CSTAR = 8 * (1 + arb(7).sqrt()) / 3 / (2 * arb.pi())
LANDAU = arb("0.7857468704")  # Landau 2000, as quoted in docs/prior_art.md; not certified here

print("A. waveguide arrays (infinite line), x = 2 kappa z")
for xs in ["4.64", "7.8", "11.0"]:
    x = arb(xs)
    probs = {n: x.bessel_j(n) ** 2 for n in range(0, 200)}
    nmax = max(probs, key=lambda n: probs[n].mid())
    inside = probs[0] + 2 * sum((probs[n] for n in range(1, 11)), arb(0))
    outside = 1 - inside  # sum over all n of J_n^2 is 1 (Parseval, a paper step)
    env = CSTAR**2 * x ** (arb(-2) / 3)
    envL = LANDAU**2 * x ** (arb(-2) / 3)
    print(f"  x = {xs}: peak J_n^2 at |n| = {nmax}: {show(probs[nmax])}; LS-D envelope {show(env)} "
          f"(min with 1 applies if above 1); with Landau's constant {show(envL)}; "
          f"probability at |n| >= 11: {show(outside, 4)}")

M = 9
c = 4  # centre, 0-based


def chain(M):
    P = [[acb(0) for _ in range(M)] for _ in range(M)]
    for a in range(M):
        P[a][a] += -2
        if a + 1 < M:
            P[a][a + 1] += 1
            P[a + 1][a] += 1
    return acb_mat(P)


def bond_layer(M, dt, parity):
    """exp(i dt A_parity), A_parity the hopping on bonds (a, a+1) with a = parity mod 2; exact 2x2 blocks."""
    U = [[acb(1) if a == b else acb(0) for b in range(M)] for a in range(M)]
    for a in range(parity, M - 1, 2):
        U[a][a] = acb(dt.cos())
        U[a + 1][a + 1] = acb(dt.cos())
        U[a][a + 1] = acb(0, 1) * dt.sin()
        U[a + 1][a] = acb(0, 1) * dt.sin()
    return acb_mat(U)


print(f"B. open chain, M = {M}, excitation at the centre site {c + 1}")
exact = {}
for ts in ["1", "2"]:
    t = arb(ts)
    U = (chain(M) * (acb(0, 1) * t)).exp()
    pops = [abs(U[a, c]) ** 2 for a in range(M)]
    exact[ts] = pops
    line = [(2 * t).bessel_j(a - c) ** 2 for a in range(M)]
    diff = max((abs(p - q) for p, q in zip(pops, line)), key=lambda d: d.mid())
    m2 = sum(((a - c) ** 2 * pops[a] for a in range(M)), arb(0))
    print(f"  t = {ts}: populations sites 1..{M}: " + ", ".join(show(p, 5) for p in pops))
    print(f"          largest |p_chain - J^2|: {show(diff, 3)}; second moment {show(m2, 6)} against 2 t^2 = {show(2 * t * t, 3)}")

print("C. Trotter error on that chain (largest population error over sites), times t = 1, 2")
for order in (1, 2):
    for dts in ["0.25", "0.125"]:
        dt = arb(dts)
        if order == 1:
            step = bond_layer(M, dt, 1) * bond_layer(M, dt, 0)
        else:
            step = bond_layer(M, dt / 2, 0) * bond_layer(M, dt, 1) * bond_layer(M, dt / 2, 0)
        out = []
        for ts in ["1", "2"]:
            nsteps = int(round(float(ts) / float(dts)))
            U = step**nsteps
            pops = [abs(U[a, c]) ** 2 for a in range(M)]
            err = max((abs(p - q) for p, q in zip(pops, exact[ts])), key=lambda d: d.mid())
            layers = nsteps * (2 if order == 1 else 2) + (1 if order == 2 else 0)
            out.append(f"t = {ts}: {nsteps} steps, {layers} bond layers, error {show(err, 3)}")
        print(f"  order {order}, step {dts}: " + "; ".join(out))

print(f"python {platform.python_version()}, python-flint {flint.__version__}, FLINT {flint.__FLINT_VERSION__}, "
      f"working precision {ctx.prec} bits")
