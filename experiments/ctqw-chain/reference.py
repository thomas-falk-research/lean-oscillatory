#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Certified reference values for the registered quantum-walk experiment (docs/prereg/2026-11-16-CTQW-chain.md).

For an open chain of M identical sites with one excitation at the centre, hopping 1 (the single-excitation sector of
the exchange chain; the lattice Schrodinger equation i u' = -(u_{a+1} + u_{a-1}) with missing neighbours at the
ends), and for each registered time t:
  exact      site populations |<a| exp(i t A) |c>|^2, A the adjacency matrix (certified matrix exponential);
  trotter    the same for the registered circuit: second-order Trotter, step 1/4, bonds split even/odd;
  moment     the second moment about the centre, for both.
Every number is an Arb ball (python-flint), written as "[mid +/- rad]" strings and as decimal lower/upper bounds.
Usage: python3 -I reference.py > reference.json
"""
import json
import platform

import flint
from flint import acb, acb_mat, arb, ctx

ctx.prec = 200
CHAINS = [5, 9]
TIMES = ["0.5", "1", "1.5", "2"]
STEP = "0.25"


def adjacency(M):
    return acb_mat([[acb(1) if abs(a - b) == 1 else acb(0) for b in range(M)] for a in range(M)])


def layer(M, theta, parity):
    """exp(i theta A_parity): 2x2 blocks [[cos, i sin], [i sin, cos]] on bonds (a, a+1), a = parity mod 2."""
    U = [[acb(1) if a == b else acb(0) for b in range(M)] for a in range(M)]
    for a in range(parity, M - 1, 2):
        U[a][a] = U[a + 1][a + 1] = acb(theta.cos())
        U[a][a + 1] = U[a + 1][a] = acb(0, 1) * theta.sin()
    return acb_mat(U)


def enc(x):
    lo, hi = x.lower(), x.upper()
    return {"ball": x.str(20), "lo": lo.str(25, radius=False), "hi": hi.str(25, radius=False)}


out = {"format": "oscint-ctqw-reference/1", "step": STEP, "order": 2, "chains": {},
       "versions": {"python": platform.python_version(), "python-flint": flint.__version__,
                    "flint": flint.__FLINT_VERSION__, "precision_bits": ctx.prec}}
for M in CHAINS:
    c = M // 2
    dt = arb(STEP)
    step = layer(M, dt / 2, 0) * layer(M, dt, 1) * layer(M, dt / 2, 0)
    chain = {"sites": M, "start": c, "times": {}}
    for ts in TIMES:
        t = arb(ts)
        n = int(round(float(ts) / float(STEP)))
        Ue = (adjacency(M) * (acb(0, 1) * t)).exp()
        Ut = step**n
        pe = [abs(Ue[a, c]) ** 2 for a in range(M)]
        pt = [abs(Ut[a, c]) ** 2 for a in range(M)]
        chain["times"][ts] = {
            "steps": n, "bond_layers": 2 * n + 1,
            "exact": [enc(p) for p in pe], "trotter": [enc(p) for p in pt],
            "moment_exact": enc(sum(((a - c) ** 2 * pe[a] for a in range(M)), arb(0))),
            "moment_trotter": enc(sum(((a - c) ** 2 * pt[a] for a in range(M)), arb(0))),
            "tvd_trotter_vs_exact": enc(sum((abs(p - q) for p, q in zip(pe, pt)), arb(0)) / 2),
        }
    out["chains"][str(M)] = chain
print(json.dumps(out, indent=1))
