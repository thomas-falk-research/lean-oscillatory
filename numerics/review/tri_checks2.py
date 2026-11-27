#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Second registered numeric test of batch TRI (docs/prereg/2026-11-27-TRI-2.md).

Runs the first registered program's own criteria and functions (numerics/review/tri_checks.py, refused unless its
SHA-256 is the registered value) with exactly two changes of resolution:
1. Newton's method in the search for solutions is allowed 400 steps (mpmath findroot maxsteps=400, verify=False);
   a solution is still accepted only if both equations are below 1e-30, as before.
2. The reduced coefficients are read off with interpolation step 5e-4 instead of 1e-3.
"""
import hashlib
import importlib.util
import itertools
import os

FIRST = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tri_checks.py')
REGISTERED = '1446a8d4dea8675a6e582114bd1b02f00db754c85d3c0629062441df5a402d81'
if hashlib.sha256(open(FIRST, 'rb').read()).hexdigest() != REGISTERED:
    raise SystemExit('tri_checks.py is not the registered program')
spec = importlib.util.spec_from_file_location('tri_checks', FIRST)
tri = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tri)
mp = tri.mp


def solve_all(a, grid=24):
    sols = []
    for i, j in itertools.product(range(grid), range(grid)):
        x0 = -mp.pi + 2 * mp.pi * (i + mp.mpf(1) / 2) / grid
        y0 = -mp.pi + 2 * mp.pi * (j + mp.mpf(1) / 2) / grid
        try:
            r = mp.findroot(lambda x, y: tri.equations(a, x, y), (x0, y0), maxsteps=400, verify=False)
        except (ZeroDivisionError, ValueError):
            continue
        x = (r[0] + mp.pi) % (2 * mp.pi) - mp.pi
        y = (r[1] + mp.pi) % (2 * mp.pi) - mp.pi
        if max(abs(q) for q in tri.equations(a, x, y)) > mp.mpf('1e-30'):
            continue
        if not any(abs(mp.sin((x - p[0]) / 2)) + abs(mp.sin((y - p[1]) / 2)) < mp.mpf('1e-15') for p in sols):
            sols.append((x, y))
    return sols


def reduced(a, x0, y0):
    J0 = tri.jets(a, x0, y0)
    e = tri.kernel(J0)
    w = (-e[1], e[0])
    gx, gy = J0[(1, 0)], J0[(0, 1)]

    def f(u, s):
        dx, dy = u * e[0] + s * w[0], u * e[1] + s * w[1]
        return (mp.cos(x0 + dx) + mp.cos(y0 + dy) + a * mp.cos(x0 + y0 + dx + dy)) - gx * dx - gy * dy

    def g(u):
        s = mp.findroot(lambda s: mp.diff(lambda r: f(u, r), s), 0)
        return f(u, s)

    h = mp.mpf('5e-4')
    us = [k * h for k in range(-4, 5)]
    gs = [g(u) for u in us]
    coeffs = mp.lu_solve(mp.matrix([[u ** p for p in range(9)] for u in us]), mp.matrix(gs))
    return [coeffs[p] for p in range(9)], tri.dmul(J0, 2, [w, w])


tri.solve_all = solve_all
tri.reduced = reduced
if __name__ == '__main__':
    print('first program SHA-256 verified:', REGISTERED)
    tri.main()
