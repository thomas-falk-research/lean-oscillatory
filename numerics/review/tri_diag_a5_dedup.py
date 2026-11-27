#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Diagnostic (not a registered test) of the T1 FAIL at a = a* in run TRI-2.

Uses the registered programs' own functions (both refused unless their SHA-256 are the registered values): the
search solve_all of numerics/review/tri_checks2.py at a = a* = 1/(2 sqrt 2). For each accepted solution it prints
the position, its distance to the two predicted A5 points (theta, -theta) and (-theta, theta), cos theta = -2a*,
the residual of the two equations, the determinant of their Jacobian (central differences, step 1e-20), and the
reduced coefficients q4, q6 of the registered `reduced`. It then groups the solutions at tolerance 1e-8.
"""
import hashlib
import importlib.util
import os

HERE = os.path.dirname(os.path.abspath(__file__))
SECOND = os.path.join(HERE, 'tri_checks2.py')
if hashlib.sha256(open(SECOND, 'rb').read()).hexdigest() != \
        '4953f187d6aa17e871420bb10fdaf3f6e5da3878f159b539a29722f6b62126f1':
    raise SystemExit('tri_checks2.py is not the registered program')
spec = importlib.util.spec_from_file_location('tri_checks2', SECOND)
t2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(t2)
tri, mp = t2.tri, t2.mp


def dist(p, q):
    return abs(mp.sin((p[0] - q[0]) / 2)) + abs(mp.sin((p[1] - q[1]) / 2))


def jacdet(a, x, y):
    e = mp.mpf('1e-20')
    fx = [(u - v) / (2 * e) for u, v in zip(tri.equations(a, x + e, y), tri.equations(a, x - e, y))]
    fy = [(u - v) / (2 * e) for u, v in zip(tri.equations(a, x, y + e), tri.equations(a, x, y - e))]
    return fx[0] * fy[1] - fx[1] * fy[0]


def main():
    a = tri.ASTAR
    th = mp.acos(-2 * a)
    targets = [(th, -th), (-th, th)]
    sols = t2.solve_all(a)
    print('a* =', mp.nstr(a, 20), ' solutions accepted:', len(sols))
    groups = []
    for (x, y) in sols:
        q, _ = t2.reduced(a, x, y)
        d = [dist((x, y), p) for p in targets]
        res = max(abs(r) for r in tri.equations(a, x, y))
        print('x=%s y=%s d(th,-th)=%s d(-th,th)=%s residual=%s jacdet=%s q4=%s q6=%s' % (
            mp.nstr(x, 22), mp.nstr(y, 22), mp.nstr(d[0], 4), mp.nstr(d[1], 4), mp.nstr(res, 3),
            mp.nstr(jacdet(a, x, y), 4), mp.nstr(q[4], 4), mp.nstr(q[6], 15)))
        for g in groups:
            if dist(g[0], (x, y)) < mp.mpf('1e-8'):
                g.append((x, y))
                break
        else:
            groups.append([(x, y)])
    print('groups at tolerance 1e-8:', len(groups), 'sizes:', [len(g) for g in groups])
    print('max spread within a group:', mp.nstr(max(
        (dist(p, g[0]) for g in groups for p in g), default=0), 4))


if __name__ == '__main__':
    main()
