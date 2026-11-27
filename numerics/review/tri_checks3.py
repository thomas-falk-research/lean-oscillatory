#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Third registered numeric test of batch TRI (docs/prereg/2026-11-27-TRI-3.md).

Runs the first registered program's criteria and functions with the second registered program's two changes
(numerics/review/tri_checks2.py; both programs refused unless their SHA-256 are the registered values), and one
further change: in the search, two accepted solutions are the same solution when their distance
|sin((x - x')/2)| + |sin((y - y')/2)| is below 1e-8 (it was 1e-15). Added criterion D: for every a, every merged
solution lies within 1e-12 of the solution it was merged into, and distinct solutions are at distance at least 1e-3.
Overall PASS iff the first program's OVERALL line is PASS and D is PASS.
"""
import hashlib
import importlib.util
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SECOND = os.path.join(HERE, 'tri_checks2.py')
REGISTERED2 = '4953f187d6aa17e871420bb10fdaf3f6e5da3878f159b539a29722f6b62126f1'
if hashlib.sha256(open(SECOND, 'rb').read()).hexdigest() != REGISTERED2:
    raise SystemExit('tri_checks2.py is not the registered program')
spec = importlib.util.spec_from_file_location('tri_checks2', SECOND)
t2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(t2)
tri, mp = t2.tri, t2.mp
MERGE = mp.mpf('1e-8')
RECORD = []


def dist(p, q):
    return abs(mp.sin((p[0] - q[0]) / 2)) + abs(mp.sin((p[1] - q[1]) / 2))


def solve_all(a, grid=24):
    sols = []
    merged = mp.mpf(0)
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
        near = [dist((x, y), p) for p in sols if dist((x, y), p) < MERGE]
        if near:
            merged = max(merged, min(near))
        else:
            sols.append((x, y))
    sep = min((dist(p, q) for p, q in itertools.combinations(sols, 2)), default=mp.inf)
    RECORD.append((a, len(sols), merged, sep))
    return sols


class Tee:
    def __init__(self, out):
        self.out, self.text = out, []

    def write(self, s):
        self.text.append(s)
        return self.out.write(s)

    def flush(self):
        self.out.flush()


def main():
    print('second program SHA-256 verified:', REGISTERED2)
    tee = Tee(sys.stdout)
    sys.stdout = tee
    try:
        t2.tri.main()
    finally:
        sys.stdout = tee.out
    first_ok = 'OVERALL: PASS' in ''.join(tee.text)
    d_ok = True
    for a, n, merged, sep in RECORD:
        good = merged <= mp.mpf('1e-12') and sep >= mp.mpf('1e-3')
        d_ok &= good
        print('D a=%s solutions=%d max-merge-distance=%s min-separation=%s -> %s' % (
            mp.nstr(a, 10), n, mp.nstr(merged, 3), mp.nstr(sep, 4), 'PASS' if good else 'FAIL'))
    print('OVERALL (TRI-3):', 'PASS' if first_ok and d_ok else 'FAIL')


tri.solve_all = solve_all
if __name__ == '__main__':
    main()
