#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Registered numeric test of batch TRI (docs/prereg/2026-11-27-TRI.md).

Phase Psi_a(x, y) = cos x + cos y + a cos(x + y). Everything is computed in the original coordinates (x, y), from the
phase, by mpmath at 50 digits; nothing here uses the (s, v) algebra of the proof route.

T1  For each a in the registered list: solve det H = 0 and D^3 Psi[v, v, v] = 0 (v the unit kernel vector) by Newton
    from a 24 x 24 grid of starts on the torus; deduplicate. For every solution compute the reduced coefficients q4, q6
    of the phase restricted to its transverse critical curve (series of degree 8 by interpolation at 9 points).
    PASS iff: (i) every solution with a != +-a* has |q4| > 1e-8; (ii) for a = +-a*, exactly two solutions have
    |q4| < 1e-12, both at (theta, -theta) mod 2pi with cos(theta) = -2|a| (after (pi, pi) translation for a < 0), and
    there q6 = -1/(48 sqrt 2) to 1e-10; (iii) the matching-sign points (+-pi/2, +-pi/2) are among the solutions with
    q4 = -1/(32 a) to 1e-12; (iv) for 0 < |a| <= 1/2 the anti-diagonal point has q4 = (8a^2 - 1)/(32 a) to 1e-12.
    Signed formulas: Psi_{-a}(k + (pi, pi)) = -Psi_a(k) negates every reduced coefficient, so q6 = -sign(a)/(48 sqrt 2).
T2  Decay at a* along the anti-diagonal, by the exact Bessel series (Jacobi-Anger) with truncation |m| <= M, the tail
    bounded by |J_m(z)| <= exp(|z| sinh(eta) - |m| eta) for every eta > 0 (and |J_j(t)| <= 1 for the other factors):
    r(t) = t^(2/3) max over every n1 with |n1| <= t, n2 = -n1, of |K|.
    PASS iff r(16384)/r(4096) and r(65536)/r(16384) lie in [0.97, 1.03] (a plateau: rate t^(-2/3)) and the
    truncation bound is at most 1e-12.
K1  Control: a = 0.2, the same quantity: PASS iff r(16384)/r(4096) < 0.95 (faster than t^(-2/3) along that line).
K2  Control: a = 0: the four D4 points must be found by the same solver as solutions with Hessian rank 0 (reported
    as rank 0, not as A3/A5): PASS iff exactly four rank-0 points and no other solution.
"""
import itertools
import sys

import mpmath as mp
import numpy as np
from scipy.special import jv

mp.mp.dps = 50
ASTAR = 1 / mp.sqrt(8)
ALPHAS = [mp.mpf(x) for x in ('0.05', '0.2', '0.3', '0.4', '0.5', '0.7', '1', '2', '-0.3')] + [ASTAR, -ASTAR]


def jets(a, x, y):
    """Derivatives of Psi up to order 6 at (x, y): dict (i, j) -> d^{i+j}/dx^i dy^j."""
    c = [mp.cos, lambda t: -mp.sin(t), lambda t: -mp.cos(t), mp.sin]
    out = {}
    for i in range(7):
        for j in range(7 - i):
            v = 0
            if j == 0:
                v += c[i % 4](x) if i > 0 else mp.cos(x)
            if i == 0:
                v += c[j % 4](y) if j > 0 else mp.cos(y)
            v += a * (c[(i + j) % 4](x + y) if i + j > 0 else mp.cos(x + y))
            out[(i, j)] = v
    return out


def dmul(J, n, vecs):
    """Symmetric n-linear form of the jets on the given vectors."""
    tot = 0
    for idx in itertools.product(range(2), repeat=n):
        p = 1
        for k, b in enumerate(idx):
            p *= vecs[k][b]
        tot += J[(idx.count(0), idx.count(1))] * p
    return tot


def kernel(J):
    h11, h12, h22 = J[(2, 0)], J[(1, 1)], J[(0, 2)]
    v = (h22, -h12) if abs(h22) + abs(h12) > abs(h11) else (-h12, h11)
    n = mp.sqrt(v[0] ** 2 + v[1] ** 2)
    return (v[0] / n, v[1] / n)


def equations(a, x, y):
    J = jets(a, x, y)
    det = J[(2, 0)] * J[(0, 2)] - J[(1, 1)] ** 2
    v = kernel(J)
    return [det, dmul(J, 3, [v, v, v])]


def reduced(a, x0, y0):
    """q2..q8 of g(u) = f(u e + h(u) w), f = Psi - grad.(.) about (x0, y0), h solving d_w f = 0."""
    J0 = jets(a, x0, y0)
    e = kernel(J0)
    w = (-e[1], e[0])
    gx, gy = J0[(1, 0)], J0[(0, 1)]

    def f(u, s):
        dx, dy = u * e[0] + s * w[0], u * e[1] + s * w[1]
        return (mp.cos(x0 + dx) + mp.cos(y0 + dy) + a * mp.cos(x0 + y0 + dx + dy)) - gx * dx - gy * dy

    def g(u):
        s = mp.findroot(lambda s: mp.diff(lambda r: f(u, r), s), 0)
        return f(u, s)

    h = mp.mpf('1e-3')
    us = [k * h for k in range(-4, 5)]
    gs = [g(u) for u in us]
    coeffs = mp.lu_solve(mp.matrix([[u ** p for p in range(9)] for u in us]), mp.matrix(gs))
    return [coeffs[p] for p in range(9)], dmul(J0, 2, [w, w])


def solve_all(a, grid=24):
    sols = []
    for i, j in itertools.product(range(grid), range(grid)):
        x0 = -mp.pi + 2 * mp.pi * (i + mp.mpf(1) / 2) / grid
        y0 = -mp.pi + 2 * mp.pi * (j + mp.mpf(1) / 2) / grid
        try:
            r = mp.findroot(lambda x, y: equations(a, x, y), (x0, y0))
        except (ZeroDivisionError, ValueError):
            continue
        x = (r[0] + mp.pi) % (2 * mp.pi) - mp.pi
        y = (r[1] + mp.pi) % (2 * mp.pi) - mp.pi
        if max(abs(q) for q in equations(a, x, y)) > mp.mpf('1e-30'):
            continue
        if not any(abs(mp.sin((x - p[0]) / 2)) + abs(mp.sin((y - p[1]) / 2)) < mp.mpf('1e-15') for p in sols):
            sols.append((x, y))
    return sols


def rank0_solutions(a, grid=16):
    pts = []
    for i, j in itertools.product(range(grid), range(grid)):
        x0 = -mp.pi + 2 * mp.pi * (i + mp.mpf(1) / 2) / grid
        y0 = -mp.pi + 2 * mp.pi * (j + mp.mpf(1) / 2) / grid
        try:
            r = mp.findroot(lambda x, y: [jets(a, x, y)[(2, 0)], jets(a, x, y)[(0, 2)]], (x0, y0))
        except (ZeroDivisionError, ValueError):
            continue
        x = (r[0] + mp.pi) % (2 * mp.pi) - mp.pi
        y = (r[1] + mp.pi) % (2 * mp.pi) - mp.pi
        J = jets(a, x, y)
        if max(abs(J[(2, 0)]), abs(J[(1, 1)]), abs(J[(0, 2)])) > mp.mpf('1e-30'):
            continue
        if not any(abs(x - p[0]) + abs(y - p[1]) < mp.mpf('1e-15') for p in pts):
            pts.append((x, y))
    return pts


def ridge(a, t):
    """t^(2/3) max over the anti-diagonal n = (n1, -n1), |n1| <= t, of |K_a(t, n)| (Bessel series, float64)."""
    z = abs(t * a)
    M = int(z + 40 + 10 * z ** (1 / 3))
    eta = mp.acosh(mp.mpf(M + 1) / z)
    tail = float(2 * mp.exp(z * mp.sinh(eta) - (M + 1) * eta) / (1 - mp.exp(-eta)))
    m = np.arange(-M, M + 1)
    ph = np.array([1, -1j, -1, 1j])[m % 4]
    w = ph * jv(m, t * a)
    T = int(t)
    off = T + M
    Jt = jv(np.arange(-off, off + 1), t)
    best = 0.0
    for n1 in range(-T, T + 1):
        val = np.dot(w, Jt[n1 + m + off] * Jt[-n1 + m + off])
        best = max(best, abs(val))
    return t ** (2 / 3) * best, tail


def main():
    print('versions: python', sys.version.split()[0], 'mpmath', mp.__version__, 'numpy', np.__version__)
    ok = True
    target6 = -1 / (48 * mp.sqrt(2))
    for a in ALPHAS:
        sols = solve_all(a)
        small = []
        line = []
        for (x, y) in sols:
            q, hww = reduced(a, x, y)
            line.append((x, y, q[4], q[6]))
            if abs(q[4]) < mp.mpf('1e-12'):
                small.append((x, y, q[6]))
        exceptional = abs(abs(a) - ASTAR) < mp.mpf('1e-40')
        good = True
        if not exceptional:
            good &= all(abs(r[2]) > mp.mpf('1e-8') for r in line)
        else:
            th = mp.acos(-2 * abs(a))
            shift = 0 if a > 0 else mp.pi
            exp_pts = [(th + shift, -th + shift), (-th + shift, th + shift)]
            good &= len(small) == 2
            for (x, y, q6) in small:
                good &= any(abs(mp.sin((x - p[0]) / 2)) + abs(mp.sin((y - p[1]) / 2)) < mp.mpf('1e-12')
                            for p in exp_pts)
                good &= abs(q6 - mp.sign(a) * target6) < mp.mpf('1e-10')
        shift = 0 if a > 0 else mp.pi
        for sx, sy in ((1, 1), (-1, -1)):
            p = (sx * mp.pi / 2 + shift, sy * mp.pi / 2 + shift)
            hit = [r for r in line if abs(mp.sin((r[0] - p[0]) / 2)) + abs(mp.sin((r[1] - p[1]) / 2)) < 1e-12]
            good &= len(hit) == 1 and abs(hit[0][2] - (-1 / (32 * a))) < mp.mpf('1e-12')
        if abs(a) <= mp.mpf(1) / 2:
            th = mp.acos(-2 * abs(a))
            p = (th + shift, -th + shift)
            hit = [r for r in line if abs(mp.sin((r[0] - p[0]) / 2)) + abs(mp.sin((r[1] - p[1]) / 2)) < 1e-12]
            good &= len(hit) == 1 and abs(hit[0][2] - (8 * a ** 2 - 1) / (32 * a)) < mp.mpf('1e-12')
        print('T1 a=%s solutions=%d min|q4|=%s small-q4=%d q6(small)=%s -> %s' % (
            mp.nstr(a, 10), len(sols), mp.nstr(min(abs(r[2]) for r in line), 5), len(small),
            [mp.nstr(s[2], 12) for s in small], 'PASS' if good else 'FAIL'))
        ok &= good
    r = {t: ridge(float(ASTAR), t) for t in (4096, 16384, 65536)}
    q1, q2 = r[16384][0] / r[4096][0], r[65536][0] / r[16384][0]
    t2 = 0.97 <= q1 <= 1.03 and 0.97 <= q2 <= 1.03 and max(v[1] for v in r.values()) <= 1e-12
    print('T2 r(4096)=%.6f r(16384)=%.6f r(65536)=%.6f ratios %.5f %.5f tail<=%.1e -> %s' % (
        r[4096][0], r[16384][0], r[65536][0], q1, q2, max(v[1] for v in r.values()), 'PASS' if t2 else 'FAIL'))
    ok &= t2
    c = {t: ridge(0.2, t) for t in (4096, 16384)}
    k1 = c[16384][0] / c[4096][0] < 0.95
    print('K1 a=0.2 r(4096)=%.6f r(16384)=%.6f ratio %.5f -> %s' % (
        c[4096][0], c[16384][0], c[16384][0] / c[4096][0], 'PASS' if k1 else 'FAIL'))
    ok &= k1
    z = rank0_solutions(mp.mpf(0))
    k2 = len(z) == 4 and all(abs(abs(p[0]) - mp.pi / 2) < 1e-20 and abs(abs(p[1]) - mp.pi / 2) < 1e-20 for p in z)
    print('K2 a=0 rank-0 points: %d -> %s' % (len(z), 'PASS' if k2 else 'FAIL'))
    ok &= k2
    print('OVERALL:', 'PASS' if ok else 'FAIL')


if __name__ == '__main__':
    main()
