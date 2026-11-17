# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
# SPDX-License-Identifier: Apache-2.0
"""Numerical falsification attempts for the blueprint propositions of batch VC2 (`Blueprint/SecondDerivSharp.lean`):
double precision, composite Gauss-Legendre quadrature (64 nodes per panel; panels of length at most 1/16 on which the
phase advances by at most 1/2; cut at the kink of the kinked family; right ends shortened until the total phase is at
most 400).  Evidence, not proof.  Each test family is a phase f on [c, d] with f' > 0 on
(c, d) and f'(y) - f'(x) >= lam (y - x); the families break the symmetry of the extremal quadratic."""
import math, sys
import numpy as np

rng = np.random.default_rng(20261117)
GX, GW = np.polynomial.legendre.leggauss(64)

def integral(g, c, d, cuts=(), speed=None):
    """`speed`: an increasing bound for the phase speed; panels are then cut so that the phase advances by at most
    1/2 per panel (the first version of this script used panels of fixed length and read quadrature garbage at
    phase speeds of 1e9 as a violation)."""
    if d <= c:
        return 0.0
    pts = sorted({c, d, *[x for x in cuts if c < x < d]})
    total = 0.0
    for p, q in zip(pts[:-1], pts[1:]):
        if speed is None:
            e = np.linspace(p, q, max(1, int(math.ceil((q - p) * 16))) + 1)
        else:
            e = [p]
            while e[-1] < q:
                h = min(1 / 16, q - e[-1])
                while float(speed(np.float64(e[-1] + h))) * h > 0.5:
                    h /= 2
                e.append(min(q, e[-1] + h))
            e = np.array(e)
        h = (e[1:] - e[:-1]) / 2
        m = (e[1:] + e[:-1]) / 2
        x = m[:, None] + h[:, None] * GX[None, :]
        total += float(np.sum(h[:, None] * GW[None, :] * g(x)))
    return total

def A(w):
    return 2 * integral(lambda u: np.sin(w - u * u / 2), 0.0, math.sqrt(2 * w))

def families(lam):
    """(name, f, f', cuts): f(0) = 0, f'(0) >= 0, rate >= lam on [0, inf)."""
    out = []
    for s0 in (0.0, 0.01, 0.3, 2.0):
        out.append((f"quadratic, initial speed {s0}", lambda x, s0=s0: s0 * x + lam * x * x / 2,
                    lambda x, s0=s0: s0 + lam * x, ()))
    for k in (0.5, 3.0):
        out.append((f"quadratic + exponential, k={k}", lambda x, k=k: lam * x * x / 2 + np.exp(k * x) / k - x - 1 / k,
                    lambda x, k=k: lam * x + np.exp(k * x) - 1, ()))
    for q in (0.2, 5.0):
        out.append((f"quadratic + cubic, q={q}", lambda x, q=q: lam * x * x / 2 + q * x ** 3 / 3,
                    lambda x, q=q: lam * x + q * x * x, ()))
    for j, e in ((1.0, 0.7), (4.0, 0.2), (40.0, 1.3)):
        out.append((f"kink: rate jumps by {j} at {e}",
                    lambda x, j=j, e=e: lam * x * x / 2 + j * np.maximum(x - e, 0.0) ** 2 / 2,
                    lambda x, j=j, e=e: lam * x + j * np.maximum(x - e, 0.0), (e,)))
    return out

names = ("root", "head", "tail", "oneside")
worst = {k: (-math.inf, "") for k in names}
count = {k: 0 for k in names}
def note(k, v, where):
    count[k] += 1
    if v > worst[k][0]:
        worst[k] = (v, where)

for lam in (1.0, 0.25, 7.0):
    r = math.sqrt(lam)
    for name, f, fp, cuts in families(lam):
        for c in (0.0, 0.15 / r, 0.9 / r):              # the side [c, d]: every sub-interval is again a side
            fc = float(f(np.float64(c)))
            F = lambda x: f(x) - fc
            ds = []
            for t in (0.05, 0.4, 1.0, 1.7, 2.3, 2.9, 3.6, 4.4, 5.5, 7.0):
                d = c + t / r
                while float(F(np.float64(d))) > 400.0:      # keep the total phase below 400
                    d = c + (d - c) * 0.9
                ds.append(d)
            for d in ds:
                tag = f"lam={lam}, {name}, c={c:.3f}, d={d:.3f}"
                note("root", 2 * lam * float(F(np.float64(d))) - float(fp(np.float64(d))) ** 2, tag)
                Fd = float(F(np.float64(d)))
                for w in (Fd, Fd + 0.3, Fd + 1.0, math.pi):
                    if Fd <= w <= math.pi:
                        note("head", integral(lambda x: np.sin(w - F(x)), c, d, cuts, fp) - A(w) / (2 * r), tag + f", w={w:.3f}")
                alpha = fc - math.pi / 2                  # sin(f c - alpha) = 1
                note("tail", integral(lambda x: np.cos(f(x) - alpha), c, d, cuts, fp), tag)
                for theta in list(rng.uniform(-10, 10, 6)) + [math.pi / 2, -math.pi / 2, -3 * math.pi / 2, 0.0, 1e-9 - math.pi / 2]:
                    n = math.ceil((theta - math.pi / 2) / (2 * math.pi))
                    tp = theta - 2 * math.pi * n          # in (-3 pi/2, pi/2]
                    w = tp + math.pi / 2 if tp > -math.pi / 2 else math.pi
                    note("oneside", integral(lambda x: np.cos(F(x) - theta), c, d, cuts, fp) - A(w) / (2 * r),
                         tag + f", theta={theta:.4f}, w={w:.4f}")
ok = True
for k in names:
    good = worst[k][0] <= 1e-9
    ok = ok and good
    print(f"{k}: {count[k]} cases, largest (lhs - rhs) = {worst[k][0]:.3e} at [{worst[k][1]}]  {'PASS' if good else 'FAIL'}")
w = 2.0
lhs = integral(lambda x: np.cos(x * x / 2 - (w - math.pi / 2)), 0.0, math.sqrt(2 * w))
good = abs(lhs - A(w) / 2) < 1e-12
ok = ok and good
print(f"oneside attained by the quadratic from rest (lam = 1, w = 2, d = 2): lhs - A(w)/2 = {lhs - A(w) / 2:.3e}  {'PASS' if good else 'FAIL'}")
amax = max(A(x) for x in np.linspace(0, math.pi, 3142))
print(f"max of A on a grid of step 0.001 over [0, pi]: {amax:.9f}  {'PASS' if amax <= 3.5 else 'FAIL'}")
sys.exit(0 if ok else 1)
