#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Registered numeric test of the draft statement TSD-C (docs/prereg/2026-11-20-TSD-core.md).
Tooling, not evidence for a Lean theorem. Cases, method, criteria and controls are fixed in that file; this
program implements them and prints PASS/FAIL per criterion and an overall line.

    J     = int_R A(v) e^{i t phi(v)} dv
    lead  = 2 sqrt(2 pi/(t alpha)) Re[e^{-i pi/4} A(s) e^{i t phi(s)}]
    claim |J - lead| <= G (eps_core + 2 eps_tr + eps_mid + eps_far),  G = 2 |A(s)| sqrt(2 pi/(t alpha))

Arithmetic: IEEE-754 binary64, round to nearest, NumPy; composite Gauss-Legendre quadrature with 12 nodes per
panel, panels summed in the order of the path. No random numbers. Every quadrature is run at two panel widths and
the difference is printed as its error estimate.
"""
import datetime
import hashlib
import sys

import numpy as np

GLX, GLW = np.polynomial.legendre.leggauss(12)
E4 = np.exp(-0.25j * np.pi)


# ---------------------------------------------------------------- phases
class Airy:
    """phi(z) = sig^2 z - z^3/3; phi' = sig^2 - z^2; exact C2 = 2, C3 = 0 on every strip."""

    def __init__(self, sig):
        self.sig = sig
        self.name = f"P1(sigma={sig})"
        self.s, self.alpha, self.beta = sig, 2 * sig, sig

    def phi(self, z):
        return self.sig ** 2 * z - z ** 3 / 3

    def dphi(self, z):
        return self.sig ** 2 - z ** 2

    def bounds(self, delta):
        return 2.0, 0.0


class Root:
    """phi'(z) = x - sqrt(1 + z^2), phi(0) = 0; s = sqrt(x^2 - 1), alpha = s/x, beta = (x - 1)/s.
    On |Im z| <= delta with 2 delta^2 <= 1: |phi'''| <= (1 - delta^2)^(-3/2), |phi''''| <= 3/(1 - delta^2)^2."""

    def __init__(self, x):
        self.x = x
        self.name = f"P2(x={x})"
        self.s = float(np.sqrt(x * x - 1))
        self.alpha, self.beta = self.s / x, (x - 1) / self.s

    def phi(self, z):
        w = np.sqrt(1 + z * z)
        return self.x * z - (z * w + np.log(z + w)) / 2

    def dphi(self, z):
        return self.x - np.sqrt(1 + z * z)

    def bounds(self, delta):
        assert 2 * delta * delta <= 1
        return (1 - delta ** 2) ** -1.5, 3 / (1 - delta ** 2) ** 2


# ---------------------------------------------------------------- amplitudes
def sech(w):
    w = np.where(np.real(w) >= 0, w, -w)
    e = np.exp(-w)
    return 2 * e / (1 + e * e)


class Sech:
    """A = sech(kap z); M = kap max(1, tan(kap delta)), M' = kap^2 sec^2(kap delta); needs kap delta < pi/2."""
    line = True

    def __init__(self, kap):
        self.kap = kap
        self.name = f"A1(kappa={kap})"
        self.X = 40.0 / kap

    def A(self, z):
        return sech(self.kap * z)

    def bounds(self, delta):
        a = self.kap * delta
        assert a < np.pi / 2
        return self.kap * max(1.0, np.tan(a)), self.kap ** 2 / np.cos(a) ** 2


class LinSech:
    """A = (1 + i gam z) sech(kap z); needs |gam| delta < 1 and kap delta < pi/2."""
    line = True

    def __init__(self, gam, kap):
        self.gam, self.kap = gam, kap
        self.name = f"A2(gamma={gam},kappa={kap})"
        self.X = 48.0 / kap

    def A(self, z):
        return (1 + 1j * self.gam * z) * sech(self.kap * z)

    def bounds(self, delta):
        a, g = self.kap * delta, abs(self.gam)
        assert a < np.pi / 2 and g * delta < 1
        return (g / (1 - g * delta) + self.kap * max(1.0, np.tan(a)),
                g ** 2 / (1 - g * delta) ** 2 + self.kap ** 2 / np.cos(a) ** 2)


class Rational:
    """A = a^2/(a^2 + z^2); needs a^2 >= 3 delta^2; M = 1/sqrt(a^2 - 2 delta^2),
    M' = 2/(a^2 - delta^2) + 1/(a^2 - 2 delta^2). Decays like v^-2: no quadrature on the line."""
    line = False

    def __init__(self, a):
        self.a = a
        self.name = f"A3(a={a})"

    def A(self, z):
        return self.a ** 2 / (self.a ** 2 + z * z)

    def bounds(self, delta):
        a2, d2 = self.a ** 2, delta ** 2
        assert a2 >= 3 * d2
        return 1 / np.sqrt(a2 - 2 * d2), 2 / (a2 - d2) + 1 / (a2 - 2 * d2)


# ---------------------------------------------------------------- quadrature
def path_integral(f, zfun, dz, a, b, hfun, refine):
    """int_a^b f(z(p)) z'(p) dp, z' = dz constant; panel width hfun(p)/refine at the panel's left end."""
    edges = [a]
    p = a
    while p < b:
        p = min(b, p + hfun(p) / refine)
        edges.append(p)
    edges = np.array(edges)
    lo, hi = edges[:-1], edges[1:]
    total = 0j
    step = 20000
    for k in range(0, len(lo), step):
        l, h = lo[k:k + step, None], hi[k:k + step, None]
        nodes = (l + h) / 2 + (h - l) / 2 * GLX[None, :]
        vals = f(zfun(nodes)) * ((h - l) / 2) * GLW[None, :]
        total += vals.sum()
    return total * dz


class Case:
    def __init__(self, label, phase, amp, delta, t):
        self.label, self.ph, self.am, self.delta, self.t = label, phase, amp, delta, t
        self.s, self.alpha, self.beta = phase.s, phase.alpha, phase.beta
        self.C2, self.C3 = phase.bounds(delta)
        self.M, self.Mp = amp.bounds(delta)
        self.ell = min(np.sqrt(2) * delta, self.alpha / self.C2,
                       1.5 * np.sqrt(2) * self.beta / self.C2, 1 / self.M)
        self.u = self.ell / np.sqrt(2)
        self.r = min(self.ell, (6 / (t * self.C2)) ** (1 / 3))

    def f(self, z):
        return self.am.A(z) * np.exp(1j * self.t * self.ph.phi(z))

    def hyp(self):
        """the inequalities of hypotheses (6) and (7); (1)-(5) hold by construction of the families."""
        t, ell, u = self.t, self.ell, self.u
        return {"ell<=sqrt2 delta": ell <= np.sqrt(2) * self.delta * (1 + 1e-15),
                "C2 ell<=alpha": self.C2 * ell <= self.alpha * (1 + 1e-15),
                "C2 ell<=(3 sqrt2/2) beta": self.C2 * ell <= 1.5 * np.sqrt(2) * self.beta * (1 + 1e-15),
                "M ell<=1": self.M * ell <= 1 + 1e-15,
                "r<=ell": self.r <= ell,
                "t C2 r^3<=6": t * self.C2 * self.r ** 3 <= 6 * (1 + 1e-12),
                "2M<=t beta u": 2 * self.M <= t * self.beta * u * (1 + 1e-12),
                "t alpha>=8": t * self.alpha >= 8 * (1 - 1e-12)}

    def eps(self):
        t, al, be, C2, C3, M, Mp = self.t, self.alpha, self.beta, self.C2, self.C3, self.M, self.Mp
        ell, u, r = self.ell, self.u, self.r
        K = (np.e - 2) * (M * M + Mp)
        core = K / (t * al) + (C3 / 8 + M * C2 / 2 + K * C2) / (t * al ** 2) \
            + (0.57 + 0.52 * M) * C2 ** 2 / (t * al ** 3)
        tr = 3 * np.exp(M * ell) * np.exp(-t * al * r * r / 3) / (np.sqrt(2 * np.pi) * r * np.sqrt(t * al))
        mid = 2 * np.exp(M * u) * np.sqrt(al / (2 * np.pi * t)) * np.exp(-t * be * u * u / 4) / (be * u)
        far = np.sqrt(2 / np.pi) * np.exp(M * u) * np.exp(-t * al * u * u / 4) / (u * np.sqrt(t * al))
        return core, tr, mid, far

    def G(self):
        return 2 * abs(self.am.A(self.s + 0j)) * np.sqrt(2 * np.pi / (self.t * self.alpha))

    def lead(self, quarter=E4, alpha=None):
        al = self.alpha if alpha is None else alpha
        z = quarter * self.am.A(self.s + 0j) * np.exp(1j * self.t * self.ph.phi(self.s + 0j))
        return 2 * np.sqrt(2 * np.pi / (self.t * al)) * z.real

    def h(self, zfun):
        return lambda p: min(0.02, 1.0 / (self.t * abs(self.ph.dphi(zfun(p))) + 1.0))

    def J_line(self, refine):
        """R1: the whole real line, truncated at |v| = X; returns the complex value."""
        X = self.am.X
        zf = lambda p: p + 0j
        return path_integral(self.f, zf, 1.0, -X, X, self.h(zf), refine)

    def J_contour(self, ell, refine):
        """R2/R3: 2 Re of the right half of the five-piece contour with window ell (height ell/sqrt 2)."""
        u, s = ell / np.sqrt(2), self.s
        Xf = s + u + 40.0 / (self.t * self.alpha * u)
        z1 = lambda p: p + 1j * u
        z2 = lambda p: s + p * E4
        z3 = lambda p: p - 1j * u
        Jp = path_integral(self.f, z1, 1.0, 0.0, s - u, self.h(z1), refine) \
            + path_integral(self.f, z2, E4, -ell, ell, self.h(z2), refine) \
            + path_integral(self.f, z3, 1.0, s + u, Xf, self.h(z3), refine)
        return 2 * Jp.real


CASES = [
    Case("C1", Airy(1.0), Sech(1.0), 0.5, 60.0),
    Case("C2", Airy(0.5), Sech(1.0), 0.5, 200.0),
    Case("C3", Airy(2.0), LinSech(0.5, 1.5), 0.4, 40.0),
    Case("C4", Root(1.5), Sech(2.0), 0.5, 1200.0),
    Case("C5", Root(1.1), LinSech(-0.8, 1.0), 0.3, 2000.0),
    Case("C6", Airy(1.0), Rational(1.5), 0.5, 80.0),
    Case("C7", Root(3.0), Rational(1.0), 0.4, 400.0),
    Case("C8", Airy(1.0), Sech(1.0), 0.5, 4.0),
    Case("C9", Airy(1.0), Sech(20.0), 0.05, 20000.0),
]
# informational only: hypothesis (7) fails; no criterion depends on it
INFO = Case("I1", Airy(1.0), Sech(30.0), 0.04, 450.0)


def main():
    src = open(__file__, "rb").read()
    print("tsd_core_checks.py sha256", hashlib.sha256(src).hexdigest())
    print("run", datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
          "python", sys.version.split()[0], "numpy", np.__version__)
    ok = {"h": True, "a": True, "q": True, "im": True}
    k1 = k2 = 0
    for c in CASES:
        hy = c.hyp()
        bad = [k for k, v in hy.items() if not v]
        ok["h"] &= not bad
        core, tr, mid, far = c.eps()
        tot = core + 2 * tr + mid + far
        G = c.G()
        J2, J2h = c.J_contour(c.ell, 1), c.J_contour(c.ell, 2)
        J3, J3h = c.J_contour(c.ell / 2, 1), c.J_contour(c.ell / 2, 2)
        qerr = max(abs(J2 - J2h), abs(J3 - J3h), abs(J2h - J3h)) / G
        im = 0.0
        if c.am.line:
            J1, J1h = c.J_line(1), c.J_line(2)
            qerr = max(qerr, abs(J1 - J1h) / G, abs(J1h.real - J2h) / G)
            im = abs(J1h.imag) / G
        E = abs(J2h - c.lead()) / G
        Ek1 = abs(J2h - c.lead(quarter=np.conj(E4))) / G
        Ek2 = abs(J2h - c.lead(alpha=c.alpha / 2)) / G
        a_ok, q_ok, im_ok = E <= tot + 1e-9, qerr < 1e-8, im < 1e-8
        ok["a"] &= a_ok
        ok["q"] &= q_ok
        ok["im"] &= im_ok
        k1 += Ek1 > tot
        k2 += Ek2 > tot
        print(f"{c.label} {c.ph.name} {c.am.name} delta={c.delta} t={c.t}: s={c.s:.6g} alpha={c.alpha:.6g} "
              f"beta={c.beta:.6g} C2={c.C2:.6g} C3={c.C3:.6g} M={c.M:.6g} M'={c.Mp:.6g} ell={c.ell:.6g} "
              f"u={c.u:.6g} r={c.r:.6g}")
        print(f"   hypotheses (6),(7): {'all hold' if not bad else 'FAIL ' + ', '.join(bad)}")
        print(f"   J={J2h:.12e} lead={c.lead():.12e} G={G:.6e}")
        print(f"   eps: core={core:.4e} tr={tr:.4e} mid={mid:.4e} far={far:.4e} total={tot:.4e}")
        print(f"   measured E=|J-lead|/G={E:.4e} bound/measured={tot / E if E > 0 else float('inf'):.4g} "
              f"(a) {'PASS' if a_ok else 'FAIL'}")
        print(f"   quadrature: max disagreement/G={qerr:.2e} (q) {'PASS' if q_ok else 'FAIL'}; "
              f"|Im J|/G={im:.2e} (im) {'PASS' if im_ok else 'FAIL'}"
              + ("" if c.am.line else " [no line route for this amplitude]"))
        print(f"   controls: wrong quarter phase E={Ek1:.4e} ({'exceeds' if Ek1 > tot else 'within'} the bound); "
              f"alpha halved E={Ek2:.4e} ({'exceeds' if Ek2 > tot else 'within'} the bound)")
    c = INFO
    core, tr, mid, far = c.eps()
    tot = core + 2 * tr + mid + far
    J = c.J_contour(c.ell, 2)
    E = abs(J - c.lead()) / c.G()
    bad = [k for k, v in c.hyp().items() if not v]
    print(f"I1 (informational, no criterion) {c.ph.name} {c.am.name} delta={c.delta} t={c.t}: "
          f"failing hypotheses: {', '.join(bad) if bad else 'none'}; M={c.M:.6g} ell={c.ell:.6g}; "
          f"formula total={tot:.4e} measured E={E:.4e}")
    n = len(CASES)
    lines = [("(h) the inequalities of hypotheses (6) and (7) hold in all cases", ok["h"]),
             ("(a) |J - lead| <= G * total in all cases", ok["a"]),
             ("(q) quadrature routes and refinements agree within 1e-8 G", ok["q"]),
             ("(im) |Im J| < 1e-8 G where the line route exists", ok["im"]),
             (f"K1 wrong quarter phase exceeds the bound in {k1} of {n} cases (required: at least 4)", k1 >= 4),
             (f"K2 halved alpha exceeds the bound in {k2} of {n} cases (required: at least 4)", k2 >= 4)]
    for text, good in lines:
        print(("PASS " if good else "FAIL ") + text)
    allok = all(g for _, g in lines)
    print("OVERALL:", "PASS" if allok else "FAIL", f"({sum(g for _, g in lines)} of {len(lines)} lines PASS)")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
