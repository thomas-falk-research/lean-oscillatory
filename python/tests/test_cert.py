# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Tests of oscint_cert: properties on random inputs (fixed seed), adversarial certificates, and differential tests
against Arb (python-flint, a development dependency only; those tests are skipped, and say so, if it is missing).

Run from the python/ directory:  python3 -m unittest -v tests.test_cert
"""
import copy
import json
import os
import random
import unittest
from fractions import Fraction as F

from oscint_cert import cert as C
from oscint_cert import kernels, phase
from oscint_cert import rational as R

try:
    import flint
    from flint import arb
    flint.ctx.prec = 300
except ImportError:  # pragma: no cover
    flint = None

HERE = os.path.dirname(os.path.abspath(__file__))
STATEMENTS, SHA = C.load_statements(os.path.join(HERE, "..", "..", "stamps", "statements.json"))
RNG = random.Random(20261116)


def A(q):
    return arb(q.numerator) / arb(q.denominator)


def arb_inside(iv, x):
    """The Arb ball x lies inside the rational interval iv (certified)."""
    return bool(A(iv[0]) <= x) and bool(x <= A(iv[1]))


def rand_rational(lo, hi, den=1000):
    return F(RNG.randint(int(lo * den), int(hi * den)), den)


class Rational(unittest.TestCase):
    def test_parse_accepts_exact_forms(self):
        self.assertEqual(R.parse_rational("7/2"), F(7, 2))
        self.assertEqual(R.parse_rational("-0.125"), F(-1, 8))
        self.assertEqual(R.parse_rational(3), F(3))

    def test_parse_rejects_inexact_or_hostile(self):
        for bad in ["nan", "NaN", "inf", "-Infinity", "1e5", "0x10", "", " ", "1/0", "1/2/3", "1.5/2", "²", "1_000",
                    1.5, float("nan"), float("inf"), True, None, [1], {"x": 1}, "9" * 5000]:
            with self.assertRaises((ValueError, ZeroDivisionError), msg=repr(bad)):
                R.parse_rational(bad)

    def test_roots_bracket(self):
        for _ in range(300):
            q = rand_rational(0, 10**RNG.randint(0, 12), 10**RNG.randint(0, 9))
            k = RNG.choice([2, 3, 4, 7])
            lo, hi = R.root(R.iv(q), k, 25)
            self.assertLessEqual(lo**k, q)
            self.assertGreaterEqual(hi**k, q)
            self.assertLess(hi - lo, F(3, 10**25))
            lo2, hi2 = R.sqrt(R.iv(q), 25)
            self.assertTrue(lo2 * lo2 <= q <= hi2 * hi2)

    def test_pi(self):
        lo, hi = R.pi(60)
        # pi = 3.14159265358979323846264338327950288419716939937510582097494459230781640628...
        ref_lo = F("3.14159265358979323846264338327950288419716939937510582097494459")
        ref_hi = ref_lo + F(1, 10**62)
        self.assertTrue(lo <= ref_hi and ref_lo <= hi)  # the enclosure meets [ref_lo, ref_hi], which contains pi
        self.assertLess(hi - lo, F(1, 10**58))
        self.assertEqual(R.root(R.iv(1), 3, 20), (F(1), F(1)))  # exact on perfect powers
        self.assertEqual(R.sqrt(R.iv(F(9, 4)), 20), (F(3, 2), F(3, 2)))

    @unittest.skipIf(flint is None, "python-flint not installed: differential tests against Arb skipped")
    def test_pi_against_arb(self):
        for d in (10, 30, 80):
            self.assertTrue(arb_inside(R.pi(d), arb.pi()))

    def test_sincos_pythagoras_and_range(self):
        for _ in range(300):
            x = rand_rational(-64, 64, 10**RNG.randint(0, 6))
            s, c = R.sincos(x, 25)
            one = R.add(R.mul(s, s), R.mul(c, c))
            self.assertTrue(one[0] <= 1 <= one[1], x)
            self.assertLess(one[1] - one[0], F(1, 10**15), x)
        with self.assertRaises(R.Unresolved):
            R.sincos(F(65), 20)

    @unittest.skipIf(flint is None, "python-flint not installed: differential tests against Arb skipped")
    def test_sincos_against_arb(self):
        for _ in range(300):
            x = rand_rational(-64, 64, 10**RNG.randint(0, 6))
            s, c = R.sincos(x, 25)
            self.assertTrue(arb_inside(s, A(x).sin()), x)
            self.assertTrue(arb_inside(c, A(x).cos()), x)


class Kernels(unittest.TestCase):
    def test_bessel_edge_cases(self):
        self.assertEqual(kernels.bessel_j(0, F(0)), (F(1), F(1)))
        self.assertEqual(kernels.bessel_j(5, F(0)), (F(0), F(0)))
        with self.assertRaises(R.Unresolved):
            kernels.bessel_j(0, F(401))
        lo, hi = kernels.bessel_j(-3, F(-2))  # J_{-3}(-2) = J_3(2) > 0
        self.assertTrue(0 < lo <= hi)
        lo, hi = kernels.bessel_j(100000, F(1, 2), 10)  # far outside the light cone: tiny, and still an enclosure
        self.assertTrue(lo <= hi and abs(hi) < F(1, 10**100))

    def test_population_sums_to_at_most_one(self):
        for t in [F(1, 10), F(1), F(5, 2), F(7)]:
            total_hi = sum(kernels.population(n, t, 20)[1] for n in range(-80, 81))
            total_lo = sum(kernels.population(n, t, 20)[0] for n in range(-80, 81))
            self.assertLessEqual(total_lo, 1)
            self.assertGreater(total_hi, F(999999, 1000000))

    def test_envelope_dominates_population(self):
        """LS-D (machine-checked) against LS-K's kernel: the envelope enclosure is never below a population."""
        for _ in range(200):
            t = rand_rational(F(1, 100), 30, 100)
            n = RNG.randint(-70, 70)
            env = kernels.ls_d_envelope(1, t, 20)
            pop = kernels.population(n, t, 20)
            self.assertGreaterEqual(env[0] * env[0], pop[1], (n, t))

    def test_envelope_scales_and_limits(self):
        self.assertEqual(kernels.ls_d_envelope(1, F(1, 10**30)), (F(1), F(1)))
        self.assertEqual(kernels.ls_d_envelope(0, F(5)), (F(1), F(1)))
        lo, hi = kernels.ls_d_envelope(64, F(10**6), 30)
        self.assertTrue(0 < lo <= hi < F(1, 10**100))
        with self.assertRaises(ValueError):
            kernels.ls_d_envelope(1, F(0))

    @unittest.skipIf(flint is None, "python-flint not installed: differential tests against Arb skipped")
    def test_against_arb(self):
        for _ in range(250):
            n = RNG.randint(-60, 60)
            x = rand_rational(-120, 120, RNG.choice([1, 7, 1000]))
            self.assertTrue(arb_inside(kernels.bessel_j(n, x, 25), A(x).bessel_j(n)), (n, x))
        cst = 8 * (1 + arb(7).sqrt()) / 3 / (2 * arb.pi())
        self.assertTrue(arb_inside(kernels.cstar_over_two_pi(40), cst))
        for _ in range(100):
            d = RNG.randint(0, 6)
            t = rand_rational(F(1, 50), 500, 50)
            ref = cst**d * (2 * A(abs(t))) ** (arb(-d) / 3)
            e = kernels.ls_d_envelope(d, t, 25)
            ref = ref if ref < 1 else (arb(1) if ref > 1 else None)
            if ref is not None:
                self.assertTrue(arb_inside((e[0] - F(1, 10**20), e[1] + F(1, 10**20)), ref), (d, t))


def rand_phase():
    return [(rand_rational(-3, 3, 4), RNG.randint(1, 4), RNG.choice(["cos", "sin"])) for _ in range(RNG.randint(1, 3))]


class Phase(unittest.TestCase):
    COS = [(F(1), 1, "cos")]

    def test_pass_fail_unresolved_on_cosine(self):
        # |cos''| = |cos| >= cos(1/2) = 0.8775825... on [-1/2, 1/2]
        self.assertEqual(phase.check_lower_bound(self.COS, 2, F(-1, 2), F(1, 2), F(4, 5))[0], "PASS")
        st, det = phase.check_lower_bound(self.COS, 2, F(-1, 2), F(1, 2), F(9, 10))
        self.assertEqual(st, "FAIL")
        self.assertTrue(F(-1, 2) <= R.parse_rational(det["point"]) <= F(1, 2))
        # the third derivative sin vanishes at 0: any positive mu fails there
        self.assertEqual(phase.check_lower_bound(self.COS, 3, F(-1, 2), F(1, 2), F(1, 1000))[0], "FAIL")

    def test_near_degenerate_never_passes_falsely(self):
        cos_half = F("0.87758256189037271611628158260382965199164519710974")
        just_below = phase.check_lower_bound(self.COS, 2, F(-1, 2), F(1, 2), cos_half - F(1, 10**12))[0]
        just_above = phase.check_lower_bound(self.COS, 2, F(-1, 2), F(1, 2), cos_half + F(1, 10**12))[0]
        self.assertIn(just_below, ("PASS", "UNRESOLVED"))
        self.assertIn(just_above, ("FAIL", "UNRESOLVED"))  # the minimum is at the end points only

    def test_budget_and_range(self):
        self.assertEqual(phase.check_lower_bound(self.COS, 2, F(0), F(100), F(1, 2))[0], "UNRESOLVED")
        hard = [(F(1), 1000, "cos")]
        self.assertEqual(phase.check_lower_bound(hard, 2, F(0), F(1, 100), F(1), max_pieces=8)[0] in
                         ("UNRESOLVED", "FAIL", "PASS"), True)
        with self.assertRaises(ValueError):
            phase.check_lower_bound(self.COS, 2, F(1), F(0), F(1))
        with self.assertRaises(ValueError):
            phase.parse_phase([{"amp": "1", "freq": 1.5, "fn": "cos"}])
        with self.assertRaises(ValueError):
            phase.parse_phase([{"amp": "1", "freq": 1, "fn": "tan"}])

    @unittest.skipIf(flint is None, "python-flint not installed: differential tests against Arb skipped")
    def test_verdicts_against_arb_sampling(self):
        """PASS is never contradicted by a sampled point; FAIL always exhibits a certified violation."""
        counts = {"PASS": 0, "FAIL": 0, "UNRESOLVED": 0}
        for _ in range(150):
            terms = rand_phase()
            order = RNG.randint(2, 4)
            a = rand_rational(-3, 2, 10)
            b = a + rand_rational(0, 1, 10)
            mu = rand_rational(F(1, 100), 3, 100)
            st, det = phase.check_lower_bound(terms, order, a, b, mu, max_pieces=512)
            counts[st] += 1
            d = phase.derivative(terms, order)

            def val(x):
                return sum((A(am) * ((f * A(x)).cos() if fn == "cos" else (f * A(x)).sin()) for am, f, fn in d), arb(0))

            if st == "PASS":
                for i in range(201):
                    x = a + (b - a) * F(i, 200)
                    self.assertFalse(bool(abs(val(x)) < A(mu)), (terms, order, a, b, mu, x))
            elif st == "FAIL":
                x = R.parse_rational(det["point"])
                self.assertTrue(a <= x <= b)
                self.assertTrue(bool(abs(val(x)) < A(mu)))
        self.assertGreater(counts["PASS"], 5)
        self.assertGreater(counts["FAIL"], 5)


EXAMPLES = [
    ("bessel-j", {"n": 3, "x": "4.64"}),
    ("lattice-population", {"n": 1, "t": "1"}),
    ("lattice-envelope", {"d": 1, "t": "2"}),
    ("vdc-hypothesis", {"phase": [{"amp": "1", "freq": 1, "fn": "cos"}], "order": 2, "a": "-1/2", "b": "1/2",
                        "mu": "4/5", "t": "100"}),
]


class Certificates(unittest.TestCase):
    def setUp(self):
        self.certs = [C.make(k, i, STATEMENTS, 15) for k, i in EXAMPLES]

    def status(self, c, statements=None):
        return C.check(c, statements or STATEMENTS, SHA)["status"]

    def test_honest_certificates_are_certified(self):
        for c in self.certs:
            v = C.check(json.loads(json.dumps(c)), STATEMENTS, SHA)
            self.assertEqual(v["status"], "CERTIFIED", v)
            self.assertEqual(v["statements_sha256"], SHA)

    def test_shifted_claim_is_rejected_and_narrowed_claim_is_not_certified(self):
        for c in self.certs:
            box = c["claim"]["bound"] if c["kind"] == "vdc-hypothesis" else c["claim"]
            lo, hi = F(box["lo"]), F(box["hi"])
            w = max(hi - lo, F(1, 10**40))
            c1 = copy.deepcopy(c)
            b1 = c1["claim"]["bound"] if c["kind"] == "vdc-hypothesis" else c1["claim"]
            b1["lo"], b1["hi"] = R.fmt(lo + 5 * w), R.fmt(hi + 5 * w)
            self.assertEqual(self.status(c1), "REJECTED", c["kind"])
            c2 = copy.deepcopy(c)
            b2 = c2["claim"]["bound"] if c["kind"] == "vdc-hypothesis" else c2["claim"]
            mid = (lo + hi) / 2
            b2["lo"], b2["hi"] = R.fmt(mid), R.fmt(mid)  # a point claim: the truth is irrational or not exactly mid
            self.assertNotEqual(self.status(c2), "CERTIFIED", c["kind"])

    def test_statement_tampering(self):
        for c in self.certs:
            if c["statement"] is None:
                c1 = copy.deepcopy(c)
                c1["statement"] = {"label": "LS-D", "name": "x", "commitment": "y"}
                self.assertEqual(self.status(c1), "REJECTED")
                continue
            for key, val in [("commitment", "0" * 64), ("name", "OscInt.Statements.Other"), ("label", "S1.1")]:
                c1 = copy.deepcopy(c)
                c1["statement"][key] = val
                self.assertEqual(self.status(c1), "REJECTED", (c["kind"], key))
            unproved = copy.deepcopy(STATEMENTS)
            unproved[c["statement"]["label"]]["proved_by"] = None
            self.assertEqual(self.status(c, unproved), "UNRESOLVED", c["kind"])

    def test_structure_tampering_never_certifies(self):
        for c in self.certs:
            mutants = []
            for key in list(c):
                m = copy.deepcopy(c)
                del m[key]
                mutants.append(m)
            m = copy.deepcopy(c); m["extra"] = 1; mutants.append(m)
            m = copy.deepcopy(c); m["format"] = "oscint-certificate/9.9"; mutants.append(m)
            m = copy.deepcopy(c); m["assumptions"] = []; mutants.append(m) if c["assumptions"] else None
            m = copy.deepcopy(c); m["assumptions"] = c["assumptions"] + ["bessel-identification"]; mutants.append(m)
            m = copy.deepcopy(c); m["kind"] = "bessel-j" if c["kind"] != "bessel-j" else "lattice-envelope"; mutants.append(m)
            m = copy.deepcopy(c); m["inputs"] = dict(c["inputs"], extra="1"); mutants.append(m)
            for bad in [float("nan"), float("inf"), 1.5, "nan", "1e3", None, True, [], {}]:
                m = copy.deepcopy(c)
                k0 = sorted(m["inputs"])[-1]
                m["inputs"][k0] = bad
                mutants.append(m)
                m = copy.deepcopy(c)
                box = m["claim"]["bound"] if c["kind"] == "vdc-hypothesis" else m["claim"]
                box["lo"] = bad
                mutants.append(m)
            for m in mutants:
                self.assertNotEqual(self.status(m), "CERTIFIED", json.dumps(m, default=str)[:200])
        for junk in [None, 3, "x", [], [self.certs[0]]]:
            self.assertEqual(self.status(junk), "REJECTED")

    def test_false_hypothesis_is_rejected(self):
        c = copy.deepcopy(self.certs[3])
        c["inputs"]["mu"] = "9/10"  # |cos| dips to 0.8776 on the interval
        self.assertEqual(self.status(c), "REJECTED")
        c = copy.deepcopy(self.certs[3])
        c["inputs"]["b"] = "100"
        self.assertEqual(self.status(c), "UNRESOLVED")
        with self.assertRaises(C.CertError):
            C.make("vdc-hypothesis", dict(EXAMPLES[3][1], mu="9/10"), STATEMENTS)

    def test_out_of_range_inputs_are_unresolved_not_wrong(self):
        c = copy.deepcopy(self.certs[0])
        c["inputs"]["x"] = "401"
        self.assertEqual(self.status(c), "UNRESOLVED")
        c = copy.deepcopy(self.certs[2])
        c["inputs"]["t"] = "0"
        self.assertEqual(self.status(c), "REJECTED")


if __name__ == "__main__":
    unittest.main()
