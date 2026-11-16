# The certificate contract, version 0.1 (experimental)

One language-neutral contract between everything that produces an evaluated OscInt result and the one program that
may call it CERTIFIED. Version 0.1 is experimental: it is versioned from the start, and it is frozen as version 1
only after consumers from two different domains have used it (`docs/ROADMAP.md`, item I5). The statement index it
refers to is `stamps/statements.json` (format `oscint-statements 1`); the reference implementation is the Python
package under `python/oscint_cert/` (standard library only).

## 1. Trust boundary

- **Only the checker confers CERTIFIED.** A producer, a wrapper in another language, a notebook or a web page
  transports and displays certificates and verdicts; none of them may assign the status.
- **The checker trusts nothing in a certificate.** It recomputes every number, looks the statement up in the
  statement list it was given, and derives the list of assumptions from the certificate's kind.
- **No floating point.** All arithmetic in the checker is exact rational interval arithmetic. A result that cannot
  be decided within the budget is UNRESOLVED; it is never rounded into a verdict.
- **What CERTIFIED means, and no more:** (a) the statement named is in the statement list, with the same name and
  commitment, and has a machine-checked proof there (`proved_by` is set); (b) the claimed enclosure contains the
  checker's own enclosure of the quantity; (c) the assumptions listed in the verdict are the only steps not covered
  by (a) and (b). The verdict prints the rung of each part: the statement at L4 (machine-checked; statement fidelity
  reviewed by AI referees, not yet by a human expert), the arithmetic at L2, each assumption with its own rung.
- **What it does not mean:** that the statement is the right model of a device (every lattice statement is about an
  infinite lattice); that the checker's code is verified (it is tested, section 6; it is not proved correct:
  ASSUMED(L4, a proof of the checker's arithmetic in Lean is not planned yet, lead)).

## 2. Numbers

Every number is a JSON string holding an exact rational: `"p/q"` with integers p and q ≠ 0, an integer such as
`"-3"`, or a finite decimal such as `"0.25"`. Integers that index things (a site, a dimension, an order, a
frequency) are JSON integers. JSON floats, exponents, `NaN` and `Infinity` are rejected. An enclosure is an object
`{"lo": …, "hi": …}` with lo ≤ hi, meaning the closed interval.

## 3. Certificate

A JSON object with exactly these keys:

| Key | Content |
|---|---|
| `format` | `"oscint-certificate/0.1"` |
| `kind` | one of the kinds of section 4 |
| `statement` | `null`, or `{"label", "name", "commitment"}` copied from the statement list |
| `inputs` | the kind's inputs, exactly the keys listed in section 4 |
| `claim` | the kind's claim |
| `assumptions` | the list of assumption keys fixed for the kind, in order |
| `producer` | a free string naming what made the certificate; ignored by the checker |

## 4. Kinds

| Kind | Statement | Inputs | Quantity enclosed by the claim | Assumptions |
|---|---|---|---|---|
| `bessel-j` | none | `n` integer, `x` rational, \|x\| ≤ 400 | `J_n(x)` | none |
| `lattice-population` | LS-K | `n` integer, `t` rational | `J_n(2t)²`: the probability at site n at time t for the lattice Schrödinger group on ℤ started at site 0 | `bessel-identification`, `single-site-datum` |
| `lattice-envelope` | LS-D | `d` integer in 0…64, `t` rational, t ≠ 0 | `min{1, (C*/2π)^d (2\|t\|)^{−d/3}}`, `C* = 8(1 + √7)/3` | `unit-l1-datum` |
| `vdc-hypothesis` | S1.k | `phase`, `order` integer k in 2…16, `a`, `b`, `mu`, `t` rationals with a ≤ b, mu > 0, t > 0 | claim `{"holds": true, "bound": enclosure}`: `\|ω^{(k)}\| ≥ mu` on [a, b], and the bound `(5·2^{k−1} − 2)(t·mu)^{−1/k}` | `amplitude-one` |

A `phase` is a list of 1 to 64 terms `{"amp": rational, "freq": integer with |freq| ≤ 1000, "fn": "cos" or "sin"}`,
meaning `ω(k) = Σ amp · fn(freq · k)`. For `vdc-hypothesis` the frequency times either end of the interval must not
exceed 64 in modulus; beyond that the checker answers UNRESOLVED.

Assumption keys and their meaning (the text is the checker's, never the certificate's):

| Key | Meaning | Rung |
|---|---|---|
| `bessel-identification` | `I(t, n) = 2π iⁿ J_n(t)` for the lattice kernel of the statements (DLMF 10.9.2) | L3 on paper, validated at L2 (`numerics/results-unlock-chain-checks-2026-11-16.txt`, check K2); not machine-checked |
| `single-site-datum` | the initial datum is the unit vector at site 0 of the infinite lattice ℤ | a modelling assumption |
| `unit-l1-datum` | the bound is for a datum of ℓ¹ norm 1 on the infinite lattice ℤ^d; a device is finite | a modelling assumption |
| `amplitude-one` | the bound is for the amplitude 1 on [a, b] and the phase `tω(k) + ξk`, for every real ξ | a modelling assumption |

## 5. Verdict

The checker prints a JSON object:

| Key | Content |
|---|---|
| `format` | `"oscint-verdict/0.1"` |
| `status` | `"CERTIFIED"`, `"REJECTED"` or `"UNRESOLVED"` |
| `kind` | the certificate's kind, if it could be read |
| `reasons` | a list of strings; empty for CERTIFIED |
| `checker` | the checker's name and version |
| `statements_sha256` | SHA-256 of the statement list used |
| `statement` | `null`, or label, name, commitment, `proved_by` and the rung |
| `numeric_rung` | the rung of the arithmetic |
| `assumptions` | the assumptions with their text |
| `recomputed` | the checker's own enclosure |
| `hypothesis` | for `vdc-hypothesis`: `{"status": "PASS", "FAIL" or "UNRESOLVED", "detail": …}`; a FAIL names a rational point of the interval where the hypothesis is violated |

Rules:
1. Malformed input of any kind (missing or extra keys, a float where a string is required, a statement that does
   not match the list, wrong assumptions, an input outside the statement's hypotheses such as t = 0) gives REJECTED.
2. The claimed enclosure is compared with the checker's own. Contained in the claim: go on. Disjoint from it:
   REJECTED. Otherwise the checker doubles its precision once and compares again; still neither: UNRESOLVED.
3. For `vdc-hypothesis` the hypothesis is decided first: FAIL gives REJECTED, UNRESOLVED gives UNRESOLVED.
4. A statement without a machine-checked proof in the list gives UNRESOLVED, never CERTIFIED.
5. An input outside the supported range or the computation budget gives UNRESOLVED.
6. CERTIFIED is returned only if every step above passed.

Command line of the reference implementation (run from `python/`): `python3 -m oscint_cert make <kind> --inputs
'<json>' --statements ../stamps/statements.json` writes a certificate to standard output; `python3 -m oscint_cert
check <file> --statements ../stamps/statements.json` writes a verdict. Exit codes: 0 CERTIFIED (or certificate
written), 1 REJECTED, 2 UNRESOLVED, 3 usage or input error. A second implementation must reproduce the status of
every certificate in a shared corpus; it may differ in the digits of `recomputed`.

## 6. Evidence for the reference implementation

`python/tests/test_cert.py` (22 tests, run on 2026-11-16 with Python 3.13.18 and, for the differential tests,
python-flint 0.9.0 with FLINT 3.6.0; all pass; without python-flint four tests are skipped):
- properties on random inputs with a fixed seed: root, π and sine/cosine enclosures; populations sum to at most 1;
  the LS-D envelope dominates every population (200 random sites and times);
- differential tests against Arb: sine and cosine at 300 points, Bessel values at 250 points with orders up to 60 and
  arguments up to 120 in modulus, the constant and the envelope;
- the phase checker against Arb sampling on 150 random trigonometric polynomials: a PASS is never contradicted at
  201 sample points, a FAIL always exhibits a certified violation; a near-degenerate case (the threshold within
  1e-12 of the true minimum) never passes falsely;
- adversarial certificates: every single-key deletion, an extra key, a wrong format, altered assumptions, a swapped
  kind, floats, NaN, infinities, booleans, nulls and containers in inputs and claims, a shifted claim (REJECTED), a
  point claim (not CERTIFIED), a wrong commitment, name or label (REJECTED), a statement whose proof is removed from
  the list (UNRESOLVED), inputs out of range (UNRESOLVED): none is CERTIFIED.

Dependencies: the runtime has none beyond the standard library. The build and test dependencies are pinned in
`python/pyproject.toml` (setuptools 84.2.1, python-flint 0.9.0); `pip-audit` 2.10.1 reported "No known
vulnerabilities found" for both on 2026-11-16 (pins by version, not yet by hash).

Not yet done, and so not claimed: a second, independent implementation with differential tests; a run of a worked
example by someone who has seen only this page; a published package (publication needs the owner's approval).

## 7. The strongest case against relying on a verdict

The checker is about 630 lines of tested, unverified Python. Its numbers agree with an independent ball-arithmetic
library at every point tested, but agreement is not proof. The statements it cites are machine-checked, but they are
statements about ideal, infinite systems, and one identification (the Bessel form of the kernel) is a paper step.
The envelope it evaluates is not the best known: at lattice sites Landau's constant 0.7857 replaces 1.5473
(`docs/prior_art.md`). And the `vdc-hypothesis` bound uses the textbook constants of S1.k, which are valid but far
from sharp.
