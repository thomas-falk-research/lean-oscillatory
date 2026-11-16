# The certificate contract, version 0.1, revision 2 (experimental)

One language-neutral contract between everything that produces an evaluated OscInt result and the one program that
may call it CERTIFIED. Version 0.1 is experimental: it is versioned from the start, and it is frozen as version 1
only after consumers from two different domains have used it (`docs/ROADMAP.md`, item I5). The statement index it
refers to is `stamps/statements.json` (format `oscint-statements 1`). There are two implementations: the Python
package under `python/oscint_cert/` (standard library only) and a Rust crate under `rust/oscint-cert/`, written by a
separate agent from revision 1 of this page alone. Revision 2 (2026-11-16) closes the gaps that agent reported and
that a differential test of the two confirmed (section 6); the format strings are unchanged because no certificate
had left the repository.

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

Every number is a JSON string holding an exact rational in one of three forms, ASCII digits only: an integer
`-?D+`, a fraction `-?D+/D+` with a nonzero denominator, or a finite decimal `-?D+.D+`. No leading `+`, no spaces, no
exponent, no sign on the denominator, no digit separators; leading zeros, `-0` and unreduced fractions are accepted.
A numeral longer than 4000 characters is beyond the supported range (UNRESOLVED). Integers that index things (a site,
a dimension, an order, a frequency) are JSON integers written without a fraction or an exponent (`1.0` and `1e0` are
rejected, as are booleans); an integer of more than 300 digits is malformed. JSON floats, `NaN` and `Infinity` are
rejected. An enclosure is an object with exactly the keys `lo` and `hi`, lo ≤ hi, meaning the closed interval.

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
| `producer` | a string naming what made the certificate; its content is ignored by the checker |

"Exactly these keys" holds at every level: the certificate, `statement`, `inputs`, an enclosure, the claim and each
phase term. An object with a duplicate key, at any depth, is malformed. The claim of the kinds `bessel-j`,
`lattice-population` and `lattice-envelope` is the enclosure object itself.

## 4. Kinds

| Kind | Statement | Inputs | Quantity enclosed by the claim | Assumptions |
|---|---|---|---|---|
| `bessel-j` | none | `n` integer, `x` rational, \|x\| ≤ 400 | `J_n(x)` | none |
| `lattice-population` | LS-K | `n` integer, `t` rational | `J_n(2t)²`: the probability at site n at time t for the lattice Schrödinger group on ℤ started at site 0 | `bessel-identification`, `single-site-datum` |
| `lattice-envelope` | LS-D | `d` integer in 0…64, `t` rational, t ≠ 0 | `min{1, (C*/2π)^d (2\|t\|)^{−d/3}}`, `C* = 8(1 + √7)/3` | `unit-l1-datum` |
| `vdc-hypothesis` | S1.k | `phase`, `order` integer k in 2…16, `a`, `b`, `mu`, `t` rationals with a ≤ b, mu > 0, t > 0 | claim `{"holds": true, "bound": enclosure}`: `\|ω^{(k)}\| ≥ mu` on [a, b], and the bound `(5·2^{k−1} − 2)(t·mu)^{−1/k}` | `amplitude-one` |

Inputs outside the table are of two sorts, and the two get different verdicts (section 5):

| Input | Malformed or outside the statement's hypotheses: REJECTED | Valid, but beyond what the checker supports: UNRESOLVED |
|---|---|---|
| `bessel-j`, `lattice-population` | `n` not a JSON integer | \|n\| > 10000; \|x\| > 400; \|2t\| > 400 |
| `lattice-envelope` | d < 0; t = 0 | d > 64 |
| `vdc-hypothesis` | order < 2; a > b; mu ≤ 0; t ≤ 0; an empty phase; a term with other keys or another `fn` | order > 16; more than 64 terms; \|freq\| > 1000; \|freq\| times an end of the interval above 64 |

`lattice-population` accepts t = 0 (the value is exactly 1 or 0). A frequency 0 and an interval with a = b are valid.

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

Every key of the table is present in every verdict; a value that does not apply is `null`.

Rules, applied in this order; the first that decides, decides:
1. **Structure.** Anything that is not a certificate as specified in sections 2 to 4 gives REJECTED: text that is
   not JSON (also an empty file, a byte-order mark, a duplicate key, `NaN`), missing or extra keys, a float where a
   string is required, wrong assumptions, a statement whose label, name or commitment does not match the list, a
   `holds` that is not `true`, an input in the REJECTED column of section 4.
2. **Supported range.** An input in the UNRESOLVED column of section 4, or a computation that exceeds the checker's
   budget, gives UNRESOLVED. Nothing is compared.
3. **Hypothesis** (`vdc-hypothesis` only), decided before any bound is compared: FAIL gives REJECTED, UNRESOLVED
   gives UNRESOLVED. The method and the budget (the reference uses bisection with a mean-value bound and at most
   4096 pieces) are the implementation's; two implementations may therefore differ between PASS and UNRESOLVED on
   thresholds within about 1e-9 of the true minimum, never between PASS and FAIL.
4. **Claim.** The claimed enclosure is compared with the checker's own. Disjoint from it: REJECTED. Containing it:
   go on. Otherwise the checker recomputes once at twice its working precision (the reference: 30, then 60 decimal
   digits) and compares again; still neither: UNRESOLVED. A claim of zero width is CERTIFIED only if the quantity
   is exactly that rational number and the checker's enclosure is that point (for example `J_0(0) = 1`).
5. **Proof.** A statement whose `proved_by` in the list is not a non-empty string gives UNRESOLVED.
6. Otherwise CERTIFIED.

Conformance of two implementations is defined on claims that are either at least 1e-25 wide relative to
`max(1, |value|)` or wrong by at least that much; inside that margin they may differ between UNRESOLVED and the
other two statuses, never between CERTIFIED and REJECTED.

Command line of the reference implementation (run from `python/`): `python3 -m oscint_cert make <kind> --inputs
'<json>' --statements ../stamps/statements.json` writes a certificate to standard output; `python3 -m oscint_cert
check <file> --statements ../stamps/statements.json` writes a verdict. Exit codes: 0 CERTIFIED (or certificate
written), 1 REJECTED, 2 UNRESOLVED, 3 for the command line, an unreadable file, an unusable statement list, or a
`make` that cannot produce a certificate. A certificate with bad content is a REJECTED verdict with exit code 1, not
an error. `statements_sha256` is the SHA-256 of the statement list's bytes. Implementations may differ in the digits
of `recomputed` and in the wording of `reasons`.

## 6. Evidence

**The Python implementation.** `python/tests/test_cert.py` (23 tests, run on 2026-11-16 with Python 3.13.18 and, for
the differential tests against Arb, python-flint 0.9.0 with FLINT 3.6.0; all pass; without python-flint four are
skipped):
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

**The second implementation.** `rust/oscint-cert/` (Rust, exact big rationals, no floating point, no `unsafe`;
dependencies pinned exactly: num-bigint 0.4.8, num-integer 0.1.47, num-rational 0.4.2, num-traits 0.2.19,
serde_json 1.0.154). It was written by a fresh-context agent of the lead that was allowed to read only revision 1 of
this page and the statement list (its own statement; the lead did not audit its file accesses). Its agent reports 58
tests passing, a clean `cargo audit` (cargo-audit 0.23.0, 1509 advisories loaded, 17 crates scanned) and cross-checks
against mpmath; the lead re-ran its build and tests (record below). Both implementations are by AI agents of one
model family: independent in code, not in kind.

**The differential test** (`python/tests/differential.py`, 1429 certificates from a fixed seed: 160 valid ones over
the four kinds, their mutations, range and edge cases, and six raw-text cases; each checked by both command lines):
- First run, Python 0.1.0 against the Rust checker: **86 disagreements**. None had one side CERTIFIED for a false
  claim, but 82 had Python CERTIFIED where Rust said REJECTED: Python accepted the numerals `"1/-2"`, `".5"`,
  `"+1"`, `" 1"` and `"5."` (81 cases) and a duplicate key (1 case). In 4 cases Python said REJECTED where UNRESOLVED was right (an
  order, a dimension, a frequency and a Bessel order beyond the supported range), one of them through a crash on
  printing an integer of more than 4300 digits.
- Revision 2 of this page states the rules that settle each case; the Python checker was changed to follow them
  (version 0.2.0; five regression tests in `test_strictness_found_by_the_differential_test`).
- Second run, Python 0.2.0 against the unchanged Rust checker: **0 disagreements in 1429**; both certify all 160
  valid certificates. Record: `python/tests/differential-2026-11-16.txt`.

The Rust agent listed twenty ambiguities of revision 1. Revision 2 answers the ones that change a status: the claim
shape (section 3), malformed against unsupported inputs (section 4), the order of the rules, the starting precision
and point claims (section 5), number and integer syntax (section 2), duplicate keys (section 3), the exit code of a
bad certificate (section 5). Left open: the exact shape of `detail`, the text of `reasons`, and the hypothesis method.

Dependencies: the Python runtime has none beyond the standard library. Its build and test dependencies are pinned in
`python/pyproject.toml` (setuptools 84.2.1, python-flint 0.9.0); `pip-audit` 2.10.1 reported "No known
vulnerabilities found" for both on 2026-11-16 (pins by version, not yet by hash).

Not yet done, and so not claimed: a run of a worked example by someone who has seen only this page; a published
package or crate (publication needs the owner's approval); a C interface.

## 7. The strongest case against relying on a verdict

A `vdc-hypothesis` certificate binds its bound to `order`, `t` and `mu` only; the phase and the interval enter
through the hypothesis alone, so two different phases that both satisfy it carry the same bound. That is what the
statement says, and a reader should not take the bound as a property of the phase.

The checker is about 700 lines of tested, unverified Python, and its second implementation is unverified Rust. Its numbers agree with an independent ball-arithmetic
library at every point tested, but agreement is not proof. The statements it cites are machine-checked, but they are
statements about ideal, infinite systems, and one identification (the Bessel form of the kernel) is a paper step.
The envelope it evaluates is not the best known: at lattice sites Landau's constant 0.7857 replaces 1.5473
(`docs/prior_art.md`). And the `vdc-hypothesis` bound uses the textbook constants of S1.k, which are valid but far
from sharp.
