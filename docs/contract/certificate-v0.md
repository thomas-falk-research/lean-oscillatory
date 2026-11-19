<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# The certificate contract, version 0.1, revision 3 (experimental)

One language-neutral contract between everything that produces an evaluated OscInt result and the one program that
may call it CERTIFIED. Version 0.1 is experimental: it is versioned from the start, and it is frozen as version 1
only after consumers from two different domains have used it (`docs/ROADMAP.md`, item I5). The statement index it
refers to is `stamps/statements.json` (format `oscint-statements 1`). There are two implementations: the Python
package under `python/oscint_cert/` (standard library only) and a Rust crate under `rust/oscint-cert/`, written by a
separate agent from revision 1 of this page alone. Revision 2 (2026-11-16) closes the gaps that agent reported and
that a differential test of the two confirmed (section 6). Revision 3 (2026-11-16) answers a test by a reader who
had only this page and the package's README (section 6): it adds two keys to the verdict, the option that pins the
statement list, a limit on the length of input numerals, and the missing definitions. The format strings are
unchanged because no certificate had left the repository.

**Terms.** OscInt is a Lean 4 library of machine-checked estimates for oscillatory integrals. A *statement* is one
frozen Lean proposition of that library, with a short label (LS-K, LS-D and S1.k below), a Lean name and a
*commitment* (a hash of its kernel-level form); `docs/statements.md` gives each statement in ordinary mathematical
notation. A *rung* says how a claim is supported: L0 typed code, L1 property or fuzz tests, L2 exact or certified
computation, L3 a proof on paper, L4 a machine-checked proof. `ASSUMED(rung, reason, owner)` marks a step that
has not reached the rung named, with the reason and who owns closing it.

## 1. Trust boundary

- **Only the checker confers CERTIFIED.** A producer, a wrapper in another language, a notebook or a web page
  transports and displays certificates and verdicts; none of them may assign the status.
- **The checker trusts nothing in a certificate.** It recomputes every number, looks the statement up in the
  statement list it was given, and derives the list of assumptions from the certificate's kind.
- **No floating point.** All arithmetic in the checker is exact rational interval arithmetic. A result that cannot
  be decided within the budget is UNRESOLVED; it is never rounded into a verdict.
- **CERTIFIED is relative to the statement list the checker was given.** The checker cannot tell a genuine list from
  a home-made one whose entries claim proofs. A reader who relies on a verdict must know which list was used: pass
  `--expect-statements-sha256` with the SHA-256 of the list from a source they trust (the release notes of the
  release they use, or `sha256sum stamps/statements.json` in a checkout whose `make statements-check` passes), or
  compare the verdict's `statements_sha256` with that value. A verdict records whether the list was pinned
  (`statements_pinned`). A verdict whose `statements_pinned` is `false` says "certified against the list with this
  hash" and nothing about where that list came from. No fixed value is printed here because the list grows with
  every batch of statements.
- **A verdict is bound to its certificate by `certificate_sha256`**, the SHA-256 of the bytes checked; a verdict does
  not repeat the inputs or the claim.
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
A numeral longer than 4000 characters is beyond the supported range (UNRESOLVED), and so is a numeral of more than
100 characters among the `inputs` other than a phase amplitude (the cost of the computation grows with the size of
the inputs; the limit is the budget). Integers that index things (a site,
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
| `lattice-population` | LS-K | `n` integer, `t` rational | `J_n(2t)²`: the probability at site n at time t for `i u′ = −Δu` on ℤ, `(Δu)(n) = u(n+1) + u(n−1) − 2u(n)`, started at site 0 | `bessel-identification`, `single-site-datum` |
| `lattice-envelope` | LS-D | `d` integer in 0…64, `t` rational, t ≠ 0 | `min{1, (C*/2π)^d (2\|t\|)^{−d/3}}`, `C* = 8(1 + √7)/3`: a bound for the **amplitude** `\|u(t, x)\|` at every site, for a datum of ℓ¹ norm 1 | `unit-l1-datum` |
| `vdc-hypothesis` | S1.k | `phase`, `order` integer k in 2…16, `a`, `b`, `mu`, `t` rationals with a ≤ b, mu > 0, t > 0 | claim `{"holds": true, "bound": enclosure}`: `\|ω^{(k)}\| ≥ mu` on [a, b], and the bound `(5·2^{k−1} − 2)(t·mu)^{−1/k}` for `\|∫_a^b e^{i(t·ω(k) + ξk)} dk\|`, every real ξ | `amplitude-one` |

Inputs outside the table are of two sorts, and the two get different verdicts (section 5):

| Input | Malformed or outside the statement's hypotheses: REJECTED | Valid, but beyond what the checker supports: UNRESOLVED |
|---|---|---|
| every kind | a numeral that is not of the forms of section 2 | an input numeral of more than 100 characters (phase amplitudes: 4000) |
| `bessel-j`, `lattice-population` | `n` not a JSON integer | \|n\| > 10000; \|x\| > 400; \|2t\| > 400 |
| `lattice-envelope` | d < 0; t = 0 | d > 64 |
| `vdc-hypothesis` | order < 2; a > b; mu ≤ 0; t ≤ 0; an empty phase; a term with other keys or another `fn` | order > 16; more than 64 terms; \|freq\| > 1000; \|freq\| times an end of the interval above 64 |

`lattice-population` accepts t = 0 (the value is exactly 1 or 0). A frequency 0 and an interval with a = b are valid.

Units and reading. Time is in units of ħ divided by the hopping amplitude: for a tight-binding Hamiltonian with
hopping amplitude κ between neighbours (`H = −κ Σ |n⟩⟨n+1| + h.c.`, any on-site constant), the `t` of this page is
κ·(physical time)/ħ, and the population is `J_n(2κt_phys/ħ)²`. The envelope of `lattice-envelope` bounds an
amplitude; the probability at a site is bounded by its square (and, since the envelope is at most 1, also by the
envelope itself). The `vdc-hypothesis` bound is for an oscillatory integral with amplitude 1; it can exceed the
trivial bound `b − a`, and then says nothing new.

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
| `certificate_sha256` | SHA-256 (lower-case hexadecimal) of the bytes of the certificate that was checked |
| `statements_pinned` | `true` if the statement list was required to have a given SHA-256 (`--expect-statements-sha256`) and has it; otherwise `false` |

Every key of the table is present in every verdict; a value that does not apply, or was not reached, is `null`
(for example `recomputed` in a verdict that was decided by the structure or by the hypothesis).

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

Conformance of two implementations is defined on claims whose two end points are each at least
`1e-25 · max(1, |value|)` away from the value (on either side); for a claim with an end point inside that margin they
may differ between UNRESOLVED and the other two statuses, never between CERTIFIED and REJECTED. Where rule 1 and a
length limit both apply to one numeral, rule 1 decides (a malformed numeral is REJECTED whatever its length).
`statements_pinned` reports the pin, whatever the status.

Command line of the reference implementation (run from `python/`): `python3 -m oscint_cert make <kind> --inputs
'<json>' --statements ../stamps/statements.json` writes a certificate to standard output; `python3 -m oscint_cert
check <file> --statements ../stamps/statements.json [--expect-statements-sha256 <hex>]` writes a verdict (`-` as the
file reads standard input).

Exit codes of `check`: 0 CERTIFIED, 1 REJECTED, 2 UNRESOLVED; in these three cases, and only in these, a verdict is
on standard output. Exit code 3, with a message on standard error and nothing on standard output: a wrong command
line, an unreadable file, a statement list that is unusable (not strict JSON, not of the format `oscint-statements
1`, an entry without a non-empty string `label`, `name` and `commitment`, or two entries with one label), or a
statement list whose SHA-256 is not the expected one (compared without regard to letter case). A certificate with
bad content (also `null`, an empty file, bytes that are not UTF-8) is a REJECTED verdict with exit code 1, not an
error. Exit codes of `make`: 0 and a certificate on standard output; 3 and a message on standard error in every
other case (an input outside the tables of section 4, in either column; a hypothesis that fails, in which case the
message names the point, or that is undecided). With the default precision on both sides, `make` writes only
certificates that `check` certifies against the same statement list; the one exception is a statement without a
proof in that list (UNRESOLVED).

`statements_sha256` is the SHA-256 of the statement list's bytes. Implementations may differ in the digits of
`recomputed`, in the wording of `reasons` and in the shape of `detail`. The reference prints enclosures rounded
outward to at most 80 decimal digits, as fractions (`"lo": "447213595…/500000000…"`); a consumer converts them with
exact rational arithmetic. The reference's option `--digits` (10 to 200, default 30) sets the working precision of
rule 4; the conformance statement below is for the default.

## 6. Evidence

**The Python implementation** (version 0.2.1). `python/tests/test_cert.py`: 32 tests, run on 2026-11-16 with Python
3.13.18 and, for the differential tests against Arb, python-flint 0.9.0 with FLINT 3.6.0; all pass in about 5 s:
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
  the list (UNRESOLVED), inputs out of range (UNRESOLVED): none is CERTIFIED;
- the command line (added in 0.2.1): files that are not certificates, the statement-list pin, unusable statement
  lists, exit codes, the keys of every verdict, the failing-hypothesis path on a long interval, the budgets.

**The second implementation** (version 0.2.0). `rust/oscint-cert/` (Rust, exact big rationals, no floating point, no
`unsafe`; dependencies pinned exactly: num-bigint 0.4.8, num-integer 0.1.47, num-rational 0.4.2, num-traits 0.2.19,
serde_json 1.0.154). It was written by a fresh-context agent of the lead from revision 1 of this page and the
statement list alone, and brought to revision 3 by another such agent from revisions 2 and 3 alone, in a copy of
the crate outside the repository (their own statements; the lead did not audit their file accesses). The lead
re-ran its build and tests (85 pass) and `cargo audit` (exit code 0, 17 crates scanned). Both implementations are
by AI agents of one model family: independent in code, not in kind.

**The differential tests** (`python/tests/differential.py`; a corpus from a fixed seed, each certificate checked by
both command lines):
- First run, Python 0.1.0 against the Rust checker, 1429 certificates: **86 disagreements**. None had one side
  CERTIFIED for a false claim, but 82 had Python CERTIFIED where Rust said REJECTED: Python accepted the numerals
  `"1/-2"`, `".5"`, `"+1"`, `" 1"` and `"5."` (81 cases) and a duplicate key (1 case). In 4 cases Python said REJECTED
  where UNRESOLVED was right (an order, a dimension, a frequency and a Bessel order beyond the supported range), one
  of them through a crash on printing an integer of more than 4300 digits. Revision 2 states the rules that settle
  each case; Python 0.2.0 follows them.
- Second run, Python 0.2.0 against the unchanged Rust checker: 0 disagreements in 1429. Record:
  `python/tests/differential-2026-11-16.txt`.
- Third run, Python 0.2.1 against Rust 0.2.0, both at revision 3: 1463 certificates (the 1429 and 34 new ones: files
  that are not certificates, numerals of 100 and 101 characters, tiny and huge arguments, a failing hypothesis on a
  long interval, 64 and 65 terms, the largest supported order). **0 disagreements**; compared this time are the
  status, the exit code, the set of verdict keys, the certificate hash, the list hash and the pin flag. 22
  command-line cases without a verdict (unusable statement lists, the pin, wrong command lines, `make` failures):
  both as specified. 8 certificates made by one implementation and checked by the other: all CERTIFIED. Record:
  `python/tests/differential-2026-11-16-revision3.txt`.

**A test by a reader with the documentation only** (2026-11-16). A fresh-context agent of the lead was given
revision 2 of this page, the README and the Python package, and four tasks (two uses, an attempt to obtain a false
CERTIFIED, hostile inputs). It completed them without reading source code. In more than 300 hand-made attempts
against the shipped statement list it obtained no CERTIFIED for a false claim. It found these defects, all fixed in
Python 0.2.1 and stated in revision 3: CERTIFIED is only as good as the statement list given, and the documents
named no way to pin it (section 1; the option `--expect-statements-sha256`); the failing-hypothesis path crashed
on long intervals with a false reason; no budget on time (a 64-term phase and a 200-digit Bessel argument ran for
minutes); tracebacks for `null`, non-UTF-8 files and a bare-array statement list; verdict keys omitted instead of
`null`; exit code 2 for wrong command lines; missing definitions and units. The same tests now run in 5 s where
they took 451 s (enclosures are rounded outward inside the sine and cosine doubling). A probe of worst-case inputs
by the lead then found two more defects of one kind (the root of a tiny number had lower end 0, so two decidable
cases came out UNRESOLVED): fixed, with a regression test.

The agents that wrote and updated the Rust checker listed ambiguities of revisions 1 and 3. Answered in the text:
the claim shape (section 3), malformed against unsupported inputs (section 4), the order of the rules, the
starting precision and point claims (section 5), number and integer syntax (section 2), duplicate keys (section 3),
exit codes, the conformance margin and the precedence of rule 1 over length limits (section 5). Left to the
implementation: the exact shape of `detail`, the text of `reasons`, the hypothesis method, the working precision,
options beyond those named here.

Performance on one machine (4 cores, virtual): ordinary inputs well under a second in both. Worst cases the limits
allow: Python (the lead's probe), Bessel values and populations at an argument near 400 written with 100
characters, 32 s to 76 s; Rust (its agent's measurements, not repeated by the lead), the same in 0.01 s by a
different method, and at most about 28 s on 64-term phases with 4000-digit amplitudes (UNRESOLVED by its
arithmetic budget).

Dependencies: the Python runtime has none beyond the standard library. Its build and test dependencies are pinned in
`python/pyproject.toml` (setuptools 84.2.1, python-flint 0.9.0); `pip-audit` 2.10.1 reported "No known
vulnerabilities found" for both on 2026-11-16 (pins by version, not yet by hash).

Not yet done, and so not claimed: a published package or crate (publication needs the owner's approval); a C
interface; a consumer from a second domain; a proof of either checker's arithmetic.

## 7. The strongest case against relying on a verdict

A `vdc-hypothesis` certificate binds its bound to `order`, `t` and `mu` only; the phase and the interval enter
through the hypothesis alone, so two different phases that both satisfy it carry the same bound. That is what the
statement says, and a reader should not take the bound as a property of the phase.

A verdict is relative to the statement list given to the checker, and a verdict whose `statements_pinned` is
`false` says nothing about where that list came from (section 1). The verdict carries the hash of the certificate,
not its content: whoever relies on a verdict must hold the certificate too.

The checker is about 750 lines of tested, unverified Python, and its second implementation is about 4800 lines of
unverified Rust. Its numbers agree with an independent ball-arithmetic
library at every point tested, but agreement is not proof. The statements it cites are machine-checked, but they are
statements about ideal, infinite systems, and one identification (the Bessel form of the kernel) is a paper step.
The envelope it evaluates is not the best known: at lattice sites Landau's constant 0.7857 replaces 1.5473
(`docs/prior_art.md`). And the `vdc-hypothesis` bound uses the textbook constants of S1.k, which are valid but far
from sharp.
