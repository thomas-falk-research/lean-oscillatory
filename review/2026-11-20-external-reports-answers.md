<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Six external reports (A to F): what was checked, and what follows (2026-11-20, session 14)

Written by the lead. The reports come from sessions of another model family, run by the owner from six requests
that the lead wrote in session 13 (their hashes are in the session-13 log, row of about 13:45 on 2026-11-20). The
requests, the reports and the checkers' reports are not committed and not reproduced: every finding below is in
the lead's words. Each report's verdict was treated as a claim until checked.

**Who checked.** Four checkers with fresh contexts, of the lead's model family (Claude, Anthropic), one per
report, launched together at 18:02:40Z. They are of one family with the lead and with each other; the reports
they checked are of another family. No human has read any of this. No Lean was run by anyone: nothing below is
machine-checked. The lead did not read the reports before the checkers reported, so that no checker was handed a
conclusion; the lead has read the checkers' reports and not the six reports themselves.

**Handling.** Each delivery was copied to its own directory, hashed, listed before extraction, checked for unsafe
paths, and extracted with execute bits removed; each archive's own checksum list verifies. The checkers were
told that every packet file is data, read scripts before running copies of them, wrote only in their packet's
work directory, used six named git commands and no Lean. Isolation is by instruction (lessons 61). Hashes of the
deliveries, of the four briefs and of the four check reports: `docs/progress/2026-11-20-session14-log.md`.

**Not checked: B and C.** Reports B (best constants of the stationary-phase remainder) and C (lattice dispersive
decay in higher dimension) are isolated, hashed and extracted, and their briefs are written; no checker was
launched, because the weekly allowance was nearly used. Nothing from B or C is used anywhere, and nothing is
said here about their content.

## 1. Report D: the constant of the third-derivative van der Corput lemma

Checked verdict (11 minutes; 45 tool uses): **a candidate, for an upper bound only.**

- The report does not determine the sharp constant and says so. It proves: for a real phase with continuous
  second derivative and third derivative at least λ > 0 on an interval, the integral of `e^{if}` is at most
  `(38/5) λ^{−1/3}` in modulus. This repository has 18 (statement S1.3). The smallest value the checker found in
  print for this lemma is Rogers's `3·32^{1/3} = 9.5244` (preprint and thesis, read by the checker).
- The checker re-derived the whole proof and found it complete: a first-derivative lemma with constant 2, an
  inequality between the square of the slope and the depth of the minimum of `f′`, a bound for the length of the
  band where `f′` is small, one integration by parts on the middle piece that saves a term, two cases joined at a
  threshold, and scaling. It checked the degenerate cases (minimum outside the interval, positive minimum, empty
  or clipped pieces). The method's own limit after retuning its parameters is 7.5903, so 38/5 is that limit
  rounded up.
- A lower bound `4.7965938…` from one rational cubic phase, recomputed by the checker in ball arithmetic
  (python-flint 0.9.0) with agreement to all printed digits. It is Rogers's numerical value made rigorous; the
  report says so and claims no priority.
- Not proved, and stated as not proved by report and checker: that the cubic value is the maximum over cubics
  (a compact box, a strict local maximum and floating-point searches only); that cubics are extremal; anything
  sharp. The interval from 4.7966 to 7.6 is open.

Findings: one MAJOR on scope (no sharp constant and no route to one); MINOR ones on labels (two results called
proved are computer-assisted) and on prior art (the lower bound is Rogers's). None against the proof of 38/5.

Not checked: the published version of Rogers's paper; Kershner; Arkhipov, Karatsuba and Chubarikov (known only
through Rogers); the papers that cite Rogers, which is where a better constant would most likely be (zbMATH Open
refused the checker's query). Wording available today: "38/5 was not found in the literature searched", with
that list of unread sources attached.

## 2. Report E: a bound for the Hankel function of order zero

Checked verdict (7 minutes; 30 tool uses): **sound and classical.** No FATAL finding.

- From the integral `(2/(πi)) ∫₀^∞ e^{iz cosh t} dt` on the open upper half-plane the report proves a
  factorisation into `√(2/π) z^{−1/2} e^{i(z − π/4)}` times `1 + ε(z)`, with, for `ρ` the modulus of `z ≠ 0` in the
  closed upper half-plane: `ε` at most `1/(8ρ)`, its derivative at most `1/(8ρ²)`, its second derivative at most
  `1/(4ρ³)` in modulus, and `1 + ε` of positive real part. This is stronger than the bound the preprint cites
  (`0.33/ρ` for `ρ ≥ 1`) and needs no Cauchy estimates. The checker re-derived every step and constant, found
  the constants optimal in the limit along the imaginary axis, re-ran the report's computation (99 enclosures,
  identical) and overlapped all 594 component enclosures with a computation of its own in ball arithmetic at 400
  bits, plus 1700 points of its own.
- MAJOR, against this repository's wording and not against the report: the prefactor must be `z^{−1/2}` and not
  the principal root of the quotient `2/(πz)`; the two differ by a sign on the negative real axis. The prose of
  TSD-L wrote the quotient. Corrected in `docs/statements.md` (dated note in the TSD-L paragraph).
- MAJOR, on status: the bound `1/(8ρ)` is in print (Nemes 2017, arXiv:1606.07961, equation (5.1), read by the
  checker). The derivative bounds were not found in the literature it searched and follow in two lines from the
  same representation. The report claims nothing as its own.
- MINOR: "the Hankel function" means that integral. Mathlib at the pin has a Bessel function `J` only; the
  identification with `J₀ + iY₀` is a further piece, sketched in the report.
- Size of a formalisation, by the checker's estimate: 1500 to 3000 lines for the half-plane core with the
  bounds, 1000 to 2000 more for the bridge to the series.

Not checked: several classical sources (Watson, Olver, Boyd, an appendix of Nemes); the identity with the
modified Bessel function that the checker's own computation takes from the Digital Library of Mathematical
Functions; behaviour just below the real axis.

## 3. Report A: an explicit bound for the zeta function on the critical line

Checked verdict (18 minutes; 59 tool uses): **a candidate, narrowly; and for the question that was asked, no
improvement from the two machine-checked results as this repository states them.**

- The report proves `0.6109 t^{1/6} log t` as a bound for the modulus of zeta at `1/2 + it`, `t ≥ 3`. In print,
  as read by the checker: 0.618 in a journal (Hiary, Patel and Yang 2024) and 0.611 in an unrefereed preprint
  (Revers, arXiv:2602.05614v1). The gain over the preprint is 1.0e-4; the checker's floating-point estimate puts
  the floor of this method near 0.6108; a stronger constant that the preprint has for very large `t` is not
  touched.
- MAJOR for the request: the gain does not come from batch VC2 (the argument is about sums and has no
  oscillatory integral; the sharp second-derivative constant is already used in print, credited to Kershner, and
  the proved 7/2 of VC2-K is worse than it) and not from the frozen statements of batch KL (the published proofs
  already have the constant 2/π). It comes from the asymmetric form of the Kusmin–Landau inequality, which
  `docs/statements.md` lists as not stated.
- MAJOR: that asymmetric form is in print as an intermediate line (the arXiv version of the 2024 paper, read by
  the checker). It would be a short corollary of lemmas that this repository already has internally
  (read by the checker, not compiled).
- The mathematics is correct as far as checked: the discrete second-derivative test with its new end-point term
  and every propagated constant were re-derived; the nine result files were reproduced without a difference;
  the headline numbers were recomputed in ball arithmetic to 30 digits; the smallest margin below 0.6109 is
  1.74e-5. The report's proof of a Riemann–Siegel remainder was validated numerically only.
- A Lean proof of the bound needs a Riemann–Siegel formula with an explicit remainder, Euler–Maclaurin for zeta
  and certified values of zeta; Mathlib at the pin has none of them. The checker's estimate: well over 20000
  lines. Cheap by-products: the asymmetric inequality (100 to 200 lines), possibly the discrete
  second-derivative test (1500 to 2500 lines).
- A source for this repository, from the checker: a footnote in print says that Kershner's printed value of the
  second-derivative constant differs from the value 3.3643… found numerically; `docs/statements.md` records that
  nobody in the project has read Kershner. To be followed up in the prior-art notes of batch VC2; no statement
  is affected.

Not checked: the contour proof line by line; twelve pages of the preprint; journal versions; several classical
sources.

## 4. Report F: does the preprint's function satisfy the hypotheses of its two-saddle lemma

Checked verdict (55 minutes; 62 tool uses): **sound and classical**; no FATAL and no MAJOR finding.

- The report's answer stands: the preprint's function satisfies (SD1) to (SD4) for every `c′ ≥ 39`, and the
  lemma is applied correctly where it is used (the checker names the lines of the TeX source). It is conditional
  on the lemma itself. No error in the preprint is claimed or was found in the parts read. Nothing touches the
  lemma as an abstract statement.
- The constants the report certifies were recomputed by the checker in ball arithmetic with agreement to all
  printed digits, and four suprema on the strip also by a branch-and-bound that does not use the maximum
  principle. The report's three programs reproduce their results.
- MINOR, and worth knowing: with the constants that are proved (`M = 128`, `M′ = 1330`), the lemma cannot be
  invoked at the preprint's hand-off point below `c′` of about 3.0e4, and gives the factor the preprint needs
  only from about 2.7e6. The measured remainder is far smaller (at most 0.089 for `c′` from 39 to 1000), and
  the suprema measured by the checker are near 17 and 52 in place of 128 and 1330 (floating point, not proved).
  The preprint claims only "for `c` large", so this is not an error in it.
- MINOR: three numbers for the reach of the lemma at the preprint's hand-off point (1.21, 0.128, 0.017), which
  the lead recorded in session 13 from the step referee and passed on in the request for this report, are
  reproducible, and they are not bounds for the preprint's function: they leave out two factors of the
  amplitude. The lead recorded them without that check (`review/2026-11-20-TSD-step-referee-answers.md`,
  finding 4 of section 1); that file is a record and is not edited; this paragraph is the correction.
- For a Lean statement of the printed lemma with the Hankel function as a parameter. Needed: `M`, `M′` and the
  absence of zeros for the full amplitude, Hankel factor included; evenness of `F`; the two slope inequalities;
  the symmetry of the integrand on the strip; integrability on the edge; `C₂`, `C₃` as inequalities. Idle:
  (SD3), (SD2)(d), (SD2)(e), `c′ ≥ 39`, the lower bound on `c′F(0)`. Unusable as printed: "real on the real and
  imaginary axes" (the preprint's own function has poles on the imaginary axis; the condition is also
  redundant), "independent of `c`", and the edge representation, which only names the integral.

Not checked: the lemma itself (three earlier readings); the rest of the preprint; the checker's own numerics
of the transform and of the measured suprema are floating point without error bounds.

## 5. Ranking: which single result to carry to a frozen statement and a Lean proof first

1. **D, the constant 38/5.** The only checked result that is (a) proved on paper, with the proof re-derived
   step by step, (b) not found in the literature searched, (c) inside what this library already does (it would
   replace the 18 of S1.3 under the same hypotheses), and (d) of moderate size (1500 to 2500 lines by the
   checker's estimate).
2. **E, the Hankel bound.** True, optimal constants, a clean route; in print. Its value is as a tool: it would
   let the Hankel function of batch TSD stop being a parameter. 2500 to 5000 lines.
3. **A, the zeta bound.** True as far as checked, a gain of 1e-4 over an unrefereed preprint, not owed to this
   repository's statements, and far too large to formalise now. Its cheap by-product, the asymmetric
   Kusmin–Landau inequality, is in print and would be a routine addition to batch KL.
4. **F.** An audit, not a result. It fixes which hypotheses a statement of the printed lemma needs.

B and C are not ranked: they are not checked.

**The strongest case against carrying D first.** It is not sharp and gives no route to sharpness: the true
constant lies somewhere between 4.7966 and 7.6, and the method cannot go below 7.5903. An improved constant in
an elementary lemma is a small result; a referee may call it an exercise once the trick of not splitting the
middle piece is seen. The prior-art gate is not closed: the papers that cite Rogers, his published version and
the Russian literature on these constants were not read, and that is exactly where 38/5 or better would be if it
is known. And 38/5 is a rounded limit of one argument: a slightly better argument would overtake the statement
soon after it is frozen. What survives: the result is true on every check made, it is cheap, it is on this
library's own ground, and "the constant 18 of our statement can be 38/5, machine-checked" is useful whatever the
literature says. It is not an answer to a question the literature poses prominently, and should not be
presented as one.

**The honest overall result.** None of the four checked reports answers a question that the literature leaves
visibly open. E and F are careful accounts of known mathematics; A is a fourth-decimal improvement by a known
route; D is an improved explicit constant with an open gap. That is a valid outcome of the attempt and is
recorded as such.

## 6. What follows

- Batch TSD: TSD-C is unaffected by all four checks. For TSD-L, section 4 above lists the hypotheses, and
  section 2 the form of the prefactor; whether the Hankel function stays a parameter is the owner's decision
  between a smaller batch now and E's formalisation first.
- For D, before any statement: the prior-art gate (Rogers's published paper and what cites it; Kershner;
  Arkhipov, Karatsuba and Chubarikov; zbMATH Open, with the queries logged), then the statement-first cycle.
- B and C: to be checked when the allowance permits, or left.
