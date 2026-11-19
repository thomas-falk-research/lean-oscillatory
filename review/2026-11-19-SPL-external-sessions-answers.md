<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL: three external sessions of another model family, and the lead's answers (2026-11-19)

Written by the lead. On 2026-11-19 the owner ran three sessions with an AI system of another model family, each in
its own conversation, from briefs the lead had drafted in the session (not committed; the reports are not
reproduced here, every finding is in the lead's words). The reports and evidence archives are kept in the lead's
scratch and are not in the repository; their SHA-256 values are in the session log. None of the sessions could run
Lean. Two reports were then checked by agents with fresh contexts of the lead's own model family (briefs' SHA-256
in the session log), which re-derived the mathematics and wrote their own numerics; the third (literature) was
checked by the lead on its three most consequential items. Every statement below says who verified what.

What these sessions are and are not: they are the only work on this batch by a different model family, and the
first of them did not see the lead's kernel, constant or proof before it had its own. They are not human review,
and nothing in them is machine-checked.

## 1. Blind derivation (the problem only; then a comparison with the lead's claim)

Asked: the best constant K in `|R(g, λ)| ≤ K ‖g‴‖₁ λ^{−3/2}`, with proof, sharpness, digits, a finite certificate for
`K ≤ 73/100`, and attempts to break the statement.

Its result, in the lead's notation: an identity `R = −∫ Q g‴` at `λ = 1` with a kernel `Q`, the best constant
`sup |Q|`, sharpness by four bumps whose moments of order 0, 1, 2 vanish, and the value
`0.72197399899801734661…` with a rational enclosure of width `2 · 10⁻⁴²`. In its second part it found `Q = iκ` for
the lead's kernel κ, so its identity is the lead's (T2) and the constants are the same number.

| # | Finding (lead's words) | Checked by | Answer |
|---|---|---|---|
| 1 | The identity and the best constant agree with the lead's after the change of notation `Q = iκ`, `C = 2L`. | Checker: re-derived (derivatives of `Q`, the jump at 0, the boundary terms) and compared numerically to `10⁻⁴¹`. | The draft statements stand. This is the strongest check the batch has had: an independent derivation by another family. |
| 2 | The lead's "K = 0.7219740, attained at 1.62460" are rounded values, not equalities: `0.7219740 − K = 1.0 · 10⁻⁹`, and the maximiser is `6.2 · 10⁻⁷` to the right of 1.62460. | Consistent with the registered output (`K − K* = 1.00e-09`). | Accepted. The registration says "0.7219740" as a constant chosen above `K*` and "near 1.6246"; records written from now on use "≈" for both. |
| 3 | Stronger bounds than the lead's: the kernel is within `1/τ³` of its limit (the lead has `4/τ³`), and `\|L − F(τ)\| ≤ 1/τ` (the lead has `2/τ`). Its proofs rotate contours (Cauchy's theorem on sectors). | Checker: re-derived the three rotations with their arc estimates; on (0, 60] the largest value of `τ³ \|κ − L/2\|` is 0.999998. The lead's grid (to 40) had found 0.99999. | Accepted as true. For Lean the contour proofs are costly; the checker gives two real-variable routes, not refereed: constant 1 through the integrals `∫₀^∞ v^k e^{−xv−iv²/2} dv` and one exchange of integrals, and constant 3 by one more integration by parts in the lead's Lemma 1′. Recorded in `docs/proof-SPL.md`, addendum. |
| 4 | A finite certificate for `K ≤ 73/100`: 145 grid points `j/64` on `[0, 9/4]` with `\|Q\| ≤ 361/500`, Lipschitz constant 1, a tail bound, values enclosed by a 48-term power series with an explicit remainder in exact rational arithmetic. | Checker: read and reran the scripts (outputs byte-identical), and wrote its own exact check with a different formula and a different series for π: all 145 points pass; largest value at `x = 13/8`. It also found the certificate over-provisioned (91 points suffice) and designed smaller ones. | Accepted: SPL-N now has a route that two families have run in exact arithmetic. With the lead's present bounds (tail constant 4), the checker's second-order design needs 10 cells and 16 series terms for 73/100, and 6 cells and 14 terms for 3/4. None has been run in a proof assistant; SPL-N stays out of the first freeze and becomes the next statement. |
| 5 | The enclosure of `K` uses `K ≤ 0.73` inside its argument. | Checker: not circular (the bound 0.73 comes from the grid certificate, which does not use the enclosure), and not needed (7/8 suffices there). | No action. |
| 6 | Integrability of `g′` and `g″` follows from that of `g` and `g‴`: `‖g′‖₁ ≤ ‖g‖₁ + ‖g‴‖₁/6`, `‖g″‖₁ ≤ 4‖g‖₁ + ‖g‴‖₁/3`. | Checker: re-derived both identities and both constants. | Accepted as proved on paper. The draft statements keep all four hypotheses (a statement with two hypotheses fewer is a possible later corollary); `docs/statements.md`, item 3, now says the redundancy is proved on paper and by whom it was checked. |
| 7 | `\|F\| ≤ 7/4` for the lead's primitive, from five exact enclosures. | Checker: own enclosures at the five points. | Consistent with the route of SPL-K through VC2-S and VC2-N, which needs no certificate. |

Not checked by the checker: the report's sections on weakened hypotheses beyond item 6, its table of twelve
amplitudes, and its two high-precision computations (which share one arithmetic library, as the report says).

## 2. Literature (two parts)

The session's verdict: the identity follows from a published exact remainder formula (Ali Mehmeti and Dewez,
arXiv:1412.5789, Theorem 1.3 with `N = 3`, after Erdélyi) by adding the two half-lines; the folded kernel with the
constant 0.72197… was not found in what it read; Olver (1974) and Erdélyi's originals remained unread (paywalls),
so no attribution is possible either way. This matches the lead's reader (`review/2026-11-19-SPL-plan-referee-answers.md`,
section 2) and comes from another family's search (265 search requests in its ledger).

New, and checked by the lead by fetching and reading the public source files (not compiled):

- **A quadratic-phase leading term is formalised in Lean.** `openai/math`, file
  `lean/OAI/Dynamics/ThreeTorus/StationaryPhase.lean` at commit 4eaee87: `quadratic_stationary_identity`,
  `quadratic_stationary_error`, `quadratic_stationary_limit`, for Schwartz amplitudes, with the remainder
  `(π/t) ∫ ξ² |𝓕⁻¹f|`; in the lead's normalisation a bound of order `λ^{−3/2}` in a Fourier-moment norm. The file
  has no `sorry` and no axiom declaration. **The lead's sentence "no formalisation of a stationary-phase leading
  term was found" (opening note and prior-art page, 2026-11-19) was wrong and is corrected.** What batch SPL
  would add to it: the remainder in `‖g‴‖₁` with an explicit kernel and constant, for amplitudes that need not be
  Schwartz; neither bound implies the other.
- **The value of the Fresnel integral is formalised in Lean** in two public repositories (`tendsto_fresnelC`,
  `tendsto_fresnelS` in an FLMF release; `fresnel_integrals_elementary` in lean-DLMF). Mathlib at the pin still
  has none; the batch derives the value from the Gaussian integral and imports nothing.

Taken from the report without a check by the lead: Zworski's quadratic-phase theorem read directly (remainder by a
Fourier L¹ norm, constants not numerical; in one variable `(2√(2π))⁻¹ λ^{−3/2} ∫ ξ² |ĝ|`); a second later account of
Olver's theorem (one-sided, total variation, integer powers of the parameter); Hörmander's Lemma 7.7.3 read in a
translation with a damaged main inequality.

## 3. General phase (stage 2 of the batch plan)

Asked: an explicit constant for `∫ a e^{iλφ}` minus its leading term, for `φ″ ≥ α > 0`, with the power of α.

Its result: for `φ` of class C^{3,1} with `φ″ ≥ α`, `a ∈ C_c³`, the remainder is at most `C λ^{−3/2}` with
`C = 2√π · min(B_gen, B_sharp)`, explicit in `α`, `sup |a|, |a′|, |a″|`, `sup |φ‴|` and the Lipschitz constant of
`φ‴`; `B_sharp` grows like `α^{−5/2}`, and that power is necessary (the family `αx²/2 + x⁴/24`); C^{3,1} is the
threshold in the Hölder scale; a second route by homotopy avoids the square-root substitution; and a generic fold
cannot occur in this class when the amplitude at the stationary point is bounded away from 0.

Checked by an agent of the lead's family: all six claims re-derived, every constant reproduced, the report's
table reproduced with the checker's own quadrature, the scripts rerun with byte-identical outputs; attempts to
break the bound (stationary point at the edge of or outside the support hull, complex amplitudes, amplitude
vanishing at the stationary point, 400 random cases) found no violation; largest ratio seen 0.354. No FATAL or
MAJOR finding.

| # | Finding or qualification (lead's words) | Answer |
|---|---|---|
| 1 | The lead's plan called stage 2 "uniformity toward a fold". In a strongly convex class with fixed bounds a generic fold cannot occur: `\|a(x₀)\| \|φ‴(x₀)\|² ≤ 4 M₄ A₀ β + A₂ β²`. The checker adds the hypotheses this needs: the interval is the support hull of the amplitude with `x₀` inside it, `φ″ > 0` there, and the amplitude and its derivative vanish at both ends. | Accepted. The opening note is corrected: stage 2 is uniformity in α within the convex class (relative remainder small when `λα² → ∞`); the fold regime, with two stationary points, is stage 3 and is not convex. |
| 2 | The worst-case power is `α^{−5/2}`, not the `α^{−7/2}` suggested by the classical second term. | Accepted (checker: second term re-derived and compared numerically at three values of α). The exponent is sharp; the constants are not: upper and lower prefactors differ by a factor of about 129. |
| 3 | It uses its own quadratic estimate, `2√π ‖g″‖_∞ λ^{−3/2}`, not SPL-K. | Noted: a different norm, suited to low regularity of the phase; `2√π` is not sharp (the checker estimates the best constant near 2.85). Stage 2 can be built on either. |
| 4 | The report's numerical evidence is thinner than described: its two quadratures share the integrand code, and no script tests the inequalities behind the constants. | The constants rest on the proofs, which the checker re-derived by hand and with computer algebra. |

Not checked: the report's proof of joint sharpness in full, and most of its table of necessary hypotheses.

## 4. What changes

- No draft statement changes. `docs/statements.md` ("Batch SPL": prior art in "Why", items 3 and 6), the prior-art
  page, the opening note (sections 4 and 6) and the proof page (addendum) are updated.
- SPL-N: the next statement after the first freeze, with a certificate design chosen after a prototype.
- Stage 2: target statement from section 3, to be framed, registered and reviewed like any batch.
- Still unread in the original: Olver (1974), Erdélyi (1955, 1956), Hörmander's and Zworski's books in a clean
  copy. The owner has been asked for copies if a library gives access.

## 5. Critique of the draft statements before the freeze (a fourth session, later the same day)

The owner ran one more session of the same other-family system on two attachments only: the draft Lean statement
file (SHA-256 12f8d3b6…b40c715, the text committed at a7fa3dc) and the section "Batch SPL" of `docs/statements.md`.
It could not run Lean and says so. Its report reached the lead as text in the session (no file, so no hash).
Not checked by a second agent; the lead read it against the statement file and re-derived the items marked below.

Verdicts: SPL-I, SPL-S, SPL-K, SPL-A each FAITHFUL to the prose and true as formalised; no BLOCKER. It checked the
quantifier order, the coercions, the precedence of the exponent `-(3 : ℝ) / 2`, the Bochner integral under the
stated integrability, the kernel's definition by cases, and that `HasDerivAt` at every point leaves no freedom in
`g₁, g₂, g₃`; it derived SPL-I with its sign and scaling on its own, proved 7/8 by an elementary route that does
not use batch VC2 (polynomial bounds on [0, 2] and a tail from a Laplace-type representation), justified the
existential form of SPL-S by the argument the proof page now uses, and proved SPL-A by the four-bump construction.

| # | Severity (its own) | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | MAJOR (usability) | A user of SPL-K must supply three derivative functions, three pointwise derivative proofs and four integrability proofs. A corollary for a compactly supported C³ function with canonical derivatives is needed, and a precise theorem for the phase −u²/2: `R₋(g, λ) = conj(R₊(conj g, λ))`; "conjugate" in the prose is right but too short for a complex amplitude. | Accepted. Not by changing the four draft statements (the sanity layer is being built against their text): a second freeze of this batch will state a front end for compactly supported C³ amplitudes, the negative phase, sharpness for general λ, and SPL-N. `docs/statements.md` now gives the conjugation rule exactly and names these as planned statements. |
| 2 | MAJOR (process) | Twenty-four single-token mutations with explicit data, and four edits that must not be flagged (harmless rewrites). | Accepted. Those not already in the lead's plant list were sent to the sanity-layer agent as an addendum. One corrects the lead's brief: an even extension of the kernel is refuted outright by a Gaussian amplitude (the planted identity makes the remainder vanish by parity), where the brief had expected "not detected before the proof". Re-derived by the lead: with `g₃` odd and an even kernel the integral is 0. |
| 3 | MINOR | `Integrable g₁` and `Integrable g₂` are redundant, with a one-parameter family of inequalities. | Consistent with section 1, item 6. The statements keep them. |
| 4 | MINOR | Sharpness for general λ and a normalised form (`‖g₃‖₁ = 1`) should be stated; a nonzero amplitude always has `‖g₃‖₁ > 0`. | Planned statement (item 1). The positivity is used by the sanity layer's consistency theorem. |
| 5 | NIT | "Attained" in SPL-A means approximated to any tolerance, not an extremiser. The reflexive pin theorems check nothing about content. | The prose label becomes "sharpness (attained in the limit)". The pins are bookkeeping for the commitment tools and were never evidence. |

What the session did not check, by its own account: compilation; the imported file; the paper proof; the
numerical optimum; attribution.
