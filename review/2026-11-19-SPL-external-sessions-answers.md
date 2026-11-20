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

## 6. The fold regime, blind (a fifth session; stage 3 of the batch plan)

Asked: a uniform leading-term approximation of `I(λ, ε) = ∫ a(x) e^{iλ(x³/3 − εx)} dx` near `ε = 0`, with an explicit
remainder. Report (PDF SHA-256 9b28050e…18f5984, archive c8ee6478…565c31ee; in the lead's scratch).

Its result: with `α, β` the two-point interpolation of the amplitude at `±√ε` (at 0 for `ε ≤ 0`) and
`U = 2π [λ^{−1/3} α Ai(−λ^{2/3} ε) − i λ^{−2/3} β Ai′(−λ^{2/3} ε)]`: `|I − U| ≤ 147 ‖a″‖_∞ / λ` for every `λ > 0` and every
real ε, for `a ∈ C_c²`; `(‖a‴‖₁/2 + ‖a″‖_∞)/λ` when the third derivative is integrable; two derivatives are the
least for a class-wide remainder `O(1/λ)`; and no threshold in `λ ε^{3/2}` alone guarantees a relative error of
the two-saddle formula, because the two saddle terms can cancel.

Checked by an agent of the lead's family (brief SHA-256 18e12b90…82049cf): all five claims confirmed; the main
theorem re-derived in full with every constant of its table (16/3, 83/9, 1759/12); the scripts rerun with
byte-identical outputs; a grid of 13 amplitudes of the checker's own found no violation (largest ratio to the
case constants 0.631 against 146.6). No FATAL or MAJOR finding.

| # | Finding or qualification (lead's words) | Answer |
|---|---|---|
| 1 | The lead's brief asked for the range of `λ ε^{3/2}` in which the two-saddle formula has a given relative error. No such range exists for arbitrary amplitudes: for an amplitude equal to 1 near both saddles the two terms cancel at arbitrarily large `λ ε^{3/2}` and the relative error is 1. | Accepted (checker: reproduced numerically for `λ ε^{3/2}` from 8 to 946). A relative statement needs a lower bound on the two-saddle sum as a hypothesis; the report gives that conditional form. |
| 2 | The constant 147 is far from the truth: the checker's scan of the kernel suggests about 1.36 (cases `ε ≤ 0` and small `λ ε^{3/2}`) and 0.96 (large). | Recorded as numerical only. A sharp-constant version is a possible later statement, as for the quadratic phase. |
| 3 | The report's own numerics do not test its main bound (it is the binding bound in none of 216 rows). | The proof carries the claim; the checker re-derived it and tested it separately. |
| 4 | Checker's addition, not refereed: a form with no Airy function, no improper integral and no compact support: for `\|a″\| ≤ M` on `[−T, T]` and `T ≥ 2 max(λ^{−1/3}, √ε₊)`, `\|∫_{−T}^{T} (a − α − βx) e^{iλφ}\| ≤ 164 M/λ` (case constants 41/6, 100/9, 1963/12). | This is the form a Lean statement of stage 3 would take (Mathlib has no Airy function). It needs its own referee before it is used. |

Not checked: the cited Airy remainder bounds beyond numerics; the normal-form theorem cited for a general fold;
most of the report's table of hypotheses.

## 7. A general-phase proof suited to a proof assistant (a sixth session; stage 2)

Asked: a proof of the general-phase bound with the power `α^{−5/2}` that avoids differentiating an inverse map.
Report (PDF SHA-256 d8034823…fc0f72, archive ee2294fe…5b4ee; in the lead's scratch).

Its result: for `φ` of class C³ on ℝ with `φ‴` M-Lipschitz and `φ″ ≥ α > 0` on all of ℝ, `a ∈ C_c²`: remainder at most
`C_F λ^{−3/2}`, `C_F = (14√2/3)(A₂ α^{−3/2} + √2 A₁ √M α^{−2} + (13/12) A₀ M α^{−5/2})`. The proof builds the forward map
`q = x √H`, two auxiliary expressions with the cancellations `D′ = b q²`, `E′ = 5bD − c w q²`, three "derivative
certificates" `j₀, j₁, j₂`, and transports the amplitude by the fundamental theorem of calculus; it lists 17
elementary lemmas.

Checked by an agent of the lead's family (brief SHA-256 0bbf3f35…059d8d): all nine claims re-derived, by hand and
with computer algebra; own numerics on six phases and five amplitudes found no violation; scripts rerun with the
recorded outputs. No FATAL finding.

| # | Severity | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | MAJOR (scope) | The proof uses convexity and the Lipschitz bound outside the hull of the support and the stationary point, in one step (`\|φ‴\|² ≤ 2M(φ″ − α)`). The earlier general-phase result (section 3) assumed convexity on the hull only, so "smaller in every coefficient" compares two different theorems. A sufficient hypothesis: the hull enlarged by `sup \|φ‴\| / M`. Under hull-only convexity the constant is neither proved nor refuted (38,639 random cases; largest ratio 0.9965). | Accepted. A statement of stage 2 by this route must carry the enlarged-region hypothesis in its text, and its blind review must test exactly this. Both results stay in the plan: section 3's for hull-only convexity, this one for the cheaper proof. |
| 2 | MINOR | Its quadratic estimate has the constant `14√2/3 = 6.60`; the best constant for the norm `‖g″‖_∞` is the L¹ norm of the derivative of the kernel of batch SPL, about 2.85 (checker's quadrature), and section 3's `2√π = 3.54` is also better. | Accepted: stage 2 would combine this report's bound on the transported amplitude with the better quadratic estimate. The value 2.85 is numerical only. |
| 3 | MINOR | Its normalisation of the Fresnel integral uses the bound of SPL-K, which is a frozen statement and not yet a theorem here. | Noted as a dependency: stage 2 comes after the proofs of this batch. |
| 4 | MINOR | The scripts test only the final inequality on one amplitude. | The intermediate bounds rest on the proofs, re-derived by the checker, which also tested them numerically (largest ratios 0.36 and 0.23 for the two key bounds). |
| 5 | NIT | The transport step needs one more line (the difference quotient is a positive-weight average); the lemma inventory lacks five supporting items (translation, the bridge between integrals on the line and on intervals, evenisation, extension of a bound by density, the representation of C^{3,1}). | For the blueprint of stage 2. |

Not checked: the report's local estimates for its counterexample to a homotopy shortcut beyond its constants;
anything in Lean (Mathlib names were found by search, nothing compiled).

## 8. Certificates for the supremum of the kernel (a seventh session; for the statement SPL-N)

Report: a bundle of 379 files (archive SHA-256 d11f6929…f848cee1, equal to the value it states). Its claims:
real-variable proofs, with no contour, of `|κ − L/2| ≤ 1/τ³`, `|κ′| ≤ min(1, 1/τ²)`, `|κ″| ≤ min(√(π/2), 1/τ)`, each
coefficient best possible; a second-order certificate method; certificates for `sup |κ| ≤ 3/4` (3 cells),
`≤ 73/100` (4 cells, 10 series terms), `≤ 29/40`, `≤ 657/910`, the last being the least rational with denominator
at most 1000 that bounds the supremum; and one correction to the lead's brief (the power series quoted there is
valid for `x ≥ 0` only; on the line its quadratic term is `(iL/2) x|x|`), which is right.

Checked by an agent of the lead's family (brief SHA-256 a88bc4a9…644e39de): all four claims confirmed. The proofs
were re-derived step by step and stay inside integration by parts on bounded intervals, absolutely convergent
limits, dominated convergence, Tonelli and the Gaussian integral; the verifier was read line by line and passes
on the four certificates; the checker's own exact-arithmetic code agrees on all four and rechecked all 16,304
exclusion bins of the minimality proofs. No FATAL or MAJOR finding.

| # | Finding (lead's words) | Answer |
|---|---|---|
| 1 | The bundle's certificates are fragile: their smallest margins are 1.3 · 10⁻⁵, 1.2 · 10⁻⁶, 2.4 · 10⁻⁵ and 9.7 · 10⁻¹¹, and all four fail if its correlated Taylor remainder is replaced by the simpler sum of two remainders, or if the weaker bounds `\|κ″\| ≤ 2/τ` and tail constant 4 are used. | Accepted: they are not what a Lean proof should follow. The checker built four sturdier certificates with the simpler remainder, margins of about 10⁻³ and only `1.7724 < √π < 1.7725`: two for the weak bounds (5 cells for 3/4, 7 cells for 73/100) and two for the sharp bounds (3 and 4 cells). Their data are in the lead's scratch (SHA-256 b6a55f83…c067f55d) and will be committed with the statement SPL-N when it is prepared. |
| 2 | The claimed minimal numbers of series terms hold only at the minimal number of cells (a certificate for 29/40 with 5 cells and 14 terms exists). | Noted; no claim of this repository depends on those minima. |
| 3 | Its verifier's routine for the term minima checks less than its proof says, although the data satisfy the missing conditions. | Noted. |

Consequence for the plan: SPL-N is to be stated with 73/100 (or 3/4), proved through one of the checker's
certificates; which one depends on how the limit of the Fresnel primitive is proved in Lean.

## 9. Sharp constants for every order of the expansion (an eighth session; a research attempt)

Report: a bundle of 184 files (archive SHA-256 262d8939…ece5b20). Its claims: for every `N ≥ 1` an exact identity
for the remainder after `N` terms with a kernel `κ_N` defined by absolutely convergent real integrals, and the
best constant `K_N = sup |κ_N|` for the norm `‖g^{(2N+1)}‖₁`; a positive product formula for the moduli of the
kernels; the supremum is attained at the first positive critical point, for every `N`; `K_1 … K_8` with exact
certificates; an asymptotic law `K_N = (√(2π)/(2^{N+1} N!)) (ρ + β/N + O(N⁻²))` with explicit `ρ = 1.0694…`,
`β = 0.0939…`; the dual constants for the norm `‖g^{(2N)}‖_∞`.

Checked by an agent of the lead's family (brief SHA-256 5c3bdf31…38f12c5): seven claims re-derived, the dual
constants confirmed numerically only. The identity was tested on 27 cases for `N = 1, 2, 3`; the product formula
to 34 digits; "first maximum is global" for `N ≤ 10` and for `N = 20, 50, 100, 300` (later local maxima reach at
most 93.5 % of the first); the asymptotic law by extrapolation up to `N = 12800`; the eight constants by the
checker's own 60-digit computation. For `N = 1` its kernel is the kernel of this batch. No FATAL or MAJOR finding.

What matters for this repository: (i) the identity for general `N` is the computation of `N = 1` repeated by
induction, `R_N = R_{N−1} − 2 B_{N−1} g^{(2N−2)}(0)`, with no product formula and no geometry; (ii) the certificates
for `N ≤ 8` do not depend on the product formula, contrary to the bundle's own dependency list; (iii) the checker
wrote the N-term statement in a form that could be frozen. Not checked: the bundle's literature log, and so any
question of novelty; the sharpness construction for the dual constants. Nothing of this is claimed as new here.

## 10. Several variables (a ninth session; a research attempt, for the roadmap's two-variable leading term)

Report: a package of 279 files (archive SHA-256 cd99ea12…11d7626a, equal to the value it states). Its claims: for
a diagonal quadratic form in `n` variables and every `λ > 0`, the remainder after the leading term is at most an
explicit constant times `λ^{−n/2−1}` times a sum of `n` mixed derivative norms `‖∂_j³ ∏_{k≠j} ∂_k g‖₁`, by applying the
one-variable results coordinate by coordinate; total order `n + 2` cannot be lowered; for `n = 2` the constant
`(3/8)(√(π/2) + 7/4)`; a rotation-invariant version; a comparison with the Fourier-side bound and with an `H⁴`
bound. It says itself that the best constant of the uniform two-variable bound is not determined.

Checked by an agent of the lead's family (brief SHA-256 678887c5…82b7f912): all six claims re-derived; the
checker's own numerics in two variables (five amplitudes, diagonal, strongly anisotropic and rotated matrices,
`λ` from 0.001 to 1000) found no violation: largest ratio 0.455 for generic amplitudes, 0.9924 for a near-extremal
product.

| # | Severity | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | MAJOR (usability, not correctness) | The package's own target for formalisation cannot be frozen as written: its class is an abstract completion, and its constants 3/4 and 7/4 rest on a certificate in Python and on analytic lemmas that this repository does not have. | Accepted. The checker's form is the one to use: `ContDiff ℝ 4` with compact support first; the constants 7/8 (SPL-K) and a bound `J₀ = 11/5` for the Fresnel primitive; symmetric form `(7/16)(√(π/2) + 11/5) λ⁻² (‖g_xxxy‖₁ + ‖g_xyyy‖₁)` for unit moduli. It needs six one-variable lemmas beyond SPL-K, listed in the checker's report (the bound of the full oscillatory integral by `‖f′‖₁`, the trace identity, the negative phase, Fubini on sections). |
| 2 | MINOR | The proof of the main theorem is a sketch at the exchange of integrals; the checker completed it and says which integrability each step needs. | For the blueprint of that later batch. |
| 3 | MINOR | The package's checks are mostly arithmetic identities, and its numerics do not exercise the dependence on the eigenvalues. | The claims rest on the proofs, re-derived by the checker, and on the checker's numerics. |

## 11. Where the plan stands after nine sessions

Frozen and blind-reviewed: SPL-I, SPL-S, SPL-K, SPL-A (the proofs are next). Candidates for later freezes, each
resting on a result that another model family proved on paper and an agent of the lead's family re-derived, none
machine-checked and none refereed by a human: SPL-N (section 8); a front end for compactly supported amplitudes,
the negative phase, sharpness for every λ (section 5); the N-term expansion (section 9); a general convex phase
(sections 3 and 7); the fold with a finite-interval, Airy-free statement (section 6); two variables (section 10).
