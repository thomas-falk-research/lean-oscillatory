<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch TSD: the checks made before any statement is drafted (2026-11-20)

Written by the lead. The object is Lemma E.1 of the preprint hexagon:2611.00174v1 ("Two-saddle steepest descent
with a uniform remainder"; `docs/design/batch-TSD-opening.md`). Three reports bear on it. The briefs are not
committed and the reports are not reproduced: every finding is in the lead's words (hashes of the briefs in the
session log). Nothing here is machine-checked, and no statement of the batch exists yet.

## 1. Step referee of the published proof (an agent of the lead's model family, fresh context)

Launched 11:15:03Z, finished about 12:07Z. It is of the same model family as the system that wrote the preprint;
its verdict is not independent in that sense. It read the appendix in the TeX source and the definitions it
needed elsewhere in the paper. No Lean, no network.

**Verdict: the lemma is true as printed.** Every displayed formula and every constant of the six steps of the
proof was re-derived: the factorisation and the symmetry; the Taylor bounds and the convexity inequalities; the
contour of five pieces (they join, stay in the strip, and the deformation is justified by the stated decay, which
is needed only below the line); the middle and far bounds; the coefficients of the remainder at the saddle and
every number that comes from the Gaussian moments (`K_A = 4.5 M² + 1.625 M′`, `C₃/8`, `M C₂/2`, `15e/72 ≤ 0.57`,
`2.51` and `1.45`, which the third largeness condition turns into `1` and `0.52`); the completion of the Gaussian
and the factor 2 on the transition term; the assembly of amplitude and phase. Corollaries E.2 and E.3: the
arguments go through.

Numerics, floating point (double precision, 20 and 50 digits where needed; not interval arithmetic): two
quadrature routes per instance (along the line and along the paper's contour), a closed form in the Airy
instance, 1526 random instances that satisfy the lemma's conditions and about twenty chosen ones (near
coalescence, at the edge of each condition, each error term dominant in turn). No violation of the total bound or
of any single term. The bound is attained in the limit: on a constructed instance the ratio of the bound to the
measured error is 1.0017, so the constants of the core term cannot be lowered in general; with an amplitude like
the paper's outer factor the bound is loose by a factor of 20 to 900.

No FATAL and no MAJOR finding.

| # | Severity | Finding (lead's words) | Consequence for the batch |
|---|---|---|---|
| 1 | MINOR | Hypotheses that the lemma states and its main claim does not use: `c′ ≥ 39`; `δ₁ ≤ 1/4` (any `δ₁ < 1/2` serves); the lower bound on `c′ F(0)`; the bound on the Hankel remainder (used only for the absence of zeros of the amplitude, for (E.14) and for a remark); the evenness of `F` and of `h₀` (only the symmetry of the integrand is used); decay below the line beyond integrability on the line (the bounded logarithmic derivative of the amplitude carries it down). | The core statement drops them; the corollary in the lemma's own form keeps the printed hypotheses, so that "as printed" stays exact. |
| 2 | MINOR | Needed and only implicit: the amplitude has no zero on the strip and `M`, `M′` are finite; the conventions `1/M = ∞` when `M = 0`. | The Lean statement takes `A ≠ 0` and the bounds as hypotheses, and takes the window `ℓ` as a parameter with inequalities in place of a minimum, which removes every division by `C₂`, `M`, `M′`. |
| 3 | NIT | Redundancies: the second largeness condition follows from the first (the chord slope is at most the slope at the saddle); the far term never exceeds the middle term; the entries `1` and `v₀` of the window's minimum are implied by others. | The statement may keep them for fidelity; the proof can use them freely. |
| 4 | MINOR | Reach for the paper's own function: with its outer factor the first condition forces `c′` of at least about 46 divided by the chord slope, so at `c′ = 39` the lemma says nothing; at the paper's hand-off point the bound is 1.21 at `c′ = 400`, 0.128 at 4000 and 0.017 at 40000. | A limit of the lemma's use, consistent with "for `c` large" in the paper; recorded, not a finding against the lemma. |
| 5 | NIT | The roundings that a formal proof must budget: `e^{3/2} ≤ 4.5` (0.4 % slack), `15e/72 ≤ 0.57` (0.65 %), `0.5112 ≤ 0.52`, `0.8873 ≤ 1`. | For the blueprint. |

Not checked by the referee: the edge representation that the lemma assumes; the verification of the hypotheses
for the paper's function (its appendix E.4), beyond four constants; the bounds from the Digital Library of
Mathematical Functions behind the Hankel remainder (taken from memory, checked numerically only); that the Hankel
function has no zero in the closed upper half-plane.

### The formal core the referee proposes (mathematics; to be turned into statements)

With `w = b − i/2` the line becomes the real axis. Data: real `c, δ, v₀, α, σ, ℓ, r₁ > 0` and `C₂, C₃, M, M′ ≥ 0`;
`u₀ = ℓ/√2`; the half-strip `S = {Re w ≥ 0, |Im w| ≤ δ}`; `φ` and `A` holomorphic on an open set containing `S`;
`f = e^{cφ} A`; `e = e^{−iπ/4}`.

Hypotheses. (P1) `Re φ = 0` on `[0, ∞)`, so that `φ′ = −i g` there with `g` real. (P2) `φ′(v₀) = 0` and
`φ″(v₀) = −iα`. (P3) `g(v) ≤ −σ (v₀ − v)` on `[0, v₀ − u₀]` and `g(v) ≥ α (v − v₀)` on `[v₀ + u₀, ∞)`. (P4)
`|φ‴| ≤ C₂` and `|φ⁗| ≤ C₃` on `S`. (A1) on `S`: `A ≠ 0`, `|A′/A| ≤ M`, `|(A′/A)′| ≤ M′`. (L) `ℓ ≤ √2 δ`,
`ℓ ≤ v₀`, `C₂ ℓ ≤ α`, `C₂ ℓ ≤ (3/√2) σ`, `M ℓ ≤ 1`, `M′ ℓ² ≤ 1`, `r₁ ≤ ℓ`, `c C₂ r₁³ ≤ 6`. (C) `c u₀ σ ≥ 2M`,
`c α u₀ ≥ 2M`, `c α ≥ 8`.

Part I (estimates only; no symmetry, no decay, no theorem of Cauchy). With

    J₊ = ∫₀^{v₀−u₀} f(v + iu₀) dv + e ∫_{−ℓ}^{ℓ} f(v₀ + r e) dr + ∫_{v₀+u₀}^∞ f(v − iu₀) dv,
    Z  = −i e^{cφ(v₀)} A(v₀) √(2π/(cα)),

the last integrand is integrable and `|e J₊ − Z| ≤ |Z| (ε_core + 2 ε_tr + ε_mid + ε_far)`, where
`K_A = 4.5 M² + 1.625 M′` and

    ε_core = K_A/(cα) + (C₃/8 + M C₂/2 + K_A C₂)/(cα²) + (0.57 + 0.52 M) C₂²/(cα³),
    ε_tr   = 3 e^{Mℓ} e^{−cα r₁²/3} / (√(2π) r₁ √(cα)),
    ε_mid  = 2 e^{M u₀} √(α/(2πc)) e^{−cσ u₀²/4} / (σ u₀),
    ε_far  = √(2/π) e^{M u₀} e^{−cα u₀²/4} / (u₀ √(cα)).

Part II (deformation). If in addition `A` is integrable on `[0, ∞)` and `e f(iu)` is real for `0 ≤ u ≤ u₀`, then
`f` is integrable on `[0, ∞)` and `Re(e ∫₀^∞ f) = Re(e J₊)`: Cauchy's theorem on one trapezoid on each side of
the saddle; the segment on the imaginary axis contributes an imaginary number; the closing segment at `Re w = X`
tends to zero because integrability with a bounded logarithmic derivative forces `A(X) → 0`.

The printed lemma is recovered with `c = c′`, `φ(w) = Φ₀(w + i/2) + (4πi/3) x w`, `A` the amplitude of the lemma
at `b = w + i/2`, `g = (4π/3)(F − x)`, `α = α_x`, `σ = (4π/3) s_ch`, `ℓ` and `r₁` as printed; then
`ĥ₀ = (2πc′/3) P · 2 Re(e ∫₀^∞ f)` with `P = √(2/(πk_x)) e^{−k_x/2}`, and amplitude and phase are the algebra of
the lemma's last step. The Hankel function enters only through the definition of `A`, the two conditions of
Part II and the remark (E.14).

## 2. Prior-art reader (an agent of the lead's model family)

Launched 11:15:03Z, finished about 11:28Z; 30 web queries, 24 fetches, searches of zbMATH Open, of arXiv through a
paper index and of public repositories, and a direct search of the Mathlib sources at the pin. Its log is in the
lead's scratch and is not committed.

- **In print.** The mechanism is textbook: the ordinary two-saddle formula holds while the large parameter times
  the cube of the separation of the saddles is large, and the uniform form goes through Airy functions (Chester,
  Friedman and Ursell; cited from memory by the reader). With every constant it is in print for Bessel functions
  (Krasikov, arXiv:1107.2007, Theorem 15, read; Nemes, arXiv:1309.2209, through a summary) and for the Airy
  function. General one-saddle lemmas with all constants exist (Simonic and Starichkova, arXiv:2105.06821,
  Proposition 1, statement read; Bennett, Howls, Nemes and Olde Daalhuis, arXiv:1710.10073, section 5, read;
  Boyd 1993 and Olver's bounds, not readable). No general two-saddle lemma with a closed-form remainder under
  analyticity in a thin strip was found, and none of the results read implies the lemma. Verdict: classical in
  substance; this quantified general form not found by these queries, with moderate confidence (the three most
  likely sources were not readable; several databases were not searched). Wording to use: "we are not aware of
  this form in the literature"; never "new".
- **Formalised.** Nothing found on steepest descent, the saddle-point method, stationary phase with a remainder
  or Hankel asymptotics in Lean, Isabelle, Coq or HOL Light (the latter two by indirect searches only).
- **Mathlib at the pin** (read in the sources): Cauchy's theorem on rectangles
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` and variants); primitives of holomorphic functions
  on convex sets (`Convex.exists_forall_hasDerivWithinAt`), which covers a strip and gives the trapezoids of
  Part II; a worked shift of a horizontal line in the Fourier transform of the Gaussian; Cauchy estimates; the
  Gaussian integrals. A definition of the Bessel function `J` only; no Hankel function, no asymptotics.
- **The Lean development that the announcement mentions**: not found; the post gives no link and no scope, and
  the preprint's text does not contain the word.

## 3. A report by another model family (run by the owner from the lead's prompt)

Received 2026-11-20 about 11:40Z: a document of 27 pages (SHA-256 147ef74b…0a06e15eb7) and an archive of 26 files
(SHA-256 4698803e…e1529bf9; its own checksum list verifies). **Its check by an agent of the lead's family was
running when this file was written and has no recorded result; until one is recorded here, nothing of the report
is used.** Its claims, unverified: the lemma is true as printed with every constant; an independent derivation,
written before it read the printed proof, with the same decomposition and another core term; 226 instances
searched without a violation; and a theorem about two analytic functions on the whole strip, symmetric under
`z ↦ −z̄`, from which the printed lemma follows, with the amplitude coefficient `(e − 2)(M² + M′)` in place of
`4.5 M² + 1.625 M′` and without the condition `M′ ℓ² ≤ 1`. That theorem and the referee's two parts above are
compatible in shape (whole line with a symmetry against half-line with a reality condition).

## What follows for the batch

No stop gate of the opening note is triggered. Next, in this order: record the result of the check of the
external report; write the prose of the statements (a core statement on two analytic functions, in the whole-line
symmetric form, with the window as a parameter; the printed lemma as a corollary with the Hankel function as a
parameter and the printed constants); register a numeric test; then the Lean statements with a sanity layer and
plants, freeze, blind review, and only then proofs, with the referee's Part I and Part II as the natural
blueprint.
