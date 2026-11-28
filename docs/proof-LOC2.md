<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route of batch LOC2 (K2-FQ)

Written by the lead after the blind pre-proof review (answers `review/2026-11-28-SPLN-A5U-LOC2-preproof-answers.md`, stamped `stamps/20261128T154444Z-e9c0ea9fb732`). Source: the external packet of 2026-11-28 (localisation work
package), re-derived by the lead (`review/2026-11-28-postK2-packet-answers.md`, section 4). Mathlib names are
`#check`ed at the pin in `MathlibNames.lean` before any part is proved.

Given χ (C², `tsupport χ ⊆ (−π, π)²`), Ψ, t, p, B. Round coordinatewise `tp = j + ρ`, `j ∈ ℤ²`, `ρ ∈ [−1/2, 1/2]²`
(as K2's torus expansion does with `rep`). Put `h(k) = χ(k) e^{iρ·k}`; it is C², vanishes near the boundary of the
box, and its biperiodic extension is C². Normalised coefficients `ĥ(n) = (2π)^{−2} ∫_box h e^{−in·k}`.

| Part | Content | Reuse |
|---|---|---|
| Q1 | `(1 + \|n\|²) ĥ(n) = ĝ(n)` with `g = (1 − Δ)h`, by two integrations by parts per coordinate (boundary terms vanish: compact support inside the open box) | C² variant of `OscInt.K2…ibp` (`TriangularDecayFourier.lean`, stated there for `Good` = C^∞ ∧ compact support) |
| Q2 | Bessel: `Σ_n \|ĝ(n)\|² ≤ (2π)^{−2} ∫_box \|g\|²` | Mathlib Parseval/Bessel on `UnitAddTorus` (`mFourierBasis` or `tsum_sq_mFourierCoeff`; to be `#check`ed), through K2's `lift` and `mFourierCoeff_lift` |
| Q3 | `Σ_n (1 + \|n\|²)^{−2} ≤ 13`: shells `‖n‖∞ = m` have `8m` points and `\|n\|² ≥ m²`; `1 + 8 Σ m^{−3} ≤ 1 + 8·(3/2)` | elementary (`summable` over ℤ²) |
| Q4 | Cauchy–Schwarz: `Σ \|ĥ(n)\| ≤ √13 ‖g‖₂ ≤ 4 ‖g‖₂` | `tsum` Cauchy–Schwarz (Mathlib `tsum_mul_le…` / `inner_le_norm_mul_norm` on `ℓ²`) |
| Q5 | `g = e^{iρ·k}[(1 + \|ρ\|²)χ − 2iρ·∇χ − Δχ]`, so `‖g‖₂ ≤ (3/2)‖χ‖₂ + ‖∂₁χ‖₂ + ‖∂₂χ‖₂ + ‖Δχ‖₂` (Minkowski, `\|ρ\|² ≤ 1/2`, `2\|ρᵢ\| ≤ 1`) | product and chain rules for `fderiv`, `iteratedFDeriv` of order 2 |
| Q6 | Absolutely summable coefficients and continuity give `h = Σ ĥ(n) e^{in·k}` on the box; exchange sum and integral; each term `ĥ(n) ∫ e^{itΨ + i(n + j)·k}` is at most `\|ĥ(n)\| B` | K2's `hasSum_amp`, `continuous_lift` (continuity + summability only) |

Assembly: `|∫ χ e^{it(Ψ + p·k)}| = |Σ ĥ(n) ∫ e^{itΨ + i(n+j)·k}| ≤ B Σ|ĥ(n)| ≤ 4 B ‖g‖₂ ≤ locConstC2 χ · B`. Note
`B ≥ 0` follows from the hypothesis (a norm is at most B).

Risks: Q1 for C² (the K2 lemma is for C^∞; its proof uses only one derivative per integration by parts and compact
support, so a C¹ version should go through); Q2's Mathlib API on `UnitAddTorus`; the identification of the box
integral with the torus integral (K2 already does this in `mFourierCoeff_lift`).

## Revision after the route referee (2026-11-28; `review/2026-11-28-SPLN-LOC2-route-answers.md`)

- Notation: this page writes `j` for the rounded integer and `n` for the coefficient index; the blueprint
  `Blueprint/TorusLocalizationC2.lean` and the assembly use them the other way round.
- Q2 is stated for every continuous g on the box (it need not vanish on the boundary), so K2's `lift` (which needs
  support inside the open box) cannot be reused. As proved (agent QB, `OscInt/Front/TorusLocalizationC2Fourier.lean`):
  a lift through `MeasureTheory.measurableEquivPiIoc`, membership in L², Mathlib's
  `UnitAddTorus.hasSum_sq_mFourierCoeff`, box–torus identities for the coefficients and for `∫ |g|²`, and the null set
  between `Ioc²` and `Icc²`.
- Q4 as proved uses the weighted inequality `8Xwa ≤ X²w² + 16a²` (constant 29/8 ≤ 4) instead of Cauchy–Schwarz.
- Q1 as proved (agent QA, `OscInt/Front/TorusLocalizationC2Ibp.lean`): a C¹ integration by parts on ℝ² applied twice,
  the box integral equal to the integral over ℝ² by the support condition, and `iteratedFDeriv_two_apply` for the
  Laplacian. Q5 as proved: the product rule, a pointwise bound and Minkowski on the box from Hölder.
- Q6 as proved: K2's `torusExpansion` argument with `Continuous χ`.
