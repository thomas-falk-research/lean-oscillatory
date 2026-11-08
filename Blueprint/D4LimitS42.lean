/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4Limit

/-!
# Blueprint for S4.2 (definitions only)

Route: `docs/proof-S42.md`. New parts E1–E3, proved as `theorem OscInt.D4.<part> : <Prop>` under `OscInt/D4/`; the
assembly `OscInt.D4.d4Limit_of` (`OscInt/D4/LimitAssembly.lean`) also uses the S4.1′ parts and the S4.3 results.
-/

namespace OscInt.Blueprint

open Set MeasureTheory Filter Topology OscInt.Statements
open scoped ContDiff

/-- **E1** Polar evaluation: for `disc q ≠ 0` and an even smooth compactly supported cut-off `χ` equal to `1` on
`B̄(0, 1)`, `∫ e^{iC(w)} χ(w/R) dw → c_C` as `R → ∞` (given the S4.3 facts used in the route). -/
def CubicCutoffLimitFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 →
    Tendsto cosMomentPartial atTop (𝓝 cosMoment) →
    IntervalIntegrable (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) volume 0 (2 * Real.pi) →
    ∀ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z, χ (-z) = χ z) → (∀ z, ‖z‖ ≤ 1 → χ z = 1) →
      Tendsto (fun R : ℝ => oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ))) atTop
        (𝓝 ((d4Constant q : ℝ) : ℂ))

/-- **E2** Inner limit (dominated convergence): for a jointly continuous family of phases, a continuous compactly
supported `B` and a continuous `A`, `∫ e^{iΨ_s} B · A(s ·) → A(0) ∫ e^{iΨ₀} B` as `s → 0`. -/
def InnerLimitFacts : Prop :=
  ∀ Ψ : ℝ → ℝ × ℝ → ℝ, Continuous (fun p : ℝ × (ℝ × ℝ) => Ψ p.1 p.2) →
    ∀ B : ℝ × ℝ → ℂ, Continuous B → HasCompactSupport B → ∀ A : ℝ × ℝ → ℂ, Continuous A →
      Tendsto (fun s : ℝ => oscInt2 (Ψ s) (fun w => B w * A (s • w))) (𝓝 0) (𝓝 (oscInt2 (Ψ 0) B * A 0))

/-- **E3** Dyadic tail at scale `ρ = R t^{-1/3}`: the number `N` of annuli up to `δ`, their scales
`ε_{j+1} = 2^{j+1} ρ` (`j < N`) stay below `2δ`, and `∑_{j<N} ε_{j+1}² (t ε_{j+1}³)^{-5/6} ≤ 3 R^{-1/2} t^{-2/3}`. -/
def DyadicTailFacts : Prop :=
  ∀ t R δ : ℝ, 0 < t → 1 ≤ R → 0 < δ →
    ∃ N : ℕ, δ ≤ 2 ^ N * (R * t ^ (-(1 : ℝ) / 3)) ∧
      (∀ j : ℕ, j < N → 2 ^ (j + 1) * (R * t ^ (-(1 : ℝ) / 3)) < 2 * δ) ∧
      ∑ j ∈ Finset.range N, (2 ^ (j + 1) * (R * t ^ (-(1 : ℝ) / 3))) ^ 2 *
          (t * (2 ^ (j + 1) * (R * t ^ (-(1 : ℝ) / 3))) ^ 3) ^ (-(5 : ℝ) / 6) ≤
        3 * R ^ (-(1 : ℝ) / 2) * t ^ (-(2 : ℝ) / 3)

/-! ## E1 split (route referee, `review/2026-11-06-S42-proof-route.md`, MINOR 2–3 and §3) -/

/-- **E1a** Radial identity: for a `C¹` profile `ψ` equal to `1` on `[0, 1]` and `0` on `[K, ∞)`,
`λ^{2/3} ∫₀^K cos(λ r³) ψ(r) r dr = −(1/3) ∫₁^K ψ′(ρ) · cosMomentPartial(λ ρ³) dρ`. -/
def RadialIdentityFacts : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ K : ℝ, 1 ≤ K → (∀ r ∈ Icc (0 : ℝ) 1, ψ r = 1) → (∀ r, K ≤ r → ψ r = 0) →
    ∀ l : ℝ, 0 < l →
      l ^ ((2 : ℝ) / 3) * ∫ r in (0 : ℝ)..K, Real.cos (l * r ^ 3) * ψ r * r =
        -(1 / 3) * ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (l * ρ ^ 3)

/-- **E1b** Polar reduction: for an even cut-off vanishing outside the max-norm ball of radius `K₀`, the integral
is real and equals an iterated polar integral (θ outer, `r ≤ 2K₀R`). -/
def PolarReductionFacts : Prop :=
  ∀ (q : ℝ × ℝ × ℝ × ℝ) (χ : ℝ × ℝ → ℝ), Continuous χ → (∀ z, χ (-z) = χ z) →
    ∀ K₀ : ℝ, 0 < K₀ → (∀ z, K₀ ≤ ‖z‖ → χ z = 0) → ∀ R : ℝ, 0 < R →
      oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ)) =
        (((∫ θ in (-Real.pi)..Real.pi, ∫ r in (0 : ℝ)..(2 * K₀ * R),
            Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r) : ℝ) : ℂ)

/-- **E1c** The zeros of the cubic on the circle form a null set. -/
def CircleZerosNullFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → volume {θ : ℝ | circleCubic q θ = 0} = 0

/-- **E1d** E1 from E1a–E1c (rescaling `r = Rρ`, uniform bounds, dominated convergence in `θ`, periodicity). -/
def CubicCutoffLimitCombineFacts : Prop :=
  RadialIdentityFacts → PolarReductionFacts → CircleZerosNullFacts → CubicCutoffLimitFacts

end OscInt.Blueprint
