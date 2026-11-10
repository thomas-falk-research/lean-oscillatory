/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase
import OscInt.Statements.Cusp

/-!
# Blueprint for batch A3 (S5.1′, S5.1): the parts of the route (definitions only)

Route: `docs/proof-A3.md`. The route is the exact transverse dephasing of the S2/S3 core estimate (L6), with an
order-4 van der Corput estimate in the outer variable and an outer linear term carried through; the unbounded
transverse frequencies are handled by one integration by parts. Each part is proved as
`theorem OscInt.Cusp.<part> : <Prop>` under `OscInt/Cusp/`.
-/

namespace OscInt.Blueprint

open Set MeasureTheory OscInt.Statements
open scoped ContDiff

/-- **A3-P1** Order-4 van der Corput with amplitude, constant `38 = 5·2³ − 2`, uniform in a linear term: the
instance `k = 4` of S1.k, to be proved from S1.3 (not from S1.k). -/
def VdC4Facts : Prop :=
  ∀ (D : ℕ → ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b μ p : ℝ), a ≤ b → 0 < μ →
    DerivChain D 4 a b → (∀ x ∈ Ioo a b, μ ≤ |D 4 x|) → AmplitudeOn ψ ψ' a b →
    ‖oscInt (fun x => D 0 x + p * x) ψ a b‖ ≤ 38 * μ ^ (-(1 : ℝ) / 4) * ampNorm ψ ψ' a b

/-- **A3-P2** Core estimate of order 4 with an outer linear term: under `CoreHyps 4`, for amplitudes supported in
the box, `|I(m(Q + p x), A)| ≤ C M m^{-3/4}` with `C` depending only on `(a, b, μ, ν, D)`, uniformly in `p ∈ ℝ`. -/
def CoreEstimate4Facts : Prop :=
  ∀ (a b μ ν D : ℝ), 0 < a → 0 < b → 0 < μ → 0 < ν →
    ∃ C : ℝ, ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m p : ℝ),
      CoreHyps 4 a b μ ν D Q ys → AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ m →
        ‖oscInt2 (fun k => m * (Q k + p * k.1)) A‖ ≤ C * M * m ^ (-(3 / 4 : ℝ))

/-- Normal point of order 4 (an A3 point in normal coordinates) at the origin: `∂_yΨ(0) = 0`, `∂²_yΨ(0) ≠ 0`,
`∂_x∂_yΨ(0) = 0`, and the reduced quartic `∂⁴_xΨ(0) − 3 (∂²_x∂_yΨ(0))² / ∂²_yΨ(0)` is nonzero. -/
def NormalPoint4 (Ψ : ℝ × ℝ → ℝ) : Prop :=
  fderiv ℝ Ψ 0 (0, 1) = 0 ∧ dd Ψ 0 (0, 1) (0, 1) ≠ 0 ∧ dd Ψ 0 (0, 1) (1, 0) = 0 ∧
    iteratedFDeriv ℝ 4 Ψ 0 ![(1, 0), (1, 0), (1, 0), (1, 0)] -
      3 * ddd Ψ 0 (1, 0) (1, 0) (0, 1) ^ 2 / dd Ψ 0 (0, 1) (0, 1) ≠ 0

/-- **A3-P3** Normalized data of order 4: a `C⁴` family with a normal point of order 4 at `τ₀` satisfies
`CoreHyps 4` with one set of constants on a neighbourhood of `τ₀` (the reduced fourth derivative is continuous). -/
def NormalizedData4Facts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T),
    FamilyCk 4 Q → NormalPoint4 (Q τ₀) →
    ∃ U ∈ nhds τ₀, ∃ a b μ ν D : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : T → ℝ → ℝ, ∀ τ ∈ U, CoreHyps 4 a b μ ν D (Q τ) (ys τ)

/-- **A3-P4** Non-stationary in the second variable: if `|∂_yΦ| ≥ c` and `|∂²_yΦ| ≤ D` on the box, then
`|I(mΦ, A)| ≤ C M / m` for amplitudes supported in the box, with `C` depending only on `(a, b, c, D)`. Nothing is
assumed about the first variable, so a linear term `p x` with any `p` is allowed. -/
def TransverseNonStatFacts : Prop :=
  ∀ (a b c D : ℝ), 0 < a → 0 < b → 0 < c →
    ∃ C : ℝ, ∀ (Φ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m : ℝ), ContDiff ℝ 2 Φ →
      (∀ k ∈ Icc (-a) a ×ˢ Icc (-b) b, c ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D) →
      AmpBound 1 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ m →
        ‖oscInt2 (fun k => m * Φ k) A‖ ≤ C * M / m

/-- **A3-P5** Normalisation at an A3 point: there is a linear automorphism `L` (from the witnesses `v, w`,
`L(u, s) = u v + s w`) such that `φ ∘ L` minus its affine part at `0` has a normal point of order 4. -/
def A3NormalizeFacts : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → IsA3Point φ 0 →
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), NormalPoint4 (fun k => φ (L k) - φ 0 - fderiv ℝ φ 0 (L k))

end OscInt.Blueprint
