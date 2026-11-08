/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Global

/-!
# Blueprint for batch GD (interfaces only)

Route: `docs/proof-GD.md`. Each `…Facts` is proved in its own file by one part; the lead's assemblies use them as
hypotheses (`OscInt/Front/Global.lean`). Nothing here is proved.
-/

namespace OscInt.Blueprint.GD

open OscInt.Statements Filter Topology
open scoped ContDiff

/-- R1. Near a D4 point the bound holds for amplitudes supported in a small ball, uniformly over all linear terms
(FE-S4.1′L moved from `0` to `k₀` by translation). -/
def D4PieceFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (k₀ : ℝ × ℝ), IsOpen U → k₀ ∈ U → ContDiffOn ℝ 4 Ψ U → IsD4Point Ψ k₀ →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall k₀ δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3)

/-- R2a. Smooth bumps: for `ρ > 0` a `C^∞` function with values in `[0, 1]`, equal to `1` on `B̄(k₀, ρ/2)`, with
`tsupport ⊆ B̄(k₀, ρ)` and bounded derivatives of order `≤ 2`. -/
def BumpFacts : Prop :=
  ∀ (k₀ : ℝ × ℝ) (ρ : ℝ), 0 < ρ →
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Metric.closedBall k₀ ρ ∧
      (∀ k ∈ Metric.closedBall k₀ (ρ / 2), χ k = 1) ∧ (∀ k, 0 ≤ χ k ∧ χ k ≤ 1) ∧
      ∃ B : ℝ, ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j χ k‖ ≤ B

/-- R2b. Leibniz: multiplying an amplitude by a `C²` real function with bounded derivatives keeps derivative bounds,
with a constant depending only on the multiplier. -/
def MulBoundFacts : Prop :=
  ∀ (χ : ℝ × ℝ → ℝ) (B : ℝ), ContDiff ℝ 2 χ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j χ k‖ ≤ B) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ), ContDiff ℝ 2 A → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j (fun k => (χ k : ℂ) * A k) k‖ ≤ C * M

/-- R4. Large linear terms are non-critical on a compact set. -/
def LargeLFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)), IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 2 Ψ U →
    ∃ R : ℝ, ∀ L : (ℝ × ℝ) →L[ℝ] ℝ, R ≤ ‖L‖ → ∀ k ∈ K, 1 ≤ ‖fderiv ℝ Ψ k + L‖

/-- R6. The unfolding weight: explicit, exported for T6 and T6L. -/
def UnfoldFacts (η : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ tsupport η ⊆ Metric.closedBall 0 4 ∧ η (Real.pi / 2, Real.pi / 2) = 1 ∧
    ∀ g : ℝ × ℝ → ℂ, Continuous g → (∀ k : ℝ × ℝ, g (k.1 + 2 * Real.pi, k.2) = g k) →
      (∀ k : ℝ × ℝ, g (k.1, k.2 + 2 * Real.pi) = g k) →
      ∫ k in torusBox, g k = ∫ k : ℝ × ℝ, (η k : ℂ) * g k

/-- The four D4 points of `cos k₁ + cos k₂` in `[−4, 4]²`. -/
noncomputable def latticeD4 : Finset (ℝ × ℝ) :=
  {(Real.pi / 2, Real.pi / 2), (-(Real.pi / 2), Real.pi / 2), (Real.pi / 2, -(Real.pi / 2)),
    (-(Real.pi / 2), -(Real.pi / 2))}

/-- R7. The lattice symbol is classified on `B̄(0, 4)` with exceptional set `latticeD4`. -/
def LatticeSymbolFacts : Prop :=
  Classified (fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2) (Metric.closedBall 0 4) latticeD4

/-- R9 data: the translated diagonal phase `φ(κ) = −sin κ₁ − sin κ₂ + κ₁ + κ₂` satisfies F2's hypotheses with
`disc (cubicCoeffs φ) = −1/48`, and `cos (π/2 + κ₁) + cos (π/2 + κ₂) + (π/2 + κ₁) + (π/2 + κ₂) = π + φ κ`. -/
def DiagPhaseFacts : Prop :=
  let φ : ℝ × ℝ → ℝ := fun κ => -Real.sin κ.1 - Real.sin κ.2 + κ.1 + κ.2
  ContDiff ℝ 4 φ ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧ (∀ v w, dd φ 0 v w = 0) ∧ disc (cubicCoeffs φ) = -1 / 48 ∧
    ∀ κ : ℝ × ℝ, Real.cos (Real.pi / 2 + κ.1) + Real.cos (Real.pi / 2 + κ.2) + ((Real.pi / 2 + κ.1) + (Real.pi / 2 + κ.2)) =
      Real.pi + φ κ

end OscInt.Blueprint.GD
