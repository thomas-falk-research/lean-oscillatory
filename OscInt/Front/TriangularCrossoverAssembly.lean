/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayUpper

/-!
# Batch A5U: the lead's assembly of `TriCrossoverUpperStatement` against the blueprint interfaces

Route `stmts/proof-A5U-draft.md`, section 5. Stage A gives the window bound at `k* = (θ₀, −θ₀)`
(A1–A3 → A4, A5–A11 → A12a → A12); every A5 point of `triPhase a₀` is `σ k* + 2πj` (TRI-X,
`OscInt.API.triA5Locus`), so A13 moves the window bound there. Every other point has a `t^{−3/4}` bound uniform in
`α` (B1 → B2), which is at most the weight for `|α − a₀| ≤ 1` (A7(i)). B3 patches the local bounds over the torus
with the weight `W α t = t^{−2/3} E(|α − a₀| t^{1/3})`.
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.A5U
open scoped ContDiff

/-- `cos (σ x + 2π j) = cos x` for `σ = ±1`. -/
theorem cos_sigma_add (σ x : ℝ) (j : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Real.cos (σ * x + 2 * Real.pi * j) = Real.cos x := by
  rw [show σ * x + 2 * Real.pi * j = σ * x + (j : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  rcases hσ with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, Real.cos_neg]

/-- `triPhase α` is invariant under `κ ↦ σ κ + 2π j`, `σ = ±1`. -/
theorem triPhase_sigma (α σ : ℝ) (j₁ j₂ : ℤ) (hσ : σ = 1 ∨ σ = -1) (κ : ℝ × ℝ) :
    triPhase α (σ • κ + (2 * Real.pi * j₁, 2 * Real.pi * j₂)) = triPhase α κ := by
  simp only [triPhase, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [cos_sigma_add σ κ.1 j₁ hσ, cos_sigma_add σ κ.2 j₂ hσ,
    show σ * κ.1 + 2 * Real.pi * j₁ + (σ * κ.2 + 2 * Real.pi * j₂) =
      σ * (κ.1 + κ.2) + 2 * Real.pi * ((j₁ + j₂ : ℤ) : ℝ) by push_cast; ring,
    cos_sigma_add σ (κ.1 + κ.2) (j₁ + j₂) hσ]

/-- The amplitude bound forces `0 ≤ M`. -/
theorem ampBound_nonneg {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (hA : AmpBound 2 K A M) : 0 ≤ M :=
  le_trans (norm_nonneg _) (hA.2.2 0 (by norm_num) 0)

/-- The local hypothesis of B3 at an A5 point of `triPhase a₀`: the window bound (A12) moved by A13. -/
theorem local_a5 (hW : A5WindowLocalBound) (hT : LocalTransferFacts) {a₀ : ℝ} (ha₀ : |a₀| = triExceptional)
    {k₀ : ℝ × ℝ} (hk : IsA5Point (triPhase a₀) k₀) :
    ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * crossWeight a₀ α t := by
  obtain ⟨δ, hδ, r, hr, C, hC⟩ := hW a₀ ha₀
  obtain ⟨-, j₁, j₂, hk'⟩ := OscInt.API.triA5Locus a₀ k₀ hk
  -- `k₀ = σ k* + 2π j`
  obtain ⟨σ, hσ, hkσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      k₀ = σ • a5Centre a₀ + (2 * Real.pi * j₁, 2 * Real.pi * j₂) := by
    rcases hk' with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h]; ext <;> simp [a5Centre, a5Theta]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h]; ext <;> simp [a5Centre, a5Theta]
  refine ⟨δ, hδ, r, hr, C, fun α hα A M y t hA ht => ?_⟩
  have hφ : ∀ κ, (fun κ => t * triPhase α κ) (σ • κ + (2 * Real.pi * j₁, 2 * Real.pi * j₂)) =
      (fun κ => t * triPhase α κ) κ := fun κ => by
    simp only [triPhase_sigma α σ j₁ j₂ hσ κ]
  have hloc : ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ), AmpBound 2 (Metric.closedBall (a5Centre a₀) δ) A M →
      ‖oscInt2 (fun κ => (fun κ => t * triPhase α κ) κ + lin y κ) A‖ ≤ (C * crossWeight a₀ α t) * M :=
    fun A M y hA => by
      have := hC α hα A M y t hA ht
      calc _ ≤ C * M * crossWeight a₀ α t := this
        _ = (C * crossWeight a₀ α t) * M := by ring
  have hA' : AmpBound 2 (Metric.closedBall (σ • a5Centre a₀ + (2 * Real.pi * j₁, 2 * Real.pi * j₂)) δ) A M := by
    rw [← hkσ]; exact hA
  have := hT (fun κ => t * triPhase α κ) (a5Centre a₀) (2 * Real.pi * j₁, 2 * Real.pi * j₂) σ δ
    (C * crossWeight a₀ α t) hσ hφ hloc A M y hA'
  calc _ ≤ (C * crossWeight a₀ α t) * M := this
    _ = C * M * crossWeight a₀ α t := by ring

/-- The local hypothesis of B3 at a point that is not an A5 point of `triPhase a₀`: B2's `t^{−3/4}` bound,
weakened to the weight by A7(i) on `|α − a₀| ≤ 1`. -/
theorem local_rest (hE : CrossEnvelopeFacts) (hB : ComplementLocalBound) {a₀ : ℝ} (ha₀ : a₀ ≠ 0)
    {k₀ : ℝ × ℝ} (hk : ¬ IsA5Point (triPhase a₀) k₀) :
    ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * crossWeight a₀ α t := by
  obtain ⟨δ, hδ, ρ, hρ, C, hC⟩ := hB a₀ ha₀ k₀ hk
  refine ⟨δ, hδ, min ρ 1, lt_min hρ one_pos, max C 0, fun α hα A M y t hA ht => ?_⟩
  have hM := ampBound_nonneg hA
  have hαρ : |α - a₀| ≤ ρ := hα.trans (min_le_left _ _)
  have hα1 : |α - a₀| ≤ 1 := hα.trans (min_le_right _ _)
  have henv := hE.1 |α - a₀| t (abs_nonneg _) hα1 ht
  have hp : 0 ≤ t ^ (-(3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4) := hC α hαρ A M y t hA ht
    _ ≤ max C 0 * M * t ^ (-(3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) hp
    _ ≤ max C 0 * M * crossWeight a₀ α t :=
        mul_le_mul_of_nonneg_left henv (mul_nonneg (le_max_right _ _) hM)

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.A5U
open scoped ContDiff

/-- **A5U** `TriCrossoverUpperStatement` from the parts A1–A13 (with A12a) and B1–B3, TRI-X and K2's periodicity
lemmas. -/
theorem triCrossoverUpper_of (h1 : LevelCrossingFacts) (h2 : AmpNormRestrictFacts) (h3 : PiecewiseVdCFacts)
    (h4 : CoreEstimateMultiFacts) (h5 : EvenJetTaylorFacts) (h6 : JetSeparationFacts) (h7 : CrossEnvelopeFacts)
    (h8 : A5FixedChartFacts) (h9 : A5BaseDataFacts) (h10 : PerturbLongitudinalFacts) (h11 : A5TiltJetFacts)
    (h12a : A5CoreWindowFacts) (h12 : A5WindowLocalFacts) (h13 : LocalTransferFacts)
    (hB1 : ReducedOrderBoundParamFacts) (hB2 : ComplementLocalFacts) (hB3 : TorusPatchParamFacts) :
    TriCrossoverUpperStatement := by
  -- Stage A: the window bound at `k*`
  have hW : A5WindowLocalBound :=
    h12 h8 (h12a (h4 (h3 h1 h2)) h5 h6 h7 h8 (h9 h8) h10 (h11 h8))
  -- Stage B: the complement
  have hR : ComplementLocalBound := hB2 hB1
  intro a₀ ha₀
  have ha₀0 : a₀ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at ha₀
    exact (OscInt.API.TriDeriv.triExceptional_pos).ne ha₀
  have hloc : ∀ k₀ : ℝ × ℝ, ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * crossWeight a₀ α t := by
    intro k₀
    by_cases hk : IsA5Point (triPhase a₀) k₀
    · exact local_a5 hW h13 ha₀ hk
    · exact local_rest h7 hR ha₀0 hk
  obtain ⟨r, hr, C, hC⟩ := hB3 triPhase (fun α t => crossWeight a₀ α t) a₀
    (fun α => (OscInt.API.TriDeriv.triPhase_smooth α).continuous)
    (fun α k => OscInt.K2.TriDecayUpperAux.triPhase_per₁ α k)
    (fun α k => OscInt.K2.TriDecayUpperAux.triPhase_per₂ α k) hloc
  refine ⟨r, hr, C, fun α t n hα ht => ?_⟩
  have := hC α hα t n ht
  calc ‖triKernel α t n‖ ≤ C * crossWeight a₀ α t := this
    _ = C * t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3)) := by
        rw [crossWeight, mul_assoc]

end OscInt.A5UAux
