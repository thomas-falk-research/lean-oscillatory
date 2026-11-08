/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.D4.Final

/-!
# S4.1 non-vacuity (from the adversarial review, `review/2026-11-06-S4-adversarial.md`, MINOR 4)

`ampBound_exists_delta`: for every `δ > 0` there is an amplitude with `AmpBound 2 (closedBall 0 δ) A M` and
`A 0 = 1`, so the class of amplitudes in S4.1 is nonempty for whatever `δ` the theorem produces (the pre-proof NIT
"amplitudes for every δ"). `d4Bound_instance_cubes` applies `OscInt.d4Bound` to `x³ + y³` with such an amplitude.
Lemma and instance written by the adversarial reviewer (scratch file), adapted by the lead.
-/

namespace OscInt.D4

open OscInt.Statements
open scoped ContDiff


/-- For every δ > 0 there is a nonzero amplitude admissible in S4.1. -/
theorem ampBound_exists_delta (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M ∧ A 0 = 1 := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let A : ℝ × ℝ → ℂ := fun k => (b k : ℂ)
  have hA : ContDiff ℝ ∞ A := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hs : Function.support A = Function.support b := by ext k; simp [A]
  have hsupp : tsupport A ⊆ Metric.closedBall 0 δ := by
    rw [tsupport, hs, ← tsupport, b.tsupport_eq]
  have hcs : HasCompactSupport A :=
    HasCompactSupport.intro (isCompact_closedBall 0 δ) fun k hk => image_eq_zero_of_notMem_tsupport
      (fun h => hk (hsupp h))
  choose B hB using fun j : ℕ =>
    ((hA.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      (hcs.iteratedFDeriv j).norm)
  refine ⟨A, ∑ j ∈ Finset.range 3, max (B j) 0,
    ⟨hA.of_le (WithTop.coe_le_coe.mpr le_top), hsupp, fun j hj k => ?_⟩, ?_⟩
  · calc ‖iteratedFDeriv ℝ j A k‖ ≤ max (B j) 0 := (hB j ⟨k, rfl⟩).trans (le_max_left _ _)
      _ ≤ ∑ i ∈ Finset.range 3, max (B i) 0 :=
        Finset.single_le_sum (f := fun i => max (B i) 0) (fun i _ => le_max_right _ _)
          (Finset.mem_range.mpr (by omega))
  · simp only [A]
    rw [b.one_of_mem_closedBall (by simp [b]; positivity)]
    simp

/-- Non-vacuity on the `x³ + y³` instance: the `δ` produced by `d4Bound` admits a nonzero amplitude, and the
constant satisfies `0 ≤ C * M`. -/
theorem d4Bound_instance_cubes : ∃ δ > 0, ∃ C : ℝ, ∃ A : ℝ × ℝ → ℂ, ∃ M : ℝ, AmpBound 2 (Metric.closedBall 0 δ) A M ∧ A 0 = 1 ∧
    0 ≤ C * M ∧ ∀ (y : ℝ × ℝ) (t : ℝ), 1 ≤ t →
      ‖oscInt2 (fun κ => t * (κ.1 ^ 3 + κ.2 ^ 3) + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3) := by
  obtain ⟨h1, h2, -, h4⟩ := sanity_D4_hyps
  obtain ⟨δ, hδ, C, hC⟩ := OscInt.d4Bound _ h1 h2 (by rw [h4]; norm_num)
  obtain ⟨A, M, hA, hA0⟩ := ampBound_exists_delta δ hδ
  refine ⟨δ, hδ, C, A, M, hA, hA0, ?_, fun y t ht => hC A M y t hA ht⟩
  have := hC A M 0 1 hA le_rfl
  simp at this
  exact (norm_nonneg _).trans this

end OscInt.D4
