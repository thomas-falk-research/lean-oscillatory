/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayPatch

/-!
# Batch A5U, part B3: `TorusPatchParamFacts`

Route: `stmts/proof-A5U-draft.md`, section 5. A clone of `OscInt.K2.torusPatch`
(`OscInt/Front/TriangularDecayPatch.lean`) for a family `Ψ α` with a weight `W α t`:

* T1 (`OscInt.API.torusUnfold`) gives the cutoff `η`, independent of `α`;
* one finite subcover of `tsupport η` by the balls `ball k_j δ_j` of the local hypothesis, and one smooth partition
  of unity `χ_j` subordinate to it, so the pieces `χ_j η` and their bounds `M_j` do not depend on `α`;
* `r = min (1, min_j ρ_j) > 0`; for `|α − α₀| ≤ r` every local bound applies, and the sum of the pieces gives
  `(Σ_j C_j M_j) W α t`.
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint
open scoped ContDiff

/-- A positive lower bound for finitely many positive numbers (`min (1, min_i ρ_i)`). -/
theorem a5uG3_exists_pos_le {ι : Type*} (s : Finset ι) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ r > 0, ∀ i ∈ s, r ≤ ρ i := by
  have hne : (insert (1 : ℝ) (s.image ρ)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert (1 : ℝ) (s.image ρ)).min' hne, ?_, fun i hi => ?_⟩
  · have hm := Finset.min'_mem _ hne
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]; norm_num
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      rw [← hj]; exact hρ j
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ρ hi))

/-- The summation step of the torus patch for one phase `Φ`: if the cutoff `η` of T1 splits as `Σ_i A_i` into
compactly supported continuous pieces with `‖oscInt2 (tΦ + n·k) A_i‖ ≤ B_i w`, the box integral is at most
`(Σ_i B_i) w`. -/
theorem a5uG3_sum_bound {ι : Type*} [Fintype ι] (Φ : ℝ × ℝ → ℝ) (hΦ : Continuous Φ)
    (hΦ1 : ∀ k : ℝ × ℝ, Φ (k.1 + 2 * Real.pi, k.2) = Φ k) (hΦ2 : ∀ k : ℝ × ℝ, Φ (k.1, k.2 + 2 * Real.pi) = Φ k)
    (η : ℝ × ℝ → ℝ)
    (hunf : ∀ g : ℝ × ℝ → ℂ, Continuous g → (∀ k : ℝ × ℝ, g (k.1 + 2 * Real.pi, k.2) = g k) →
      (∀ k : ℝ × ℝ, g (k.1, k.2 + 2 * Real.pi) = g k) → ∫ k in torusBox, g k = ∫ k : ℝ × ℝ, (η k : ℂ) * g k)
    (A : ι → ℝ × ℝ → ℂ) (hsum : ∀ k, (η k : ℂ) = ∑ i, A i k) (hAc : ∀ i, Continuous (A i))
    (hAs : ∀ i, HasCompactSupport (A i)) (t : ℝ) (n : ℤ × ℤ) (B : ι → ℝ) (w : ℝ)
    (hB : ∀ i, ‖oscInt2 (fun κ => t * Φ κ + lin ((n.1 : ℝ), (n.2 : ℝ)) κ) (A i)‖ ≤ B i * w) :
    ‖∫ k in torusBox, Complex.exp (↑(t * Φ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤
      (∑ i, B i) * w := by
  set y : ℝ × ℝ := ((n.1 : ℝ), (n.2 : ℝ)) with hy
  set g : ℝ × ℝ → ℂ := fun k =>
    Complex.exp (↑(t * Φ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I) with hg
  have hgc : Continuous g := by fun_prop
  have hg1 : ∀ k : ℝ × ℝ, g (k.1 + 2 * Real.pi, k.2) = g k := by
    intro k
    have e : t * Φ (k.1 + 2 * Real.pi, k.2) + ((n.1 : ℝ) * (k.1 + 2 * Real.pi) + (n.2 : ℝ) * k.2) =
        t * Φ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2) + (n.1 : ℝ) * (2 * Real.pi) := by
      rw [hΦ1 k]; ring
    simp only [hg]
    rw [e, OscInt.K2.TorusPatchAux.exp_add_two_pi_int]
  have hg2 : ∀ k : ℝ × ℝ, g (k.1, k.2 + 2 * Real.pi) = g k := by
    intro k
    have e : t * Φ (k.1, k.2 + 2 * Real.pi) + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * (k.2 + 2 * Real.pi)) =
        t * Φ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2) + (n.2 : ℝ) * (2 * Real.pi) := by
      rw [hΦ2 k]; ring
    simp only [hg]
    rw [e, OscInt.K2.TorusPatchAux.exp_add_two_pi_int]
  have hsplit : ∀ k, (η k : ℂ) * g k = ∑ i, Complex.exp (↑(t * Φ k + lin y k) * Complex.I) * A i k := by
    intro k
    have hlin : lin y k = (n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2 := rfl
    rw [hsum k, ← Finset.mul_sum, hlin, mul_comm]
  have hint : ∀ i, Integrable (fun k => Complex.exp (↑(t * Φ k + lin y k) * Complex.I) * A i k) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ (hAs i).mul_left
    have := hAc i
    simp only [lin]
    fun_prop
  have heq : ∫ k in torusBox, g k = ∑ i, oscInt2 (fun κ => t * Φ κ + lin y κ) (A i) := by
    rw [hunf g hgc hg1 hg2, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_finsetSum _ (fun i _ => hint i)]
    rfl
  calc ‖∫ k in torusBox, Complex.exp (↑(t * Φ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖
      = ‖∑ i, oscInt2 (fun κ => t * Φ κ + lin y κ) (A i)‖ := by rw [← heq]
    _ ≤ ∑ i, ‖oscInt2 (fun κ => t * Φ κ + lin y κ) (A i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, B i * w := Finset.sum_le_sum fun i _ => hB i
    _ = (∑ i, B i) * w := by rw [Finset.sum_mul]

open OscInt.K2.TorusPatchAux in
/-- **B3** Family torus patching. -/
theorem torusPatchParam : OscInt.Blueprint.A5U.TorusPatchParamFacts := by
  intro Ψ W α₀ hΨ hΨ1 hΨ2 hloc
  choose δ hδ ρ hρ C hC using hloc
  obtain ⟨η, hη, hηs, hunf⟩ := OscInt.API.torusUnfold
  have hKc : IsCompact (tsupport η) :=
    (isCompact_closedBall (0 : ℝ × ℝ) 4).of_isClosed_subset (isClosed_tsupport _) hηs
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover (fun k₀ => Metric.ball k₀ (δ k₀))
    (fun _ => Metric.isOpen_ball)
    (fun k _ => mem_iUnion.mpr ⟨k, Metric.mem_ball_self (hδ k)⟩)
  obtain ⟨χ, hχ, -, hχs, -, hχ1⟩ :=
    OscInt.StationaryPhase.PartitionAux.exists_smooth_partition_compact (ι := s) (tsupport η)
      (fun i => Metric.ball (i : ℝ × ℝ) (δ i)) hKc (fun _ => Metric.isOpen_ball)
      (by
        intro k hk
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hk)
        obtain ⟨his, hk'⟩ := mem_iUnion.mp hi
        exact mem_iUnion.mpr ⟨⟨i, his⟩, hk'⟩)
  obtain ⟨r, hr, hrρ⟩ := a5uG3_exists_pos_le s ρ hρ
  -- the pieces `A_i = χ_i η`
  set A : s → ℝ × ℝ → ℂ := fun i k => ((χ i k * η k : ℝ) : ℂ) with hA
  have hAc : ∀ i, ContDiff ℝ ∞ (A i) := fun i =>
    Complex.ofRealCLM.contDiff.comp ((hχ i).mul hη)
  have hAs : ∀ i : s, tsupport (A i) ⊆ Metric.closedBall (i : ℝ × ℝ) (δ i) := by
    intro i
    refine (closure_mono ?_).trans ((hχs i).trans Metric.ball_subset_closedBall)
    intro k hk
    simp only [Function.mem_support, hA] at hk ⊢
    intro h0
    exact hk (by simp [h0])
  have hM : ∀ i : s, ∃ M : ℝ, AmpBound 2 (Metric.closedBall (i : ℝ × ℝ) (δ i)) (A i) M := fun i =>
    OscInt.API.ampBoundOfContDiff 2 _ (A i) (isCompact_closedBall _ _) ((hAc i).of_le (by simp))
      (hAs i)
  choose M hMb using hM
  refine ⟨r, hr, ∑ i : s, C i * M i, fun α hα t n ht => ?_⟩
  have hαi : ∀ i : s, |α - α₀| ≤ ρ i := fun i => hα.trans (hrρ i i.2)
  have hsum : ∀ k, (η k : ℂ) = ∑ i : s, A i k := by
    intro k
    simp only [hA]
    rw [show (∑ i : s, ((χ i k * η k : ℝ) : ℂ)) = (((∑ i : s, χ i k) * η k : ℝ) : ℂ) by
      push_cast [Finset.sum_mul]; rfl]
    by_cases hk : k ∈ tsupport η
    · rw [hχ1 k hk, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hk]
      simp
  have hcs : ∀ i : s, HasCompactSupport (A i) := fun i =>
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hAs i)
  exact a5uG3_sum_bound (Ψ α) (hΨ α) (hΨ1 α) (hΨ2 α) η hunf A hsum (fun i => (hAc i).continuous) hcs t n
    (fun i => C i * M i) (W α t) (fun i => hC i α (hαi i) (A i) (M i) _ t (hMb i) ht)
