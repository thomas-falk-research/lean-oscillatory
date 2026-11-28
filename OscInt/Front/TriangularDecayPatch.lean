/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Front.GlobalFinal
import OscInt.Front.Core
import OscInt.StationaryPhase.Partition

/-!
# Batch K2, part P7: `TorusPatchFacts`

Route: `docs/proof-K2.md`, section 2 ("P7") and section 8 (N1).

* T1 (`OscInt.API.torusUnfold`) turns the box integral of the continuous biperiodic integrand
  `e^{i(tΨ + n·k)}` into `∫ η · e^{i(tΨ + n·k)}` with `η` smooth and `tsupport η ⊆ closedBall 0 4`.
* The compact `tsupport η` is covered by finitely many open balls `ball k_j δ_j` from the local hypothesis
  (`IsCompact.elim_finite_subcover`).
* A smooth partition of unity `χ_j` subordinate to that cover
  (`OscInt.StationaryPhase.PartitionAux.exists_smooth_partition_compact`, F2a) splits `η = Σ_j χ_j η`.
* F1 (`OscInt.API.ampBoundOfContDiff`) bounds each `χ_j η` by some `M_j` on `closedBall k_j δ_j`; the local bound
  with `y = n` gives `C_j M_j t^{-β}`; sum. The constant is `Σ_j C_j M_j` (no sign condition on `C_j` is needed,
  since the triangle inequality is applied to the norms themselves).
-/

namespace OscInt.K2

open Set MeasureTheory OscInt.Statements OscInt.Blueprint
open scoped ContDiff

namespace TorusPatchAux

/-- `e^{i(a + 2π n)} = e^{ia}` for an integer `n`. -/
theorem exp_add_two_pi_int (a : ℝ) (n : ℤ) :
    Complex.exp (↑(a + (n : ℝ) * (2 * Real.pi)) * Complex.I) = Complex.exp (↑a * Complex.I) := by
  have : (↑(a + (n : ℝ) * (2 * Real.pi)) * Complex.I : ℂ) =
      ↑a * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end TorusPatchAux

open TorusPatchAux in
/-- **P7** Torus patching. -/
theorem torusPatch : OscInt.Blueprint.K2.TorusPatchFacts := by
  intro Ψ β hΨ _hβ hΨ1 hΨ2 hloc
  choose δ hδ C hC using hloc
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
  refine ⟨∑ i : s, C i * M i, fun t n ht => ?_⟩
  set y : ℝ × ℝ := ((n.1 : ℝ), (n.2 : ℝ)) with hy
  set g : ℝ × ℝ → ℂ := fun k =>
    Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I) with hg
  have hgc : Continuous g := by
    have := hΨ.continuous
    fun_prop
  have hg1 : ∀ k : ℝ × ℝ, g (k.1 + 2 * Real.pi, k.2) = g k := by
    intro k
    have e : t * Ψ (k.1 + 2 * Real.pi, k.2) + ((n.1 : ℝ) * (k.1 + 2 * Real.pi) + (n.2 : ℝ) * k.2) =
        t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2) + (n.1 : ℝ) * (2 * Real.pi) := by
      rw [hΨ1 k]; ring
    simp only [hg]
    rw [e, exp_add_two_pi_int]
  have hg2 : ∀ k : ℝ × ℝ, g (k.1, k.2 + 2 * Real.pi) = g k := by
    intro k
    have e : t * Ψ (k.1, k.2 + 2 * Real.pi) + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * (k.2 + 2 * Real.pi)) =
        t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2) + (n.2 : ℝ) * (2 * Real.pi) := by
      rw [hΨ2 k]; ring
    simp only [hg]
    rw [e, exp_add_two_pi_int]
  have hsplit : ∀ k, (η k : ℂ) * g k = ∑ i : s, Complex.exp (↑(t * Ψ k + lin y k) * Complex.I) * A i k := by
    intro k
    have hlin : lin y k = (n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2 := rfl
    simp only [hA, hlin, ← Finset.mul_sum]
    rw [show (∑ i : s, ((χ i k * η k : ℝ) : ℂ)) = (((∑ i : s, χ i k) * η k : ℝ) : ℂ) by
      push_cast [Finset.sum_mul]; rfl]
    by_cases hk : k ∈ tsupport η
    · rw [hχ1 k hk, one_mul, mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport hk]
      simp
  have hint : ∀ i, Integrable (fun k => Complex.exp (↑(t * Ψ k + lin y k) * Complex.I) * A i k) := by
    intro i
    have hcs : HasCompactSupport (A i) :=
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hAs i)
    refine Continuous.integrable_of_hasCompactSupport ?_ hcs.mul_left
    have := hΨ.continuous
    have := (hAc i).continuous
    simp only [lin]
    fun_prop
  have heq : ∫ k in torusBox, g k = ∑ i : s, oscInt2 (fun κ => t * Ψ κ + lin y κ) (A i) := by
    rw [hunf g hgc hg1 hg2, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_finsetSum _ (fun i _ => hint i)]
    rfl
  calc ‖∫ k in torusBox, Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖
      = ‖∑ i : s, oscInt2 (fun κ => t * Ψ κ + lin y κ) (A i)‖ := by rw [← heq]
    _ ≤ ∑ i : s, ‖oscInt2 (fun κ => t * Ψ κ + lin y κ) (A i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : s, C i * M i * t ^ (-β) := Finset.sum_le_sum fun i _ => hC i (A i) (M i) y t (hMb i) ht
    _ = (∑ i : s, C i * M i) * t ^ (-β) := by rw [Finset.sum_mul]

end OscInt.K2

