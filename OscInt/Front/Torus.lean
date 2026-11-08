/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Global

/-!
# GD-P2: the unfolding weight (route R6 of `docs/proof-GD.md`)

`unfoldWeight k = η₁ k₁ · η₁ k₂` with `η₁ s = h (s + π) − h (s − π)`, `h s = smoothTransition (s + 1/2)`.
-/

open MeasureTheory
open scoped ContDiff

namespace OscInt.API.Torus

/-- The smooth step: `0` for `s ≤ −1/2`, `1` for `s ≥ 1/2`. -/
noncomputable def unfoldStep (s : ℝ) : ℝ := Real.smoothTransition (s + 1 / 2)

/-- The 1D unfolding weight. -/
noncomputable def unfoldWeight₁ (s : ℝ) : ℝ := unfoldStep (s + Real.pi) - unfoldStep (s - Real.pi)

/-- The 2D unfolding weight. -/
noncomputable def unfoldWeight (k : ℝ × ℝ) : ℝ := unfoldWeight₁ k.1 * unfoldWeight₁ k.2

end OscInt.API.Torus

namespace OscInt.API.TorusAux

open OscInt.API.Torus

theorem unfoldStep_contDiff : ContDiff ℝ ∞ unfoldStep :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.add contDiff_const)

theorem unfoldStep_continuous : Continuous unfoldStep :=
  Real.smoothTransition.continuous.comp (continuous_id.add continuous_const)

theorem unfoldStep_zero {s : ℝ} (hs : s ≤ -1 / 2) : unfoldStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem unfoldStep_one {s : ℝ} (hs : 1 / 2 ≤ s) : unfoldStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem unfoldWeight₁_contDiff : ContDiff ℝ ∞ unfoldWeight₁ :=
  (unfoldStep_contDiff.comp (contDiff_id.add contDiff_const)).sub
    (unfoldStep_contDiff.comp (contDiff_id.sub contDiff_const))

theorem unfoldWeight₁_continuous : Continuous unfoldWeight₁ :=
  unfoldWeight₁_contDiff.continuous

theorem unfoldWeight₁_eq_zero {s : ℝ} (hs : Real.pi + 1 / 2 ≤ |s|) : unfoldWeight₁ s = 0 := by
  have h3 := Real.pi_gt_three
  unfold unfoldWeight₁
  rcases le_abs'.mp hs with h | h
  · rw [unfoldStep_zero (by linarith), unfoldStep_zero (by linarith)]; ring
  · rw [unfoldStep_one (by linarith), unfoldStep_one (by linarith)]; ring

theorem pi_add_half_lt_four : Real.pi + 1 / 2 < 4 := by
  have := Real.pi_lt_d2; norm_num at this ⊢; linarith

theorem unfoldWeight₁_eq_zero_of_four {s : ℝ} (hs : s ∉ Set.Ioc (-4) 4) : unfoldWeight₁ s = 0 := by
  have := pi_add_half_lt_four
  apply unfoldWeight₁_eq_zero
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
  rcases hs with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem support_unfoldWeight_subset :
    Function.support unfoldWeight ⊆ Metric.closedBall 0 (Real.pi + 1 / 2) := by
  intro k hk
  rw [mem_closedBall_zero_iff, norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  by_contra h
  rw [not_and_or, not_le, not_le] at h
  apply hk
  rcases h with h | h
  · simp [unfoldWeight, unfoldWeight₁_eq_zero h.le]
  · simp [unfoldWeight, unfoldWeight₁_eq_zero h.le]

/-- The 1D unfolding identity. -/
theorem unfold_one (f : ℝ → ℂ) (hf : Continuous f) (hp : ∀ s, f (s + 2 * Real.pi) = f s) :
    ∫ s in (-Real.pi)..Real.pi, f s = ∫ s, (unfoldWeight₁ s : ℂ) * f s := by
  have h3 := Real.pi_gt_three
  have h4 := pi_add_half_lt_four
  set G : ℝ → ℂ := fun s => f s * (unfoldStep (s + Real.pi) : ℂ) with hG
  have hGc : Continuous G :=
    hf.mul (Complex.continuous_ofReal.comp (unfoldStep_continuous.comp (continuous_id.add continuous_const)))
  have hsplit : ∀ s, (unfoldWeight₁ s : ℂ) * f s = G s - G (s - 2 * Real.pi) := by
    intro s
    have : f (s - 2 * Real.pi) = f s := by simpa using (hp (s - 2 * Real.pi)).symm
    simp only [hG, this, unfoldWeight₁, Complex.ofReal_sub]
    ring_nf
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-4) 4)
    (fun s hs => by simp [unfoldWeight₁_eq_zero_of_four hs]),
    ← intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [hsplit]
  have hI : IntervalIntegrable (fun x => G (x - 2 * Real.pi)) volume (-4) 4 :=
    (hGc.comp (continuous_sub_right _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hGc.intervalIntegrable _ _) hI,
    intervalIntegral.integral_comp_sub_right G,
    intervalIntegral.integral_interval_sub_interval_comm (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)]
  have hz : ∫ x in (-4 : ℝ)..(-4 - 2 * Real.pi), G x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))]
    · simp
    intro x hx
    rw [Set.uIcc_of_ge (by linarith), Set.mem_Icc] at hx
    simp [hG, unfoldStep_zero (show x + Real.pi ≤ -1 / 2 by linarith)]
  have hone : ∫ x in (4 - 2 * Real.pi)..(4 : ℝ), G x = ∫ x in (4 - 2 * Real.pi)..(4 : ℝ), f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hx
    simp [hG, unfoldStep_one (show 1 / 2 ≤ x + Real.pi by linarith)]
  have hper : Function.Periodic f (2 * Real.pi) := hp
  rw [hz, intervalIntegral.integral_symm (4 - 2 * Real.pi) 4, hone, zero_sub, neg_neg]
  have := hper.intervalIntegral_add_eq (4 - 2 * Real.pi) (-Real.pi)
  rw [show 4 - 2 * Real.pi + 2 * Real.pi = 4 by ring, show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
  exact this.symm

end OscInt.API.TorusAux

namespace OscInt.API.Torus

open OscInt.API.TorusAux

theorem unfoldWeight_contDiff : ContDiff ℝ ∞ unfoldWeight :=
  (unfoldWeight₁_contDiff.comp contDiff_fst).mul (unfoldWeight₁_contDiff.comp contDiff_snd)

theorem tsupport_unfoldWeight : tsupport unfoldWeight ⊆ Metric.closedBall 0 4 :=
  (closure_minimal support_unfoldWeight_subset Metric.isClosed_closedBall).trans
    (Metric.closedBall_subset_closedBall pi_add_half_lt_four.le)

theorem unfoldWeight_pi_div_two : unfoldWeight (Real.pi / 2, Real.pi / 2) = 1 := by
  have h3 := Real.pi_gt_three
  have : unfoldWeight₁ (Real.pi / 2) = 1 := by
    rw [unfoldWeight₁, unfoldStep_one (by linarith), unfoldStep_zero (by linarith)]; ring
  simp [unfoldWeight, this]

theorem unfoldFacts : OscInt.Blueprint.GD.UnfoldFacts unfoldWeight := by
  refine ⟨unfoldWeight_contDiff, tsupport_unfoldWeight, unfoldWeight_pi_div_two, ?_⟩
  intro g hg hp1 hp2
  have hpi := Real.pi_pos
  -- the left side as iterated interval integrals
  have hL : ∫ k in OscInt.Statements.torusBox, g k =
      ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, g (x, y) := by
    rw [OscInt.Statements.torusBox, Measure.volume_eq_prod,
      setIntegral_prod _ ((hg.continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  -- the right side by Fubini
  have hcs : HasCompactSupport (fun k : ℝ × ℝ => (unfoldWeight k : ℂ) * g k) := by
    have : HasCompactSupport (fun k : ℝ × ℝ => (unfoldWeight k : ℂ)) :=
      (HasCompactSupport.intro (isCompact_closedBall 0 4) (fun k hk => by
        have := image_eq_zero_of_notMem_tsupport (fun h => hk (tsupport_unfoldWeight h))
        simp [this])).comp_left Complex.ofReal_zero
    exact this.mul_right
  have hint : Integrable (fun k : ℝ × ℝ => (unfoldWeight k : ℂ) * g k) (volume.prod volume) :=
    ((Complex.continuous_ofReal.comp unfoldWeight_contDiff.continuous).mul hg).integrable_of_hasCompactSupport
      hcs
  rw [hL, Measure.volume_eq_prod, integral_prod _ hint]
  have hin : ∀ x, ∫ y in (-Real.pi)..Real.pi, g (x, y) =
      ∫ y, (unfoldWeight₁ y : ℂ) * g (x, y) := fun x =>
    unfold_one (fun y => g (x, y)) (hg.comp (continuous_const.prodMk continuous_id)) (fun y => hp2 (x, y))
  have hF : Continuous fun x => ∫ y in (-Real.pi)..Real.pi, g (x, y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun x y => g (x, y)) hg _ _
  rw [unfold_one _ hF (fun x => by
    show ∫ y in (-Real.pi)..Real.pi, g (x + 2 * Real.pi, y) = ∫ y in (-Real.pi)..Real.pi, g (x, y)
    congr 1; ext y; exact hp1 (x, y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hin, unfoldWeight, Complex.ofReal_mul]
  rw [← integral_const_mul]
  congr 1; ext y; ring

end OscInt.API.Torus
