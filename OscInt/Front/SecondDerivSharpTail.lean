/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Batch VC2, part VC3: from the start of a negative arc (`Vdc2TailFacts`, route `docs/proof-VC2.md`, V4)

On a side with `sin (f c - α) = 1` the integral of `cos (f - α)` over the side is `≤ 0`. One period is handled by
two monotone comparisons at the speed `f' m` of the point `m` where the phase has gained `π`; the general case
follows by induction on the number of periods.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- A sub-interval of a side is a side. -/
theorem vdc2L_side_mono {f f' : ℝ → ℝ} {c d lam p q : ℝ} (h : Vdc2Side f f' c d lam) (hcp : c ≤ p)
    (hpq : p ≤ q) (hqd : q ≤ d) : Vdc2Side f f' p q lam := by
  obtain ⟨_, hlam, hc, hd, hr, hp⟩ := h
  have hsub : Ioo p q ⊆ Ioo c d := Ioo_subset_Ioo hcp hqd
  exact ⟨hpq, hlam, hc.mono (Icc_subset_Icc hcp hqd), fun x hx => hd x (hsub hx),
    fun x hx y hy hxy => hr x (hsub hx) y (hsub hy) hxy, fun x hx => hp x (hsub hx)⟩

/-- On a side the phase is strictly increasing on `[c, d]`. -/
theorem vdc2L_side_strictMonoOn {f f' : ℝ → ℝ} {c d lam : ℝ} (h : Vdc2Side f f' c d lam) :
    StrictMonoOn f (Icc c d) := by
  obtain ⟨_, _, hc, hd, _, hp⟩ := h
  refine strictMonoOn_of_deriv_pos (convex_Icc c d) hc fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hp x hx

/-- The primitive of a real function continuous on `[p, q]` is continuous on `[p, q]`, with derivative the
function at every point of `(p, q)`. -/
theorem vdc2L_primitive (h : ℝ → ℝ) (p q : ℝ) (hpq : p ≤ q) (hh : ContinuousOn h (Icc p q)) :
    ContinuousOn (fun y => ∫ x in p..y, h x) (Icc p q) ∧
      ∀ x ∈ Ioo p q, HasDerivAt (fun y => ∫ t in p..y, h t) (h x) x := by
  refine ⟨?_, fun x hx => ?_⟩
  · have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume) (a := p) (b := q)
      (f := h) (by rw [uIcc_of_le hpq]; exact hh.integrableOn_Icc)
    rwa [uIcc_of_le hpq] at this
  · have hsub : Icc p x ⊆ Icc p q := Icc_subset_Icc_right hx.2.le
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · exact (hh.mono hsub).intervalIntegrable_of_Icc hx.1.le
    · exact (hh.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    · exact hh.continuousAt (Icc_mem_nhds hx.1 hx.2)

/-- Trigonometry at the start of a negative arc: if `sin (v - α) = 1` then `cos (u - α) = -sin (u - v)` and
`sin (u - α) = cos (u - v)`. -/
theorem vdc2L_trig (u v α : ℝ) (h : Real.sin (v - α) = 1) :
    Real.cos (u - α) = -Real.sin (u - v) ∧ Real.sin (u - α) = Real.cos (u - v) := by
  have hcos : Real.cos (v - α) = 0 := by
    have h1 := Real.sin_sq_add_cos_sq (v - α)
    rw [h] at h1
    have h2 : Real.cos (v - α) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  have hsplit : u - α = (u - v) + (v - α) := by ring
  constructor
  · rw [hsplit, Real.cos_add, h, hcos]; ring
  · rw [hsplit, Real.sin_add, h, hcos]; ring

/-- Monotone comparison: if `cos (g x) * (g' x / s - 1) ≥ 0` inside `[p, q]`, then
`∫_p^q cos g ≤ (sin (g q) - sin (g p)) / s`. -/
theorem vdc2L_compare (g g' : ℝ → ℝ) (p q s : ℝ) (hpq : p ≤ q) (hg : ContinuousOn g (Icc p q))
    (hd : ∀ x ∈ Ioo p q, HasDerivAt g (g' x) x)
    (hsign : ∀ x ∈ Ioo p q, 0 ≤ Real.cos (g x) * (g' x / s - 1)) :
    ∫ x in p..q, Real.cos (g x) ≤ (Real.sin (g q) - Real.sin (g p)) / s := by
  have hc : ContinuousOn (fun x => Real.cos (g x)) (Icc p q) := Real.continuous_cos.comp_continuousOn hg
  obtain ⟨hPc, hPd⟩ := vdc2L_primitive (fun x => Real.cos (g x)) p q hpq hc
  have hHc : ContinuousOn
      (fun x => (Real.sin (g x) - Real.sin (g p)) / s - ∫ t in p..x, Real.cos (g t)) (Icc p q) :=
    (((Real.continuous_sin.comp_continuousOn hg).sub continuousOn_const).div_const s).sub hPc
  have hHd : ∀ x ∈ Ioo p q, HasDerivAt
      (fun x => (Real.sin (g x) - Real.sin (g p)) / s - ∫ t in p..x, Real.cos (g t))
      (Real.cos (g x) * (g' x / s - 1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => Real.sin (g x)) (Real.cos (g x) * g' x) x := (hd x hx).sin
    have h2 := ((h1.sub_const (Real.sin (g p))).div_const s).sub (hPd x hx)
    have he : Real.cos (g x) * (g' x / s - 1) = Real.cos (g x) * g' x / s - Real.cos (g x) := by ring
    rw [he]
    exact h2
  have hmono : MonotoneOn
      (fun x => (Real.sin (g x) - Real.sin (g p)) / s - ∫ t in p..x, Real.cos (g t)) (Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) hHc ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hHd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hHd x hx).deriv]
      exact hsign x hx
  have hfin := hmono (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
  simp only [intervalIntegral.integral_same, sub_self, zero_div] at hfin
  linarith

/-- One period: a side with `sin (f c - α) = 1` and `f d - f c ≤ 2π` has `∫_c^d cos (f - α) ≤ 0`. -/
theorem vdc2L_one_period {f f' : ℝ → ℝ} {c d lam α : ℝ} (h : Vdc2Side f f' c d lam)
    (hsin : Real.sin (f c - α) = 1) (hper : f d - f c ≤ 2 * Real.pi) :
    ∫ x in c..d, Real.cos (f x - α) ≤ 0 := by
  have hmono := vdc2L_side_strictMonoOn h
  obtain ⟨hcd, hlam, hfc, hfd, hrate, hpos⟩ := h
  have hgc : ContinuousOn (fun x => f x - α) (Icc c d) := hfc.sub continuousOn_const
  have hcosc : ContinuousOn (fun x => Real.cos (f x - α)) (Icc c d) :=
    Real.continuous_cos.comp_continuousOn hgc
  by_cases hpi : f d - f c ≤ Real.pi
  · -- the integrand is nonpositive on the whole side
    have hnn : 0 ≤ ∫ x in c..d, -Real.cos (f x - α) := by
      refine intervalIntegral.integral_nonneg hcd fun x hx => ?_
      rw [(vdc2L_trig (f x) (f c) α hsin).1, neg_neg]
      have h1 : f c ≤ f x := hmono.monotoneOn (left_mem_Icc.mpr hcd) hx hx.1
      have h2 : f x ≤ f d := hmono.monotoneOn hx (right_mem_Icc.mpr hcd) hx.2
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [intervalIntegral.integral_neg] at hnn
    linarith
  · -- the point `m` where the phase has gained `π`
    have hpi' : Real.pi < f d - f c := not_le.mp hpi
    have hpipos := Real.pi_pos
    obtain ⟨m, hm, hfm⟩ := intermediate_value_Icc hcd hfc
      (show f c + Real.pi ∈ Icc (f c) (f d) from ⟨by linarith, by linarith⟩)
    have hcm : c < m := by
      rcases hm.1.eq_or_lt with heq | hlt
      · rw [← heq] at hfm; linarith
      · exact hlt
    have hmd : m < d := by
      rcases hm.2.eq_or_lt with heq | hlt
      · rw [heq] at hfm; linarith
      · exact hlt
    have hmI : m ∈ Ioo c d := ⟨hcm, hmd⟩
    have hs : 0 < f' m := hpos m hmI
    -- the first half `[c, m]`: the cosine is nonpositive and the speed is at most `f' m`
    have hA : ∫ x in c..m, Real.cos (f x - α) ≤ (Real.sin (f m - α) - Real.sin (f c - α)) / f' m := by
      refine vdc2L_compare (fun x => f x - α) f' c m (f' m) hcm.le (hgc.mono (Icc_subset_Icc le_rfl hmd.le))
        (fun x hx => (hfd x ⟨hx.1, hx.2.trans hmd⟩).sub_const α) fun x hx => ?_
      have hxI : x ∈ Ioo c d := ⟨hx.1, hx.2.trans hmd⟩
      have hxc : x ∈ Icc c d := ⟨hxI.1.le, hxI.2.le⟩
      have h1 : f c ≤ f x := hmono.monotoneOn (left_mem_Icc.mpr hcd) hxc hx.1.le
      have h2 : f x ≤ f m := hmono.monotoneOn hxc hm hx.2.le
      have hcos : Real.cos (f x - α) ≤ 0 := by
        rw [(vdc2L_trig (f x) (f c) α hsin).1, neg_nonpos]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hr := hrate x hxI m hmI hx.2.le
      have hle : f' x ≤ f' m := by nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hx.2.le)]
      have hq : f' x / f' m - 1 ≤ 0 := by
        have := (div_le_one hs).mpr hle
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos hcos hq
    -- the second half `[m, d]`: the cosine is nonnegative and the speed is at least `f' m`
    have hB : ∫ x in m..d, Real.cos (f x - α) ≤ (Real.sin (f d - α) - Real.sin (f m - α)) / f' m := by
      refine vdc2L_compare (fun x => f x - α) f' m d (f' m) hmd.le (hgc.mono (Icc_subset_Icc hcm.le le_rfl))
        (fun x hx => (hfd x ⟨hcm.trans hx.1, hx.2⟩).sub_const α) fun x hx => ?_
      have hxI : x ∈ Ioo c d := ⟨hcm.trans hx.1, hx.2⟩
      have hxc : x ∈ Icc c d := ⟨hxI.1.le, hxI.2.le⟩
      have h1 : f m ≤ f x := hmono.monotoneOn hm hxc hx.1.le
      have h2 : f x ≤ f d := hmono.monotoneOn hxc (right_mem_Icc.mpr hcd) hx.2.le
      have hcos : 0 ≤ Real.cos (f x - α) := by
        rw [(vdc2L_trig (f x) (f c) α hsin).1, neg_nonneg]
        have hshift : Real.sin (f x - f c) = -Real.sin (f x - f c - Real.pi) := by
          rw [Real.sin_sub_pi, neg_neg]
        rw [hshift, neg_nonpos]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hr := hrate m hmI x hxI hx.1.le
      have hle : f' m ≤ f' x := by nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hx.1.le)]
      have hq : 0 ≤ f' x / f' m - 1 := by
        have := (one_le_div hs).mpr hle
        linarith
      exact mul_nonneg hcos hq
    have hsm : Real.sin (f m - α) = -1 := by
      rw [(vdc2L_trig (f m) (f c) α hsin).2, hfm, add_sub_cancel_left, Real.cos_pi]
    have hsd : Real.sin (f d - α) ≤ 1 := Real.sin_le_one _
    have hi1 : IntervalIntegrable (fun x => Real.cos (f x - α)) MeasureTheory.volume c m :=
      (hcosc.mono (Icc_subset_Icc le_rfl hmd.le)).intervalIntegrable_of_Icc hcm.le
    have hi2 : IntervalIntegrable (fun x => Real.cos (f x - α)) MeasureTheory.volume m d :=
      (hcosc.mono (Icc_subset_Icc hcm.le le_rfl)).intervalIntegrable_of_Icc hmd.le
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hB' : (Real.sin (f d - α) - Real.sin (f m - α)) / f' m ≤ 2 / f' m :=
      div_le_div_of_nonneg_right (by rw [hsm]; linarith) hs.le
    have hA' : (Real.sin (f m - α) - Real.sin (f c - α)) / f' m = -(2 / f' m) := by
      rw [hsm, hsin]; ring
    linarith

/-- Induction on the number of periods: a side with `sin (f c - α) = 1` and `f d - f c ≤ 2π (n + 1)` has
`∫_c^d cos (f - α) ≤ 0`. -/
theorem vdc2L_periods (f f' : ℝ → ℝ) (lam α : ℝ) (n : ℕ) : ∀ c d : ℝ, Vdc2Side f f' c d lam →
    Real.sin (f c - α) = 1 → f d - f c ≤ 2 * Real.pi * (n + 1) → ∫ x in c..d, Real.cos (f x - α) ≤ 0 := by
  induction n with
  | zero =>
    intro c d h hsin hper
    refine vdc2L_one_period h hsin ?_
    simpa using hper
  | succ n ih =>
    intro c d h hsin hper
    by_cases hone : f d - f c ≤ 2 * Real.pi
    · exact vdc2L_one_period h hsin hone
    · have hgt : 2 * Real.pi < f d - f c := not_le.mp hone
      have hpipos := Real.pi_pos
      have hcd : c ≤ d := h.1
      have hfc : ContinuousOn f (Icc c d) := h.2.2.1
      obtain ⟨q, hq, hfq⟩ := intermediate_value_Icc hcd hfc
        (show f c + 2 * Real.pi ∈ Icc (f c) (f d) from ⟨by linarith, by linarith⟩)
      have h1 : Vdc2Side f f' c q lam := vdc2L_side_mono h le_rfl hq.1 hq.2
      have h2 : Vdc2Side f f' q d lam := vdc2L_side_mono h hq.1 hq.2 le_rfl
      have hI1 : ∫ x in c..q, Real.cos (f x - α) ≤ 0 :=
        vdc2L_one_period h1 hsin (by rw [hfq]; linarith)
      have hsinq : Real.sin (f q - α) = 1 := by
        have : f q - α = f c - α + 2 * Real.pi := by rw [hfq]; ring
        rw [this, Real.sin_add_two_pi, hsin]
      have hI2 : ∫ x in q..d, Real.cos (f x - α) ≤ 0 := by
        refine ih q d h2 hsinq ?_
        rw [hfq]
        push_cast at hper
        linarith
      have hcosc : ContinuousOn (fun x => Real.cos (f x - α)) (Icc c d) :=
        Real.continuous_cos.comp_continuousOn (hfc.sub continuousOn_const)
      have hi1 : IntervalIntegrable (fun x => Real.cos (f x - α)) MeasureTheory.volume c q :=
        (hcosc.mono (Icc_subset_Icc le_rfl hq.2)).intervalIntegrable_of_Icc hq.1
      have hi2 : IntervalIntegrable (fun x => Real.cos (f x - α)) MeasureTheory.volume q d :=
        (hcosc.mono (Icc_subset_Icc hq.1 le_rfl)).intervalIntegrable_of_Icc hq.2
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      linarith

/-- **V-tail**: from the start of a negative arc the integral of the cosine never becomes positive. -/
theorem vdc2TailFacts : Vdc2TailFacts := by
  intro f f' c d lam α h hsin
  obtain ⟨n, hn⟩ := exists_nat_gt ((f d - f c) / (2 * Real.pi))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by have := Real.pi_pos; linarith
  refine vdc2L_periods f f' lam α n c d h hsin ?_
  have h1 : f d - f c < n * (2 * Real.pi) := (div_lt_iff₀ h2pi).mp hn
  nlinarith

end OscInt.SecondDerivSharpAux
