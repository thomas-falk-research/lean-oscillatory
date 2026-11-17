/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Batch VC2, part VC4: the one-sided bound (`Vdc2OneSideFacts`) from the head and the tail

Route `docs/proof-VC2.md`, section V5. The rotation `θ` is reduced modulo `2π` to `θ′ ∈ (−3π/2, π/2]`. In case A
(`−π/2 < θ′`) the integrand is `sin (w − (f − f c))` with `w = θ′ + π/2`: a positive arc (V-head) followed by a tail
that starts at a negative arc (V-tail). In case B the integrand is first `≤ 0`, until the phase has gained
`v₀ = θ′ + 3π/2`, and from there it is the integrand of case A with `w = π`. Both cases use one lemma,
`vdc2S_arc`: a positive arc of phase length `w ∈ (0, π]` from the left end, followed by anything.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- A sub-interval of a side is a side. -/
theorem vdc2S_side_mono {f f' : ℝ → ℝ} {c d lam p q : ℝ} (h : Vdc2Side f f' c d lam) (hcp : c ≤ p) (hpq : p ≤ q)
    (hqd : q ≤ d) : Vdc2Side f f' p q lam := by
  obtain ⟨_, hlam, hc, hd, hr, hp⟩ := h
  have hsub : Ioo p q ⊆ Ioo c d := Ioo_subset_Ioo hcp hqd
  exact ⟨hpq, hlam, hc.mono (Icc_subset_Icc hcp hqd), fun x hx => hd x (hsub hx),
    fun x hx y hy hxy => hr x (hsub hx) y (hsub hy) hxy, fun x hx => hp x (hsub hx)⟩

/-- On a side the phase is strictly increasing on the closed interval. -/
theorem vdc2S_strictMonoOn {f f' : ℝ → ℝ} {c d lam : ℝ} (h : Vdc2Side f f' c d lam) : StrictMonoOn f (Icc c d) := by
  obtain ⟨_, _, hc, hd, _, hp⟩ := h
  refine strictMonoOn_of_deriv_pos (convex_Icc c d) hc fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hp x hx

/-- On a side every phase value strictly between `0` and the total gain is taken at an interior point. -/
theorem vdc2S_exists_phase {f f' : ℝ → ℝ} {c d lam v : ℝ} (h : Vdc2Side f f' c d lam) (hv0 : 0 < v)
    (hv : v < f d - f c) : ∃ q, c < q ∧ q < d ∧ f q - f c = v := by
  obtain ⟨hcd, _, hc, _, _, _⟩ := h
  have hmem : f c + v ∈ Icc (f c) (f d) := ⟨by linarith, by linarith⟩
  obtain ⟨q, hq, hfq⟩ := intermediate_value_Icc hcd hc hmem
  have hqc : q ≠ c := fun e => by rw [e] at hfq; linarith
  have hqd : q ≠ d := fun e => by rw [e] at hfq; linarith
  exact ⟨q, lt_of_le_of_ne hq.1 (Ne.symm hqc), lt_of_le_of_ne hq.2 hqd, by linarith⟩

/-- A function continuous on `[c, d]` is interval integrable on every sub-interval. -/
theorem vdc2S_integrable {g : ℝ → ℝ} {c d p q : ℝ} (hg : ContinuousOn g (Icc c d)) (hcp : c ≤ p) (hpq : p ≤ q)
    (hqd : q ≤ d) : IntervalIntegrable g MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hpq]
  exact hg.mono (Icc_subset_Icc hcp hqd)

/-- The integral of a function that is `≤ 0` on `[p, q]` is `≤ 0`. -/
theorem vdc2S_integral_nonpos {g : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q) (hg : ∀ x ∈ Icc p q, g x ≤ 0) :
    ∫ x in p..q, g x ≤ 0 := by
  have h : 0 ≤ ∫ x in p..q, -g x := intervalIntegral.integral_nonneg hpq fun x hx => neg_nonneg.mpr (hg x hx)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The bound of the head is nonnegative (the head on the degenerate side `[c, c]`). -/
theorem vdc2S_profile_nonneg (hH : Vdc2HeadFacts) {f f' : ℝ → ℝ} {c d lam : ℝ} (h : Vdc2Side f f' c d lam) :
    0 ≤ vdc2Profile Real.pi / (2 * Real.sqrt lam) := by
  have h0 := hH f f' c c lam Real.pi (vdc2S_side_mono h le_rfl le_rfl h.1) Real.pi_pos.le le_rfl
    (by rw [sub_self]; exact Real.pi_pos.le)
  rwa [intervalIntegral.integral_same] at h0

/-- A positive arc of phase length `w ∈ (0, π]` from the left end of a side, followed by the rest of the side:
`∫_c^d sin (w − (f − f c)) ≤ A(w) / (2 √lam)`. -/
theorem vdc2S_arc (hH : Vdc2HeadFacts) (hT : Vdc2TailFacts) {f f' : ℝ → ℝ} {c d lam w : ℝ}
    (h : Vdc2Side f f' c d lam) (hw0 : 0 < w) (hw : w ≤ Real.pi) :
    ∫ x in c..d, Real.sin (w - (f x - f c)) ≤ vdc2Profile w / (2 * Real.sqrt lam) := by
  by_cases hle : f d - f c ≤ w
  · exact hH f f' c d lam w h hw0.le hw hle
  · obtain ⟨q, hcq, hqd, hfq⟩ := vdc2S_exists_phase h hw0 (not_le.mp hle)
    have hcont : ContinuousOn (fun x => Real.sin (w - (f x - f c))) (Icc c d) :=
      Real.continuous_sin.comp_continuousOn (continuousOn_const.sub (h.2.2.1.sub continuousOn_const))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (vdc2S_integrable hcont le_rfl hcq.le hqd.le) (vdc2S_integrable hcont hcq.le hqd.le le_rfl)
    have h1 := hH f f' c q lam w (vdc2S_side_mono h le_rfl hcq.le hqd.le) hw0.le hw hfq.le
    have hstart : Real.sin (f q - (f c + w - Real.pi / 2)) = 1 := by
      rw [show f q - (f c + w - Real.pi / 2) = Real.pi / 2 by linarith, Real.sin_pi_div_two]
    have h2 := hT f f' q d lam (f c + w - Real.pi / 2) (vdc2S_side_mono h hcq.le hqd.le le_rfl) hstart
    have heq : ∫ x in q..d, Real.sin (w - (f x - f c)) = ∫ x in q..d, Real.cos (f x - (f c + w - Real.pi / 2)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      show Real.sin (w - (f x - f c)) = Real.cos (f x - (f c + w - Real.pi / 2))
      rw [← Real.sin_pi_div_two_sub]
      congr 1
      ring
    rw [← hsplit, heq]
    linarith

/-- Case A of the one-sided bound: `−π/2 < θ′ ≤ π/2`, with `w = θ′ + π/2`. -/
theorem vdc2S_caseA (hH : Vdc2HeadFacts) (hT : Vdc2TailFacts) {θ' : ℝ} (h1 : -(Real.pi / 2) < θ')
    (h2 : θ' ≤ Real.pi / 2) {f f' : ℝ → ℝ} {c d lam : ℝ} (h : Vdc2Side f f' c d lam) :
    ∫ x in c..d, Real.cos (f x - f c - θ') ≤ vdc2Profile (θ' + Real.pi / 2) / (2 * Real.sqrt lam) := by
  have heq : ∫ x in c..d, Real.cos (f x - f c - θ') = ∫ x in c..d, Real.sin (θ' + Real.pi / 2 - (f x - f c)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    show Real.cos (f x - f c - θ') = Real.sin (θ' + Real.pi / 2 - (f x - f c))
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  rw [heq]
  exact vdc2S_arc hH hT h (by linarith) (by linarith)

/-- Case B of the one-sided bound: `−3π/2 < θ′ ≤ −π/2`, with `w = π`. -/
theorem vdc2S_caseB (hH : Vdc2HeadFacts) (hT : Vdc2TailFacts) {θ' : ℝ} (h1 : -(3 * Real.pi / 2) < θ')
    (h2 : θ' ≤ -(Real.pi / 2)) {f f' : ℝ → ℝ} {c d lam : ℝ} (h : Vdc2Side f f' c d lam) :
    ∫ x in c..d, Real.cos (f x - f c - θ') ≤ vdc2Profile Real.pi / (2 * Real.sqrt lam) := by
  have hpi := Real.pi_pos
  have hmono := vdc2S_strictMonoOn h
  have hcd : c ≤ d := h.1
  have hnn := vdc2S_profile_nonneg hH h
  -- the integrand as a sine: `cos (v − θ′) = sin (v − v₀)`, `v₀ = θ′ + 3π/2`
  have hpt : ∀ x, Real.cos (f x - f c - θ') = Real.sin (f x - f c - (θ' + 3 * Real.pi / 2)) := by
    intro x
    rw [show f x - f c - (θ' + 3 * Real.pi / 2) = f x - f c - θ' + Real.pi / 2 - 2 * Real.pi by ring,
      Real.sin_sub_two_pi, Real.sin_add_pi_div_two]
  -- the integrand is `≤ 0` as long as the phase has gained at most `v₀`
  have hneg : ∀ p ∈ Icc c d, f p - f c ≤ θ' + 3 * Real.pi / 2 → ∫ x in c..p, Real.cos (f x - f c - θ') ≤ 0 := by
    intro p hp hfp
    refine vdc2S_integral_nonpos hp.1 fun x hx => ?_
    have hxm : x ∈ Icc c d := ⟨hx.1, hx.2.trans hp.2⟩
    have hx1 : f c ≤ f x := hmono.monotoneOn (left_mem_Icc.mpr hcd) hxm hx.1
    have hx2 : f x ≤ f p := hmono.monotoneOn hxm hp hx.2
    rw [hpt x]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  by_cases hle : f d - f c ≤ θ' + 3 * Real.pi / 2
  · exact (hneg d (right_mem_Icc.mpr hcd) hle).trans hnn
  · obtain ⟨p, hcp, hpd, hfp⟩ := vdc2S_exists_phase h (by linarith) (not_le.mp hle)
    have hcont : ContinuousOn (fun x => Real.cos (f x - f c - θ')) (Icc c d) :=
      Real.continuous_cos.comp_continuousOn ((h.2.2.1.sub continuousOn_const).sub continuousOn_const)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (vdc2S_integrable hcont le_rfl hcp.le hpd.le) (vdc2S_integrable hcont hcp.le hpd.le le_rfl)
    have hA := hneg p ⟨hcp.le, hpd.le⟩ hfp.le
    have hB := vdc2S_arc hH hT (vdc2S_side_mono h hcp.le hpd.le le_rfl) hpi le_rfl
    have heq : ∫ x in p..d, Real.cos (f x - f c - θ') = ∫ x in p..d, Real.sin (Real.pi - (f x - f p)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      show Real.cos (f x - f c - θ') = Real.sin (Real.pi - (f x - f p))
      rw [hpt x, Real.sin_pi_sub]
      congr 1
      linarith
    rw [← hsplit, heq]
    linarith

/-- **V-side** from the head and the tail: for every rotation `θ` there is `w ∈ [0, π]`, depending on `θ` only,
with `∫_c^d cos (f − f c − θ) ≤ A(w) / (2 √lam)` on every side. -/
theorem vdc2OneSideFacts_of (hH : Vdc2HeadFacts) (hT : Vdc2TailFacts) : Vdc2OneSideFacts := by
  intro θ
  have hpi := Real.pi_pos
  -- reduce `θ` modulo `2π` to `θ′ ∈ (−3π/2, π/2]`
  have hn1 : (θ - Real.pi / 2) / (2 * Real.pi) ≤ (⌈(θ - Real.pi / 2) / (2 * Real.pi)⌉ : ℝ) := Int.le_ceil _
  have hn2 : (⌈(θ - Real.pi / 2) / (2 * Real.pi)⌉ : ℝ) < (θ - Real.pi / 2) / (2 * Real.pi) + 1 :=
    Int.ceil_lt_add_one _
  generalize ⌈(θ - Real.pi / 2) / (2 * Real.pi)⌉ = n at hn1 hn2
  rw [div_le_iff₀ (by positivity)] at hn1
  have hn3 : (n : ℝ) * (2 * Real.pi) < θ - Real.pi / 2 + 2 * Real.pi := by
    have := mul_lt_mul_of_pos_right hn2 (show (0 : ℝ) < 2 * Real.pi by positivity)
    rwa [add_mul, one_mul, div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at this
  have hcos : ∀ (f : ℝ → ℝ) (c d : ℝ), ∫ x in c..d, Real.cos (f x - f c - θ) =
      ∫ x in c..d, Real.cos (f x - f c - (θ - n * (2 * Real.pi))) := by
    intro f c d
    refine intervalIntegral.integral_congr fun x _ => ?_
    show Real.cos (f x - f c - θ) = Real.cos (f x - f c - (θ - n * (2 * Real.pi)))
    rw [show f x - f c - (θ - n * (2 * Real.pi)) = f x - f c - θ + n * (2 * Real.pi) by ring,
      Real.cos_add_int_mul_two_pi]
  by_cases hA : -(Real.pi / 2) < θ - n * (2 * Real.pi)
  · refine ⟨θ - n * (2 * Real.pi) + Real.pi / 2, ⟨by linarith, by linarith⟩, fun f f' c d lam h => ?_⟩
    rw [hcos f c d]
    exact vdc2S_caseA hH hT hA (by linarith) h
  · refine ⟨Real.pi, ⟨hpi.le, le_rfl⟩, fun f f' c d lam h => ?_⟩
    rw [hcos f c d]
    exact vdc2S_caseB hH hT (by linarith) (not_lt.mp hA) h

end OscInt.SecondDerivSharpAux
