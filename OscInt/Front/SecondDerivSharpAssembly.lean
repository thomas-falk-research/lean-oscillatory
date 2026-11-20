/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import OscInt.VanDerCorput.Amplitude
import OscInt.VanDerCorput.Split
import OscInt.VanDerCorput.Assembly

/-!
# Batch VC2: the lead's assembly against the blueprint (route `docs/proof-VC2.md`)

VC2-S from the turning point and the one-sided bound (the modulus of `∫ e^{if}` is the integral of a cosine after a
rotation; the left side of the turning point is the right side of the reflected phase). VC2-K from VC2-S, VC2-N, the
sign of `φ″` and the amplitude transfer proved for S1.k. VC2-A and VC2-N are parts. Written after the stamp of the
review answers (`stamps/20261117T010311Z-a93c4e1e44f7`) and compiled before any part was proved.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- `‖z‖ = Re (z e^{−i arg z})`. -/
theorem norm_eq_re_mul_exp_arg (z : ℂ) : ‖z‖ = (z * Complex.exp (-(Complex.arg z : ℂ) * Complex.I)).re := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have h2 : z * Complex.exp (-(Complex.arg z : ℂ) * Complex.I) = (‖z‖ : ℂ) := by
    conv_lhs => rw [← h]
    rw [mul_assoc, ← Complex.exp_add]
    simp
  rw [h2, Complex.ofReal_re]

/-- The modulus of `∫ e^{if}` as the integral of a cosine. -/
theorem norm_integral_exp_eq (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ‖∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I)‖ =
      ∫ x in a..b, Real.cos (f x - Complex.arg (∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I))) := by
  set J := ∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I) with hJ
  have hint : IntervalIntegrable (fun x => Complex.exp (((f x : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-(Complex.arg J : ℂ) * Complex.I)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ((Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hf).mul continuousOn_const))).mul continuousOn_const
  rw [norm_eq_re_mul_exp_arg J, hJ, ← intervalIntegral.integral_mul_const, ← hJ]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Complex.reCLM_apply]
  rw [← Complex.exp_add]
  have : ((f x : ℝ) : ℂ) * Complex.I + -(Complex.arg J : ℂ) * Complex.I =
      ((f x - Complex.arg J : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- A sub-interval of a side is a side. -/
theorem Vdc2Side.mono {f f' : ℝ → ℝ} {c d lam p q : ℝ} (h : Vdc2Side f f' c d lam) (hcp : c ≤ p) (hpq : p ≤ q)
    (hqd : q ≤ d) : Vdc2Side f f' p q lam := by
  obtain ⟨_, hlam, hc, hd, hr, hp⟩ := h
  have hsub : Ioo p q ⊆ Ioo c d := Ioo_subset_Ioo hcp hqd
  exact ⟨hpq, hlam, hc.mono (Icc_subset_Icc hcp hqd), fun x hx => hd x (hsub hx),
    fun x hx y hy hxy => hr x (hsub hx) y (hsub hy) hxy, fun x hx => hp x (hsub hx)⟩

/-- **VC2-S** from the turning point and the one-sided bound. -/
theorem secondDerivSharp_of (hT : Vdc2TurningPointFacts) (hO : Vdc2OneSideFacts) : SecondDerivSharpStatement := by
  intro f f' a b lam hab hlam hf hrate
  obtain ⟨x₀, hx₀, hneg, hpos⟩ := hT f' a b lam hab hlam hrate
  set J := ∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I) with hJ
  obtain ⟨w, hw, hside⟩ := hO (Complex.arg J - f x₀)
  refine ⟨w, hw, ?_⟩
  -- the right side `[x₀, b]`
  have hR : Vdc2Side f f' x₀ b lam :=
    ⟨hx₀.2, hlam, hf.1.mono (Icc_subset_Icc hx₀.1 le_rfl), fun x hx => hf.2 x ⟨hx₀.1.trans_lt hx.1, hx.2⟩,
      fun x hx y hy hxy => hrate x ⟨hx₀.1.trans_lt hx.1, hx.2⟩ y ⟨hx₀.1.trans_lt hy.1, hy.2⟩ hxy, hpos⟩
  -- the left side, reflected: `x ↦ f (−x)` on `[−x₀, −a]`
  have hL : Vdc2Side (fun x => f (-x)) (fun x => -f' (-x)) (-x₀) (-a) lam := by
    refine ⟨neg_le_neg hx₀.1, hlam, ?_, ?_, ?_, ?_⟩
    · refine (hf.1.mono (Icc_subset_Icc le_rfl hx₀.2)).comp continuousOn_neg fun x hx => ?_
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro x hx
      have hx' : -x ∈ Ioo a b := ⟨by linarith [hx.2], by linarith [hx.1, hx₀.2]⟩
      have h : HasDerivAt (fun x => f (-x)) (f' (-x) * -1) x := (hf.2 (-x) hx').comp x (hasDerivAt_neg x)
      simpa using h
    · intro x hx y hy hxy
      have hx' : -x ∈ Ioo a b := ⟨by linarith [hx.2], by linarith [hx.1, hx₀.2]⟩
      have hy' : -y ∈ Ioo a b := ⟨by linarith [hy.2], by linarith [hy.1, hx₀.2]⟩
      have := hrate (-y) hy' (-x) hx' (by linarith)
      linarith
    · intro x hx
      have := hneg (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      linarith
  have h1 := hside f f' x₀ b lam hR
  have h2 := hside _ _ (-x₀) (-a) lam hL
  simp only [neg_neg] at h2
  rw [intervalIntegral.integral_comp_neg (fun x => Real.cos (f x - f x₀ - (Complex.arg J - f x₀)))] at h2
  simp only [neg_neg] at h2
  -- the modulus as an integral of a cosine, split at `x₀`
  have hcont : ContinuousOn (fun x => Real.cos (f x - f x₀ - (Complex.arg J - f x₀))) (Icc a b) :=
    Real.continuous_cos.comp_continuousOn ((hf.1.sub continuousOn_const).sub continuousOn_const)
  have hi1 : IntervalIntegrable (fun x => Real.cos (f x - f x₀ - (Complex.arg J - f x₀))) MeasureTheory.volume a x₀ :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hx₀.1]; exact hcont.mono (Icc_subset_Icc le_rfl hx₀.2))
  have hi2 : IntervalIntegrable (fun x => Real.cos (f x - f x₀ - (Complex.arg J - f x₀))) MeasureTheory.volume x₀ b :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hx₀.2]; exact hcont.mono (Icc_subset_Icc hx₀.1 le_rfl))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hnorm : ‖J‖ = ∫ x in a..b, Real.cos (f x - f x₀ - (Complex.arg J - f x₀)) := by
    rw [hJ, norm_integral_exp_eq f a b hab hf.1, ← hJ]
    exact intervalIntegral.integral_congr fun x _ => by ring_nf
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  rw [hnorm, ← hsplit]
  have : vdc2Profile w / Real.sqrt lam = vdc2Profile w / (2 * Real.sqrt lam) + vdc2Profile w / (2 * Real.sqrt lam) := by
    field_simp; ring
  rw [this]
  exact add_le_add h2 h1

/-- **VC2-K** from VC2-S, VC2-N and the amplitude transfer of batch S1. -/
theorem secondDerivSevenHalves_of (hS : SecondDerivSharpStatement) (hN : Vdc2ProfileBoundStatement) :
    SecondDerivSevenHalvesStatement := by
  intro φ φ' φ'' ψ ψ' a b μ p hab hμ hφ hφ' hlow hψ
  have hsq : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hφp := OscInt.VanDerCorput.HasDerivOn.add_linear hφ p
  have hne : ∀ x ∈ Ioo a b, φ'' x ≠ 0 := fun x hx h0 => by
    have := hlow x hx; rw [h0, abs_zero] at this; linarith
  -- a bound for one phase with an increasing derivative
  have plain : ∀ (g g' : ℝ → ℝ) (y : ℝ), a ≤ y → HasDerivOn g g' a y → DerivIncreasesAtRate g' a y μ →
      ‖∫ x in a..y, Complex.exp (((g x : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 / Real.sqrt μ := by
    intro g g' y hay hg hr
    obtain ⟨w, hw, hb⟩ := hS g g' a y μ hay hμ hg hr
    exact hb.trans (div_le_div_of_nonneg_right (hN w hw) hsq.le)
  have key : ∀ y ∈ Icc a b, ‖∫ x in a..y, Complex.exp (((φ x + p * x : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 / Real.sqrt μ := by
    intro y hy
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo a b)
        (fun x hx => (hφ'.2 x hx).hasDerivWithinAt) hne with hneg | hpos
    · -- `φ″ ≤ −μ`: conjugate
      have hle : ∀ x ∈ Ioo a b, μ ≤ -φ'' x := fun x hx => by
        have := hlow x hx; rwa [abs_of_neg (hneg x hx)] at this
      have hg' : HasDerivOn (fun x => -φ' x) (fun x => -φ'' x) a b := ⟨hφ'.1.neg, fun x hx => (hφ'.2 x hx).neg⟩
      have hinc := OscInt.VanDerCorput.SplitAux.mul_sub_le_of_le_deriv hg' hle
      have hg : HasDerivOn (fun x => -(φ x + p * x)) (fun x => -(φ' x + p)) a y :=
        ⟨(hφp.1.mono (Icc_subset_Icc le_rfl hy.2)).neg, fun x hx => (hφp.2 x ⟨hx.1, hx.2.trans_le hy.2⟩).neg⟩
      have hr : DerivIncreasesAtRate (fun x => -(φ' x + p)) a y μ := by
        intro x hx z hz hxz
        have := hinc x ⟨hx.1.le, hx.2.le.trans hy.2⟩ z ⟨hz.1.le, hz.2.le.trans hy.2⟩ hxz
        linarith
      have hb := plain _ _ y hy.1 hg hr
      have hconj : (∫ x in a..y, Complex.exp (((-(φ x + p * x) : ℝ) : ℂ) * Complex.I)) =
          (starRingEnd ℂ) (∫ x in a..y, Complex.exp (((φ x + p * x : ℝ) : ℂ) * Complex.I)) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
        congr 1; push_cast; ring
      rw [hconj, RCLike.norm_conj] at hb
      exact hb
    · have hle : ∀ x ∈ Ioo a b, μ ≤ φ'' x := fun x hx => by
        have := hlow x hx; rwa [abs_of_pos (hpos x hx)] at this
      have hinc := OscInt.VanDerCorput.SplitAux.mul_sub_le_of_le_deriv hφ' hle
      have hg : HasDerivOn (fun x => φ x + p * x) (fun x => φ' x + p) a y :=
        OscInt.VanDerCorput.HasDerivOn.mono hφp le_rfl hy.2
      have hr : DerivIncreasesAtRate (fun x => φ' x + p) a y μ := by
        intro x hx z hz hxz
        have := hinc x ⟨hx.1.le, hx.2.le.trans hy.2⟩ z ⟨hz.1.le, hz.2.le.trans hy.2⟩ hxz
        linarith
      exact plain _ _ y hy.1 hg hr
  have h := OscInt.VanDerCorput.amplitudeTransfer (fun x => φ x + p * x) ψ ψ' a b (7 / 2 / Real.sqrt μ) hab
    (by positivity) hφp.1 hψ key
  have hpow : μ ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt μ := by
    rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg hμ.le, one_div, one_div]
  rw [hpow]
  calc ‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ 7 / 2 / Real.sqrt μ * ampNorm ψ ψ' a b := h
    _ = 7 / 2 * (1 / Real.sqrt μ) * ampNorm ψ ψ' a b := by ring

end OscInt.SecondDerivSharpAux
