/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen, Thomas Falk III
Modified 2026 by Thomas Falk III: derived from roos-j/lean-oscillatory and adapted to OscInt's frozen
statements; the changes are described in this file's module docstring.
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.VanDerCorput
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.IntermediateValue

/-!
# P1: first-derivative van der Corput bound, no amplitude

Proves `OscInt.VanDerCorput.vdc1Plain : OscInt.Blueprint.VdC1PlainFacts`:
if `φ'` is monotone on `(a, b)` with `ν ≤ |φ'|` there, then `‖∫_a^b e^{iφ}‖ ≤ 3 / ν`.

Route (adapted from J. Roos and M. Praveen, `roos-j/lean-oscillatory`,
`LeanOscillatory/VanDerCorput.lean`, `norm_integral_exp_mul_I_le_of_order_one'`, Apache-2.0;
after Stein, *Harmonic Analysis*, VIII §1.2). By continuity and the intermediate value theorem
`φ'` has one sign and `ν ≤ |φ'|` on all of `[a, b]`. Integrate by parts with `u = (iφ')⁻¹`,
`v = e^{iφ}`: the boundary terms give `2 / ν`. The remainder is bounded by `∫ |h'|` with
`h = 1/φ'`; since `φ'` is monotone, `h' = -φ''/φ'²` has one sign on `(a, b)`, so `h'` is
integrable (`intervalIntegrable_deriv_of_nonneg`) and `∫ |h'| = |h b - h a| ≤ 1 / ν`
(`φ' a`, `φ' b` have the same sign).
-/

open Set MeasureTheory Complex OscInt.Statements

namespace OscInt.VanDerCorput.OneAux

/-- An inequality on `(a, b)` between continuous functions extends to `[a, b]`. -/
theorem le_on_Icc {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (h : ∀ x ∈ Ioo a b, f x ≤ g x) : ∀ x ∈ Icc a b, f x ≤ g x := by
  intro x hx
  have hx' : x ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  exact ContinuousWithinAt.closure_le hx' ((hf x hx).mono Ioo_subset_Icc_self)
    ((hg x hx).mono Ioo_subset_Icc_self) h

/-- A derivative of a function monotone on `(a, b)` is nonnegative there. -/
theorem deriv_nonneg_of_monotoneOn {g g' : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hd : HasDerivAt g (g' x) x) (hg : MonotoneOn g (Ioo a b)) : 0 ≤ g' x := by
  have hacc : AccPt x (Filter.principal (Ioo a b)) := by
    have := (PerfectSpace.univ_preperfect (α := ℝ)).open_inter (isOpen_Ioo (a := a) (b := b))
    rw [inter_univ] at this
    exact this x hx
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hg

/-- A continuous function on `[a, b]` with `ν ≤ |f|` on `(a, b)` has `ν ≤ f` on `[a, b]` or
`f ≤ -ν` on `[a, b]`. -/
theorem sign_of_abs_ge {f : ℝ → ℝ} {a b ν : ℝ} (hab : a < b) (hν : 0 < ν)
    (hf : ContinuousOn f (Icc a b)) (h : ∀ x ∈ Ioo a b, ν ≤ |f x|) :
    (∀ x ∈ Icc a b, ν ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ -ν) := by
  have key : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, 0 < f x → 0 < f y := by
    intro x hx y hy hfx
    by_contra hfy
    rw [not_lt] at hfy
    have hsub : uIcc x y ⊆ Ioo a b := (ordConnected_Ioo).uIcc_subset hx hy
    have hc : ContinuousOn f (uIcc x y) := hf.mono (hsub.trans Ioo_subset_Icc_self)
    obtain ⟨z, hz, hfz⟩ := intermediate_value_uIcc hc (show (0 : ℝ) ∈ uIcc (f x) (f y) from
      mem_uIcc.2 (Or.inr ⟨hfy, hfx.le⟩))
    have := h z (hsub hz)
    rw [hfz, abs_zero] at this
    linarith
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  rcases lt_or_ge 0 (f m) with hpos | hneg
  · left
    refine le_on_Icc hab continuousOn_const hf fun x hx => ?_
    have := h x hx
    rw [abs_of_pos (key m hm x hx hpos)] at this
    exact this
  · right
    refine le_on_Icc hab hf continuousOn_const fun x hx => ?_
    have hx0 : f x ≤ 0 := by
      by_contra hx0
      rw [not_le] at hx0
      have := key x hx m hm hx0
      linarith
    have := h x hx
    rw [abs_of_nonpos hx0] at this
    linarith

/-- Arithmetic: for `x, y` of the same sign with `|x|, |y| ≥ ν`, `|x⁻¹ - y⁻¹| ≤ ν⁻¹`. -/
theorem abs_inv_sub_inv_le {x y ν : ℝ} (hν : 0 < ν)
    (h : (ν ≤ x ∧ ν ≤ y) ∨ (x ≤ -ν ∧ y ≤ -ν)) : |x⁻¹ - y⁻¹| ≤ ν⁻¹ := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have h1 : x⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hx
    have h2 : y⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hy
    have h3 : 0 < x⁻¹ := inv_pos.2 (by linarith)
    have h4 : 0 < y⁻¹ := inv_pos.2 (by linarith)
    rw [abs_le]; constructor <;> linarith
  · have h1 : (-x)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (by linarith)
    have h2 : (-y)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (by linarith)
    have h3 : 0 < (-x)⁻¹ := inv_pos.2 (by linarith)
    have h4 : 0 < (-y)⁻¹ := inv_pos.2 (by linarith)
    rw [inv_neg] at h1 h2 h3 h4
    rw [abs_le]; constructor <;> linarith

/-- FTC with a sign: if `h' ≥ 0` is the derivative of `h` on `(a, b)`, then `h'` is integrable and
any `f` with `‖f‖ ≤ |h'|` on `(a, b)` has `‖∫ f‖ ≤ |h b - h a|`. -/
theorem ftc_bound_of_nonneg {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn h (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x) (hpos : ∀ x ∈ Ioo a b, 0 ≤ h' x) :
    IntervalIntegrable h' volume a b ∧ ∀ f : ℝ → ℂ, (∀ x ∈ Ioo a b, ‖f x‖ ≤ |h' x|) →
      ‖∫ x in a..b, f x‖ ≤ |h b - h a| := by
  have hint : IntervalIntegrable h' volume a b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := h)
    · rwa [uIcc_of_le hab]
    · rwa [min_eq_left hab, max_eq_right hab]
    · rwa [min_eq_left hab, max_eq_right hab]
  refine ⟨hint, fun f hf => ?_⟩
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simp [ae_iff, measure_singleton]
  have hle : ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, h' x := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hint
    filter_upwards [hae] with t ht htI
    have htI' : t ∈ Ioo a b := ⟨htI.1, lt_of_le_of_ne htI.2 ht⟩
    rw [← abs_of_nonneg (hpos t htI')]
    exact hf t htI'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd hint] at hle
  exact hle.trans (le_abs_self _)

/-- `ftc_bound_of_nonneg` for a derivative of constant sign. -/
theorem ftc_bound {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn h (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hsign : (∀ x ∈ Ioo a b, 0 ≤ h' x) ∨ (∀ x ∈ Ioo a b, h' x ≤ 0)) :
    IntervalIntegrable h' volume a b ∧ ∀ f : ℝ → ℂ, (∀ x ∈ Ioo a b, ‖f x‖ ≤ |h' x|) →
      ‖∫ x in a..b, f x‖ ≤ |h b - h a| := by
  rcases hsign with hpos | hneg
  · exact ftc_bound_of_nonneg hab hc hd hpos
  · obtain ⟨hint, hb⟩ := ftc_bound_of_nonneg (h := fun x => -h x) (h' := fun x => -h' x) hab hc.neg
      (fun x hx => (hd x hx).neg) (fun x hx => neg_nonneg.2 (hneg x hx))
    refine ⟨by convert hint.neg using 1; funext x; simp, fun f hf => ?_⟩
    have := hb f (fun x hx => by rw [abs_neg]; exact hf x hx)
    rwa [show -h b - -h a = -(h b - h a) by ring, abs_neg] at this

/-- Integration by parts with `u = (i φ')⁻¹`, `v = e^{iφ}`: the integral is bounded by the two
boundary terms plus `|1/φ'(b) - 1/φ'(a)|`, given the FTC bound for `h' = (1/φ')'`. -/
theorem ibp_bound {φ φ' h' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hφc : ContinuousOn φ (Icc a b))
    (hφd : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x) (hφ'c : ContinuousOn φ' (Icc a b))
    (hne : ∀ x ∈ Icc a b, φ' x ≠ 0) (hhd : ∀ x ∈ Ioo a b, HasDerivAt (fun x => (φ' x)⁻¹) (h' x) x)
    (hint : IntervalIntegrable h' volume a b)
    (hbound : ∀ f : ℝ → ℂ, (∀ x ∈ Ioo a b, ‖f x‖ ≤ |h' x|) →
      ‖∫ x in a..b, f x‖ ≤ |(φ' b)⁻¹ - (φ' a)⁻¹|) :
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤
      |φ' b|⁻¹ + |φ' a|⁻¹ + |(φ' b)⁻¹ - (φ' a)⁻¹| := by
  set u : ℝ → ℂ := fun x => -I * ((φ' x)⁻¹ : ℝ) with hu
  set u' : ℝ → ℂ := fun x => -I * (h' x : ℂ) with hu'
  set v : ℝ → ℂ := fun x => Complex.exp (↑(φ x) * I) with hv
  set v' : ℝ → ℂ := fun x => Complex.exp (↑(φ x) * I) * (↑(φ' x) * I) with hv'
  have hvc : ContinuousOn v (Icc a b) :=
    ((continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const).cexp
  have huc : ContinuousOn u (Icc a b) :=
    continuousOn_const.mul (continuous_ofReal.comp_continuousOn (hφ'c.inv₀ hne))
  have hv'c : ContinuousOn v' (Icc a b) :=
    hvc.mul ((continuous_ofReal.comp_continuousOn hφ'c).mul continuousOn_const)
  have hu'i : IntervalIntegrable u' volume a b :=
    (show IntervalIntegrable (fun x => (h' x : ℂ)) volume a b from
      ⟨hint.1.ofReal, hint.2.ofReal⟩).const_mul (-I)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := u) (v := v) (u' := u') (v' := v') (by rwa [uIcc_of_le hab.le])
    (by rwa [uIcc_of_le hab.le])
    (fun x hx => by
      rw [min_eq_left hab.le, max_eq_right hab.le] at hx
      exact (((hhd x hx).ofReal_comp).const_mul (-I)).hasDerivWithinAt)
    (fun x hx => by
      rw [min_eq_left hab.le, max_eq_right hab.le] at hx
      exact (((hφd x hx).ofReal_comp).mul_const I).cexp.hasDerivWithinAt)
    hu'i (hv'c.intervalIntegrable_of_Icc hab.le)
  have hcongr : ∫ x in a..b, Complex.exp (↑(φ x) * I) = ∫ x in a..b, u x * v' x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hab.le] at hx
    have h0 : (φ' x : ℂ) ≠ 0 := ofReal_ne_zero.2 (hne x hx)
    simp only [hu, hv', ofReal_inv]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have huv : ∀ x, ‖u x * v x‖ = |φ' x|⁻¹ := fun x => by
    simp [hu, hv, Complex.norm_exp_ofReal_mul_I]
  have hrem : ‖∫ x in a..b, u' x * v x‖ ≤ |(φ' b)⁻¹ - (φ' a)⁻¹| :=
    hbound _ fun x _ => by simp [hu', hv, Complex.norm_exp_ofReal_mul_I]
  rw [hcongr, hibp]
  calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
      ≤ ‖u b * v b‖ + ‖u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ _ := by rw [huv, huv]; linarith

end OscInt.VanDerCorput.OneAux

namespace OscInt.VanDerCorput

open OneAux

/-- **P1.** First-derivative van der Corput bound without amplitude, constant 3. -/
theorem vdc1Plain : OscInt.Blueprint.VdC1PlainFacts := by
  intro φ φ' φ'' a b ν hab hν ⟨hφc, hφd⟩ ⟨hφ'c, hφ'd⟩ hmono hlow
  rcases hab.eq_or_lt with rfl | hab
  · simp only [intervalIntegral.integral_same, norm_zero]; positivity
  have hsign := sign_of_abs_ge hab hν hφ'c hlow
  have habs : ∀ x ∈ Icc a b, ν ≤ |φ' x| := by
    rcases hsign with h | h <;> intro x hx
    · exact (h x hx).trans (le_abs_self _)
    · have := h x hx; rw [abs_of_neg (by linarith)]; linarith
  have hne : ∀ x ∈ Icc a b, φ' x ≠ 0 := fun x hx h0 => by
    have := habs x hx; rw [h0, abs_zero] at this; linarith
  set h : ℝ → ℝ := fun x => (φ' x)⁻¹ with h_def
  set h' : ℝ → ℝ := fun x => -φ'' x / φ' x ^ 2 with h'_def
  have hhc : ContinuousOn h (Icc a b) := hφ'c.inv₀ hne
  have hhd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    (hφ'd x hx).inv (hne x (Ioo_subset_Icc_self hx))
  have hh'sign : (∀ x ∈ Ioo a b, 0 ≤ h' x) ∨ (∀ x ∈ Ioo a b, h' x ≤ 0) := by
    rcases hmono with hm | hm
    · right; intro x hx
      have := deriv_nonneg_of_monotoneOn hx (hφ'd x hx) hm
      simp only [h'_def, neg_div]
      exact neg_nonpos.2 (div_nonneg this (sq_nonneg _))
    · left; intro x hx
      have := deriv_nonneg_of_monotoneOn (g' := fun x => -φ'' x) hx (hφ'd x hx).fun_neg hm.neg
      exact div_nonneg this (sq_nonneg _)
  obtain ⟨hint, hbound⟩ := ftc_bound hab.le hhc hhd hh'sign
  have hmain := ibp_bound hab hφc hφd hφ'c hne hhd hint hbound
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have h1 : |φ' b|⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (habs b hb)
  have h2 : |φ' a|⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (habs a ha)
  have h3 : |(φ' b)⁻¹ - (φ' a)⁻¹| ≤ ν⁻¹ := abs_inv_sub_inv_le hν (by
    rcases hsign with hs | hs
    · exact Or.inl ⟨hs b hb, hs a ha⟩
    · exact Or.inr ⟨hs b hb, hs a ha⟩)
  rw [div_eq_mul_inv]
  linarith

end OscInt.VanDerCorput
