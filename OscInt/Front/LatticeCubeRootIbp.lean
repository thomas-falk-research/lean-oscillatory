/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeCubeRoot

/-!
# Batch LE2: the parts P-ibp, P-var and P-sym (route `docs/proof-LE2.md`)

* P-ibp: one integration by parts with `F = e^{iφ}/(i g)`, whose derivative is `e^{iφ} + e^{iφ} · i g′/g²`.
* P-var: the derivative of `1/(ξ − t sin k)` is `t cos k/(ξ − t sin k)²`; the sign of `cos` on each piece removes the
  absolute value.
* P-sym: the substitution `k ↦ −k`.
-/

namespace OscInt.LatticeCubeRootAux.Ibp

open Set OscInt.Statements OscInt.Blueprint.LatticeCubeRoot Real

/-! ### P-ibp -/

/-- The derivative of `F = e^{iφ}/(i g)`. -/
theorem ibp_hasDerivAt (φ g : ℝ → ℝ) (gx g'x : ℝ) (x : ℝ) (hφ : HasDerivAt φ gx x) (hgx : g x = gx)
    (hg : HasDerivAt g g'x x) (h0 : g x ≠ 0) :
    HasDerivAt (fun y => Complex.exp (↑(φ y) * Complex.I) / (Complex.I * ↑(g y)))
      (Complex.exp (↑(φ x) * Complex.I) +
        Complex.exp (↑(φ x) * Complex.I) * (Complex.I * ↑g'x / ↑(g x) ^ 2)) x := by
  have hE : HasDerivAt (fun y => Complex.exp (↑(φ y) * Complex.I))
      (Complex.exp (↑(φ x) * Complex.I) * (↑gx * Complex.I)) x :=
    (hφ.ofReal_comp.mul_const Complex.I).cexp
  have hD : HasDerivAt (fun y => Complex.I * (↑(g y) : ℂ)) (Complex.I * ↑g'x) x :=
    hg.ofReal_comp.const_mul Complex.I
  have hD0 : Complex.I * (↑(g x) : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h0)
  convert hE.div hD hD0 using 1
  have hg0 : (↑(g x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
  subst hgx
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The norm of the boundary term. -/
theorem ibp_norm_F (φ g : ℝ → ℝ) (x : ℝ) :
    ‖Complex.exp (↑(φ x) * Complex.I) / (Complex.I * ↑(g x))‖ = 1 / |g x| := by
  rw [norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul]

/-- The norm of the remainder integrand. -/
theorem ibp_norm_rem (φ g g' : ℝ → ℝ) (x : ℝ) :
    ‖Complex.exp (↑(φ x) * Complex.I) * (Complex.I * ↑(g' x) / ↑(g x) ^ 2)‖ = |g' x| / g x ^ 2 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]

theorem ibpFacts : IbpFacts := by
  intro φ g g' a b hab hφ hg hg'c hg0
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hφc : ContinuousOn φ (Icc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun x => Complex.exp (↑(φ x) * Complex.I)) (Icc a b) := by fun_prop
  have hRc : ContinuousOn (fun x => Complex.exp (↑(φ x) * Complex.I) *
      (Complex.I * ↑(g' x) / ↑(g x) ^ 2)) (Icc a b) := by
    refine hEc.mul ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg'c)).div
      ((Complex.continuous_ofReal.comp_continuousOn hgc).pow 2) fun x hx => ?_)
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hg0 x hx))
  have hEi : IntervalIntegrable (fun x => Complex.exp (↑(φ x) * Complex.I)) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable (by rwa [hu])
  have hRi : IntervalIntegrable (fun x => Complex.exp (↑(φ x) * Complex.I) *
      (Complex.I * ↑(g' x) / ↑(g x) ^ 2)) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable (by rwa [hu])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun x hx => ibp_hasDerivAt φ g (g x) (g' x) x (hφ x (hu ▸ hx)) rfl (hg x (hu ▸ hx)) (hg0 x (hu ▸ hx)))
    (hEi.add hRi)
  rw [intervalIntegral.integral_add hEi hRi] at hftc
  rw [eq_sub_of_add_eq hftc]
  have hrem : ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * (Complex.I * ↑(g' x) / ↑(g x) ^ 2)‖ ≤
      ∫ x in a..b, |g' x| / g x ^ 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    exact intervalIntegral.integral_congr fun x _ => ibp_norm_rem φ g g' x
  calc _ ≤ ‖Complex.exp (↑(φ b) * Complex.I) / (Complex.I * ↑(g b)) -
          Complex.exp (↑(φ a) * Complex.I) / (Complex.I * ↑(g a))‖ +
        ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * (Complex.I * ↑(g' x) / ↑(g x) ^ 2)‖ := norm_sub_le _ _
    _ ≤ (1 / |g b| + 1 / |g a|) + ∫ x in a..b, |g' x| / g x ^ 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (by rw [ibp_norm_F, ibp_norm_F])
    _ = _ := by ring

/-! ### P-var -/

/-- FTC for `1/(ξ − t sin k)`. -/
theorem var_ftc (t ξ a b : ℝ) (hab : a ≤ b) (h0 : ∀ k ∈ Icc a b, ξ - t * sin k ≠ 0) :
    ∫ k in a..b, t * cos k / (ξ - t * sin k) ^ 2 = 1 / (ξ - t * sin b) - 1 / (ξ - t * sin a) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hd : ∀ k ∈ uIcc a b, HasDerivAt (fun k => 1 / (ξ - t * sin k)) (t * cos k / (ξ - t * sin k) ^ 2) k := by
    intro k hk
    have h := ((hasDerivAt_sin k).const_mul t).const_sub ξ
    convert (hasDerivAt_const k (1 : ℝ)).div h (h0 k (hu ▸ hk)) using 1
    ring
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable ?_)
  rw [hu]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun k hk => pow_ne_zero 2 (h0 k hk)

theorem varFacts : VarFacts := by
  intro t ξ a b ht hab h0
  constructor
  · intro hsub
    rw [← var_ftc t ξ a b hab h0]
    refine intervalIntegral.integral_congr fun k hk => ?_
    rw [uIcc_of_le hab] at hk
    have hc := cos_nonneg_of_mem_Icc (hsub hk)
    rw [abs_neg, abs_of_nonneg (mul_nonneg ht.le hc)]
  · intro hsub
    have hc : ∀ k ∈ uIcc a b, cos k ≤ 0 := by
      intro k hk
      rw [uIcc_of_le hab] at hk
      rcases hsub with hs | hs
      · exact cos_nonpos_of_pi_div_two_le_of_le (hs hk).1 (hs hk).2
      · rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [(hs hk).2]) (by linarith [(hs hk).1])
    have heq : ∫ k in a..b, |-(t * cos k)| / (ξ - t * sin k) ^ 2 =
        ∫ k in a..b, -(t * cos k / (ξ - t * sin k) ^ 2) := by
      refine intervalIntegral.integral_congr fun k hk => ?_
      rw [abs_of_nonneg (by nlinarith [hc k hk] : 0 ≤ -(t * cos k)), neg_div]
    rw [heq, intervalIntegral.integral_neg, var_ftc t ξ a b hab h0]
    ring

/-! ### P-sym -/

theorem symFacts : SymFacts := by
  intro t ξ
  unfold latticeKernel1
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun k : ℝ => Complex.exp (↑(t * cos k + ξ * k) * Complex.I))
  simp only [neg_neg, cos_neg] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun k _ => ?_
  simp only [neg_mul, mul_neg]

end OscInt.LatticeCubeRootAux.Ibp
