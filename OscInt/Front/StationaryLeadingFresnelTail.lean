/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Batch SPL, part P-tail: the Fresnel primitive has a limit at rate `2/x` (route `docs/proof-SPL.md`, section 1)

With `e(v) = e^{iv²/2}`, `P(v) = e(v)/(iv)` and `q(v) = e(v)/(iv²)`: `P′ = e − q` for `v ≠ 0`, so for `0 < x ≤ y`
`F(y) − F(x) = P(y) − P(x) + ∫ₓʸ q`, of modulus at most `1/y + 1/x + (1/x − 1/y) = 2/x`.
Cauchy's criterion along `x = n + 1` gives a limit `L′`; letting `y → ∞` gives `|F(x) − L′| ≤ 2/x` for `x > 0`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory Set Filter Topology OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- `e(v) = e^{iv²/2}` is continuous. -/
theorem fresnelTail_continuous_fresnelE : Continuous fresnelE := by
  unfold fresnelE
  fun_prop

/-- `|e(v)| = 1`. -/
theorem fresnelTail_norm_fresnelE (v : ℝ) : ‖fresnelE v‖ = 1 := by
  unfold fresnelE
  exact Complex.norm_exp_ofReal_mul_I _

/-- `e′(v) = i v e(v)`. -/
theorem fresnelTail_hasDerivAt_fresnelE (v : ℝ) :
    HasDerivAt fresnelE (Complex.I * (v : ℂ) * fresnelE v) v := by
  have h0 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) v v := by
    have h := (hasDerivAt_pow 2 v).div_const 2
    convert h using 1
    simp
  have h1 : HasDerivAt (fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)) ((v : ℝ) : ℂ) v := h0.ofReal_comp
  have h2 := (h1.mul_const Complex.I).cexp
  have h3 : Complex.exp (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) * (((v : ℝ) : ℂ) * Complex.I) =
      Complex.I * (v : ℂ) * fresnelE v := by
    unfold fresnelE
    ring
  rw [h3] at h2
  exact h2

/-- `P(v) = e(v)/(iv) = −i e(v) v⁻¹`, the boundary term of the integration by parts. -/
noncomputable def fresnelTailP (v : ℝ) : ℂ := -(Complex.I * (fresnelE v * ((v⁻¹ : ℝ) : ℂ)))

/-- `q(v) = e(v)/(iv²) = −i e(v) v⁻²`, the integrand left by the integration by parts. -/
noncomputable def fresnelTailQ (v : ℝ) : ℂ := -(Complex.I * (fresnelE v * (((v ^ 2)⁻¹ : ℝ) : ℂ)))

/-- `P′(v) = e(v) − q(v)` for `v ≠ 0`. -/
theorem fresnelTail_hasDerivAt_P (v : ℝ) (hv : v ≠ 0) :
    HasDerivAt fresnelTailP (fresnelE v - fresnelTailQ v) v := by
  have h1 : HasDerivAt (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) ((-(v ^ 2)⁻¹ : ℝ) : ℂ) v :=
    (hasDerivAt_inv hv).ofReal_comp
  have h2 := (((fresnelTail_hasDerivAt_fresnelE v).mul h1).const_mul Complex.I).neg
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hv' : (v : ℂ) * (v : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hv)
  have h3 : -(Complex.I * (Complex.I * (v : ℂ) * fresnelE v * ((v⁻¹ : ℝ) : ℂ) +
      fresnelE v * ((-(v ^ 2)⁻¹ : ℝ) : ℂ))) = fresnelE v - fresnelTailQ v := by
    unfold fresnelTailQ
    push_cast
    linear_combination (-(fresnelE v * ((v : ℂ) * (v : ℂ)⁻¹))) * hI + fresnelE v * hv'
  rw [h3] at h2
  exact h2

/-- `|P(v)| = 1/v` for `v > 0`. -/
theorem fresnelTail_norm_P (v : ℝ) (hv : 0 < v) : ‖fresnelTailP v‖ = v⁻¹ := by
  unfold fresnelTailP
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, fresnelTail_norm_fresnelE, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv)]
  ring

/-- `|q(v)| = 1/v²`. -/
theorem fresnelTail_norm_Q (v : ℝ) : ‖fresnelTailQ v‖ = (v ^ 2)⁻¹ := by
  unfold fresnelTailQ
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, fresnelTail_norm_fresnelE, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg v))]
  ring

/-- `q` is continuous away from `0`. -/
theorem fresnelTail_continuousOn_Q : ContinuousOn fresnelTailQ {v : ℝ | v ≠ 0} := by
  have h1 : ContinuousOn (fun v : ℝ => (v ^ 2)⁻¹) {v : ℝ | v ≠ 0} :=
    (continuous_pow 2).continuousOn.inv₀ (fun v hv => pow_ne_zero 2 hv)
  have h2 : ContinuousOn (fun v : ℝ => (((v ^ 2)⁻¹ : ℝ) : ℂ)) {v : ℝ | v ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn h1
  exact (continuousOn_const.mul (fresnelTail_continuous_fresnelE.continuousOn.mul h2)).neg

/-- A compact interval with positive endpoints avoids `0`. -/
theorem fresnelTail_uIcc_subset (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : uIcc x y ⊆ {v : ℝ | v ≠ 0} := by
  intro v hv
  rw [uIcc_of_le hxy] at hv
  exact (lt_of_lt_of_le hx hv.1).ne'

/-- `q` is interval integrable on `[x, y]` for `0 < x ≤ y`. -/
theorem fresnelTail_intervalIntegrable_Q (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    IntervalIntegrable fresnelTailQ volume x y :=
  (fresnelTail_continuousOn_Q.mono (fresnelTail_uIcc_subset x y hx hxy)).intervalIntegrable

/-- `F(y) − F(x) = ∫ₓʸ e`. -/
theorem fresnelTail_prim_sub (x y : ℝ) :
    fresnelPrim y - fresnelPrim x = ∫ v in x..y, fresnelE v :=
  intervalIntegral.integral_interval_sub_left
    (fresnelTail_continuous_fresnelE.intervalIntegrable 0 y)
    (fresnelTail_continuous_fresnelE.intervalIntegrable 0 x)

/-- Integration by parts: `F(y) − F(x) = P(y) − P(x) + ∫ₓʸ q` for `0 < x ≤ y`. -/
theorem fresnelTail_prim_sub_eq (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    fresnelPrim y - fresnelPrim x =
      fresnelTailP y - fresnelTailP x + ∫ v in x..y, fresnelTailQ v := by
  have hq := fresnelTail_intervalIntegrable_Q x y hx hxy
  have he : IntervalIntegrable fresnelE volume x y :=
    fresnelTail_continuous_fresnelE.intervalIntegrable x y
  have h1 : ∫ v in x..y, (fresnelE v - fresnelTailQ v) = fresnelTailP y - fresnelTailP x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => fresnelTail_hasDerivAt_P v (fresnelTail_uIcc_subset x y hx hxy hv)) (he.sub hq)
  rw [intervalIntegral.integral_sub he hq] at h1
  rw [fresnelTail_prim_sub, ← h1]
  ring

/-- `∫ₓʸ v⁻² dv = 1/x − 1/y` for `0 < x ≤ y`. -/
theorem fresnelTail_integral_inv_sq (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ∫ v in x..y, (v ^ 2)⁻¹ = x⁻¹ - y⁻¹ := by
  have hd : ∀ v ∈ uIcc x y, HasDerivAt (fun u : ℝ => -u⁻¹) ((v ^ 2)⁻¹) v := by
    intro v hv
    have h := (hasDerivAt_inv (fresnelTail_uIcc_subset x y hx hxy hv)).neg
    rw [neg_neg] at h
    exact h
  have hc : ContinuousOn (fun v : ℝ => (v ^ 2)⁻¹) (uIcc x y) :=
    (continuous_pow 2).continuousOn.inv₀
      (fun v hv => pow_ne_zero 2 (fresnelTail_uIcc_subset x y hx hxy hv))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- `|∫ₓʸ q| ≤ 1/x − 1/y` for `0 < x ≤ y`. -/
theorem fresnelTail_norm_integral_Q (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖∫ v in x..y, fresnelTailQ v‖ ≤ x⁻¹ - y⁻¹ := by
  have h := intervalIntegral.norm_integral_le_integral_norm (f := fresnelTailQ) (μ := volume) hxy
  have h2 : ∫ v in x..y, ‖fresnelTailQ v‖ = ∫ v in x..y, (v ^ 2)⁻¹ :=
    intervalIntegral.integral_congr (fun v _ => fresnelTail_norm_Q v)
  rw [h2, fresnelTail_integral_inv_sq x y hx hxy] at h
  exact h

/-- Lemma 1 of the route: `|F(y) − F(x)| ≤ 2/x` for `0 < x ≤ y`. -/
theorem fresnelTail_norm_prim_sub_le (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖fresnelPrim y - fresnelPrim x‖ ≤ 2 / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [fresnelTail_prim_sub_eq x y hx hxy]
  have h1 := norm_add_le (fresnelTailP y - fresnelTailP x) (∫ v in x..y, fresnelTailQ v)
  have h2 := norm_sub_le (fresnelTailP y) (fresnelTailP x)
  rw [fresnelTail_norm_P y hy, fresnelTail_norm_P x hx] at h2
  have h3 := fresnelTail_norm_integral_Q x y hx hxy
  have h4 : 2 / x = y⁻¹ + x⁻¹ + (x⁻¹ - y⁻¹) := by ring
  rw [h4]
  linarith

/-- The sequence `F(n + 1)` is Cauchy. -/
theorem fresnelTail_cauchySeq : CauchySeq fun n : ℕ => fresnelPrim ((n : ℝ) + 1) := by
  have hb : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at h
    exact h
  refine cauchySeq_of_le_tendsto_0' (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) ?_ hb
  intro n m hnm
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have h := fresnelTail_norm_prim_sub_le ((n : ℝ) + 1) ((m : ℝ) + 1) hn hle
  rw [dist_comm, dist_eq_norm]
  have h5 : 2 * (1 / ((n : ℝ) + 1)) = 2 / ((n : ℝ) + 1) := by ring
  rw [h5]
  exact h

/-- **P-tail** The Fresnel primitive has a limit `L′` at `+∞`, with `|F(x) − L′| ≤ 2/x` for every `x > 0`. -/
theorem splFresnelTailFacts : SplFresnelTailFacts := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete fresnelTail_cauchySeq
  refine ⟨L, fun x hx => ?_⟩
  have ht : Tendsto (fun n : ℕ => ‖fresnelPrim x - fresnelPrim ((n : ℝ) + 1)‖) atTop
      (𝓝 ‖fresnelPrim x - L‖) := (tendsto_const_nhds.sub hL).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
  have hxn : x ≤ (n : ℝ) + 1 := by
    have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h2 : (⌈x⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [norm_sub_rev]
  exact fresnelTail_norm_prim_sub_le x ((n : ℝ) + 1) hx hxn

end OscInt.StationaryLeadingAux
