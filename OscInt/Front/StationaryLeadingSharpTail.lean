/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.StationaryLeadingFresnelTail
import OscInt.Front.StationaryLeadingFresnelValue
import OscInt.Front.StationaryLeadingFresnel
import OscInt.Front.StationaryLeadingKernel
import Blueprint.StationaryLeadingSharp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Batch SPL-N, part L: the tail branch of N8, `‖κ₊(x)‖ ≤ 277/400` for `x ≥ 4`

Route `docs/proof-SPLN.md`, section 2, N8 (second half). With `e(v) = e^{iv²/2}`, `q = 1/v` and
`G(v) = e(v)(−iq − q³ + 3iq⁵)`, one has `G′ = e − 15i e q⁶` for `v ≠ 0` (this is the three integrations by parts
`J₀ = iE/x − iJ₂`, `J₂ = iE/x³ − 3iJ₄`, `J₄ = iE/x⁵ − 5iJ₆` of the route, done at once on `[x, y]`). Hence
`F(y) − F(x) − (G(y) − G(x)) = 15i ∫ₓʸ e q⁶`, of norm at most `3/x⁵`; letting `y → ∞` (`F → L`, `G → 0`) gives
`R = L − F(x) + G(x)` with `‖R‖ ≤ 3/x⁵`, the improper integral `15i J₆` of the route, taken as a limit. The algebra
`κ₊ = L/2 + e q³ + (3/2) i e q⁵ + ((ix² − 1)/2) R` then gives `‖κ₊ − L/2‖ ≤ 5/(2x³) + 3/x⁵ ≤ 1/16` for `x ≥ 4`, and
`‖L‖/2 = √(π/2)/2 ≤ 63/100` from `π < 3.15`, so `‖κ₊‖ ≤ 63/100 + 1/16 = 277/400`.
-/

namespace OscInt.SPLNAux

open MeasureTheory Set Filter Topology OscInt.Statements OscInt.Blueprint.StationaryLeading
  OscInt.StationaryLeadingAux

/-- `q(v) = 1/v`, as a complex number. -/
noncomputable def splnL_q (v : ℝ) : ℂ := ((v⁻¹ : ℝ) : ℂ)

/-- `P(q) = −iq − q³ + 3iq⁵`, the polynomial factor of the boundary term. -/
noncomputable def splnL_P (w : ℂ) : ℂ := -(Complex.I * w) - w ^ 3 + 3 * Complex.I * w ^ 5

/-- `G(v) = e(v) P(q(v))`, the boundary term of the three integrations by parts. -/
noncomputable def splnL_G (v : ℝ) : ℂ := fresnelE v * splnL_P (splnL_q v)

/-- `H(v) = e(v) q(v)⁶`, the integrand left after the three integrations by parts. -/
noncomputable def splnL_H (v : ℝ) : ℂ := fresnelE v * splnL_q v ^ 6

/-- `q′ = −q²` away from `0`. -/
theorem splnL_hasDerivAt_q (v : ℝ) (hv : v ≠ 0) : HasDerivAt splnL_q (-(splnL_q v ^ 2)) v := by
  have h : HasDerivAt splnL_q (((-(v ^ 2)⁻¹ : ℝ)) : ℂ) v := (hasDerivAt_inv hv).ofReal_comp
  refine h.congr_deriv ?_
  simp [splnL_q]

/-- `v q(v) = 1` for `v ≠ 0`. -/
theorem splnL_mul_q (v : ℝ) (hv : v ≠ 0) : (v : ℂ) * splnL_q v = 1 := by
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv
  simp [splnL_q, hv']

/-- `G′ = e − 15i H` away from `0`. -/
theorem splnL_hasDerivAt_G (v : ℝ) (hv : v ≠ 0) :
    HasDerivAt splnL_G (fresnelE v - 15 * Complex.I * splnL_H v) v := by
  have hq := splnL_hasDerivAt_q v hv
  have hP : HasDerivAt (fun u => splnL_P (splnL_q u))
      (-(Complex.I * -(splnL_q v ^ 2)) - 3 * splnL_q v ^ 2 * -(splnL_q v ^ 2) +
        3 * Complex.I * (5 * splnL_q v ^ 4 * -(splnL_q v ^ 2))) v := by
    have h := ((hq.const_mul Complex.I).neg.sub (hq.pow 3)).add ((hq.pow 5).const_mul (3 * Complex.I))
    refine h.congr_deriv ?_
    norm_num
  have h := (fresnelTail_hasDerivAt_fresnelE v).mul hP
  refine h.congr_deriv ?_
  have hvq := splnL_mul_q v hv
  simp only [splnL_H, splnL_P]
  set q := splnL_q v
  set E := fresnelE v
  linear_combination E * (1 - Complex.I * q ^ 2 - 3 * q ^ 4) * hvq +
    (E * (-((v : ℂ) * q) + 3 * (v : ℂ) * q ^ 5)) * Complex.I_sq

/-- `q` is continuous away from `0`. -/
theorem splnL_continuousAt_q (v : ℝ) (hv : v ≠ 0) : ContinuousAt splnL_q v :=
  (splnL_hasDerivAt_q v hv).continuousAt

/-- `H` is interval integrable on `[x, y]` for `0 < x ≤ y`. -/
theorem splnL_intervalIntegrable_H (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    IntervalIntegrable splnL_H volume x y := by
  refine ContinuousOn.intervalIntegrable fun v hv => ?_
  have hv0 := fresnelTail_uIcc_subset x y hx hxy hv
  exact (fresnelTail_continuous_fresnelE.continuousAt.mul
    ((splnL_continuousAt_q v hv0).pow 6)).continuousWithinAt

/-- `F(y) − F(x) − (G(y) − G(x)) = 15i ∫ₓʸ H` for `0 < x ≤ y`. -/
theorem splnL_prim_sub_eq (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    fresnelPrim y - fresnelPrim x - (splnL_G y - splnL_G x) =
      15 * Complex.I * ∫ v in x..y, splnL_H v := by
  have hH := splnL_intervalIntegrable_H x y hx hxy
  have hE : IntervalIntegrable fresnelE volume x y :=
    fresnelTail_continuous_fresnelE.intervalIntegrable x y
  have h1 : ∫ v in x..y, (fresnelE v - 15 * Complex.I * splnL_H v) = splnL_G y - splnL_G x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => splnL_hasDerivAt_G v (fresnelTail_uIcc_subset x y hx hxy hv))
      (hE.sub (hH.const_mul _))
  rw [intervalIntegral.integral_sub hE (hH.const_mul _), intervalIntegral.integral_const_mul] at h1
  rw [fresnelTail_prim_sub, ← h1]
  ring

/-- `∫ₓʸ (v⁻¹)⁶ dv = ((x⁻¹)⁵ − (y⁻¹)⁵)/5` for `0 < x ≤ y`. -/
theorem splnL_integral_inv_pow_six (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ∫ v in x..y, v⁻¹ ^ 6 = (x⁻¹ ^ 5 - y⁻¹ ^ 5) / 5 := by
  have hd : ∀ v ∈ uIcc x y, HasDerivAt (fun u : ℝ => -(u⁻¹ ^ 5) / 5) (v⁻¹ ^ 6) v := by
    intro v hv
    have hv0 : v ≠ 0 := fresnelTail_uIcc_subset x y hx hxy hv
    have h := (((hasDerivAt_inv hv0).pow 5).neg).div_const 5
    refine h.congr_deriv ?_
    rw [show (5 : ℕ) - 1 = 4 from rfl, ← inv_pow]
    push_cast
    ring
  have hc : ContinuousOn (fun v : ℝ => v⁻¹ ^ 6) (uIcc x y) := fun v hv =>
    ((continuousAt_inv₀ (fresnelTail_uIcc_subset x y hx hxy hv)).pow 6).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- `‖∫ₓʸ H‖ ≤ (x⁻¹)⁵/5` for `0 < x ≤ y`. -/
theorem splnL_norm_integral_H (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖∫ v in x..y, splnL_H v‖ ≤ x⁻¹ ^ 5 / 5 := by
  have h := intervalIntegral.norm_integral_le_integral_norm (f := splnL_H) (μ := volume) hxy
  have h2 : ∫ v in x..y, ‖splnL_H v‖ = ∫ v in x..y, v⁻¹ ^ 6 := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv0 : 0 < v := lt_of_lt_of_le hx (by rw [uIcc_of_le hxy] at hv; exact hv.1)
    simp only [splnL_H, splnL_q, norm_mul, norm_pow, fresnelTail_norm_fresnelE, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv0), one_mul]
  rw [h2, splnL_integral_inv_pow_six x y hx hxy] at h
  have hy : 0 ≤ y⁻¹ ^ 5 := pow_nonneg (inv_nonneg.mpr (by linarith)) 5
  linarith

/-- `‖F(y) − F(x) − (G(y) − G(x))‖ ≤ 3 (x⁻¹)⁵` for `0 < x ≤ y`. -/
theorem splnL_norm_sub_le (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖fresnelPrim y - fresnelPrim x - (splnL_G y - splnL_G x)‖ ≤ 3 * x⁻¹ ^ 5 := by
  rw [splnL_prim_sub_eq x y hx hxy, norm_mul, norm_mul, Complex.norm_I]
  have h := splnL_norm_integral_H x y hx hxy
  have h15 : ‖(15 : ℂ)‖ = 15 := by norm_num
  rw [h15]
  linarith

/-- `G(y) → 0` as `y → +∞`. -/
theorem splnL_tendsto_G : Tendsto splnL_G atTop (𝓝 0) := by
  have hq : Tendsto splnL_q atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    rw [Complex.ofReal_zero] at h
    exact h
  have hP : Tendsto (fun y => splnL_P (splnL_q y)) atTop (𝓝 0) := by
    have h := ((hq.const_mul Complex.I).neg.sub (hq.pow 3)).add ((hq.pow 5).const_mul (3 * Complex.I))
    simp only [mul_zero, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      add_zero] at h
    exact h
  refine squeeze_zero_norm (fun y => le_of_eq ?_) (tendsto_zero_iff_norm_tendsto_zero.1 hP)
  rw [splnL_G, norm_mul, fresnelTail_norm_fresnelE, one_mul]

/-- `R = L − F(x) + G(x)` has `‖R‖ ≤ 3 (x⁻¹)⁵` for `x > 0` (the limit `y → ∞` of `splnL_norm_sub_le`). -/
theorem splnL_norm_R_le (x : ℝ) (hx : 0 < x) :
    ‖fresnelLimit - fresnelPrim x + splnL_G x‖ ≤ 3 * x⁻¹ ^ 5 := by
  have hF := splKer_tendsto_fresnelPrim (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)
  have ht : Tendsto (fun y => ‖fresnelPrim y - fresnelPrim x - (splnL_G y - splnL_G x)‖) atTop
      (𝓝 ‖fresnelLimit - fresnelPrim x - (0 - splnL_G x)‖) :=
    ((hF.sub_const _).sub (splnL_tendsto_G.sub_const _)).norm
  have h := le_of_tendsto ht (eventually_atTop.2 ⟨x, fun y hy => splnL_norm_sub_le x y hx hy⟩)
  have he : fresnelLimit - fresnelPrim x - (0 - splnL_G x) = fresnelLimit - fresnelPrim x + splnL_G x := by
    ring
  rwa [he] at h

/-- `κ₊(x) = L/2 + e q³ + (3/2) i e q⁵ + ((ix² − 1)/2) R` for `x ≠ 0`. -/
theorem splnL_kernelPos_eq (x : ℝ) (hx : x ≠ 0) :
    splKernelPos x = fresnelLimit / 2 + fresnelE x * splnL_q x ^ 3 +
      3 / 2 * Complex.I * fresnelE x * splnL_q x ^ 5 +
      (Complex.I * (x : ℂ) ^ 2 - 1) / 2 * (fresnelLimit - fresnelPrim x + splnL_G x) := by
  have hvq := splnL_mul_q x hx
  have hE : Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) = fresnelE x := rfl
  rw [splKernelPos, hE, splnL_G, splnL_P]
  set q := splnL_q x
  set E := fresnelE x
  linear_combination (-(E / 2) * ((x : ℂ) - Complex.I * q * ((x : ℂ) * q + 1) -
      3 * q ^ 3 * ((x : ℂ) * q + 1))) * hvq +
    (-(E / 2) * (-((x : ℂ) ^ 2 * q) + 3 * (x : ℂ) ^ 2 * q ^ 5)) * Complex.I_sq

/-- `‖L‖ ≤ 63/50`: `‖L‖² = π/2` and `π < 3.15`. -/
theorem splnL_norm_fresnelLimit_le : ‖fresnelLimit‖ ≤ 63 / 50 := by
  unfold fresnelLimit
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat]
  have h1 : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have h2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have h3 := Real.pi_lt_d2
  have hs := Real.sqrt_nonneg Real.pi
  have hn := norm_nonneg ((1 : ℂ) + Complex.I)
  have h4 : (Real.sqrt Real.pi * ‖(1 : ℂ) + Complex.I‖) ^ 2 < (126 / 50) ^ 2 := by
    rw [mul_pow, h1, h2]
    norm_num at h3 ⊢
    linarith
  have h5 : Real.sqrt Real.pi * ‖(1 : ℂ) + Complex.I‖ < 126 / 50 := by
    nlinarith [mul_nonneg hs hn]
  linarith

/-- `‖((ix² − 1)/2)‖ ≤ (x² + 1)/2`. -/
theorem splnL_norm_coef_le (x : ℝ) : ‖(Complex.I * (x : ℂ) ^ 2 - 1) / 2‖ ≤ (x ^ 2 + 1) / 2 := by
  rw [norm_div, Complex.norm_ofNat]
  have : ‖Complex.I * (x : ℂ) ^ 2 - 1‖ ≤ x ^ 2 + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_one, one_mul]
  linarith

/-- **N8, tail branch** `‖κ₊(x)‖ ≤ 277/400` for `x ≥ 4`. -/
theorem splnTail : ∀ x : ℝ, 4 ≤ x → ‖OscInt.Statements.splKernelPos x‖ ≤ 277 / 400 := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hxr : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  have hr4 : x⁻¹ ≤ 1 / 4 := by nlinarith
  have hr3 : x⁻¹ ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hr0.le hr4 3
  have hr5 : x⁻¹ ^ 5 ≤ (1 / 4) ^ 5 := pow_le_pow_left₀ hr0.le hr4 5
  have hx2 : x ^ 2 * x⁻¹ ^ 5 = x⁻¹ ^ 3 := by
    have : x ^ 2 * x⁻¹ ^ 5 = (x * x⁻¹) ^ 2 * x⁻¹ ^ 3 := by ring
    rw [this, hxr]
    ring
  have hq : ‖splnL_q x‖ = x⁻¹ := by
    rw [splnL_q, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  rw [splnL_kernelPos_eq x hx0.ne']
  have t1 : ‖fresnelLimit / 2‖ ≤ 63 / 100 := by
    rw [norm_div, Complex.norm_ofNat]
    linarith [splnL_norm_fresnelLimit_le]
  have t2 : ‖fresnelE x * splnL_q x ^ 3‖ = x⁻¹ ^ 3 := by
    rw [norm_mul, norm_pow, fresnelTail_norm_fresnelE, hq, one_mul]
  have t3 : ‖3 / 2 * Complex.I * fresnelE x * splnL_q x ^ 5‖ = 3 / 2 * x⁻¹ ^ 5 := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, fresnelTail_norm_fresnelE, hq, Complex.norm_I, norm_div,
      Complex.norm_ofNat, Complex.norm_ofNat]
    ring
  have t4 : ‖(Complex.I * (x : ℂ) ^ 2 - 1) / 2 * (fresnelLimit - fresnelPrim x + splnL_G x)‖ ≤
      (x ^ 2 + 1) / 2 * (3 * x⁻¹ ^ 5) := by
    rw [norm_mul]
    exact mul_le_mul (splnL_norm_coef_le x) (splnL_norm_R_le x hx0) (norm_nonneg _) (by positivity)
  have n1 := norm_add_le (fresnelLimit / 2 + fresnelE x * splnL_q x ^ 3 +
      3 / 2 * Complex.I * fresnelE x * splnL_q x ^ 5)
    ((Complex.I * (x : ℂ) ^ 2 - 1) / 2 * (fresnelLimit - fresnelPrim x + splnL_G x))
  have n2 := norm_add_le (fresnelLimit / 2 + fresnelE x * splnL_q x ^ 3)
    (3 / 2 * Complex.I * fresnelE x * splnL_q x ^ 5)
  have n3 := norm_add_le (fresnelLimit / 2) (fresnelE x * splnL_q x ^ 3)
  linarith

end OscInt.SPLNAux
