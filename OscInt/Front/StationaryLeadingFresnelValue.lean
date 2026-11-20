/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Batch SPL, part P-value: the value of the Fresnel integral (route `docs/proof-SPL.md`, sections 10 and 11)

Abel summation. For `ε > 0` the mean `A(ε) = ∫₀^∞ e^{−εv²/2} e^{iv²/2} dv` is a complex Gaussian integral,
`A(ε) = (π/((ε − i)/2))^{1/2}/2 → (2πi)^{1/2}/2 = √π (1 + i)/2` as `ε → 0+` (principal branch, continuous at `2πi`).
One integration by parts gives `A(ε) = ∫₀^∞ εv e^{−εv²/2} F(v) dv`, and `∫₀^∞ εv e^{−εv²/2} dv = 1`; so if
`|F(x) − L′| ≤ 2/x` then `|A(ε) − L′| ≤ ∫₀^∞ 2ε e^{−εv²/2} dv = √(2πε) → 0`, and `L′ = √π (1 + i)/2`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory Set Filter OscInt.Statements OscInt.Blueprint.StationaryLeading
open scoped Topology

/-! ## The Fresnel primitive -/

/-- `e(v) = e^{iv²/2}` is continuous. -/
theorem splValue_fresnelE_continuous : Continuous fresnelE := by
  show Continuous fun u : ℝ => Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)
  fun_prop

/-- `|e(v)| = 1`. -/
theorem splValue_norm_fresnelE (v : ℝ) : ‖fresnelE v‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `F′ = e` on the line (fundamental theorem of calculus). -/
theorem splValue_prim_hasDerivAt (x : ℝ) : HasDerivAt fresnelPrim (fresnelE x) x :=
  (splValue_fresnelE_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- `F` is continuous. -/
theorem splValue_prim_continuous : Continuous fresnelPrim :=
  continuous_iff_continuousAt.2 fun x => (splValue_prim_hasDerivAt x).continuousAt

/-- `F(0) = 0`. -/
theorem splValue_prim_zero : fresnelPrim 0 = 0 := by
  unfold fresnelPrim
  exact intervalIntegral.integral_same

/-- `|F(v)| ≤ |v|`, since `|e| = 1`. -/
theorem splValue_norm_prim_le (v : ℝ) : ‖fresnelPrim v‖ ≤ |v| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := v) (C := 1) (f := fresnelE)
    (fun x _ => (splValue_norm_fresnelE x).le)
  rwa [one_mul, sub_zero] at h

/-- A number approached by `F` at rate `2/x` is the limit of `F` at `+∞`. -/
theorem splValue_tendsto_prim {L' : ℂ} (hyp : ∀ x : ℝ, 0 < x → ‖fresnelPrim x - L'‖ ≤ 2 / x) :
    Tendsto fresnelPrim atTop (𝓝 L') := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun x : ℝ => (2 : ℝ) / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with x hx using hyp x hx

/-! ## The closed form of the Abel mean and its limit -/

/-- With `b = (ε − i)/2`, Mathlib's half-line Gaussian integral is the Abel mean of `e`:
`∫₀^∞ e^{−εv²/2} e(v) dv = (π/b)^{1/2}/2`. -/
theorem splValue_abel_shape (ε : ℝ) (hε : 0 < ε) :
    ∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v =
      ((Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ) / 2 := by
  have hb : 0 < ((((ε : ℂ) - Complex.I) / 2)).re := by simp; linarith
  rw [← integral_gaussian_complex_Ioi hb]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [fresnelE]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At `ε = 0` the base is `π/(−i/2) = 2πi`. -/
theorem splValue_base_zero :
    (Real.pi : ℂ) / (((0 : ℂ) - Complex.I) / 2) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  push_cast
  linear_combination ((2 : ℂ) * Real.pi) * Complex.I_sq

/-- `√(2π) e^{iπ/4} = 2 · √π (1 + i)/2`. -/
theorem splValue_sqrt_two_pi_mul_exp :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = 2 * fresnelLimit := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  unfold fresnelLimit
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h2]
  push_cast
  linear_combination ((Real.sqrt Real.pi : ℂ) * (1 + Complex.I) / 2) * h3

/-- The value at `ε = 0` on the principal branch: `(2πi)^{1/2}/2 = √π (1 + i)/2`. -/
theorem splValue_abel_value :
    ((Real.pi : ℂ) / (((0 : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ) / 2 = fresnelLimit := by
  have h2pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 h2pos.ne') Complex.I_ne_zero
  rw [splValue_base_zero, Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul h2pos Complex.I_ne_zero,
    Complex.log_I]
  have h3 : (((Real.log (2 * Real.pi) : ℝ) : ℂ) + (Real.pi : ℂ) / 2 * Complex.I) * (1 / 2 : ℂ) =
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h3, Complex.exp_add, ← Complex.ofReal_exp]
  have h4 : Real.exp (Real.log (2 * Real.pi) / 2) = Real.sqrt (2 * Real.pi) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2pos]
    congr 1
    ring
  rw [h4, splValue_sqrt_two_pi_mul_exp]
  ring

/-- The closed form of the Abel mean tends to `√π (1 + i)/2` as `ε → 0+`: the principal square root is continuous
at `2πi`. -/
theorem splValue_closed_tendsto :
    Tendsto (fun ε : ℝ => ((Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ) / 2) (𝓝[>] 0)
      (𝓝 fresnelLimit) := by
  have hne : (((0 : ℝ) : ℂ) - Complex.I) / 2 ≠ 0 := by
    rw [Complex.ofReal_zero, zero_sub]
    exact div_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) two_ne_zero
  have hin : (Real.pi : ℂ) / ((((0 : ℝ) : ℂ) - Complex.I) / 2) ∈ Complex.slitPlane := by
    rw [Complex.ofReal_zero, splValue_base_zero]
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    simp [Real.pi_ne_zero]
  have h1 : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) 0 :=
    continuousAt_const.div (by fun_prop) hne
  have h2 : ContinuousAt (fun ε : ℝ => ((Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ)) 0 :=
    ContinuousAt.comp (g := fun z : ℂ => z ^ (1 / 2 : ℂ))
      (f := fun ε : ℝ => (Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) (x := 0) (continuousAt_cpow_const hin) h1
  have h3 : Tendsto (fun ε : ℝ => ((Real.pi : ℂ) / (((ε : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ) / 2) (𝓝[>] 0)
      (𝓝 (((Real.pi : ℂ) / ((((0 : ℝ) : ℂ) - Complex.I) / 2)) ^ (1 / 2 : ℂ) / 2)) :=
    (h2.div_const 2).tendsto.mono_left nhdsWithin_le_nhds
  rwa [Complex.ofReal_zero, splValue_abel_value] at h3

/-! ## The Gaussian weight `e^{−εv²/2}` -/

/-- The derivative of `e^{−εv²/2}` is `−εv e^{−εv²/2}`. -/
theorem splValue_weight_hasDerivAt (ε v : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-(ε / 2) * v ^ 2)) (-ε * v * Real.exp (-(ε / 2) * v ^ 2)) v := by
  have h1 : HasDerivAt (fun v : ℝ => -(ε / 2) * v ^ 2) (-ε * v) v := by
    have h := (hasDerivAt_pow 2 v).const_mul (-(ε / 2))
    convert h using 1
    push_cast
    ring
  have h2 := h1.exp
  convert h2 using 1
  ring

/-- `e^{−εv²/2} → 0` as `v → +∞`, for `ε > 0`. -/
theorem splValue_weight_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun v : ℝ => Real.exp (-(ε / 2) * v ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => -(ε / 2) * v ^ 2) atTop atBot :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith)
  exact Real.tendsto_exp_atBot.comp h1

/-- `εv e^{−εv²/2}` is integrable on the line for `ε > 0`. -/
theorem splValue_integrable_dweight (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun v : ℝ => ε * v * Real.exp (-(ε / 2) * v ^ 2)) := by
  refine ((integrable_mul_exp_neg_mul_sq (b := ε / 2) (by positivity)).const_mul ε).congr
    (Eventually.of_forall fun v => ?_)
  show ε * (v * Real.exp (-(ε / 2) * v ^ 2)) = ε * v * Real.exp (-(ε / 2) * v ^ 2)
  ring

/-- `v² e^{−εv²/2}` is integrable on the line for `ε > 0`. -/
theorem splValue_integrable_sq_weight (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun v : ℝ => v ^ 2 * Real.exp (-(ε / 2) * v ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := ε / 2) (by positivity) (s := ((2 : ℕ) : ℝ)) (by norm_num)
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [Real.rpow_natCast]

/-- `∫₀^∞ εv e^{−εv²/2} dv = 1` for `ε > 0` (the primitive is `−e^{−εv²/2}`). -/
theorem splValue_integral_dweight (ε : ℝ) (hε : 0 < ε) :
    ∫ v : ℝ in Ioi 0, ε * v * Real.exp (-(ε / 2) * v ^ 2) = 1 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun v : ℝ => -Real.exp (-(ε / 2) * v ^ 2))
      (ε * x * Real.exp (-(ε / 2) * x ^ 2)) x := by
    intro x _
    have h := (splValue_weight_hasDerivAt ε x).fun_neg
    convert h using 1
    ring
  have ht : Tendsto (fun v : ℝ => -Real.exp (-(ε / 2) * v ^ 2)) atTop (𝓝 0) := by
    have h := (splValue_weight_tendsto ε hε).neg
    rwa [neg_zero] at h
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (splValue_integrable_dweight ε hε).integrableOn ht]
  simp

/-! ## Integrability of the integrands -/

/-- `e^{−εv²/2} e(v)` is integrable on the line for `ε > 0`. -/
theorem splValue_integrable_weight_mul_E (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v) := by
  refine (integrable_exp_neg_mul_sq (b := ε / 2) (by positivity)).mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact (Continuous.mul (by fun_prop) splValue_fresnelE_continuous).aestronglyMeasurable
  · exact le_of_eq (by
      rw [norm_mul, splValue_norm_fresnelE, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le])

/-- `c v e^{−εv²/2} F(v)` is integrable on the line for `ε > 0`, since `|F(v)| ≤ |v|`. -/
theorem splValue_integrable_lin_mul_prim (c ε : ℝ) (hε : 0 < ε) :
    Integrable (fun v : ℝ => ((c * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelPrim v) := by
  refine ((splValue_integrable_sq_weight ε hε).const_mul |c|).mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact (Continuous.mul (by fun_prop) splValue_prim_continuous).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h2 : 0 ≤ |c| * |v| * Real.exp (-(ε / 2) * v ^ 2) := by positivity
    calc |c| * |v| * Real.exp (-(ε / 2) * v ^ 2) * ‖fresnelPrim v‖
        ≤ |c| * |v| * Real.exp (-(ε / 2) * v ^ 2) * |v| := mul_le_mul_of_nonneg_left (splValue_norm_prim_le v) h2
      _ = |c| * (|v| ^ 2 * Real.exp (-(ε / 2) * v ^ 2)) := by ring
      _ = |c| * (v ^ 2 * Real.exp (-(ε / 2) * v ^ 2)) := by rw [sq_abs]

/-! ## Integration by parts -/

/-- `e^{−εv²/2} F(v) → 0` as `v → 0+`. -/
theorem splValue_tendsto_zero (ε : ℝ) :
    Tendsto ((fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ)) * fresnelPrim) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous ((fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ)) * fresnelPrim) :=
    Continuous.mul (by fun_prop) splValue_prim_continuous
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa [splValue_prim_zero] using h

/-- `e^{−εv²/2} F(v) → 0` as `v → +∞`, when `F` has a limit there. -/
theorem splValue_tendsto_top {L' : ℂ} (hF : Tendsto fresnelPrim atTop (𝓝 L')) (ε : ℝ) (hε : 0 < ε) :
    Tendsto ((fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ)) * fresnelPrim) atTop (𝓝 0) := by
  have h0 : Tendsto (fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp (splValue_weight_tendsto ε hε)
  have h := h0.mul hF
  rw [Complex.ofReal_zero, zero_mul] at h
  exact h

/-- Integration by parts on the half-line: `∫₀^∞ e^{−εv²/2} e(v) dv = ∫₀^∞ εv e^{−εv²/2} F(v) dv`. -/
theorem splValue_abel_parts {L' : ℂ} (hF : Tendsto fresnelPrim atTop (𝓝 L')) (ε : ℝ) (hε : 0 < ε) :
    ∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v =
      ∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelPrim v := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun v : ℝ => ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ))
    (u' := fun v : ℝ => ((-ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ))
    (v := fresnelPrim) (v' := fresnelE)
    (fun x _ => (splValue_weight_hasDerivAt ε x).ofReal_comp) (fun x _ => splValue_prim_hasDerivAt x)
    (splValue_integrable_weight_mul_E ε hε).integrableOn (splValue_integrable_lin_mul_prim (-ε) ε hε).integrableOn
    (splValue_tendsto_zero ε) (splValue_tendsto_top hF ε hε)
  rw [h, sub_zero, zero_sub, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  push_cast
  ring

/-! ## The Abel mean tends to the limit of `F` -/

/-- `A(ε) − L′ = ∫₀^∞ εv e^{−εv²/2} (F(v) − L′) dv`, when `F → L′` at `+∞`. -/
theorem splValue_abel_sub {L' : ℂ} (hF : Tendsto fresnelPrim atTop (𝓝 L')) (ε : ℝ) (hε : 0 < ε) :
    (∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v) - L' =
      ∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * (fresnelPrim v - L') := by
  have h1 : ∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * L' = L' := by
    rw [integral_mul_const, integral_complex_ofReal, splValue_integral_dweight ε hε, Complex.ofReal_one, one_mul]
  have hi1 : IntegrableOn (fun v : ℝ => ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelPrim v) (Ioi 0) :=
    (splValue_integrable_lin_mul_prim ε ε hε).integrableOn
  have hi2 : IntegrableOn (fun v : ℝ => ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * L') (Ioi 0) :=
    ((splValue_integrable_dweight ε hε).ofReal.mul_const L').integrableOn
  calc (∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v) - L'
      = (∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelPrim v) -
          ∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * L' := by
        rw [splValue_abel_parts hF ε hε, h1]
    _ = ∫ v : ℝ in Ioi 0, (((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelPrim v -
          ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * L') := (integral_sub hi1 hi2).symm
    _ = ∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * (fresnelPrim v - L') := by
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        ring

/-- For `v > 0`: `|εv e^{−εv²/2} (F(v) − L′)| ≤ 2ε e^{−εv²/2}`, from `|F(v) − L′| ≤ 2/v`. -/
theorem splValue_pointwise_bound {L' : ℂ} (hyp : ∀ x : ℝ, 0 < x → ‖fresnelPrim x - L'‖ ≤ 2 / x) (ε : ℝ)
    (hε : 0 < ε) (v : ℝ) (hv : 0 < v) :
    ‖((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * (fresnelPrim v - L')‖ ≤
      2 * ε * Real.exp (-(ε / 2) * v ^ 2) := by
  have hk : 0 ≤ ε * v * Real.exp (-(ε / 2) * v ^ 2) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
  calc ε * v * Real.exp (-(ε / 2) * v ^ 2) * ‖fresnelPrim v - L'‖
      ≤ ε * v * Real.exp (-(ε / 2) * v ^ 2) * (2 / v) := mul_le_mul_of_nonneg_left (hyp v hv) hk
    _ = 2 * ε * Real.exp (-(ε / 2) * v ^ 2) := by
        have hv' : v ≠ 0 := hv.ne'
        field_simp

/-- `|∫₀^∞ εv e^{−εv²/2} (F(v) − L′) dv| ≤ 2ε ∫₀^∞ e^{−εv²/2} dv = 2ε · √(π/(ε/2))/2`. -/
theorem splValue_abel_bound {L' : ℂ} (hyp : ∀ x : ℝ, 0 < x → ‖fresnelPrim x - L'‖ ≤ 2 / x) (ε : ℝ)
    (hε : 0 < ε) :
    ‖∫ v : ℝ in Ioi 0, ((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * (fresnelPrim v - L')‖ ≤
      2 * ε * (Real.sqrt (Real.pi / (ε / 2)) / 2) := by
  have hg : IntegrableOn (fun v : ℝ => 2 * ε * Real.exp (-(ε / 2) * v ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq (b := ε / 2) (by positivity)).const_mul (2 * ε)).integrableOn
  have hb : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖((ε * v * Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * (fresnelPrim v - L')‖ ≤
        2 * ε * Real.exp (-(ε / 2) * v ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun v hv => splValue_pointwise_bound hyp ε hε v hv)
  have h := norm_integral_le_of_norm_le hg hb
  rwa [integral_const_mul, integral_gaussian_Ioi] at h

/-- The bound `2ε · √(π/(ε/2))/2 = √(2πε)` tends to `0` as `ε → 0+`. -/
theorem splValue_bound_tendsto :
    Tendsto (fun ε : ℝ => 2 * ε * (Real.sqrt (Real.pi / (ε / 2)) / 2)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun ε : ℝ => Real.sqrt (2 * Real.pi * ε)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun ε : ℝ => Real.sqrt (2 * Real.pi * ε) :=
      Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
    have h' := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h'
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have h1 : 2 * Real.pi * ε = ε ^ 2 * (Real.pi / (ε / 2)) := by
    field_simp
  rw [h1, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε'.le]
  ring

/-- The Abel mean tends to `L′` as `ε → 0+`, when `|F(x) − L′| ≤ 2/x` for `x > 0`. -/
theorem splValue_abel_tendsto {L' : ℂ} (hyp : ∀ x : ℝ, 0 < x → ‖fresnelPrim x - L'‖ ≤ 2 / x) :
    Tendsto (fun ε : ℝ => ∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v) (𝓝[>] 0)
      (𝓝 L') := by
  have hF := splValue_tendsto_prim hyp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ splValue_bound_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [splValue_abel_sub hF ε hε]
  exact splValue_abel_bound hyp ε hε

/-! ## P-value -/

/-- **P-value** The value of the Fresnel integral: a number approached by `F` at rate `2/x` is `√π (1 + i)/2`. -/
theorem splFresnelValueFacts : SplFresnelValueFacts := by
  intro L' hyp
  have hA := splValue_abel_tendsto hyp
  have hB : Tendsto (fun ε : ℝ => ∫ v : ℝ in Ioi 0, ((Real.exp (-(ε / 2) * v ^ 2) : ℝ) : ℂ) * fresnelE v)
      (𝓝[>] 0) (𝓝 fresnelLimit) := by
    refine splValue_closed_tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using (splValue_abel_shape ε hε).symm
  exact tendsto_nhds_unique hA hB

end OscInt.StationaryLeadingAux
