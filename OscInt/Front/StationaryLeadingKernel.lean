/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Batch SPL, part Kernel: P-kernel from P-fresnel, P-bound (route `docs/proof-SPL.md`, Lemmas 2, 2′; sections 10, 11)

With `e(u) = e^{iu²/2}`, `E₁ = F − L`, `E₂ = u (F − L) + i e`: `E₁′ = e`, `E₂′ = E₁` and `(iκ₊)′ = E₂` on the line, since
`e′ = iu e` and `κ₊′ = e + iu (L − F)`. On `[0, ∞)`: `|E₁| ≤ 7/4 + |L| ≤ 4`, `|E₂| ≤ u (2/u) + 1 = 3`. For `τ > 0`,
`G = −F/(2x²) − e/(2x) + (i/2) F` has `G′ = F/x³` and `G(x) → (i/2) L`, so `κ₊(τ) = τ² ∫_τ^∞ F(x) x^{−3} dx` and
`|κ₊(τ)| ≤ τ² (7/4) τ^{−2}/2 = 7/8`. `κ` is the odd extension of `κ₊`, continuous because `κ₊(0) = 0`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory Set Filter Topology OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- `e′(u) = iu e(u)` for `e(u) = e^{iu²/2}`. -/
theorem splKer_hasDerivAt_fresnelE (u : ℝ) : HasDerivAt fresnelE ((u : ℂ) * Complex.I * fresnelE u) u := by
  unfold fresnelE
  have h1 : HasDerivAt (fun v : ℝ => ((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) ((u : ℂ) * Complex.I) u := by
    have h := (((hasDerivAt_pow 2 u).div_const 2).ofReal_comp).mul_const Complex.I
    convert h using 2
    push_cast; ring
  have h2 := h1.cexp
  convert h2 using 1
  ring

/-- The inclusion `u ↦ (u : ℂ)` of the line has derivative `1`. -/
theorem splKer_hasDerivAt_ofReal (u : ℝ) : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
  (hasDerivAt_id u).ofReal_comp

/-- `|e(u)| = 1`. -/
theorem splKer_norm_fresnelE (u : ℝ) : ‖fresnelE u‖ = 1 := by
  unfold fresnelE
  exact Complex.norm_exp_ofReal_mul_I _

/-- `κ₊(0) = 0`. -/
theorem splKer_kernelPos_zero : splKernelPos 0 = 0 := by simp [splKernelPos, fresnelPrim]

/-- Lemma 2, first primitive: `E₁′ = e` for `E₁ = F − L`. -/
theorem splKer_hasDerivAt_primOne (hF : SplFresnelFacts) (u : ℝ) : HasDerivAt splPrimOne (fresnelE u) u :=
  (hF.1 u).sub_const fresnelLimit

/-- Lemma 2, second primitive: `E₂′ = E₁` for `E₂ = u (F − L) + i e`. -/
theorem splKer_hasDerivAt_primTwo (hF : SplFresnelFacts) (u : ℝ) : HasDerivAt splPrimTwo (splPrimOne u) u := by
  have h := ((splKer_hasDerivAt_ofReal u).mul ((hF.1 u).sub_const fresnelLimit)).add
    ((splKer_hasDerivAt_fresnelE u).const_mul Complex.I)
  have hfun : splPrimTwo = (fun v : ℝ => (v : ℂ)) * (fun v => fresnelPrim v - fresnelLimit) +
      fun v => Complex.I * fresnelE v := by
    funext v; simp [splPrimTwo]
  rw [hfun]
  convert h using 1
  simp only [splPrimOne]
  linear_combination (-(u : ℂ) * fresnelE u) * Complex.I_sq

/-- Lemma 2: `κ₊′ = e + iu (L − F)` on the line. -/
theorem splKer_hasDerivAt_kernelPos (hF : SplFresnelFacts) (u : ℝ) :
    HasDerivAt splKernelPos (fresnelE u + Complex.I * (u : ℂ) * (fresnelLimit - fresnelPrim u)) u := by
  have hid := splKer_hasDerivAt_ofReal u
  have h1 := (hF.1 u).div_const 2
  have h2 := (hid.mul (splKer_hasDerivAt_fresnelE u)).div_const 2
  have h3 := (((hid.pow 2).const_mul Complex.I).div_const 2).mul ((hF.1 u).const_sub fresnelLimit)
  have h := (h1.add h2).add h3
  have hfun : splKernelPos = ((fun v => fresnelPrim v / 2) + fun v : ℝ => ((fun v : ℝ => (v : ℂ)) * fresnelE) v / 2) +
      (fun v : ℝ => Complex.I * (fun v : ℝ => (v : ℂ)) v ^ 2 / 2) * fun v => fresnelLimit - fresnelPrim v := by
    funext v; simp [splKernelPos, fresnelE]
  rw [hfun]
  convert h using 1
  simp only [Pi.pow_apply]
  ring

/-- Lemma 2, third primitive: `(iκ₊)′ = E₂`. -/
theorem splKer_hasDerivAt_I_mul_kernelPos (hF : SplFresnelFacts) (u : ℝ) :
    HasDerivAt (fun v => Complex.I * splKernelPos v) (splPrimTwo u) u := by
  have h := (splKer_hasDerivAt_kernelPos hF u).const_mul Complex.I
  convert h using 1
  simp only [splPrimTwo]
  linear_combination (-(u : ℂ) * (fresnelLimit - fresnelPrim u)) * Complex.I_sq

/-- `|L| ≤ 9/4` for `L = √π (1 + i)/2` (from `√π ≤ 2` and `|1 + i| ≤ 2`). -/
theorem splKer_norm_fresnelLimit_le : ‖fresnelLimit‖ ≤ 9 / 4 := by
  unfold fresnelLimit
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by simp; norm_num
  have h2 : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; simp]
    exact Real.sqrt_le_sqrt Real.pi_le_four
  have h3 : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  simp only [Complex.norm_ofNat]
  nlinarith [norm_nonneg ((1 : ℂ) + Complex.I)]

/-- `|E₁| ≤ 7/4 + |L| ≤ 4` on the line. -/
theorem splKer_norm_primOne_le (hB : SplFresnelBoundFacts) (u : ℝ) : ‖splPrimOne u‖ ≤ 4 :=
  calc ‖splPrimOne u‖ ≤ ‖fresnelPrim u‖ + ‖fresnelLimit‖ := norm_sub_le _ _
    _ ≤ 7 / 4 + 9 / 4 := add_le_add (hB u) splKer_norm_fresnelLimit_le
    _ = 4 := by norm_num

/-- `|E₂(u)| ≤ u (2/u) + 1 = 3` for `u ≥ 0`. -/
theorem splKer_norm_primTwo_le (hF : SplFresnelFacts) {u : ℝ} (hu : 0 ≤ u) : ‖splPrimTwo u‖ ≤ 3 := by
  unfold splPrimTwo
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0; simp [splKer_norm_fresnelE]
  · have h := hF.2.2 u hpos
    calc ‖(u : ℂ) * (fresnelPrim u - fresnelLimit) + Complex.I * fresnelE u‖
        ≤ ‖(u : ℂ) * (fresnelPrim u - fresnelLimit)‖ + ‖Complex.I * fresnelE u‖ := norm_add_le _ _
      _ = u * ‖fresnelPrim u - fresnelLimit‖ + 1 := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu, splKer_norm_fresnelE]; simp
      _ ≤ u * (2 / u) + 1 := by gcongr
      _ = 3 := by field_simp; norm_num

/-- `κ` is odd. -/
theorem splKer_kernel_neg (τ : ℝ) : splKernel (-τ) = -splKernel τ := by
  unfold splKernel
  rcases lt_trichotomy τ 0 with h | h | h
  · rw [ite_eq_left (by linarith), ite_eq_right (by linarith)]; simp
  · subst h; simp [splKer_kernelPos_zero]
  · rw [ite_eq_right (by linarith), ite_eq_left (by linarith)]; simp

/-- `κ₊` is continuous on the line (it is differentiable). -/
theorem splKer_continuous_kernelPos (hF : SplFresnelFacts) : Continuous splKernelPos :=
  continuous_iff_continuousAt.2 fun u => (splKer_hasDerivAt_kernelPos hF u).continuousAt

/-- `κ` is continuous: the two branches `κ₊(τ)` and `−κ₊(−τ)` agree at `τ = 0`, where both vanish. -/
theorem splKer_continuous_kernel (hF : SplFresnelFacts) : Continuous splKernel := by
  have hc := splKer_continuous_kernelPos hF
  unfold splKernel
  refine Continuous.if_le hc (hc.comp continuous_neg).neg continuous_const continuous_id ?_
  intro x hx
  have hx' : x = 0 := hx.symm
  subst hx'
  simp [splKer_kernelPos_zero]

/-- `G(x) = −F(x)/(2x²) − e(x)/(2x) + (i/2) F(x)`, a primitive of `F(x)/x³` on `(0, ∞)` (Lemma 2′). -/
noncomputable def splKerG (x : ℝ) : ℂ :=
  -(fresnelPrim x / (2 * (x : ℂ) ^ 2)) - fresnelE x / (2 * (x : ℂ)) + Complex.I / 2 * fresnelPrim x

/-- `G′(x) = F(x)/x³` for `x > 0`. -/
theorem splKer_hasDerivAt_G (hF : SplFresnelFacts) {x : ℝ} (hx : 0 < x) :
    HasDerivAt splKerG (fresnelPrim x / (x : ℂ) ^ 3) x := by
  obtain ⟨hd, _, _⟩ := hF
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 x := splKer_hasDerivAt_ofReal x
  have hn1 : (2 * (x : ℂ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ hxc)
  have hn2 : (2 * (x : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hxc
  have h1 := (hd x).div ((hid.pow 2).const_mul 2) hn1
  have h2 := (splKer_hasDerivAt_fresnelE x).div (hid.const_mul 2) hn2
  have h3 := (hd x).const_mul (Complex.I / 2)
  have h := (h1.neg.sub h2).add h3
  have hfun : splKerG = (-fun y : ℝ => fresnelPrim y / (2 * (y : ℂ) ^ 2)) - (fun y : ℝ => fresnelE y / (2 * (y : ℂ))) +
      fun y => Complex.I / 2 * fresnelPrim y := by
    funext y; simp [splKerG]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- `κ₊(τ) = τ² ((i/2) L − G(τ))` for `τ > 0`. -/
theorem splKer_kernelPos_eq (τ : ℝ) (hτ : 0 < τ) :
    splKernelPos τ = (τ : ℂ) ^ 2 * (Complex.I / 2 * fresnelLimit - splKerG τ) := by
  have hτc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ.ne'
  simp only [splKernelPos, splKerG]
  have : fresnelE τ = Complex.exp (((τ ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := rfl
  rw [← this]
  field_simp
  ring

/-- `F(x) → L` as `x → +∞` (from `|F(x) − L| ≤ 2/x`). -/
theorem splKer_tendsto_fresnelPrim (hF : SplFresnelFacts) : Tendsto fresnelPrim atTop (𝓝 fresnelLimit) := by
  obtain ⟨_, _, h2x⟩ := hF
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun x : ℝ => 2 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h0
  filter_upwards [eventually_gt_atTop 0] with x hx using h2x x hx

/-- `F(x)/(2x²) → 0` as `x → +∞` (`F` is bounded). -/
theorem splKer_tendsto_G_first (hB : SplFresnelBoundFacts) :
    Tendsto (fun x : ℝ => fresnelPrim x / (2 * (x : ℂ) ^ 2)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun x : ℝ => (7 / 4 : ℝ) / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [Complex.norm_ofNat]
  have hx0 : 0 < x := by linarith
  rw [div_le_div_iff₀ (by positivity) hx0]
  have := hB x
  nlinarith [norm_nonneg (fresnelPrim x), mul_nonneg hx0.le hx0.le]

/-- `e(x)/(2x) → 0` as `x → +∞` (`|e| = 1`). -/
theorem splKer_tendsto_G_second : Tendsto (fun x : ℝ => fresnelE x / (2 * (x : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h0
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_div, splKer_norm_fresnelE, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
  simp only [Complex.norm_ofNat]
  rw [div_le_div_iff₀ (by positivity) hx]
  nlinarith

/-- `G(x) → (i/2) L` as `x → +∞`. -/
theorem splKer_tendsto_G (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) :
    Tendsto splKerG atTop (𝓝 (Complex.I / 2 * fresnelLimit)) := by
  have h3 := (splKer_tendsto_fresnelPrim hF).const_mul (Complex.I / 2)
  have h := ((splKer_tendsto_G_first hB).neg.sub splKer_tendsto_G_second).add h3
  simp only [neg_zero, sub_zero, zero_add] at h
  exact h

/-- `|F(x)/x³| ≤ (7/4) x^{−3}` for `x > 0`. -/
theorem splKer_norm_integrand_le (hB : SplFresnelBoundFacts) {x : ℝ} (hx0 : 0 < x) :
    ‖fresnelPrim x / (x : ℂ) ^ 3‖ ≤ (7 / 4 : ℝ) * x ^ (-3 : ℝ) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le, Real.rpow_neg hx0.le,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hB x) (by positivity)

/-- The majorant `(7/4) x^{−3}` is integrable on `(τ, ∞)` for `τ > 0`. -/
theorem splKer_integrableOn_majorant {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => (7 / 4 : ℝ) * x ^ (-3 : ℝ)) (Ioi τ) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) hτ).const_mul _

/-- `F(x)/x³` is integrable on `(τ, ∞)` for `τ > 0`. -/
theorem splKer_integrableOn_integrand (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => fresnelPrim x / (x : ℂ) ^ 3) (Ioi τ) := by
  have hcF : Continuous fresnelPrim := continuous_iff_continuousAt.2 fun u => (hF.1 u).continuousAt
  have hmeas : AEStronglyMeasurable (fun x : ℝ => fresnelPrim x / (x : ℂ) ^ 3) (volume.restrict (Ioi τ)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div hcF.continuousOn (by fun_prop) ?_
    intro x hx
    have hx0 : 0 < x := hτ.trans hx
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 hx0.ne')
  exact Integrable.mono' (splKer_integrableOn_majorant hτ) hmeas
    ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun _ hx => splKer_norm_integrand_le hB (hτ.trans hx)))

/-- Lemma 2′: `∫_τ^∞ F(x) x^{−3} dx = (i/2) L − G(τ)` for `τ > 0`. -/
theorem splKer_integral_eq (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x in Ioi τ, fresnelPrim x / (x : ℂ) ^ 3 = Complex.I / 2 * fresnelLimit - splKerG τ :=
  integral_Ioi_of_hasDerivAt_of_tendsto (splKer_hasDerivAt_G hF hτ).continuousAt.continuousWithinAt
    (fun _ hx => splKer_hasDerivAt_G hF (hτ.trans hx)) (splKer_integrableOn_integrand hF hB hτ)
    (splKer_tendsto_G hF hB)

/-- `|∫_τ^∞ F(x) x^{−3} dx| ≤ (7/4) τ^{−2}/2` for `τ > 0`. -/
theorem splKer_norm_integral_le (hB : SplFresnelBoundFacts) {τ : ℝ} (hτ : 0 < τ) :
    ‖∫ x in Ioi τ, fresnelPrim x / (x : ℂ) ^ 3‖ ≤ (7 / 4 : ℝ) * (τ ^ (-2 : ℝ) / 2) :=
  calc ‖∫ x in Ioi τ, fresnelPrim x / (x : ℂ) ^ 3‖ ≤ ∫ x in Ioi τ, (7 / 4 : ℝ) * x ^ (-3 : ℝ) :=
        norm_integral_le_of_norm_le (splKer_integrableOn_majorant hτ)
          ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun _ hx => splKer_norm_integrand_le hB (hτ.trans hx)))
    _ = (7 / 4 : ℝ) * (τ ^ (-2 : ℝ) / 2) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hτ]
        norm_num

/-- Lemma 2′, the constant: `|κ₊(τ)| ≤ 7/8` for `τ > 0`. -/
theorem splKer_norm_kernelPos_le (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) (τ : ℝ) (hτ : 0 < τ) :
    ‖splKernelPos τ‖ ≤ 7 / 8 := by
  rw [splKer_kernelPos_eq τ hτ, ← splKer_integral_eq hF hB hτ, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hτ.le]
  have hτ2 : τ ^ 2 * τ ^ (-2 : ℝ) = 1 := by
    rw [Real.rpow_neg hτ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  calc τ ^ 2 * ‖∫ x in Ioi τ, fresnelPrim x / (x : ℂ) ^ 3‖ ≤ τ ^ 2 * ((7 / 4 : ℝ) * (τ ^ (-2 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (splKer_norm_integral_le hB hτ) (by positivity)
    _ = 7 / 8 * (τ ^ 2 * τ ^ (-2 : ℝ)) := by ring
    _ = 7 / 8 := by rw [hτ2]; ring

/-- `|κ| ≤ 7/8` on the line. -/
theorem splKer_norm_kernel_le (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) (τ : ℝ) : ‖splKernel τ‖ ≤ 7 / 8 := by
  unfold splKernel
  rcases lt_trichotomy τ 0 with h | h | h
  · rw [ite_eq_right (by linarith), norm_neg]; exact splKer_norm_kernelPos_le hF hB (-τ) (by linarith)
  · subst h; simp [splKer_kernelPos_zero]; norm_num
  · rw [ite_eq_left h.le]; exact splKer_norm_kernelPos_le hF hB τ h

/-- **P-kernel** from P-fresnel and P-bound: the three derivatives, `|E₁| ≤ 4` and `|E₂| ≤ 3` on `[0, ∞)`, and `κ`
odd, continuous, with `|κ| ≤ 7/8`. -/
theorem splKernelFacts_of (hF : SplFresnelFacts) (hB : SplFresnelBoundFacts) : SplKernelFacts :=
  ⟨splKer_hasDerivAt_primOne hF, splKer_hasDerivAt_primTwo hF, splKer_hasDerivAt_I_mul_kernelPos hF,
    fun u _ => splKer_norm_primOne_le hB u, fun _ hu => splKer_norm_primTwo_le hF hu, splKer_kernel_neg,
    splKer_continuous_kernel hF, splKer_norm_kernel_le hF hB⟩

end OscInt.StationaryLeadingAux
