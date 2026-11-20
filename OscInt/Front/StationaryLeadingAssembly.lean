/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Batch SPL, part Assembly: SPL-I from P-line by scaling (route `docs/proof-SPL.md`, Corollary 3″ and section 10)

With `r = √λ` and `h(v) = g(v/r)`, `h₁ = g₁(·/r)/r`, `h₂ = g₂(·/r)/r²`, `h₃ = g₃(·/r)/r³` (again an amplitude), the
substitution `v = r u` gives `∫ h e = r ∫ g(u) e^{iλu²/2} du` and `∫ h₃ κ = r⁻² ∫ g₃(t) κ(r t) dt`. P-line for `h`
then reads `∫ g(u) e^{iλu²/2} du = 2 L g(0)/r − i r⁻³ ∫ g₃(t) κ(√λ t) dt`, and `√(2π/λ) e^{iπ/4} = 2L/r`,
`r⁻³ = λ^{−3/2}`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- `e^{iπ/4} = (√2/2)(1 + i)`. -/
theorem splAsm_exp_pi_div_four : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

/-- `√(2π) e^{iπ/4} = 2L` with `L = √π (1 + i)/2` the closed form `fresnelLimit`. -/
theorem splAsm_sqrt_two_pi_mul_exp :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = 2 * fresnelLimit := by
  rw [splAsm_exp_pi_div_four, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold fresnelLimit
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  push_cast
  linear_combination (((Real.sqrt Real.pi : ℝ) : ℂ) * (1 + Complex.I) / 2) * h2

/-- `√(2π/λ) e^{iπ/4} = 2L/√λ`: the constant of the leading term of `splRemainder`. -/
theorem splAsm_leading_const (lam : ℝ) :
    ((Real.sqrt (2 * Real.pi / lam) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      2 * fresnelLimit / ((Real.sqrt lam : ℝ) : ℂ) := by
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Complex.ofReal_div, div_mul_eq_mul_div,
    splAsm_sqrt_two_pi_mul_exp]

/-- `λ^{−3/2} = (√λ)⁻³` for `λ > 0` (`Real.rpow` on the left). -/
theorem splAsm_rpow_neg_three_halves {lam : ℝ} (hlam : 0 < lam) :
    lam ^ (-(3 : ℝ) / 2) = (Real.sqrt lam ^ 3)⁻¹ := by
  have e : (-(3 : ℝ) / 2) = (1 / 2 : ℝ) * (-((3 : ℕ) : ℝ)) := by norm_num
  rw [e, Real.rpow_mul hlam.le, ← Real.sqrt_eq_rpow, Real.rpow_neg (Real.sqrt_nonneg lam), Real.rpow_natCast]

/-- Chain rule for the dilation `v ↦ v/r`: if `f′ = f₁` on the line then `(f(·/r))′ = f₁(·/r)/r`. -/
theorem splAsm_hasDerivAt_comp_div {f f₁ : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f₁ x) x) (r v : ℝ) :
    HasDerivAt (fun v : ℝ => f (v / r)) (f₁ (v / r) / (r : ℂ)) v := by
  have h1 : HasDerivAt (fun v : ℝ => v / r) (1 / r) v := (hasDerivAt_id v).div_const r
  have h2 : HasDerivAt (fun v : ℝ => f (v / r)) ((1 / r : ℝ) • f₁ (v / r)) v := (hf (v / r)).scomp v h1
  convert h2 using 1
  rw [Complex.real_smul]
  push_cast
  ring

/-- The dilated amplitude `h = g(·/r)`, `h₁ = g₁(·/r)/r`, `h₂ = g₂(·/r)/r²`, `h₃ = g₃(·/r)/r³` is an amplitude. -/
theorem splAsm_amplitude_scale {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) {r : ℝ} (hr : r ≠ 0) :
    SplAmplitude (fun v : ℝ => g (v / r)) (fun v : ℝ => g₁ (v / r) / (r : ℂ))
      (fun v : ℝ => g₂ (v / r) / (r : ℂ) ^ 2) (fun v : ℝ => g₃ (v / r) / (r : ℂ) ^ 3) := by
  obtain ⟨h0, h1, h2, i0, i1, i2, i3⟩ := hg
  refine ⟨fun v => splAsm_hasDerivAt_comp_div h0 r v, fun v => ?_, fun v => ?_, i0.comp_div hr,
    (i1.comp_div hr).div_const _, (i2.comp_div hr).div_const _, (i3.comp_div hr).div_const _⟩
  · have h := (splAsm_hasDerivAt_comp_div h1 r v).div_const (r : ℂ)
    convert h using 1
    ring
  · have h := (splAsm_hasDerivAt_comp_div h2 r v).div_const ((r : ℂ) ^ 2)
    convert h using 1
    ring

/-- The substitution `v = r u` in the oscillatory integral: `∫ g(v/r) e(v) dv = r ∫ g(u) e^{i r² u²/2} du`. -/
theorem splAsm_integral_phase (g : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ v, g (v / r) * fresnelE v =
      (r : ℂ) * ∫ u, g u * Complex.exp (((r ^ 2 * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  have h := Measure.integral_comp_div
    (fun u : ℝ => g u * Complex.exp (((r ^ 2 * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) r
  rw [abs_of_pos hr, Complex.real_smul] at h
  rw [← h]
  congr 1
  funext v
  have e : r ^ 2 * (v / r) ^ 2 / 2 = v ^ 2 / 2 := by
    field_simp
  simp only [fresnelE]
  rw [e]

/-- The substitution `v = r t` in the kernel integral: `∫ (g₃(v/r)/r³) κ(v) dv = r⁻² ∫ g₃(t) κ(r t) dt`. -/
theorem splAsm_integral_kernel (g₃ : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ v, g₃ (v / r) / (r : ℂ) ^ 3 * splKernel v = ((r : ℂ) ^ 2)⁻¹ * ∫ t, g₃ t * splKernel (r * t) := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h := Measure.integral_comp_div (fun t : ℝ => g₃ t * splKernel (r * t)) r
  rw [abs_of_pos hr, Complex.real_smul] at h
  have e : (fun v : ℝ => g₃ (v / r) / (r : ℂ) ^ 3 * splKernel v) =
      fun v : ℝ => ((r : ℂ) ^ 3)⁻¹ * (g₃ (v / r) * splKernel (r * (v / r))) := by
    funext v
    rw [mul_div_cancel₀ v hr.ne']
    ring
  rw [e, integral_const_mul, h]
  field_simp

/-- **SPL-I from P-line**: the identity `R(g, λ) = −i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt` follows from the identity at
`λ = 1` applied to the dilated amplitude `g(·/√λ)`. -/
theorem stationaryLeadingIdentity_of (hL : SplLineFacts) : StationaryLeadingIdentityStatement := by
  intro g g₁ g₂ g₃ lam hg hlam
  have hr : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hrc : ((Real.sqrt lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h := hL _ _ _ _ (splAsm_amplitude_scale hg hr.ne')
  rw [splAsm_integral_phase g hr, splAsm_integral_kernel g₃ hr, Real.sq_sqrt hlam.le] at h
  simp only [zero_div] at h
  unfold splRemainder
  rw [mul_assoc, splAsm_leading_const, splAsm_rpow_neg_three_halves hlam, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp
  field_simp at h
  linear_combination h

end OscInt.StationaryLeadingAux
