/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.StationaryLeadingSharp
import OscInt.Front.StationaryLeadingFresnelTail
import OscInt.Front.StationaryLeadingFresnelValue
import OscInt.Front.StationaryLeadingFresnel
import OscInt.Front.StationaryLeadingKernel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Batch SPL-N, part Taylor: N1, N2, N4 and the small branch of N8 (route `docs/proof-SPLN.md`, section 2)

* **N1.** With `E(v) = e^{iv²/2}` and `Φ(x) = ∫₀ˣ (x − v)² E(v)/2 dv`: `κ₊(x) = x + iLx²/2 − iΦ(x)` for every real
  `x`. Proved by one application of the fundamental theorem of calculus in `v` (for fixed `x`) with the primitive
  `A(v) = (x²/2) F(v) + ix E(v) + (−iv E(v) + i F(v))/2` of `(x − v)² E(v)/2` (`F′ = E`, `E′ = ivE`); this is the
  expansion `(x − v)² = x² − 2xv + v²` of the route with `∫₀ˣ vE = −i(E(x) − 1)`, `∫₀ˣ v²E = −ixE(x) + iF(x)`.
* **N2** (`splnTaylor`). `∫₀ˣ (x − v)²/2 · (v²/2)^j/j! dv = I_j(x)`, and `Complex.exp_bound'` with `n = 32`,
  `‖iv²/2‖ = v²/2 ≤ 8` inside the integral, give `‖κ₊(x) − centre(√π, x)‖ ≤ 2 I_32(x)` on `[0, 4]`.
* **N4** (`splnSecond`). `κ₁ = E + ix(L − F)`, `κ₂ = i(L − F)`, `‖L − F(x)‖ ≤ 2/x`.
* **N8, first half** (`splnSmall`). `‖κ₊(x)‖ ≤ x + ‖L‖x²/2 + x³/6`, `‖L‖ ≤ 4/3`, so `‖κ₊‖ ≤ 11/16` on `[0, 1/2]`.
-/

namespace OscInt.SPLNAux

open MeasureTheory Set OscInt.Statements OscInt.Blueprint.StationaryLeading OscInt.Blueprint.SPLN
open OscInt.StationaryLeadingAux

/-- The proved P-fresnel facts of batch SPL. -/
theorem splnT_fresnelFacts : SplFresnelFacts :=
  splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts

/-- `Φ(x) = ∫₀ˣ (x − v)² E(v)/2 dv`. -/
noncomputable def splnT_phi (x : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..x, (((x - v) ^ 2 / 2 : ℝ) : ℂ) * fresnelE v

/-- The primitive `A(v) = (x²/2) F(v) + ix E(v) + (−iv E(v) + i F(v))/2` of `(x − v)² E(v)/2`. -/
noncomputable def splnT_anti (x : ℝ) : ℝ → ℂ := fun v =>
  (((x ^ 2 / 2 : ℝ) : ℂ) * fresnelPrim v + ((x : ℂ) * Complex.I) * fresnelE v) +
    (1 / 2 : ℂ) * (-((Complex.I * (v : ℂ)) * fresnelE v) + Complex.I * fresnelPrim v)

/-- `A′(v) = (x − v)² E(v)/2`. -/
theorem splnT_hasDerivAt_anti (x v : ℝ) :
    HasDerivAt (splnT_anti x) ((((x - v) ^ 2 / 2 : ℝ) : ℂ) * fresnelE v) v := by
  have hP := splValue_prim_hasDerivAt v
  have hE := splKer_hasDerivAt_fresnelE v
  have hid := splKer_hasDerivAt_ofReal v
  have h : HasDerivAt (splnT_anti x) _ v := ((hP.const_mul ((x ^ 2 / 2 : ℝ) : ℂ)).add (hE.const_mul ((x : ℂ) * Complex.I))).add
    ((((hid.const_mul Complex.I).mul hE).neg.add (hP.const_mul Complex.I)).const_mul (1 / 2 : ℂ))
  convert h using 1
  push_cast
  linear_combination ((-(x : ℂ) * (v : ℂ) + (v : ℂ) ^ 2 / 2) * fresnelE v) * Complex.I_sq

/-- The integrand of `Φ` is continuous. -/
theorem splnT_continuous_integrand (x : ℝ) :
    Continuous fun v : ℝ => (((x - v) ^ 2 / 2 : ℝ) : ℂ) * fresnelE v :=
  (Complex.continuous_ofReal.comp (by fun_prop)).mul splValue_fresnelE_continuous

/-- `Φ(x) = A(x) − A(0)`. -/
theorem splnT_phi_eq (x : ℝ) : splnT_phi x = splnT_anti x x - splnT_anti x 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => splnT_hasDerivAt_anti x v)
    ((splnT_continuous_integrand x).intervalIntegrable 0 x)

/-- **N1**: `κ₊(x) = x + iLx²/2 − iΦ(x)`. -/
theorem splnT_kernelPos_eq (x : ℝ) :
    splKernelPos x = (x : ℂ) + Complex.I * fresnelLimit * (x : ℂ) ^ 2 / 2 - Complex.I * splnT_phi x := by
  rw [splnT_phi_eq]
  have hE0 : fresnelE 0 = 1 := by simp [fresnelE]
  simp only [splnT_anti, splValue_prim_zero, hE0]
  unfold splKernelPos
  change fresnelPrim x / 2 + (x : ℂ) * fresnelE x / 2 + _ = _
  push_cast
  linear_combination (fresnelPrim x / 2 + (x : ℂ) * fresnelE x / 2 - x) * Complex.I_sq


/-- The real primitive of `(x − v)²/2 · (v²/2)^j/j!`. -/
noncomputable def splnT_wanti (j : ℕ) (x : ℝ) : ℝ → ℝ := fun v =>
  (1 / (2 ^ (j + 1) * (j.factorial : ℝ))) *
    ((x ^ 2 * (v ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)) - 2 * x * (v ^ (2 * j + 2) / ((2 * j + 2 : ℕ) : ℝ))) +
      v ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ))

/-- The derivative of the real primitive. -/
theorem splnT_hasDerivAt_wanti (j : ℕ) (x v : ℝ) :
    HasDerivAt (splnT_wanti j x) ((x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ j / (j.factorial : ℝ))) v := by
  have h1 := (hasDerivAt_pow (2 * j + 1) v).div_const ((2 * j + 1 : ℕ) : ℝ)
  have h2 := (hasDerivAt_pow (2 * j + 2) v).div_const ((2 * j + 2 : ℕ) : ℝ)
  have h3 := (hasDerivAt_pow (2 * j + 3) v).div_const ((2 * j + 3 : ℕ) : ℝ)
  have h : HasDerivAt (splnT_wanti j x) _ v := (((h1.const_mul (x ^ 2)).sub (h2.const_mul (2 * x))).add h3).const_mul
    (1 / (2 ^ (j + 1) * (j.factorial : ℝ)))
  convert h using 1
  rw [show 2 * j + 1 - 1 = 2 * j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    show 2 * j + 3 - 1 = 2 * j + 2 by omega, div_pow, ← pow_mul]
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hA : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hB : ((2 * j + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hC : ((2 * j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `∫₀ˣ (x − v)²/2 · (v²/2)^j/j! dv = I_j(x)`. -/
theorem splnT_integral_weight (j : ℕ) (x : ℝ) :
    ∫ v in (0 : ℝ)..x, (x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ j / (j.factorial : ℝ)) = splnI j x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => splnT_hasDerivAt_wanti j x v)
    ((by fun_prop : Continuous fun v : ℝ => (x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ j / (j.factorial : ℝ))).intervalIntegrable
      0 x)]
  simp only [splnT_wanti, splnI]
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  have hA : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have hB : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
  have hC : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  rw [zero_pow (by omega), zero_pow (by omega), zero_pow (by omega)]
  field_simp
  ring

/-- The Taylor polynomial `S(v) = Σ_{m<32} (iv²/2)^m/m!`. -/
noncomputable def splnT_S (v : ℝ) : ℂ :=
  ∑ m ∈ Finset.range 32, (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)

/-- One term: `∫₀ˣ (x − v)²/2 · (iv²/2)^j/j! dv = i^j I_j(x)`. -/
theorem splnT_integral_term (j : ℕ) (x : ℝ) :
    ∫ v in (0 : ℝ)..x, (((x - v) ^ 2 / 2 : ℝ) : ℂ) * ((((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) =
      Complex.I ^ j * (splnI j x : ℂ) := by
  have hpt : ∀ v : ℝ, (((x - v) ^ 2 / 2 : ℝ) : ℂ) * ((((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) =
      Complex.I ^ j * (((x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ j / (j.factorial : ℝ)) : ℝ) : ℂ) := by
    intro v; push_cast; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, splnT_integral_weight]

/-- The Taylor part integrates to the polynomial centre: `∫₀ˣ (x − v)²/2 · S(v) dv = Σ_{j<32} i^j I_j(x)`. -/
theorem splnT_integral_S (x : ℝ) :
    ∫ v in (0 : ℝ)..x, (((x - v) ^ 2 / 2 : ℝ) : ℂ) * splnT_S v =
      ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ) := by
  simp only [splnT_S, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => splnT_integral_term j x
  · intro j _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `Φ(x) − Σ_{j<32} i^j I_j(x) = ∫₀ˣ (x − v)²/2 · (E(v) − S(v)) dv`. -/
theorem splnT_phi_sub (x : ℝ) :
    splnT_phi x - ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ) =
      ∫ v in (0 : ℝ)..x, (((x - v) ^ 2 / 2 : ℝ) : ℂ) * (fresnelE v - splnT_S v) := by
  rw [← splnT_integral_S, splnT_phi, ← intervalIntegral.integral_sub]
  · simp only [mul_sub]
  · exact (splnT_continuous_integrand x).intervalIntegrable _ _
  · exact Continuous.intervalIntegrable (by unfold splnT_S; fun_prop) _ _

/-- The Taylor remainder of `E` on `|v| ≤ 4`: `‖E(v) − S(v)‖ ≤ 2 (v²/2)^32/32!`. -/
theorem splnT_norm_E_sub_S (v : ℝ) (hv : |v| ≤ 4) :
    ‖fresnelE v - splnT_S v‖ ≤ (v ^ 2 / 2) ^ 32 / ((32).factorial : ℝ) * 2 := by
  have hz : ‖((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I‖ = v ^ 2 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hv2 : v ^ 2 ≤ 16 := by nlinarith [abs_nonneg v, sq_abs v]
  have h := Complex.exp_bound' (x := ((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) (n := 32)
    (by rw [hz]; norm_num; nlinarith)
  rw [hz] at h
  exact h

/-- **N2** inside the integral: `‖Φ(x) − Σ_{j<32} i^j I_j(x)‖ ≤ 2 I_32(x)` on `[0, 4]`. -/
theorem splnT_norm_phi_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    ‖splnT_phi x - ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ)‖ ≤ 2 * splnI 32 x := by
  rw [splnT_phi_sub]
  have hb : ∫ v in (0 : ℝ)..x, (x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ 32 / ((32).factorial : ℝ) * 2) =
      2 * splnI 32 x := by
    rw [← splnT_integral_weight 32 x, ← intervalIntegral.integral_const_mul]
    congr 1; funext v; ring
  rw [← hb]
  refine intervalIntegral.norm_integral_le_of_norm_le hx0 (Filter.Eventually.of_forall fun v hv => ?_)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (splnT_norm_E_sub_S v (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])) (by positivity)

/-- **N1 + N2** (`SplnTaylorFacts`): `‖κ₊(x) − centre(√π, x)‖ ≤ 2 I_32(x)` for `0 ≤ x ≤ 4`. -/
theorem splnTaylor : SplnTaylorFacts := by
  intro x hx0 hx4
  have h : splKernelPos x - splnCentre (Real.sqrt Real.pi) x =
      -Complex.I * (splnT_phi x - ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ)) := by
    rw [splnT_kernelPos_eq]; unfold splnCentre fresnelLimit; ring
  rw [h, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact splnT_norm_phi_sub_le x hx0 hx4

/-- **N4** (`SplnSecondFacts`): `κ₁ = E + ix(L − F)`, `κ₂ = i(L − F)`, `‖κ₂(x)‖ ≤ 2/x` on `(0, ∞)`. -/
theorem splnSecond : SplnSecondFacts := by
  refine ⟨fun x => fresnelE x + Complex.I * (x : ℂ) * (fresnelLimit - fresnelPrim x),
    fun x => Complex.I * (fresnelLimit - fresnelPrim x),
    fun x _ => splKer_hasDerivAt_kernelPos splnT_fresnelFacts x, fun x _ => ?_, fun x hx => ?_⟩
  · have h := (splKer_hasDerivAt_fresnelE x).add (((splKer_hasDerivAt_ofReal x).const_mul Complex.I).mul
      ((splValue_prim_hasDerivAt x).const_sub fresnelLimit))
    convert h using 1
    ring
  · rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev]
    exact splnT_fresnelFacts.2.2 x hx

/-- `‖L‖ ≤ 4/3`: `‖L‖² = π/2` and `π < 3.15`. -/
theorem splnT_norm_fresnelLimit_le : ‖fresnelLimit‖ ≤ 4 / 3 := by
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hsq : ‖fresnelLimit‖ ^ 2 = Real.pi / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [fresnelLimit]
    nlinarith [hs]
  nlinarith [norm_nonneg fresnelLimit, hsq, Real.pi_lt_d2]

/-- `‖Φ(x)‖ ≤ x³/6` for `x ≥ 0`. -/
theorem splnT_norm_phi_le (x : ℝ) (hx : 0 ≤ x) : ‖splnT_phi x‖ ≤ x ^ 3 / 6 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le hx (μ := volume)
    (f := fun v : ℝ => (((x - v) ^ 2 / 2 : ℝ) : ℂ) * fresnelE v)
    (g := fun v : ℝ => (x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ 0 / ((0).factorial : ℝ)))
    (Filter.Eventually.of_forall fun v _ => by
      rw [norm_mul, splKer_norm_fresnelE, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp)
    ((by fun_prop : Continuous fun v : ℝ => (x - v) ^ 2 / 2 * ((v ^ 2 / 2) ^ 0 / ((0).factorial : ℝ))).intervalIntegrable
      0 x)
  rw [splnT_integral_weight 0 x] at h
  refine h.trans (le_of_eq ?_)
  simp [splnI]
  ring

/-- **N8, first half**: `‖κ₊(x)‖ ≤ 11/16` on `[0, 1/2]`. -/
theorem splnSmall : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → ‖OscInt.Statements.splKernelPos x‖ ≤ 11 / 16 := by
  intro x hx0 hx1
  have hL := splnT_norm_fresnelLimit_le
  have hP := splnT_norm_phi_le x hx0
  calc ‖splKernelPos x‖
      = ‖(x : ℂ) + Complex.I * fresnelLimit * (x : ℂ) ^ 2 / 2 - Complex.I * splnT_phi x‖ := by
        rw [splnT_kernelPos_eq]
    _ ≤ ‖(x : ℂ) + Complex.I * fresnelLimit * (x : ℂ) ^ 2 / 2‖ + ‖Complex.I * splnT_phi x‖ := norm_sub_le _ _
    _ ≤ ‖(x : ℂ)‖ + ‖Complex.I * fresnelLimit * (x : ℂ) ^ 2 / 2‖ + ‖Complex.I * splnT_phi x‖ := by
        gcongr; exact norm_add_le _ _
    _ = x + ‖fresnelLimit‖ * x ^ 2 / 2 + ‖splnT_phi x‖ := by
        simp [norm_pow, Complex.norm_real, abs_of_nonneg hx0]
    _ ≤ x + 4 / 3 * x ^ 2 / 2 + x ^ 3 / 6 := by gcongr
    _ ≤ 11 / 16 := by nlinarith [mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0]

end OscInt.SPLNAux
