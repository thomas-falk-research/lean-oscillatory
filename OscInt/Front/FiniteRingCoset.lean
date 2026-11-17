/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing
import OscInt.Front.PeriodicAnalyticFinal

/-!
# Batch FR, part F-coset: the method of images for the ring kernel (FR-S)

Route `docs/proof-FR.md`, "Part F-coset". The function `v(z) = e^{−2it} · e^{i(2t) cos z} · e^{irz}` is
periodic-analytic on the strip of half-width `1`; its normalised Fourier coefficient of index `k` is the line kernel
`G(t, r − k)`; its Fourier series converges to it at every real point (PA-C and the series part of batch PA); at the
`N` nodes `2πj/N` the aliasing identity of batch PA collapses the `N` series to the multiples of `N`, and the
reflection `m ↦ −m` gives the coset `r + Nℤ`.
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

/-- The symbol of the ring at time `t` and site `r`: `v(z) = e^{−2it} · e^{i(2t) cos z} · e^{irz}`. -/
noncomputable def ringS_v (t : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.cos z * Complex.I) *
    Complex.exp ((r : ℂ) * z * Complex.I)

/-- On the strip `|Im z| < 1` the modulus of `e^{irz}` is at most `e^{|r|}`. -/
theorem ringS_norm_exp_le (r : ℤ) (z : ℂ) (hz : |z.im| < 1) :
    ‖Complex.exp ((r : ℂ) * z * Complex.I)‖ ≤ Real.exp |(r : ℝ)| := by
  have hre : ((r : ℂ) * z * Complex.I).re = -((r : ℝ) * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.norm_exp, hre, Real.exp_le_exp]
  calc -((r : ℝ) * z.im) ≤ |(r : ℝ) * z.im| := neg_le_abs _
    _ = |(r : ℝ)| * |z.im| := abs_mul _ _
    _ ≤ |(r : ℝ)| * 1 := mul_le_mul_of_nonneg_left hz.le (abs_nonneg _)
    _ = |(r : ℝ)| := mul_one _

/-- The symbol is `2π`-periodic, because `r` is an integer. -/
theorem ringS_v_add_two_pi (t : ℝ) (r : ℤ) (z : ℂ) :
    ringS_v t r (z + ((2 * Real.pi : ℝ) : ℂ)) = ringS_v t r z := by
  have h2 : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; rfl
  have h3 : (r : ℂ) * (z + 2 * (Real.pi : ℂ)) * Complex.I =
      (r : ℂ) * z * Complex.I + (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  simp only [ringS_v]
  rw [h2, Complex.cos_add_two_pi, h3, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The symbol is periodic-analytic on the strip of half-width `1`, with bound `e^{|2t| sinh 1} e^{|r|}`. -/
theorem ringS_periodicAnalyticOn (t : ℝ) (r : ℤ) :
    PeriodicAnalyticOn (ringS_v t r) 1 (Real.exp (|2 * t| * Real.sinh 1) * Real.exp |(r : ℝ)|) := by
  refine ⟨?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun z : ℂ =>
        Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.cos z * Complex.I) *
          Complex.exp ((r : ℂ) * z * Complex.I) :=
      ((differentiable_const _).mul (Complex.differentiable_exp.comp
        (((differentiable_const _).mul Complex.differentiable_cos).mul (differentiable_const _)))).mul
        (Complex.differentiable_exp.comp
          (((differentiable_const _).mul differentiable_id).mul (differentiable_const _)))
    exact hd.differentiableOn
  · intro z _
    exact ringS_v_add_two_pi t r z
  · intro z hz
    have hz' : |z.im| < 1 := hz
    simp only [ringS_v]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul (OscInt.PeriodicAnalyticAux.kernelIntegrand_norm_le (2 * t) 1 z hz')
      (ringS_norm_exp_le r z hz') (norm_nonneg _) (Real.exp_pos _).le

/-- The Fourier integral of index `k` of the symbol is `e^{−2it} I(2t, r − k)`. -/
theorem ringS_fourierIntegral (t : ℝ) (r k : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ringS_v t r (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      Complex.exp (↑(-(2 * t)) * Complex.I) * latticeKernel1 (2 * t) ((r - k : ℤ) : ℝ) := by
  rw [OscInt.PeriodicAnalyticAux.kernelIntegrand_latticeKernel1_eq (2 * t) (r - k),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have h : Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      Complex.exp (↑(-(((-(r - k) : ℤ) : ℝ) * θ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [ringS_v]
  rw [← h]
  ring

/-- The normalised Fourier coefficient of index `k` of the symbol is the line kernel at `r − k`. -/
theorem ringS_coeff (t : ℝ) (r k : ℤ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ringS_v t r (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)) =
      lineKernel t (r - k) := by
  rw [ringS_fourierIntegral, lineKernel, mul_assoc]

/-- The Fourier series of the symbol, with the line kernel as coefficients, converges to it at every real point. -/
theorem ringS_hasSum_series (t : ℝ) (r : ℤ) (x : ℝ) :
    HasSum (fun k : ℤ => lineKernel t (r - k) * Complex.exp (↑((k : ℝ) * x) * Complex.I))
      (ringS_v t r (x : ℂ)) := by
  have hv := ringS_periodicAnalyticOn t r
  have h := OscInt.PeriodicAnalyticAux.fourierSeriesFacts (ringS_v t r) 1 _ one_pos hv
    (fun k => OscInt.API.fourierCoeffStrip (ringS_v t r) 1 _ k one_pos hv) x
  refine h.congr_fun fun k => ?_
  rw [ringS_coeff]

/-- At a real point the symbol is the summand of the ring kernel. -/
theorem ringS_v_ofReal (t : ℝ) (r : ℤ) (θ : ℝ) :
    ringS_v t r (θ : ℂ) = Complex.exp (↑(2 * t * (Real.cos θ - 1) + (r : ℝ) * θ) * Complex.I) := by
  simp only [ringS_v]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The aliasing identity at the `N` nodes: the ring kernel is the sum of the line kernel over `r − mN`. -/
theorem ringS_hasSum_sub (N : ℕ) (t : ℝ) (r : ℤ) (hN : 0 < N) :
    HasSum (fun m : ℤ => lineKernel t (r - m * (N : ℤ))) (ringKernel N t r) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1 := OscInt.PeriodicAnalyticAux.alias_hasSum_multiples (fun k : ℤ => lineKernel t (r - k))
    (fun j : ℕ => ringS_v t r ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ)) hN
    (fun j _ => ringS_hasSum_series t r (2 * Real.pi * (j : ℝ) / (N : ℝ)))
  have h2 := h1.mul_left ((N : ℂ)⁻¹)
  have hval : (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, ringS_v t r ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ) =
      ringKernel N t r := by
    unfold ringKernel
    rw [Complex.ofReal_natCast]
    congr 1
    exact Finset.sum_congr rfl fun j _ => ringS_v_ofReal t r _
  rw [hval] at h2
  refine h2.congr_fun fun m => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]

/-- **FR-S** Method of images: the ring kernel is the line kernel summed over the coset `r + Nℤ`. -/
theorem ringCosetSumStatement_part : RingCosetSumStatement := by
  intro N t r hN
  have h := (Equiv.neg ℤ).hasSum_iff.mpr (ringS_hasSum_sub N t r hN)
  refine h.congr_fun fun m => ?_
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [neg_mul, sub_neg_eq_add]

end OscInt.FiniteRingAux
