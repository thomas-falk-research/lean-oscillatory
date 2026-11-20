/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp

/-!
# Batch VC2, part VC6: VC2-A, the quadratic phase attains the profile (route `docs/proof-VC2.md`, V7)

With `β = √(2w)` and `z = ∫_{−β}^{β} e^{ix²/2} dx`: `−Im (e^{−iw} z) = ∫_{−β}^{β} sin(w − x²/2) dx = A(w)` (the
integrand is even), and `−Im (e^{−iw} z) ≤ |e^{−iw} z| = |z|`.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- The integrand `sin(w − x²/2)` is even: its integral over `[−β, β]` is twice the integral over `[0, β]`. -/
theorem vdc2A_integral_sin_symm (w β : ℝ) :
    ∫ x in (-β)..β, Real.sin (w - x ^ 2 / 2) = 2 * ∫ u in (0 : ℝ)..β, Real.sin (w - u ^ 2 / 2) := by
  have hc : Continuous fun x : ℝ => Real.sin (w - x ^ 2 / 2) := by fun_prop
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable (-β) 0) (hc.intervalIntegrable 0 β)
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := β) (fun x : ℝ => Real.sin (w - x ^ 2 / 2))
  simp only [neg_sq, neg_zero] at hneg
  rw [← h, ← hneg]
  ring

/-- `−Im (e^{−iw} ∫_{−β}^{β} e^{ix²/2} dx) = ∫_{−β}^{β} sin(w − x²/2) dx`. -/
theorem vdc2A_neg_im_rotated (w β : ℝ) :
    -(Complex.exp (((-w : ℝ) : ℂ) * Complex.I) *
        ∫ x in (-β)..β, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).im =
      ∫ x in (-β)..β, Real.sin (w - x ^ 2 / 2) := by
  have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (((-w : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) MeasureTheory.volume (-β) β :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← intervalIntegral.integral_const_mul, ← Complex.imCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Complex.imCLM_apply]
  rw [← Complex.exp_add]
  have hx : ((-w : ℝ) : ℂ) * Complex.I + ((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I =
      ((-(w - x ^ 2 / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hx, Complex.exp_ofReal_mul_I_im, Real.sin_neg, neg_neg]

/-- `−Im (e^{iθ} z) ≤ |z|` for real `θ`. -/
theorem vdc2A_neg_im_rotated_le_norm (θ : ℝ) (z : ℂ) :
    -(Complex.exp ((θ : ℂ) * Complex.I) * z).im ≤ ‖z‖ :=
  calc -(Complex.exp ((θ : ℂ) * Complex.I) * z).im
      ≤ |(Complex.exp ((θ : ℂ) * Complex.I) * z).im| := neg_le_abs _
    _ ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) * z‖ := Complex.abs_im_le_norm _
    _ = ‖z‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **VC2-A** The quadratic phase on `[−√(2w), √(2w)]` attains the profile: `A(w) ≤ |∫ e^{ix²/2}|`. -/
theorem secondDerivAttained_part : SecondDerivAttainedStatement := by
  intro w _
  have h := vdc2A_neg_im_rotated_le_norm (-w)
    (∫ x in (-Real.sqrt (2 * w))..(Real.sqrt (2 * w)), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I))
  rw [vdc2A_neg_im_rotated w (Real.sqrt (2 * w)), vdc2A_integral_sin_symm w (Real.sqrt (2 * w))] at h
  exact h

end OscInt.SecondDerivSharpAux
