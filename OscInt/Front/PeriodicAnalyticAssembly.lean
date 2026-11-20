/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.PeriodicAnalytic

/-!
# Batch PA: the lead's assembly against the blueprint (route `docs/proof-PA.md`)

PA-C from the contour shift (let the height tend to the edge of the strip); PA-T from PA-C, the pointwise Fourier
series and the alias bound; LC-1 from PA-C applied to `z ↦ e^{it cos z}`. Compiled before any part was proved.
-/

namespace OscInt.PeriodicAnalyticAux

open OscInt.Statements OscInt.Blueprint.PeriodicAnalytic

/-- The Fourier integral is bounded with any `b ∈ [0, a)` in place of `a`: shift the contour by `b` away from the
side on which `e^{−ikz}` grows. -/
theorem coeff_le_of_lt (hS : ContourShiftFacts) {v : ℂ → ℂ} {a M b : ℝ} (k : ℤ) (hv : PeriodicAnalyticOn v a M)
    (hb0 : 0 ≤ b) (hba : b < a) :
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)‖ ≤
      2 * Real.pi * M * Real.exp (-(b * |(k : ℝ)|)) := by
  obtain ⟨b', hb'abs, hkb⟩ : ∃ b' : ℝ, |b'| = b ∧ (k : ℝ) * b' = -(b * |(k : ℝ)|) := by
    rcases le_or_gt 0 k with h | h
    · exact ⟨-b, by rw [abs_neg, abs_of_nonneg hb0], by
        rw [abs_of_nonneg (by exact_mod_cast h)]; ring⟩
    · exact ⟨b, abs_of_nonneg hb0, by rw [abs_of_neg (by exact_mod_cast h)]; ring⟩
  rw [hS v a M b' k hv (by rw [hb'abs]; exact hba)]
  calc ‖∫ θ in (0 : ℝ)..(2 * Real.pi), v ((θ : ℂ) + (b' : ℂ) * Complex.I) *
          Complex.exp (-((k : ℂ) * ((θ : ℂ) + (b' : ℂ) * Complex.I)) * Complex.I)‖
      ≤ (M * Real.exp (-(b * |(k : ℝ)|))) * |2 * Real.pi - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro θ _
        have h1 : ‖v ((θ : ℂ) + (b' : ℂ) * Complex.I)‖ ≤ M :=
          hv.2.2 _ (by simp [openStrip, hb'abs, hba])
        have h2 : (-((k : ℂ) * ((θ : ℂ) + (b' : ℂ) * Complex.I)) * Complex.I).re = -(b * |(k : ℝ)|) := by
          rw [← hkb]; simp
        rw [norm_mul, Complex.norm_exp, h2]
        gcongr
    _ = 2 * Real.pi * M * Real.exp (-(b * |(k : ℝ)|)) := by
        rw [sub_zero, abs_of_pos Real.two_pi_pos]; ring

/-- **PA-C from the contour shift**: let `b ↑ a`. -/
theorem fourierCoeffStrip_of (hS : ContourShiftFacts) : FourierCoeffStripStatement := by
  intro v a M k ha hv
  have hcont : ContinuousWithinAt (fun b : ℝ => 2 * Real.pi * M * Real.exp (-(b * |(k : ℝ)|))) (Set.Iio a) a :=
    Continuous.continuousWithinAt (by fun_prop)
  refine ge_of_tendsto hcont.tendsto ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with b hb
  exact coeff_le_of_lt hS k hv hb.1.le hb.2

/-- **PA-T from PA-C, the Fourier series and the alias bound.** -/
theorem trapezoidalRule_of (hC : FourierCoeffStripStatement) (hF : FourierSeriesFacts) (hA : AliasBoundFacts) :
    TrapezoidalRuleStatement := by
  intro v a M N ha hN hv
  have hIb : ∀ k : ℤ, ‖∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)‖ ≤
      2 * Real.pi * M * Real.exp (-(a * |(k : ℝ)|)) := fun k => hC v a M k ha hv
  have hsum := hA
    (fun k : ℤ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I))
    (fun j : ℕ => v ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ)) a M N ha hN
    (fun k => by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le,
        inv_mul_le_iff₀ Real.two_pi_pos]
      linarith [hIb k])
    (fun j _ => hF v a M ha hv hIb (2 * Real.pi * (j : ℝ) / (N : ℝ)))
  have key : trapezoidalSum v N - ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (((N : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range N, v ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ) -
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-(((0 : ℤ) : ℝ) * θ)) * Complex.I)) := by
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    have h0 : ∀ θ : ℝ, v (θ : ℂ) * Complex.exp (↑(-(((0 : ℤ) : ℝ) * θ)) * Complex.I) = v (θ : ℂ) := by
      intro θ; simp
    simp_rw [h0]
    rw [trapezoidalSum, mul_sub, mul_inv_cancel_left₀ hpi, ← mul_assoc]
    congr 2
    push_cast
    rw [div_eq_mul_inv]
  rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  calc 2 * Real.pi * _ ≤ 2 * Real.pi * (2 * M / (Real.exp (a * (N : ℝ)) - 1)) :=
        mul_le_mul_of_nonneg_left hsum Real.two_pi_pos.le
    _ = 4 * Real.pi * M / (Real.exp (a * (N : ℝ)) - 1) := by ring

/-- **LC-1 from PA-C and the kernel integrand.** -/
theorem latticeKernel1LightCone_of (hC : FourierCoeffStripStatement) (hK : KernelIntegrandFacts) :
    LatticeKernel1LightConeStatement := by
  intro t η n hη
  rcases hη.eq_or_lt with rfl | hpos
  · rw [Real.sinh_zero, mul_zero, mul_zero, sub_zero, Real.exp_zero, mul_one, latticeKernel1]
    calc ‖∫ k in (-Real.pi)..Real.pi, Complex.exp (↑(t * Real.cos k + (n : ℝ) * k) * Complex.I)‖
        ≤ 1 * |Real.pi - -Real.pi| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x _
          rw [Complex.norm_exp_ofReal_mul_I]
      _ = 2 * Real.pi := by rw [sub_neg_eq_add, abs_of_pos (by positivity)]; ring
  · rw [hK.2 t n]
    refine (hC _ η _ (-n) hpos (hK.1 t η hpos)).trans_eq ?_
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    rw [abs_neg]
    ring

end OscInt.PeriodicAnalyticAux
