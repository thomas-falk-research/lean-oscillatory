/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.PeriodicAnalytic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Batch PA, part P-series: the Fourier series of the restriction to the real axis converges pointwise

Route `docs/proof-PA.md`, "Part P-series". The restriction `θ ↦ v θ` is continuous and `2π`-periodic, so it is
a continuous function on `AddCircle (2π)`; its Mathlib Fourier coefficients are
`(2π)⁻¹ ∫_0^{2π} v(θ) e^{−ikθ} dθ`, summable by the coefficient bound, and
`has_pointwise_sum_fourier_series_of_summable` gives the pointwise sum.
-/

namespace OscInt.PeriodicAnalyticAux

open OscInt.Statements OscInt.Blueprint.PeriodicAnalytic

/-- Real points lie in every open strip of positive half-width. -/
theorem fourierSeries_ofReal_mem {a : ℝ} (ha : 0 < a) (x : ℝ) : (x : ℂ) ∈ openStrip a := by
  simp [openStrip, ha]

/-- The restriction of a periodic-analytic function to the real axis is continuous. -/
theorem fourierSeries_continuous {v : ℂ → ℂ} {a M : ℝ} (ha : 0 < a) (hv : PeriodicAnalyticOn v a M) :
    Continuous fun θ : ℝ => v (θ : ℂ) :=
  hv.1.continuousOn.comp_continuous Complex.continuous_ofReal (fourierSeries_ofReal_mem ha)

/-- The restriction of a periodic-analytic function to the real axis has period `2π`. -/
theorem fourierSeries_periodic {v : ℂ → ℂ} {a M : ℝ} (ha : 0 < a) (hv : PeriodicAnalyticOn v a M) :
    Function.Periodic (fun θ : ℝ => v (θ : ℂ)) (2 * Real.pi) := by
  intro θ
  change v ((θ + 2 * Real.pi : ℝ) : ℂ) = v (θ : ℂ)
  rw [Complex.ofReal_add]
  exact hv.2.1 _ (fourierSeries_ofReal_mem ha θ)

/-- The geometric majorant `e^{−a|k|}` is summable over the integers. -/
theorem fourierSeries_summable_exp {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => Real.exp (-(a * |(k : ℝ)|)) := by
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable fun n : ℕ => Real.exp (-a) ^ n := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeo.congr fun n => ?_
    rw [← Real.exp_nat_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    congr 1
    ring
  · refine (hgeo.mul_left (Real.exp (-a))).congr fun n => ?_
    have hn : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hn, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring

/-- The Mathlib character `fourier k` on `AddCircle (2π)` at a real point is `e^{ikx}`, in the blueprint's shape. -/
theorem fourierSeries_fourier_coe [Fact (0 < 2 * Real.pi)] (k : ℤ) (x : ℝ) :
    (fourier k (x : AddCircle (2 * Real.pi)) : ℂ) = Complex.exp (↑((k : ℝ) * x) * Complex.I) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- The Mathlib Fourier coefficients of the lifted restriction are the blueprint's normalised Fourier integrals. -/
theorem fourierSeries_coeff [Fact (0 < 2 * Real.pi)] {u : ℝ → ℂ} (hu : Function.Periodic u (2 * Real.pi))
    (k : ℤ) :
    fourierCoeff (hu.lift : AddCircle (2 * Real.pi) → ℂ) k =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), u θ * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) := by
  rw [fourierCoeff_eq_intervalIntegral _ k 0, zero_add, one_div, Complex.real_smul, Complex.ofReal_inv]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  change fourier (-k) (θ : AddCircle (2 * Real.pi)) • hu.lift (θ : AddCircle (2 * Real.pi)) = _
  rw [Function.Periodic.lift_coe, fourierSeries_fourier_coe, smul_eq_mul, mul_comm]
  congr 3
  push_cast
  ring

/-- **P-series** The Fourier series of the restriction of a periodic-analytic function converges to it pointwise. -/
theorem fourierSeriesFacts : FourierSeriesFacts := by
  intro v a M ha hv hbound x
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hper := fourierSeries_periodic ha hv
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨hper.lift, continuous_coinduced_dom.mpr (fourierSeries_continuous ha hv)⟩
  have hcoeff : ∀ k : ℤ, fourierCoeff F k = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) :=
    fun k => fourierSeries_coeff hper k
  have hsummable : Summable (fourierCoeff F) := by
    refine Summable.of_norm_bounded ((fourierSeries_summable_exp ha).mul_left M) fun k => ?_
    rw [hcoeff k, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le,
      inv_mul_le_iff₀ Real.two_pi_pos]
    linarith [hbound k]
  have hsum := has_pointwise_sum_fourier_series_of_summable hsummable (x : AddCircle (2 * Real.pi))
  have hFx : F (x : AddCircle (2 * Real.pi)) = v (x : ℂ) := hper.lift_coe x
  rw [hFx] at hsum
  refine hsum.congr_fun fun k => ?_
  rw [smul_eq_mul, hcoeff k, fourierSeries_fourier_coe]

end OscInt.PeriodicAnalyticAux
