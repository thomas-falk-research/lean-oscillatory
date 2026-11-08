/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4Limit

/-!
# S4.3 assembly against the blueprint interfaces

`D4ConstantPosStatement` from C1–C5 (`Blueprint/D4Limit.lean`; route `docs/proof-S43.md`):
`cosMomentPartial R = R^{-1/3} sin R + (1/3) S(R)` (C1), `S(R) → S > 0` (C2) and `R^{-1/3} sin R → 0` give
`cosMomentPartial → S/3`, hence `cosMoment = S/3 > 0`; integrability of the angular integrand from C3 and C4, and
`angularMoment q > 0` from C5.
-/

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

theorem tendsto_rpow_neg_third_mul_sin :
    Tendsto (fun R : ℝ => R ^ (-(1 : ℝ) / 3) * Real.sin R) atTop (𝓝 0) := by
  have h0 : Tendsto (fun R : ℝ => R ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := (1 : ℝ) / 3) (by norm_num)
    simpa [neg_div] using this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hR.le _)]
  calc R ^ (-(1 : ℝ) / 3) * ‖Real.sin R‖ ≤ R ^ (-(1 : ℝ) / 3) * 1 :=
        mul_le_mul_of_nonneg_left (by simpa using Real.abs_sin_le_one R) (Real.rpow_nonneg hR.le _)
    _ = R ^ (-(1 : ℝ) / 3) := mul_one _

theorem contDiff_circleCubic (q : ℝ × ℝ × ℝ × ℝ) : ContDiff ℝ 1 (circleCubic q) := by
  unfold circleCubic cubicForm; fun_prop

/-- **S4.3** from the interfaces. -/
theorem d4ConstantPos_of (h1 : CosIBPFacts) (h2 : SinMomentFacts) (h3 : CircleNondegFacts)
    (h4 : SingularPowerFacts) (h5 : AngularPosFacts) : D4ConstantPosStatement := by
  obtain ⟨S, hS, hT⟩ := h2
  have hlim : Tendsto cosMomentPartial atTop (𝓝 (S / 3)) := by
    have hsum := tendsto_rpow_neg_third_mul_sin.add (hT.const_mul (1 / 3))
    rw [zero_add, show 1 / 3 * S = S / 3 by ring] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (h1 R hR).symm
  have hI : cosMoment = S / 3 := hlim.limUnder_eq
  have hpos : 0 < cosMoment := by rw [hI]; positivity
  refine ⟨hI ▸ hlim, hpos, fun q hq => ?_⟩
  have hint : IntervalIntegrable (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) volume 0 (2 * Real.pi) := by
    have := h4 (circleCubic q) (contDiff_circleCubic q) 0 (2 * Real.pi) (by positivity)
      (fun x _ => by
        by_cases hx : circleCubic q x = 0
        · exact Or.inr (h3 q hq x hx)
        · exact Or.inl hx) (2 / 3) (by norm_num) (by norm_num)
    simpa [neg_div] using this
  refine ⟨hint, ?_⟩
  have hJ := h5 q hq hint
  unfold d4Constant
  positivity

end OscInt.D4
