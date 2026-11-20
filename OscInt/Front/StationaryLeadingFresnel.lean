/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Batch SPL, part Fresnel: P-fresnel from P-tail and P-value (route `docs/proof-SPL.md`, Lemma 1, sections 10, 11)

`F(x) = ∫₀ˣ e(v) dv` with `e(v) = e^{iv²/2}` continuous, so `F′ = e` on the line (fundamental theorem of calculus); `e`
is even, so `F(−x) = −F(x)`. P-tail gives some `L′` with `|F(x) − L′| ≤ 2/x` for `x > 0`, and P-value says that such an
`L′` is the closed form `L = √π (1 + i)/2`: together they are the third clause of P-fresnel.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- `e(u) = e^{iu²/2}` is continuous on the line. -/
theorem splF_continuous_fresnelE : Continuous fresnelE := by
  unfold fresnelE
  fun_prop

/-- `F′ = e` at every point of the line: the fundamental theorem of calculus for the continuous integrand `e`. -/
theorem splF_hasDerivAt_fresnelPrim (x : ℝ) : HasDerivAt fresnelPrim (fresnelE x) x :=
  intervalIntegral.integral_hasDerivAt_right (splF_continuous_fresnelE.intervalIntegrable _ _)
    (splF_continuous_fresnelE.stronglyMeasurableAtFilter _ _) splF_continuous_fresnelE.continuousAt

/-- `F(−x) = −F(x)`: the integrand `e^{iv²/2}` is even. -/
theorem splF_fresnelPrim_neg (x : ℝ) : fresnelPrim (-x) = -fresnelPrim x := by
  unfold fresnelPrim
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
    (fun v : ℝ => Complex.exp (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I))
  simp only [neg_sq, neg_zero] at h
  rw [intervalIntegral.integral_symm, ← h]

/-- **P-fresnel** from P-tail and P-value: `F′ = e`, `F` is odd, and the number `L′` of P-tail, approached by `F` at
rate `2/x`, is the closed form `L = √π (1 + i)/2` by P-value. -/
theorem splFresnelFacts_of (hT : SplFresnelTailFacts) (hV : SplFresnelValueFacts) : SplFresnelFacts := by
  obtain ⟨L', hL'⟩ := hT
  have hL : L' = fresnelLimit := hV L' hL'
  rw [hL] at hL'
  exact ⟨splF_hasDerivAt_fresnelPrim, splF_fresnelPrim_neg, hL'⟩

end OscInt.StationaryLeadingAux
