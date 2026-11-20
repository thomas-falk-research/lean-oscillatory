/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import OscInt.Front.SecondDerivSharpFinal

/-! # Batch SPL, part Fresnel-bound: P-bound from P-fresnel (route `docs/proof-SPL.md`, section 5; sections 10, 11)

For `c ≥ 0` the phase `x²/2` on `[−c, c]` has derivative `x`, which increases at rate `1`: by VC2-S and VC2-N,
`|∫_{−c}^{c} e^{ix²/2} dx| ≤ A(w) ≤ 7/2` for some `w ∈ [0, π]`. `F` is odd (the only clause of P-fresnel used), so the
integral is `2F(c)` and `|F(c)| ≤ 7/4`; for `c < 0`, `|F(c)| = |F(−c)|`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- The phase `x²/2` is continuous on `[−c, c]` and has derivative `x` inside. -/
theorem splFB_hasDerivOn (c : ℝ) : HasDerivOn (fun x : ℝ => x ^ 2 / 2) (fun x => x) (-c) c := by
  refine ⟨by fun_prop, fun x _ => ?_⟩
  have h := (hasDerivAt_pow 2 x).div_const 2
  convert h using 1
  simp

/-- The derivative `x` of the phase `x²/2` increases at rate `1`. -/
theorem splFB_derivIncreasesAtRate (c : ℝ) : DerivIncreasesAtRate (fun x : ℝ => x) (-c) c 1 :=
  fun x _ y _ _ => by simp

/-- For odd `F`: `∫_{−c}^{c} e^{ix²/2} dx = 2F(c)`. -/
theorem splFB_integral_symm (hodd : ∀ x : ℝ, fresnelPrim (-x) = -fresnelPrim x) (c : ℝ) :
    (∫ x in (-c)..c, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) = 2 * fresnelPrim c := by
  have hcont : Continuous fun v : ℝ => Complex.exp (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable (0 : ℝ) c), intervalIntegral.integral_symm]
  have h1 : (∫ x in (0 : ℝ)..(-c), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) = fresnelPrim (-c) := rfl
  have h3 : (∫ x in (0 : ℝ)..c, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) = fresnelPrim c := rfl
  rw [h1, h3, hodd]
  ring

/-- For odd `F` and `c ≥ 0`: `|F(c)| ≤ 7/4`, from VC2-S and VC2-N for the phase `x²/2` on `[−c, c]`. -/
theorem splFB_norm_le_of_nonneg (hodd : ∀ x : ℝ, fresnelPrim (-x) = -fresnelPrim x) {c : ℝ} (hc : 0 ≤ c) :
    ‖fresnelPrim c‖ ≤ 7 / 4 := by
  obtain ⟨w, hw, hle⟩ := OscInt.API.secondDerivSharp (fun x => x ^ 2 / 2) (fun x => x) (-c) c 1 (by linarith)
    one_pos (splFB_hasDerivOn c) (splFB_derivIncreasesAtRate c)
  have hN := OscInt.API.vdc2ProfileBound w hw
  simp only [Real.sqrt_one, div_one] at hle
  rw [splFB_integral_symm hodd c, norm_mul] at hle
  simp at hle
  linarith

/-- **P-bound** from P-fresnel (oddness only): `|F| ≤ 7/4` on the line. -/
theorem splFresnelBoundFacts_of (hF : SplFresnelFacts) : SplFresnelBoundFacts := by
  obtain ⟨_, hodd, _⟩ := hF
  intro x
  rcases le_total 0 x with h | h
  · exact splFB_norm_le_of_nonneg hodd h
  · have := splFB_norm_le_of_nonneg hodd (c := -x) (by linarith)
    rwa [hodd, norm_neg] at this

end OscInt.StationaryLeadingAux
