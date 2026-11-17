/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch VC2 (the second-derivative van der Corput bound with its sharp constant)

Only `import OscInt.API` and Mathlib. Unconditional uses of the theorems of batch VC2:
* `secondDeriv_sevenHalves_plain`: if `f′` increases at rate at least `λ > 0` on `(a, b)`, then
  `|∫_a^b e^{if}| ≤ (7/2)/√λ` (VC2-S with VC2-N; the constant of S1.2 in this shape is `8`);
* `fresnel_partial_le`: every partial integral of `e^{iλx²/2}` has modulus at most `(7/2)/√λ`, on every interval.
-/

open OscInt.Statements OscInt.API

/-- If `f′` increases at rate at least `λ > 0`, then `|∫_a^b e^{if}| ≤ (7/2)/√λ`. -/
theorem secondDeriv_sevenHalves_plain (f f' : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hf : HasDerivOn f f' a b) (hr : DerivIncreasesAtRate f' a b lam) :
    ‖∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 / Real.sqrt lam := by
  obtain ⟨w, hw, h⟩ := secondDerivSharp f f' a b lam hab hlam hf hr
  exact h.trans (div_le_div_of_nonneg_right (vdc2ProfileBound w hw) (Real.sqrt_nonneg lam))

/-- Every partial integral of the Fresnel phase `e^{iλx²/2}` has modulus at most `(7/2)/√λ`. -/
theorem fresnel_partial_le (lam a b : ℝ) (hlam : 0 < lam) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (((lam * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 / Real.sqrt lam := by
  refine secondDeriv_sevenHalves_plain (fun x => lam * x ^ 2 / 2) (fun x => lam * x) a b lam hab hlam
    ⟨by fun_prop, fun x _ => ?_⟩ ?_
  · have h := ((hasDerivAt_pow 2 x).const_mul lam).div_const 2
    convert h using 1
    ring
  · intro x _ y _ _
    exact le_of_eq (by ring)
