/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch SPL (the leading term of a quadratic-phase integral with an explicit remainder)

Only `import OscInt.API` and Mathlib. Unconditional uses of the theorems of batch SPL:
* `quadratic_phase_leading_term`: for an amplitude `g` with three integrable derivatives and `λ > 0`,
  `|∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}` (SPL-K, with the remainder written out);
* `gaussian_at_four`: the same for `g(u) = e^{−u²/2}` at `λ = 4`, where both sides are closed forms.
-/

open MeasureTheory OscInt.Statements OscInt.API

/-- The stationary-phase leading term for the phase `u²/2`, with remainder at most `(7/8) ‖g‴‖₁ λ^{−3/2}`. -/
theorem quadratic_phase_leading_term (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ) (hg : SplAmplitude g g₁ g₂ g₃) (hlam : 0 < lam) :
    ‖(∫ u, g u * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) -
        g 0 * ((Real.sqrt (2 * Real.pi / lam) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      7 / 8 * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) :=
  stationaryLeadingSevenEighths g g₁ g₂ g₃ lam hg hlam

/-- The Gaussian `e^{−u²/2}` at `λ = 4`: `|(2π/(1 − 4i))^{1/2} − √(2π/4) e^{iπ/4}| ≤ (7/8)(2 + 8 e^{−3/2})/8`. -/
theorem gaussian_at_four :
    ‖(2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 4) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      7 / 8 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) :=
  OscInt.API.StationaryLeadingSanity.sevenEighths_gauss_one_four stationaryLeadingSevenEighths
