/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch PA (Fourier coefficients in a strip, the trapezoidal rule, the lattice light cone)

Only `import OscInt.API` and Mathlib. Unconditional uses of the three theorems of batch PA:
* `fourierCoeff_normalised`: the normalised Fourier coefficient satisfies `|c_k| ≤ M e^{−a|k|}`;
* `trapezoid_within`: the trapezoidal rule is within `ε` as soon as `4πM/(e^{aN} − 1) ≤ ε`;
* `lightCone_unit_rate`: `|I(t, n)| ≤ 2π e^{|t| sinh 1 − |n|}`, one e-folding per site outside the cone;
* three data points through the sanity layer, now without hypotheses.
-/

open OscInt.Statements OscInt.API

/-- PA-C in normalised form: `|(2π)⁻¹ ∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ M e^{−a|k|}`. -/
theorem fourierCoeff_normalised (v : ℂ → ℂ) (a M : ℝ) (k : ℤ) (ha : 0 < a) (hv : PeriodicAnalyticOn v a M) :
    ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)‖ ≤
      M * Real.exp (-(a * |(k : ℝ)|)) := by
  have h := fourierCoeffStrip v a M k ha hv
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le, inv_mul_le_iff₀ Real.two_pi_pos]
  linarith

/-- PA-T as a stopping rule: once `4πM/(e^{aN} − 1) ≤ ε`, the `N`-point trapezoidal sum is within `ε`. -/
theorem trapezoid_within (v : ℂ → ℂ) (a M ε : ℝ) (N : ℕ) (ha : 0 < a) (hN : 0 < N) (hv : PeriodicAnalyticOn v a M)
    (hε : 4 * Real.pi * M / (Real.exp (a * (N : ℝ)) - 1) ≤ ε) :
    ‖trapezoidalSum v N - ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ)‖ ≤ ε :=
  (trapezoidalRule v a M N ha hN hv).trans hε

/-- LC-1 at `η = 1`: the 1D lattice kernel loses a factor `e` per site beyond `|t| sinh 1`. -/
theorem lightCone_unit_rate (t : ℝ) (n : ℤ) :
    ‖latticeKernel1 t (n : ℝ)‖ ≤ 2 * Real.pi * Real.exp (|t| * Real.sinh 1 - |(n : ℝ)|) := by
  simpa using latticeKernel1LightCone t 1 n zero_le_one

/-- The sanity data of PA-T, unconditionally: the bound for `7 cos 3z` at three nodes is not below the error. -/
example (a : ℝ) (ha : 0 < a) : 14 * Real.pi ≤ 4 * Real.pi * (7 * Real.cosh (3 * a)) / (Real.exp (a * 3) - 1) :=
  PeriodicAnalyticSanity.trapezoid_cos3 trapezoidalRule a ha

/-- The sanity datum of PA-C, unconditionally. -/
example (a : ℝ) (ha : 0 < a) : 7 * Real.pi ≤ 2 * Real.pi * (7 * Real.cosh (3 * a)) * Real.exp (-(a * 3)) :=
  PeriodicAnalyticSanity.fourierCoeff_cos3 fourierCoeffStrip a ha

/-- The sanity datum of LC-1, unconditionally: five sites out at time 1 the kernel is below `2π e^{sinh 2 − 10}`. -/
example : ‖latticeKernel1 1 5‖ ≤ 2 * Real.pi * Real.exp (Real.sinh 2 - 10) :=
  PeriodicAnalyticSanity.lightCone_five latticeKernel1LightCone
