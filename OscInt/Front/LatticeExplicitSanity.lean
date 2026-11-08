/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeExplicit
import OscInt.Front.GlobalSanity

/-! # Sanity theorems through the batch-LE statement constants

As for batch GD (`OscInt/Front/GlobalSanity.lean`, lessons 33): every theorem about a frozen statement of
`OscInt/Statements/LatticeExplicit.lean` takes that statement constant as its only statement hypothesis, discharges
its hypotheses on closed data and concludes its conclusion there. Planted copies:
`docs/replay/plants/2026-11-08-LE/` with compiler output. Structural limit as for GD: a plant that weakens a hypothesis
or strengthens a conclusion is not detected and rests on the blind fidelity reviews and the pre-registered numeric
check (`numerics/results-lattice1-2026-11-08.txt`).

Data (generic where the statement has roles to separate, lessons 17):
* `I(0, 0) = 2π`, `I(0, 1) = 0` (unconditional: pins the interval `[−π, π]` and the sign and scale of `ξk`).
* T0E at `t = 8`, `ξ = 1/2` (`8^{−1/3} = 1/2` separates the two exponents; `ξ` not an integer).
* T6F at `t = 3`, `x = (1, −2)` (distinct coordinates).
* T6E at `t = 1`, `x = (1, −2)` (the threshold itself) and on the diagonal `x = (n, n)`, `t = n`.
* The size of the constant: `68 < 24 · 2^{1/4} + 36 · 2^{1/6} < 69`.
-/

namespace OscInt.API.LatticeExplicitSanity

open OscInt.Statements OscInt.API.GlobalSanity

/-- `I(0, 0) = 2π`: the interval has length `2π`. -/
theorem latticeKernel1_zero_zero : latticeKernel1 0 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp only [latticeKernel1, zero_mul, add_zero, Complex.ofReal_zero, Complex.exp_zero,
    intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast; ring

/-- `I(0, 1) = 0`: the linear term is `ξk` and the interval is a full period. -/
theorem latticeKernel1_zero_one : latticeKernel1 0 1 = 0 := by
  have h0 := integral_exp_int_mul 1 one_ne_zero
  simp only [Int.cast_one, one_mul] at h0
  simpa [latticeKernel1] using h0

/-- `8^{−1/3} = 1/2`. -/
theorem eight_rpow_neg_third : (8 : ℝ) ^ (-(1 : ℝ) / 3) = 1 / 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **T0E through the statement constant** at `t = 8`, `ξ = 1/2`. Plants detected: the exponent `−1/3 ↦ −1/2` of the
second term (then `8^{−1/3} = 1/2` no longer rewrites the conclusion); `ξ` restricted to integers; a changed constant.
Not detected: a strengthened bound (e.g. smaller constants), which the numeric check and the proof decide. -/
theorem latticeKernel1Explicit_eight (h : LatticeKernel1ExplicitStatement) :
    ‖latticeKernel1 8 (1 / 2)‖ ≤ 24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * (8 : ℝ) ^ (-(1 : ℝ) / 2) +
      18 * (2 : ℝ) ^ ((1 : ℝ) / 6) := by
  have := h 8 (1 / 2) (by norm_num)
  rw [eight_rpow_neg_third] at this
  linarith

/-- **T6F through the statement constant** on generic data. Plants detected: a coordinate used twice
(`x.2 ↦ x.1`), a changed time in a factor. -/
theorem latticeKernelFactor_generic (h : LatticeKernelFactorStatement) :
    latticeKernel 3 (1, -2) = latticeKernel1 3 1 * latticeKernel1 3 (-2) := by
  simpa using h 3 (1, -2)

/-- **T6E through the statement constant** at the threshold `t = 1`. Plant detected: the threshold `1 ≤ t ↦ 2 ≤ t`. -/
theorem latticeLaplacianExplicit_one (h : LatticeLaplacianExplicitStatement) :
    ‖latticeKernel 1 (1, -2)‖ ≤ (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by
  simpa using h 1 (1, -2) le_rfl

/-- **T6E through the statement constant** on the diagonal `x = (n, n)` at time `n` (where T6L shows the rate is
attained). Plant detected: the rate weakened (`−2/3 ↦ −1/2`). -/
theorem latticeLaplacianExplicit_diag (h : LatticeLaplacianExplicitStatement) :
    ∀ n : ℕ, 1 ≤ n → ‖latticeKernel n ((n : ℤ), (n : ℤ))‖ ≤
      (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 * (n : ℝ) ^ (-(2 : ℝ) / 3) :=
  fun n hn => h n _ (by exact_mod_cast hn)

/-- `x ^ k = c < y ^ k` with `0 ≤ y` gives `x < y`. -/
theorem lt_of_pow_eq {x y c : ℝ} {k : ℕ} (hy : 0 ≤ y) (hxc : x ^ k = c) (hcy : c < y ^ k) : x < y := by
  by_contra hle
  have := pow_le_pow_left₀ hy (not_lt.mp hle) k
  linarith

/-- `y ^ k < c = x ^ k` with `0 ≤ x` gives `y < x`. -/
theorem gt_of_pow_eq {x y c : ℝ} {k : ℕ} (hx : 0 ≤ x) (hxc : x ^ k = c) (hcy : y ^ k < c) : y < x := by
  by_contra hle
  have := pow_le_pow_left₀ hx (not_lt.mp hle) k
  linarith

theorem two_rpow_quarter_pow : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

theorem two_rpow_sixth_pow : ((2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- The size of the 1D constant: `68 < 24 · 2^{1/4} + 36 · 2^{1/6} < 69`, so the constant of T6E is below
`69² = 4761`. -/
theorem latticeConst_bounds :
    68 < 24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) ∧
      24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) < 69 := by
  have ha0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hb0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 6) := by positivity
  have ha1 : (2 : ℝ) ^ ((1 : ℝ) / 4) < 1.1893 :=
    lt_of_pow_eq (by norm_num) two_rpow_quarter_pow (by norm_num)
  have ha2 : 1.1892 < (2 : ℝ) ^ ((1 : ℝ) / 4) :=
    gt_of_pow_eq ha0 two_rpow_quarter_pow (by norm_num)
  have hb1 : (2 : ℝ) ^ ((1 : ℝ) / 6) < 1.12247 :=
    lt_of_pow_eq (by norm_num) two_rpow_sixth_pow (by norm_num)
  have hb2 : 1.1224 < (2 : ℝ) ^ ((1 : ℝ) / 6) :=
    gt_of_pow_eq hb0 two_rpow_sixth_pow (by norm_num)
  constructor <;> linarith

end OscInt.API.LatticeExplicitSanity
