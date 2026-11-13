/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeCubeRoot
import OscInt.Front.LatticeExplicitSanity
import OscInt.Front.LatticeExplicitFinal

/-! # Sanity theorems through the batch-LE2 statement constants

As for batch LE (`OscInt/Front/LatticeExplicitSanity.lean`, lessons 33): every theorem about a frozen statement of
`OscInt/Statements/LatticeCubeRoot.lean` takes that statement constant as its only statement hypothesis, discharges its
hypotheses on closed data and concludes its conclusion there. Planted copies: `docs/replay/plants/2026-11-10-LE2/` with
compiler output and, per line, the semantic evidence lessons 44 asks for.

Data (generic where the statement has roles to separate, lessons 17 and 38):
* T0E′ at `t = 8` (`8^{−1/3} = 1/2`), `ξ = 1/2` (not an integer) and `ξ = −5/2` (negative, not an integer); at
  `t = 1/8` (`(1/8)^{−1/3} = 2`; below the useful-from threshold `≈ 3.70` and below 1, so a threshold added to `t` is
  detected).
* T6E′ at `t = 1/8`, `x = (1, −2)` (`(1/8)^{−2/3} = 4`; distinct coordinates) and on the diagonal at `t = 8`.
* Comparison with batch LE: T0E′ implies T0E, and T6E′ implies T6E, through the statement constants.
* The size of the constant: `9.722 < 8(1 + √7)/3 < 9.7221`.
* Bites (unconditional): at `t = 0` the bound of T0E′ is false (so `0 < t` is needed), and
  `‖I(t, 0)‖ ≥ 2π − πt²/2` for every `t`, so at `t = (7/8)³` the bound with half the constant, `4(1 + √7)/3`, is
  false: the constant of T0E′ cannot be halved.

Added after the blind pre-proof reviews (`review/2026-11-10-LE2-pre-proof-answers.md`; the statements are unchanged):
* T0E′ and T6E′ at `t = (31/20)³ ≈ 3.724` (`t^{−1/3} = 20/31`), just above the useful-from threshold `≈ 3.7045`, where
  the conclusions are below the trivial bounds `2π` and `4π²` (at `t = 1/8` they are not; reviews A and B).
* T6E′ bites through the proved T6F (`K(t, 0) = I(t, 0)²`): at `t = 0` the bound is false; at `t = 1` the bound with
  the unsquared constant `8(1 + √7)/3` is false; at `t = (7/8)³` the bound with `(4(1 + √7)/3)²` is false (reviews A
  and B: T6E′ had no bite of its own).
-/

namespace OscInt.API.LatticeCubeRootSanity

open OscInt.Statements OscInt.API.LatticeExplicitSanity

/-- `√7` to five decimals: `2.64575 < √7 < 2.645752`. -/
theorem sqrt_seven_bounds : 2.64575 < Real.sqrt 7 ∧ Real.sqrt 7 < 2.645752 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The size of the constant: `9.722 < 8(1 + √7)/3 < 9.7221`. -/
theorem cubeRootConst_bounds :
    9.722 < 8 * (1 + Real.sqrt 7) / 3 ∧ 8 * (1 + Real.sqrt 7) / 3 < 9.7221 := by
  obtain ⟨h1, h2⟩ := sqrt_seven_bounds
  constructor <;> linarith

/-- `(1/8)^{−2/3} = 4`. -/
theorem eighth_rpow_neg_two_thirds : (1 / 8 : ℝ) ^ (-(2 : ℝ) / 3) = 4 := by
  rw [show (1 / 8 : ℝ) = 2 ^ (-3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `8^{−2/3} = 1/4`. -/
theorem eight_rpow_neg_two_thirds : (8 : ℝ) ^ (-(2 : ℝ) / 3) = 1 / 4 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `((7/8)³)^{−1/3} = 8/7`. -/
theorem cube_rpow_neg_third : (343 / 512 : ℝ) ^ (-(1 : ℝ) / 3) = 8 / 7 := by
  rw [show (343 / 512 : ℝ) = (7 / 8) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **T0E′ through the statement constant** at `t = 8`, `ξ = 1/2`. Plants detected: the rate changed (`8^{−1/3} = 1/2`
no longer rewrites the conclusion), a larger constant (the conclusion spells out `4(1 + √7)/3`), `ξ` restricted to
integers. -/
theorem latticeKernel1CubeRoot_eight (h : LatticeKernel1CubeRootStatement) :
    ‖latticeKernel1 8 (1 / 2)‖ ≤ 4 * (1 + Real.sqrt 7) / 3 := by
  have := h 8 (1 / 2) (by norm_num)
  rw [eight_rpow_neg_third] at this
  linarith

/-- **T0E′ through the statement constant** at `t = 8`, `ξ = −5/2`. Plant detected: `ξ` restricted to `ξ ≥ 0`. -/
theorem latticeKernel1CubeRoot_neg (h : LatticeKernel1CubeRootStatement) :
    ‖latticeKernel1 8 (-5 / 2)‖ ≤ 4 * (1 + Real.sqrt 7) / 3 := by
  have := h 8 (-5 / 2) (by norm_num)
  rw [eight_rpow_neg_third] at this
  linarith

/-- **T0E′ through the statement constant** at `t = 1/8`, `ξ = 1/2`. Plant detected: a threshold on `t` added
(`1 < t`, or the useful-from threshold `4 ≤ t`). -/
theorem latticeKernel1CubeRoot_eighth (h : LatticeKernel1CubeRootStatement) :
    ‖latticeKernel1 (1 / 8) (1 / 2)‖ ≤ 16 * (1 + Real.sqrt 7) / 3 := by
  have := h (1 / 8) (1 / 2) (by norm_num)
  rw [eighth_rpow_neg_third] at this
  linarith

/-- **T0E′ implies T0E** (batch LE) through the statement constants: `8(1 + √7)/3 < 36 · 2^{1/6}` and the
`t^{−1/2}` term of T0E is nonnegative. Plant detected: a constant larger than `36 · 2^{1/6} ≈ 40.4`. -/
theorem latticeKernel1Explicit_of_cubeRoot (h : LatticeKernel1CubeRootStatement) :
    LatticeKernel1ExplicitStatement := by
  intro t ξ ht
  have h1 := h t ξ ht
  have hc := cubeRootConst_bounds
  have hb : 1.1224 < (2 : ℝ) ^ ((1 : ℝ) / 6) :=
    gt_of_pow_eq (by positivity) two_rpow_sixth_pow (by norm_num)
  have hp : 0 ≤ t ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ 24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) := by positivity
  nlinarith

/-- **T6E′ through the statement constant** at `t = 1/8`, `x = (1, −2)`. Plants detected: a threshold on `t` added
(`1 ≤ t`, as T6E has), the rate changed. -/
theorem latticeLaplacianCubeRoot_eighth (h : LatticeLaplacianCubeRootStatement) :
    ‖latticeKernel (1 / 8) (1, -2)‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 2 * 4 := by
  have := h (1 / 8) (1, -2) (by norm_num)
  rwa [eighth_rpow_neg_two_thirds] at this

/-- **T6E′ through the statement constant** on the diagonal `x = (n, n)` at `t = 8`. Plant detected: a larger constant
or a slower rate. -/
theorem latticeLaplacianCubeRoot_diag (h : LatticeLaplacianCubeRootStatement) :
    ∀ n : ℤ, ‖latticeKernel 8 (n, n)‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 2 / 4 := by
  intro n
  have := h 8 (n, n) (by norm_num)
  rw [eight_rpow_neg_two_thirds] at this
  linarith

/-- **T6E′ implies T6E** (batch LE) through the statement constants, since `(8(1 + √7)/3)² < 68² <
(24 · 2^{1/4} + 36 · 2^{1/6})²`. -/
theorem latticeLaplacianExplicit_of_cubeRoot (h : LatticeLaplacianCubeRootStatement) :
    LatticeLaplacianExplicitStatement := by
  intro t x ht
  have h1 := h t x (by linarith)
  have hc := cubeRootConst_bounds
  have hl := (latticeConst_bounds).1
  have hp : 0 ≤ t ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have hsq : (8 * (1 + Real.sqrt 7) / 3) ^ 2 ≤
      (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by nlinarith
  nlinarith

/-- **Bite: `0 < t` is needed.** At `t = 0` the bound of T0E′ would say `2π ≤ 0`, since `0 ^ (−1/3) = 0` in Lean. -/
theorem cubeRoot_bound_false_at_zero :
    ¬ ‖latticeKernel1 0 0‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * (0 : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [latticeKernel1_zero_zero, Real.zero_rpow (by norm_num), mul_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  exact not_le.mpr (by positivity)

/-- A lower bound for the kernel at `ξ = 0`: `‖I(t, 0)‖ ≥ Re I(t, 0) = ∫ cos(t cos k) dk ≥ ∫ (1 − t² cos² k / 2) dk
= 2π − πt²/2`. -/
theorem latticeKernel1_zero_freq_lower (t : ℝ) :
    2 * Real.pi - Real.pi * t ^ 2 / 2 ≤ ‖latticeKernel1 t 0‖ := by
  have hcont : Continuous fun k : ℝ => Complex.exp (↑(t * Real.cos k + 0 * k) * Complex.I) := by fun_prop
  have hre : (latticeKernel1 t 0).re = ∫ k in (-Real.pi)..Real.pi, Real.cos (t * Real.cos k) := by
    rw [latticeKernel1, ← Complex.reCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable _ _)]
    congr 1
    ext k
    rw [Complex.reCLM_apply, Complex.exp_ofReal_mul_I_re]
    simp
  have hmono : ∫ k in (-Real.pi)..Real.pi, (1 - t ^ 2 / 2 * Real.cos k ^ 2) ≤
      ∫ k in (-Real.pi)..Real.pi, Real.cos (t * Real.cos k) := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    · exact (by fun_prop : Continuous fun k : ℝ => 1 - t ^ 2 / 2 * Real.cos k ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun k : ℝ => Real.cos (t * Real.cos k)).intervalIntegrable _ _
    · intro k _
      have := Real.one_sub_sq_div_two_le_cos (x := t * Real.cos k)
      nlinarith [this]
  have hval : ∫ k in (-Real.pi)..Real.pi, (1 - t ^ 2 / 2 * Real.cos k ^ 2) =
      2 * Real.pi - Real.pi * t ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun k : ℝ => t ^ 2 / 2 * Real.cos k ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_cos_sq]
    simp
    ring
  calc 2 * Real.pi - Real.pi * t ^ 2 / 2 ≤ (latticeKernel1 t 0).re := by rw [hre, ← hval]; exact hmono
    _ ≤ ‖latticeKernel1 t 0‖ := Complex.re_le_norm _

/-- **Bite: the constant cannot be halved.** At `t = (7/8)³`, `ξ = 0`, the bound with `4(1 + √7)/3 ≈ 4.861` in place of
`8(1 + √7)/3` is false: `‖I(t, 0)‖ ≥ 2π − πt²/2 > 5.578 > 4(1 + √7)/3 · 8/7`. So the best constant is above
`8(1 + √7)/6` (`docs/statements.md`, Batch LE2, modelling choice 3). -/
theorem cubeRoot_half_const_false :
    ¬ ‖latticeKernel1 (343 / 512) 0‖ ≤ 4 * (1 + Real.sqrt 7) / 3 * (343 / 512 : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [cube_rpow_neg_third]
  have hl := latticeKernel1_zero_freq_lower (343 / 512)
  have hs := sqrt_seven_bounds
  have hpi := Real.pi_gt_d4
  exact not_le.mpr (by nlinarith)

/-- `((31/20)³)^{−1/3} = 20/31` and `((31/20)³)^{−2/3} = 400/961`. -/
theorem thr_rpow : (29791 / 8000 : ℝ) ^ (-(1 : ℝ) / 3) = 20 / 31 ∧
    (29791 / 8000 : ℝ) ^ (-(2 : ℝ) / 3) = 400 / 961 := by
  have h : (29791 / 8000 : ℝ) = (31 / 20) ^ (3 : ℝ) := by norm_num
  constructor <;> rw [h, ← Real.rpow_mul (by norm_num)] <;> norm_num

/-- **T0E′ through the statement constant** at `t = (31/20)³`, just above the useful-from threshold, `ξ = 1/2`. The
conclusion `8(1 + √7)/3 · 20/31 < 6.273 < 2π` does not follow from the trivial bound. Plant detected: a threshold
`4 ≤ t` (instance level: the datum violates it). -/
theorem latticeKernel1CubeRoot_thr (h : LatticeKernel1CubeRootStatement) :
    ‖latticeKernel1 (29791 / 8000) (1 / 2)‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * (20 / 31) := by
  have := h (29791 / 8000) (1 / 2) (by norm_num)
  rwa [thr_rpow.1] at this

/-- **T6E′ through the statement constant** at `t = (31/20)³`, `x = (1, −2)`: `C*² · 400/961 < 39.35 < 4π²`. Plant
detected: a threshold `1 ≤ t` (instance level). -/
theorem latticeLaplacianCubeRoot_thr (h : LatticeLaplacianCubeRootStatement) :
    ‖latticeKernel (29791 / 8000) (1, -2)‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 2 * (400 / 961) := by
  have := h (29791 / 8000) (1, -2) (by norm_num)
  rwa [thr_rpow.2] at this

/-- The size of the right sides at `t = (31/20)³`: both are below the trivial bounds `2π` and `4π²`. -/
theorem thr_nontrivial : 8 * (1 + Real.sqrt 7) / 3 * (20 / 31) < 2 * Real.pi ∧
    (8 * (1 + Real.sqrt 7) / 3) ^ 2 * (400 / 961) < 4 * Real.pi ^ 2 := by
  have hc := cubeRootConst_bounds
  have hpi := Real.pi_gt_d4
  constructor <;> nlinarith

/-- `K(t, 0) = I(t, 0)²`, from the proved T6F. -/
theorem latticeKernel_origin (t : ℝ) : ‖latticeKernel t (0, 0)‖ = ‖latticeKernel1 t 0‖ ^ 2 := by
  rw [OscInt.API.latticeKernelFactor t (0, 0)]
  simp [sq]

/-- **Bite: `0 < t` is needed in T6E′.** At `t = 0`, `‖K(0, 0)‖ = 4π² > 0 = C*² · 0^{−2/3}`. -/
theorem laplacianCubeRoot_false_at_zero :
    ¬ ‖latticeKernel 0 (0, 0)‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 2 * (0 : ℝ) ^ (-(2 : ℝ) / 3) := by
  rw [latticeKernel_origin, latticeKernel1_zero_zero, Real.zero_rpow (by norm_num), mul_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact not_le.mpr (by positivity)

/-- **Bite: T6E′'s constant must be squared.** At `t = 1`, `‖K(1, 0)‖ ≥ (3π/2)² > 22 > 8(1 + √7)/3`. -/
theorem laplacianCubeRoot_unsquared_false :
    ¬ ‖latticeKernel 1 (0, 0)‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * (1 : ℝ) ^ (-(2 : ℝ) / 3) := by
  rw [latticeKernel_origin, Real.one_rpow, mul_one]
  have hl := latticeKernel1_zero_freq_lower 1
  have hc := cubeRootConst_bounds
  have hpi := Real.pi_gt_d4
  have h0 : 0 ≤ 2 * Real.pi - Real.pi * 1 ^ 2 / 2 := by nlinarith
  exact not_le.mpr (by nlinarith [mul_le_mul hl hl h0 (norm_nonneg _)])

/-- **Bite: T6E′'s constant cannot be quartered.** At `t = (7/8)³`, `‖K(t, 0)‖ ≥ 5.578² > 31.1 > 30.87 >
(4(1 + √7)/3)² · 64/49`. -/
theorem laplacianCubeRoot_half_const_false :
    ¬ ‖latticeKernel (343 / 512) (0, 0)‖ ≤
        (4 * (1 + Real.sqrt 7) / 3) ^ 2 * (343 / 512 : ℝ) ^ (-(2 : ℝ) / 3) := by
  have h23 : (343 / 512 : ℝ) ^ (-(2 : ℝ) / 3) = 64 / 49 := by
    rw [show (343 / 512 : ℝ) = (7 / 8) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [latticeKernel_origin, h23]
  have hl := latticeKernel1_zero_freq_lower (343 / 512)
  have hs := sqrt_seven_bounds
  have hpi := Real.pi_gt_d4
  have h0 : (5.578 : ℝ) ≤ ‖latticeKernel1 (343 / 512) 0‖ := by nlinarith
  exact not_le.mpr (by nlinarith [mul_le_mul h0 h0 (by norm_num) (norm_nonneg _)])

end OscInt.API.LatticeCubeRootSanity
