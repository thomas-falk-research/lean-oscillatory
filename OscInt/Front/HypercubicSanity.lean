/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Hypercubic
import OscInt.Front.LatticeCubeRootSanity

/-! # Sanity theorems through the batch-HC statement constants

As for batches LE and LE2 (lessons 33, 38, 44, 47): every theorem about a frozen statement of
`OscInt/Statements/Hypercubic.lean` takes that statement constant as its hypothesis, discharges its hypotheses on closed
data and concludes its conclusion there. Planted copies: `docs/replay/plants/2026-11-12-HC/`.

Data:
* Unconditional: `K_d(0, 0) = (2π)^d` for every `d` (pins the box `[−π, π]^d` and the product measure), hence
  `K_0 = 1`.
* TdF at `d = 2`, `t = 3`, `x = (1, −2)` (distinct coordinates) and at `t = −2` (no restriction on `t`); at `d = 3`.
* TdE′ at `d = 3`, `t = 8` (`8^{−3/3} = 1/8`; separates the rate `t^{−d/3}` from `t^{−1/3}`), at `d = 1`, `t = 1/8`
  (`(1/8)^{−1/3} = 2`; a threshold on `t` added is detected), and at `d = 3`, `t = (31/20)³`, just above the usefulness
  threshold, where the conclusion is below the trivial bound `(2π)³` (`hc_thr_nontrivial`).
* Bite: at `t = 0` the bound of TdE′ is false for `d = 1` (`0 < t` is needed).
-/

namespace OscInt.API.HypercubicSanity

open OscInt.Statements OscInt.API.LatticeExplicitSanity OscInt.API.LatticeCubeRootSanity

/-- The volume of the box `[−π, π]^d` is `(2π)^d`. -/
theorem hypercubeBox_volume (d : ℕ) :
    MeasureTheory.volume (hypercubeBox d) = ENNReal.ofReal (2 * Real.pi) ^ d := by
  rw [hypercubeBox, MeasureTheory.volume_pi_pi]
  simp [Real.volume_Icc, two_mul]

/-- **Unconditional**: `K_d(0, 0) = (2π)^d`. -/
theorem hypercubicKernel_zero_zero (d : ℕ) : hypercubicKernel d 0 0 = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by
  simp only [hypercubicKernel, zero_mul, Pi.zero_apply, Int.cast_zero, Finset.sum_const_zero, add_zero,
    Complex.ofReal_zero, Complex.exp_zero, MeasureTheory.setIntegral_const]
  rw [MeasureTheory.measureReal_def, hypercubeBox_volume, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]
  simp

/-- `K_0(t, x) = 1`: the integral over the one-point space. -/
theorem hypercubicKernel_dim_zero (t : ℝ) (x : Fin 0 → ℤ) : hypercubicKernel 0 t x = 1 := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  have : ∀ s : ℝ, hypercubicKernel 0 s 0 = hypercubicKernel 0 0 0 := by
    intro s; simp [hypercubicKernel]
  rw [this, hypercubicKernel_zero_zero]
  simp

/-- **TdF through the statement constant** at `d = 2`, `t = 3`, `x = (1, −2)`. Plants detected: a coordinate used
twice, a changed time in a factor. -/
theorem hypercubicFactor_two (h : HypercubicKernelFactorStatement) :
    hypercubicKernel 2 3 ![1, -2] = latticeKernel1 3 1 * latticeKernel1 3 (-2) := by
  simpa [Fin.prod_univ_two] using h 2 3 ![1, -2]

/-- **TdF through the statement constant** at a negative time. Plant detected: a restriction `0 < t` added. -/
theorem hypercubicFactor_neg (h : HypercubicKernelFactorStatement) :
    hypercubicKernel 3 (-2) ![1, 0, -3] =
      latticeKernel1 (-2) 1 * latticeKernel1 (-2) 0 * latticeKernel1 (-2) (-3) := by
  simpa [Fin.prod_univ_three] using h 3 (-2) ![1, 0, -3]

/-- **TdE′ through the statement constant** at `d = 3`, `t = 8`: `8^{−3/3} = 1/8`. Plants detected: the rate
`t^{−d/3} ↦ t^{−1/3}` (then the conclusion `C*³/8` does not follow), a larger constant. -/
theorem hypercubicCubeRoot_three (h : HypercubicCubeRootStatement) :
    ‖hypercubicKernel 3 8 ![1, 0, -3]‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 3 / 8 := by
  have := h 3 8 ![1, 0, -3] (by norm_num)
  have h8 : (8 : ℝ) ^ (-((3 : ℕ) : ℝ) / 3) = 1 / 8 := by
    rw [show (-((3 : ℕ) : ℝ) / 3) = -1 by norm_num, Real.rpow_neg_one]; norm_num
  rw [h8] at this
  linarith

/-- **TdE′ through the statement constant** at `d = 1`, `t = 1/8`: `(1/8)^{−1/3} = 2`. Plant detected: a threshold on
`t` added. -/
theorem hypercubicCubeRoot_eighth (h : HypercubicCubeRootStatement) :
    ‖hypercubicKernel 1 (1 / 8) ![2]‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * 2 := by
  have := h 1 (1 / 8) ![2] (by norm_num)
  rw [show (-((1 : ℕ) : ℝ) / 3) = -(1 : ℝ) / 3 by norm_num, eighth_rpow_neg_third, pow_one] at this
  exact this

/-- **TdE′ through the statement constant** at `d = 3`, `t = (31/20)³`: `C*³ (20/31)³`, below the trivial `(2π)³`. -/
theorem hypercubicCubeRoot_thr (h : HypercubicCubeRootStatement) :
    ‖hypercubicKernel 3 (29791 / 8000) ![1, 0, -3]‖ ≤ (8 * (1 + Real.sqrt 7) / 3 * (20 / 31)) ^ 3 := by
  have := h 3 (29791 / 8000) ![1, 0, -3] (by norm_num)
  have hr : (29791 / 8000 : ℝ) ^ (-((3 : ℕ) : ℝ) / 3) = (20 / 31) ^ 3 := by
    rw [show (-((3 : ℕ) : ℝ) / 3) = -1 by norm_num, Real.rpow_neg_one]; norm_num
  rw [hr, ← mul_pow] at this
  exact this

/-- The right side at `t = (31/20)³` is below the trivial bound `(2π)³`. -/
theorem hc_thr_nontrivial : (8 * (1 + Real.sqrt 7) / 3 * (20 / 31)) ^ 3 < (2 * Real.pi) ^ 3 := by
  have h := thr_nontrivial.1
  have h0 : 0 ≤ 8 * (1 + Real.sqrt 7) / 3 * (20 / 31) := by positivity
  exact pow_lt_pow_left₀ h h0 (by norm_num)

/-- **Bite: `0 < t` is needed.** At `d = 1`, `t = 0`, `x = 0`: `‖K_1(0, 0)‖ = 2π > 0 = C* · 0^{−1/3}`. -/
theorem hypercubicCubeRoot_false_at_zero :
    ¬ ‖hypercubicKernel 1 0 0‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 1 * (0 : ℝ) ^ (-((1 : ℕ) : ℝ) / 3) := by
  rw [hypercubicKernel_zero_zero, Real.zero_rpow (by norm_num), mul_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  exact not_le.mpr (by positivity)

end OscInt.API.HypercubicSanity
