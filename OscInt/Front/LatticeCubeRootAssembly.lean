/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeCubeRoot
import OscInt.Front.LatticeExplicitFinal

/-!
# Batch LE2: the lead's assembly against the blueprint (route `docs/proof-LE2.md`)

T0E′ from P-sym, P-r8 and P-r38 (and the length bound for `0 < t ≤ 3`); T6E′ from T0E′ and the proved T6F
(`OscInt.API.latticeKernelFactor`). Compiled before any part was proved.
-/

namespace OscInt.LatticeCubeRootAux

open OscInt.Statements OscInt.Blueprint.LatticeCubeRoot

/-- The length bound `‖I(t, ξ)‖ ≤ 2π`. -/
theorem latticeKernel1_le_two_pi (t ξ : ℝ) : ‖latticeKernel1 t ξ‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi) (C := 1)
    (f := fun k : ℝ => Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I))
    (fun k _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [abs_of_nonneg (by linarith [Real.pi_pos])] at h
  simpa [latticeKernel1, two_mul] using h

/-- `9/13 < 3^{−1/3}`. -/
theorem three_rpow_lower : (9 / 13 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hc : ((3 : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = 1 / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num [Real.rpow_neg_one]
  by_contra hle
  have := pow_le_pow_left₀ (by positivity) (not_lt.mp hle) 3
  rw [hc] at this
  norm_num at this

/-- Small times: for `0 < t ≤ 3`, the length bound is below `C* t^{−1/3}`. -/
theorem small_time (t ξ : ℝ) (ht : 0 < t) (ht3 : t ≤ 3) :
    ‖latticeKernel1 t ξ‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3) := by
  have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 3) ≤ t ^ (-(1 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ht ht3 (by norm_num)
  have h2 := three_rpow_lower
  have hs : (2.6457 : ℝ) < Real.sqrt 7 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  refine (latticeKernel1_le_two_pi t ξ).trans ?_
  have hc : 0 ≤ 8 * (1 + Real.sqrt 7) / 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]

/-- **T0E′ from the parts.** -/
theorem t0ep_of (hSym : SymFacts) (h8 : Regime8Facts) (h38 : Regime38Facts) : LatticeKernel1CubeRootStatement := by
  intro t ξ ht
  have habs : latticeKernel1 t ξ = latticeKernel1 t |ξ| := by
    rcases le_or_gt 0 ξ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hSym]
  rw [habs]
  have hv : t * (|ξ| / t) = |ξ| := by field_simp
  have hv0 : 0 ≤ |ξ| / t := div_nonneg (abs_nonneg _) ht.le
  rcases le_or_gt 8 t with h | h
  · simpa [hv] using h8 t (|ξ| / t) h hv0
  · rcases le_or_gt 3 t with h' | h'
    · simpa [hv] using h38 t (|ξ| / t) h' h.le hv0
    · exact small_time t _ ht h'.le

/-- **T6E′ from T0E′** and the proved T6F. -/
theorem t6ep_of (h : LatticeKernel1CubeRootStatement) : LatticeLaplacianCubeRootStatement := by
  intro t x ht
  rw [OscInt.API.latticeKernelFactor t x, norm_mul]
  have h1 := h t (x.1 : ℝ) ht
  have h2 := h t (x.2 : ℝ) ht
  have hsq : (t ^ (-(1 : ℝ) / 3)) ^ 2 = t ^ (-(2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  calc ‖latticeKernel1 t (x.1 : ℝ)‖ * ‖latticeKernel1 t (x.2 : ℝ)‖
      ≤ (8 * (1 + Real.sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3)) * (8 * (1 + Real.sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3)) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = (8 * (1 + Real.sqrt 7) / 3) ^ 2 * t ^ (-(2 : ℝ) / 3) := by rw [← hsq]; ring

end OscInt.LatticeCubeRootAux
