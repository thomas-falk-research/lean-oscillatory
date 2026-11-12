/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup

/-! # Batch LS: the assembly of LS-E, LS-K, LS-D, LS-D′ from the blueprint parts (compiled before any part is proved)

Route: `docs/proof-LS.md`. -/

namespace OscInt.LatticeGroupAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup

/-- **LS-E from the parts.** -/
theorem lsE_of (hOp : LapOpFacts) (hExp : ExpSolutionFacts) : LatticeSchrodingerExistsStatement := by
  intro d f
  obtain ⟨A, hA, -⟩ := hOp d
  exact ⟨_, hExp d A hA f⟩

/-- **LS-K from the parts.** -/
theorem lsK_of (hOp : LapOpFacts) (hExp : ExpSolutionFacts) (hU : UniqueFacts) (hConv : KernelConvFacts) :
    LatticeSchrodingerKernelStatement := by
  intro d f u hu t x
  obtain ⟨A, hA, -⟩ := hOp d
  have huv := hU d f u _ hu (hExp d A hA f)
  subst huv
  exact hConv d A hA f t x

/-- **LS-D from LS-K and the kernel bound.** -/
theorem lsD_of (hK : LatticeSchrodingerKernelStatement) (hB : KernelBoundFacts) :
    LatticeSchrodingerDispersiveStatement := by
  intro d f u hu hf t x ht
  obtain ⟨hs, heq⟩ := hK d f u hu t x
  set M := min 1 ((8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ d * (2 * |t|) ^ (-(d : ℝ) / 3))
  have hle : ∀ y, ‖schrodingerKernel d t (x - y) * f y‖ ≤ M * ‖f y‖ := fun y => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB d t (x - y) ht) (norm_nonneg _)
  rw [heq]
  calc ‖∑' y, schrodingerKernel d t (x - y) * f y‖ ≤ ∑' y, ‖schrodingerKernel d t (x - y) * f y‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' y, M * ‖f y‖ := hs.tsum_le_tsum hle (hf.mul_left M)
    _ = M * ∑' y, ‖f y‖ := tsum_mul_left

/-- **LS-D′ from LS-D and the envelope.** -/
theorem lsDp_of (hD : LatticeSchrodingerDispersiveStatement) (hEnv : EnvelopeFacts) :
    LatticeSchrodingerDecayStatement := by
  intro d f u hu hf t x
  have hτ : 1 ≤ (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ ((d : ℝ) / 3) :=
    Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) (by positivity)
  have hS : 0 ≤ ∑' y, ‖f y‖ := tsum_nonneg fun _ => norm_nonneg _
  rcases eq_or_ne t 0 with rfl | ht
  · rw [hu.1, abs_zero, add_zero, Real.one_rpow, mul_one]
    calc ‖f x‖ ≤ ∑' y, ‖f y‖ := hf.le_tsum x (fun _ _ => norm_nonneg _)
      _ ≤ _ := le_mul_of_one_le_left hS hτ
  · exact (hD d f u hu hf t x ht).trans (mul_le_mul_of_nonneg_right (hEnv d t ht) hS)

end OscInt.LatticeGroupAux
