/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: explicit constants for the lattice kernels (batch LE)

Only `import OscInt.API` and Mathlib. The proved theorems T0E, T6F, T6E applied on closed data through the sanity
theorems (post-proof reviews A and B, MINOR-1: non-vacuity in a compiled file), and two corollaries a user may want
(`docs/statements.md`, Batch LE, clarification 8). The bounds have content only for large `t` (clarification 6).
-/

open OscInt.Statements OscInt.API OscInt.API.LatticeExplicitSanity

namespace ConsumerLatticeExplicit

example := latticeKernel1Explicit_eight latticeKernel1Explicit
example := latticeKernel1Explicit_eighth latticeKernel1Explicit
example := latticeKernelFactor_generic latticeKernelFactor
example := latticeKernelFactor_neg latticeKernelFactor
example := latticeLaplacianExplicit_one latticeLaplacianExplicit
example := latticeLaplacianExplicit_diag latticeLaplacianExplicit

/-- T6E with the rounded constant `4761 = 69²`. -/
theorem latticeLaplacian_4761 (t : ℝ) (x : ℤ × ℤ) (ht : 1 ≤ t) :
    ‖latticeKernel t x‖ ≤ 4761 * t ^ (-(2 : ℝ) / 3) := by
  have h := latticeLaplacianExplicit t x ht
  have hc := latticeConst_bounds
  have hp : 0 ≤ t ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have hsq : (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 ≤ 4761 := by nlinarith
  nlinarith

/-- The sharper composition of T6F and T0E for every `t > 0` (clarification 8). -/
theorem latticeKernel_composed (t : ℝ) (x : ℤ × ℤ) (ht : 0 < t) :
    ‖latticeKernel t x‖ ≤
      (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) * t ^ (-(1 : ℝ) / 3)) ^ 2 := by
  rw [latticeKernelFactor t x, norm_mul, sq]
  exact mul_le_mul (latticeKernel1Explicit t _ ht) (latticeKernel1Explicit t _ ht) (norm_nonneg _)
    ((norm_nonneg (latticeKernel1 t (x.1 : ℝ))).trans (latticeKernel1Explicit t _ ht))

end ConsumerLatticeExplicit
