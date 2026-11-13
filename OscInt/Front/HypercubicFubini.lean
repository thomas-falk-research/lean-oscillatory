/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Hypercubic

/-!
# Batch HC: the part P-fubini (route `docs/proof-HC.md`)

The restriction of the product measure to the box is the product of the restricted measures; Fubini over `Fin d`; each
factor is an interval integral. The box is unfolded with `rw`, never `simp` (`Set.pi_univ_Icc`, route referee).
-/

namespace OscInt.HypercubicAux

open OscInt.Statements OscInt.Blueprint.Hypercubic MeasureTheory

/-- One factor: the integral over `Icc (−π) π` is the interval integral over `[−π, π]`. -/
theorem integral_Icc_pi (f : ℝ → ℂ) :
    ∫ x, f x ∂(volume.restrict (Set.Icc (-Real.pi) Real.pi)) = ∫ x in (-Real.pi)..Real.pi, f x := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]

/-- **P-fubini** (`HCFubiniFacts`). -/
theorem hcFubiniFacts : HCFubiniFacts := by
  intro d f _
  rw [hypercubeBox, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun j _ => integral_Icc_pi (f j)

end OscInt.HypercubicAux
