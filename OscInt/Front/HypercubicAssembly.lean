/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Hypercubic
import OscInt.Front.LatticeCubeRootFinal

/-!
# Batch HC: the lead's assembly against the blueprint (route `docs/proof-HC.md`)

TdF from P-fubini (the integrand is a product of one-variable exponentials); TdE′ from TdF and the proved T0E′
(`OscInt.API.latticeKernel1CubeRoot`). Compiled before the part was proved.
-/

namespace OscInt.HypercubicAux

open OscInt.Statements OscInt.Blueprint.Hypercubic

/-- The integrand of `hypercubicKernel` is a product of one-variable exponentials. -/
theorem integrand_prod (d : ℕ) (t : ℝ) (x : Fin d → ℤ) (k : Fin d → ℝ) :
    Complex.exp (↑(t * ∑ j, Real.cos (k j) + ∑ j, (x j : ℝ) * k j) * Complex.I) =
      ∏ j, Complex.exp (↑(t * Real.cos (k j) + (x j : ℝ) * k j) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **TdF from the part.** -/
theorem tdF_of (hF : HCFubiniFacts) : HypercubicKernelFactorStatement := by
  intro d t x
  rw [hypercubicKernel]
  simp_rw [integrand_prod]
  rw [hF d (fun j k => Complex.exp (↑(t * Real.cos k + (x j : ℝ) * k) * Complex.I)) (fun j => by fun_prop)]
  rfl

/-- **TdE′ from TdF** and the proved T0E′. -/
theorem tdEp_of (hF : HypercubicKernelFactorStatement) : HypercubicCubeRootStatement := by
  intro d t x ht
  rw [hF d t x, norm_prod]
  have hb : ∀ j ∈ Finset.univ, ‖latticeKernel1 t (x j : ℝ)‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3) :=
    fun j _ => OscInt.API.latticeKernel1CubeRoot t _ ht
  refine (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) hb).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.rpow_natCast (t ^ _),
    ← Real.rpow_mul ht.le]
  congr 2
  ring

end OscInt.HypercubicAux
