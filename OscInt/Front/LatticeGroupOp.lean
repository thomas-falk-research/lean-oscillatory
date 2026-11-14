/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Batch LS, part P-op: the lattice Laplacian as a bounded operator on ℓ²(ℤ^d)

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `LapOpFacts`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

noncomputable section

namespace OscInt.LatticeGroupAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup
open scoped BigOperators ENNReal

theorem shift_mem (d : ℕ) (z : Fin d → ℤ) (g : LatticeL2 d) :
    Memℓp (fun x => g (x + z)) 2 := by
  -- `memℓp_gen_iff`: the goal becomes summability of the shifted squared norms.
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  -- `Equiv.summable_iff`: translation is a bijective reindexing of the lattice.
  exact (Equiv.addRight z).summable_iff.mpr
    ((lp.memℓp g).summable (by norm_num))

def shiftVector (d : ℕ) (z : Fin d → ℤ) (g : LatticeL2 d) : LatticeL2 d :=
  ⟨fun x => g (x + z), shift_mem d z g⟩

theorem shiftVector_apply (d : ℕ) (z : Fin d → ℤ) (g : LatticeL2 d) (x : Fin d → ℤ) :
    shiftVector d z g x = g (x + z) := rfl

theorem shiftVector_norm (d : ℕ) (z : Fin d → ℤ) (g : LatticeL2 d) :
    ‖shiftVector d z g‖ = ‖g‖ := by
  -- `lp.norm_eq_tsum_rpow`: both norms are the square root of a sum of squared norms.
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  -- `Equiv.tsum_eq`: the two sums coincide under the translation equivalence.
  congr 1
  exact (Equiv.addRight z).tsum_eq (fun x => ‖g x‖ ^ (2 : ℝ≥0∞).toReal)

def shiftLinear (d : ℕ) (z : Fin d → ℤ) : LatticeL2 d →ₗ[ℂ] LatticeL2 d where
  toFun := shiftVector d z
  map_add' f g := by
    -- `lp.ext`: reduce vector equality to equality of coordinate functions.
    apply lp.ext
    funext x
    rfl
  map_smul' c f := by
    -- `lp.ext`: scalar multiplication is pointwise on this subtype.
    apply lp.ext
    funext x
    rfl

def lapLinear (d : ℕ) : LatticeL2 d →ₗ[ℂ] LatticeL2 d :=
  ∑ j : Fin d, (shiftLinear d (latticeUnit d j) + shiftLinear d (-latticeUnit d j) -
    (2 : ℂ) • LinearMap.id)

theorem lapLinear_apply (d : ℕ) (g : LatticeL2 d) (x : Fin d → ℤ) :
    lapLinear d g x = latticeLaplacian d (fun y => g y) x := by
  -- Finite sums and `lp` operations evaluate pointwise; `sub_eq_add_neg` matches the negative shift.
  simp only [lapLinear, LinearMap.sum_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [latticeLaplacian, sub_eq_add_neg]
  rfl

theorem lapLinear_term_bound (d : ℕ) (g : LatticeL2 d) (j : Fin d) :
    ‖shiftVector d (latticeUnit d j) g + shiftVector d (-latticeUnit d j) g -
      (2 : ℂ) • g‖ ≤ 4 * ‖g‖ := by
  -- `norm_sub_le` and `norm_add_le` give the three-term triangle inequality.
  calc
    _ ≤ ‖shiftVector d (latticeUnit d j) g + shiftVector d (-latticeUnit d j) g‖ +
        ‖(2 : ℂ) • g‖ := norm_sub_le _ _
    _ ≤ (‖shiftVector d (latticeUnit d j) g‖ + ‖shiftVector d (-latticeUnit d j) g‖) +
        ‖(2 : ℂ) • g‖ := add_le_add_left (norm_add_le _ _) _
    -- `shiftVector_norm`, `norm_smul`: the right side is `(1 + 1 + 2) * ‖g‖`.
    _ = 4 * ‖g‖ := by norm_num [shiftVector_norm, norm_smul]; ring

theorem lapLinear_bound (d : ℕ) (g : LatticeL2 d) :
    ‖lapLinear d g‖ ≤ (4 * d : ℝ) * ‖g‖ := by
  -- Evaluation of a finite sum of linear maps yields a finite sum in `LatticeL2 d`.
  change ‖(∑ j : Fin d, (shiftLinear d (latticeUnit d j) +
    shiftLinear d (-latticeUnit d j) - (2 : ℂ) • LinearMap.id) :
      LatticeL2 d →ₗ[ℂ] LatticeL2 d) g‖ ≤ _
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  -- `norm_sum_le`, `Finset.sum_le_sum`: sum the bound for each of the `d` coordinates.
  calc
    _ ≤ ∑ j : Fin d, ‖shiftVector d (latticeUnit d j) g +
        shiftVector d (-latticeUnit d j) g - (2 : ℂ) • g‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, 4 * ‖g‖ := Finset.sum_le_sum (fun j _ => lapLinear_term_bound d g j)
    _ = (4 * d : ℝ) * ‖g‖ := by simp; ring

def lapOperator (d : ℕ) : LatticeL2 d →L[ℂ] LatticeL2 d :=
  (lapLinear d).mkContinuous (4 * d) (lapLinear_bound d)

theorem lapOperator_apply (d : ℕ) (g : LatticeL2 d) (x : Fin d → ℤ) :
    lapOperator d g x = latticeLaplacian d (fun y => g y) x :=
  lapLinear_apply d g x

theorem lapOperator_norm_le (d : ℕ) : ‖lapOperator d‖ ≤ (4 * d : ℝ) := by
  -- `LinearMap.mkContinuous_norm_le`: the constructing bound controls the operator norm.
  exact LinearMap.mkContinuous_norm_le (lapLinear d) (by positivity) (lapLinear_bound d)

/-- Exact Blueprint type, with no additional hypotheses. -/
theorem lapOpFacts : LapOpFacts := by
  intro d
  exact ⟨lapOperator d, lapOperator_apply d, lapOperator_norm_le d⟩

end OscInt.LatticeGroupAux
