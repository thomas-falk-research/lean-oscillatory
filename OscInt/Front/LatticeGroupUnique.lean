/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeGroupOp
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Batch LS, part P-unique: uniqueness of solutions

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `UniqueFacts` with `ODE_solution_unique_univ`, as the route revision requires.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

noncomputable section

namespace OscInt.LatticeGroupAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup

theorem solution_hasDerivAt (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d)
    (hA : ∀ (g : LatticeL2 d) (x : Fin d → ℤ),
      A g x = latticeLaplacian d (fun y => g y) x)
    (f : LatticeL2 d) (u : ℝ → LatticeL2 d)
    (hu : IsLatticeSchrodingerSolution d f u) (t : ℝ) :
    HasDerivAt u ((Complex.I • A) (u t)) t := by
  obtain ⟨w, hw, hwx⟩ := hu.2 t
  have heq : w = (Complex.I • A) (u t) := by
    -- `lp.ext`: use every coordinate equality in the frozen solution predicate.
    apply lp.ext
    funext x
    change w x = Complex.I * (A (u t)) x
    rw [hA]
    exact hwx x
  -- Replace the derivative vector by the equal value of the bounded vector field.
  rw [← heq]
  exact hw

/-- Exact Blueprint type, with no additional hypotheses. -/
theorem uniqueFacts : UniqueFacts := by
  intro d f u v hu hv
  obtain ⟨A, hA, _⟩ := lapOpFacts d
  let B : LatticeL2 d →L[ℝ] LatticeL2 d := (Complex.I • A).restrictScalars ℝ
  -- `ODE_solution_unique_univ`: constant-in-time globally Lipschitz vector field, initial time zero.
  apply ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ)
    (K := ‖B‖₊) (t₀ := 0)
  · intro t
    -- `ContinuousLinearMap.lipschitzWith` and `LipschitzWith.lipschitzOnWith` supply the global bound.
    exact B.lipschitzWith.lipschitzOnWith
  · intro t
    exact ⟨solution_hasDerivAt d A hA f u hu t, Set.mem_univ _⟩
  · intro t
    exact ⟨solution_hasDerivAt d A hA f v hv t, Set.mem_univ _⟩
  · exact hu.1.trans hv.1.symm

end OscInt.LatticeGroupAux
