/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Batch LS, part P-exp: the exponential solves the lattice Schrödinger equation

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `ExpSolutionFacts`; the operator exponential is evaluated through `restrictScalars ℝ`, as the route revision requires.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

noncomputable section

namespace OscInt.LatticeGroupAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup

theorem expOrbit_hasDerivAt (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d)
    (f : LatticeL2 d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (Complex.I • A)) f)
      ((Complex.I • A) (NormedSpace.exp (t • (Complex.I • A)) f)) t := by
  -- `hasDerivAt_exp_smul_const'` gives `(I • A) * exp(t • (I • A))` in the operator algebra.
  -- `ContinuousLinearMap.hasFDerivAt` and `HasFDerivAt.comp_hasDerivAt` apply evaluation at `f`.
  -- Restricting evaluation to ℝ is essential: the variable `t` is real.
  exact (((ContinuousLinearMap.apply ℂ (LatticeL2 d) f).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    t (hasDerivAt_exp_smul_const' (Complex.I • A) t)

/-- Exact Blueprint type, with no additional hypotheses. -/
theorem expSolutionFacts : ExpSolutionFacts := by
  intro d A hA f
  constructor
  · -- `NormedSpace.exp_zero`: evaluation of the identity operator returns `f`.
    -- `zero_smul` does not unify here (two ℝ-actions on the operator space); prove it pointwise.
    have h0 : (0 : ℝ) • (Complex.I • A) = 0 := by
      ext g x
      simp
    beta_reduce
    rw [h0, NormedSpace.exp_zero]
    rfl
  · intro t
    refine ⟨(Complex.I • A) (NormedSpace.exp (t • (Complex.I • A)) f),
      expOrbit_hasDerivAt d A f t, ?_⟩
    intro x
    -- Scalar multiplication of operators and of `lp` vectors is pointwise.
    change Complex.I * (A (NormedSpace.exp (t • (Complex.I • A)) f)) x = _
    -- The frozen coordinate hypothesis for `A` identifies its value with the Laplacian.
    rw [hA]

end OscInt.LatticeGroupAux
