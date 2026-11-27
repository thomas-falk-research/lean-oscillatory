/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriBlueprint

/-! # Batch TRI: the assembly (`docs/proof-TRI.md`, section 7)

TRI-K, TRI-X and TRI-W from the blueprint propositions, each taken as a hypothesis. TRI-Q is proved directly in its own
part. The bite owed by the answers to the blind reviews (`review/2026-11-27-TRI-preproof-answers.md`, A2) is a
corollary of TRI-X.
-/

namespace OscInt.API.TriAssembly

open OscInt.Statements OscInt.API.TriBlueprint
open scoped ContDiff

theorem triClassification_of (hC : AlgClassify) (hW : WitA5) : TriClassificationStatement := by
  intro α hα k
  rcases hC α hα k with h | h | ⟨hab, hloc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hW α hab k hloc))

theorem triA5Locus_of (hB : Bridge) (hA : AlgA5) (hZ : AlgZero)
    (hsmooth : ∀ α : ℝ, ContDiff ℝ ∞ (triPhase α)) : TriA5LocusStatement := by
  intro α k hk
  obtain ⟨v, w, hv, hker, hww, ε, hε, h, hc, hz, -⟩ := hk
  obtain ⟨h3, h4⟩ := hB (triPhase α) k v w ε h (hsmooth α) hker hww hε hc
  have hcub : iteratedFDeriv ℝ 3 (triPhase α) k ![v, v, v] = 0 := by
    rw [← h3]; exact hz 3 (by simp)
  have hq : qinv (triPhase α) k v w = 0 := by
    have := hz 4 (by simp)
    rw [h4] at this
    exact (div_eq_zero_iff.mp this).resolve_right hww
  by_cases hα : α = 0
  · subst hα
    exact absurd hcub (hZ k v w hv hker hww)
  · obtain ⟨hab, j₁, j₂, hk'⟩ := hA α hα k v w hv hker hcub hww hq
    exact ⟨hab, j₁, j₂, hk'⟩

theorem triA5Witness_of (hW : WitA5) (hS : WitSextic) : TriA5WitnessStatement := by
  intro α hα
  refine ⟨hW α hα _ ⟨0, 0, Or.inl (by simp)⟩, hW α hα _ ⟨0, 0, Or.inr (by simp)⟩, ?_⟩
  intro ε h hε hc
  exact hS α hα ε h hε hc

/-- The bite owed with the proofs (`review/2026-11-27-TRI-preproof-answers.md`, A2): the A3 point `(π/2, π/2)` of
`triPhase (1/4)` is not an A5 point. -/
theorem quarter_halfPi_not_isA5_of (hX : TriA5LocusStatement) :
    ¬ IsA5Point (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) := by
  intro h
  have hab := (hX _ _ h).1
  have hsq : triExceptional ^ 2 = 1 / 8 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [triExceptional, div_pow, mul_pow, h2]; norm_num
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hab
  rw [← hab] at hsq
  norm_num at hsq

end OscInt.API.TriAssembly
