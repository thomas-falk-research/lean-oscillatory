/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriDeriv

/-! # Batch TRI, part P-q: TRI-Q (`docs/proof-TRI.md`, section 6)

Evaluation of the explicit derivative forms of `OscInt/Front/TriDeriv.lean` at `(π/2, π/2)` and at `(θ, −θ)`,
`θ = arccos(−2α)`.
-/

namespace OscInt.API.TriQuartic

open OscInt.Statements OscInt.API.TriDeriv

theorem triQuartic_proof : TriQuarticStatement := by
  intro α _
  refine ⟨?_, ?_⟩
  · have hc : Real.cos (Real.pi / 2 + Real.pi / 2) = -1 := by
      rw [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring, Real.cos_pi]
    have hs : Real.sin (Real.pi / 2 + Real.pi / 2) = 0 := by
      rw [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring, Real.sin_pi]
    refine ⟨fun z => ?_, ?_, ?_⟩
    · rw [triD2_mixed]; simp only [Real.cos_pi_div_two, hc]; ring
    · rw [triD3]; simp only [Real.sin_pi_div_two, hs]; ring
    · rw [triD2, triD4, triD3_mixed]; simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, hc, hs]; ring
  · intro hle
    have h1 : -1 ≤ -2 * α := by linarith [abs_le.mp hle]
    have h2 : -2 * α ≤ 1 := by linarith [abs_le.mp hle]
    have hcos : Real.cos (Real.arccos (-2 * α)) = -2 * α := Real.cos_arccos h1 h2
    have hsin : Real.sin (Real.arccos (-2 * α)) ^ 2 = 1 - (-2 * α) ^ 2 := by
      rw [Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
    dsimp only
    have hz : Real.arccos (-2 * α) + -Real.arccos (-2 * α) = 0 := by ring
    refine ⟨fun z => ?_, ?_, ?_⟩
    · rw [triD2_mixed]; simp only [Real.cos_neg, hz, Real.cos_zero, hcos]; ring
    · rw [triD3]; simp only [Real.sin_neg, hz, Real.sin_zero]; ring
    · rw [triD2, triD4, triD3_mixed]
      simp only [Real.cos_neg, Real.sin_neg, hz, Real.cos_zero, Real.sin_zero, hcos]
      linear_combination (-12) * hsin

end OscInt.API.TriQuartic
