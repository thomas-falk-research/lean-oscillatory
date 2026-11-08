/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.VanDerCorput.Final
import OscInt.StationaryPhase.Final
import OscInt.D4.Final
import OscInt.D4.ConstantPosFinal
import OscInt.D4.LimitFinal
import OscInt.D4.ClosedFormFinal
import OscInt.Statements.FrontEnd

/-!
# Front-end batch 1 (F1, F2): bridges

Proved from frozen statements (S4.2, S4.4) by short bridge lemmas. The user-facing entry point is `OscInt/API.lean`
(`import OscInt.API`), which imports this file; the table of every theorem is there.
-/

namespace OscInt.API

open Filter Topology OscInt.Statements

/-- **F1** A `Cⁿ` amplitude whose support closure lies in a compact set `K` satisfies the amplitude bound
`AmpBound n K A M` for some `M` (each `iteratedFDeriv ℝ j A`, `j ≤ n`, is continuous with support in `K`, hence
bounded). Use it to apply S2–S4 to an amplitude given in Mathlib's idiom. -/
theorem ampBoundOfContDiff : AmpBoundOfContDiffStatement := by
  intro n K A hK hA hsupp
  have hb : ∀ j ≤ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M := by
    intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j A) := hA.continuous_iteratedFDeriv (by exact_mod_cast hj)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
    by_cases hk : k ∈ K
    · exact (hC k hk).trans (le_max_left _ _)
    · have : k ∉ tsupport (iteratedFDeriv ℝ j A) := fun h => hk (hsupp (tsupport_iteratedFDeriv_subset j h))
      rw [image_eq_zero_of_notMem_tsupport this, norm_zero]; exact le_max_right _ _
  choose! Mj hMj0 hMj using hb
  refine ⟨∑ j ∈ Finset.range (n + 1), Mj j, hA, hsupp, fun j hj k => ?_⟩
  refine (hMj j hj k).trans ?_
  exact Finset.single_le_sum (f := Mj) (fun i hi => hMj0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- S4.4 in terms of the discriminant: `c_C = d4ClosedConstant (disc C)` whenever `disc C ≠ 0`. -/
theorem d4Constant_eq_closed (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    d4Constant q = d4ClosedConstant (disc q) := by
  rcases lt_or_gt_of_ne hq with h | h
  · rw [OscInt.d4ConstantClosedForm.2.1 q h, d4ClosedConstant]; simp only [h, ↓reduceIte]
  · rw [OscInt.d4ConstantClosedForm.2.2 q h, d4ClosedConstant]; simp only [not_lt.mpr h.le, ↓reduceIte]

/-- **F2** The D4 leading term with its closed-form constant: at a point where `φ`, `∇φ` and `∇²φ` vanish and the
cubic part `C` has `Disc C ≠ 0`, for every `C²` amplitude supported in a small ball,
`t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc C|^{1/6}) · A(0)` (`Disc C < 0`) or `Γ(1/3)²/(Disc C)^{1/6} · A(0)`
(`Disc C > 0`). From S4.2 (`OscInt.d4Limit`), S4.4 (`OscInt.d4ConstantClosedForm`) and F1. -/
theorem d4LimitClosedForm : D4LimitClosedFormStatement := by
  intro φ hφ h0 h1 h2 hd
  obtain ⟨δ, hδ, hlim⟩ := OscInt.d4Limit φ hφ h0 h1 h2 hd
  refine ⟨δ, hδ, fun A hA hsupp => ?_⟩
  obtain ⟨M, hM⟩ := ampBoundOfContDiff 2 _ A (isCompact_closedBall 0 δ) hA hsupp
  have := hlim A M hM
  rw [d4Constant_eq_closed _ hd] at this
  exact this

end OscInt.API
