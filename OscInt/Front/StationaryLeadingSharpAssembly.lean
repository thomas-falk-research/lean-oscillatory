/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.StationaryLeadingFinal
import Blueprint.StationaryLeadingSharp

/-!
# Batch SPL-N: the lead's assembly from the blueprint parts

The four statements from the parts of `Blueprint/StationaryLeadingSharp.lean` and the proved batch SPL
(SPL-S `OscInt.API.stationaryLeading`, SPL-A `OscInt.API.stationaryLeadingAttained`). Route `docs/proof-SPLN.md`.
-/

namespace OscInt.SPLNAux

open OscInt.Statements OscInt.Blueprint.SPLN MeasureTheory

/-- The kernel on the right half-line is at most the cap. -/
theorem kernelPos_cap (hT : SplnTaylorFacts) (hS : SplnSecondFacts) (hI : SplnInterpFacts)
    (hB : SplnBranchFacts) (hC : SplnCellsFacts) (x : ℝ) (hx : 0 ≤ x) :
    ‖splKernelPos x‖ ≤ 360987 / 500000 := by
  rcases le_or_gt x (1 / 2) with h1 | h1
  · exact (hB.1 x hx h1).trans (by norm_num)
  rcases le_or_gt x 4 with h4 | h4
  · exact hC hT hS hI x h1.le h4
  · exact (hB.2 x h4.le).trans (by norm_num)

/-- SPL-NU from the parts. -/
theorem splKernelCap_of (hT : SplnTaylorFacts) (hS : SplnSecondFacts) (hI : SplnInterpFacts)
    (hB : SplnBranchFacts) (hC : SplnCellsFacts) : SplKernelCapStatement := by
  intro τ
  unfold splKernel
  split_ifs with h
  · exact kernelPos_cap hT hS hI hB hC τ h
  · rw [norm_neg]; exact kernelPos_cap hT hS hI hB hC (-τ) (by linarith)

/-- SPL-NL from the parts. -/
theorem splKernelLower_of (hT : SplnTaylorFacts) (hL : SplnLowerFacts) : SplKernelLowerStatement := by
  unfold SplKernelLowerStatement splKernel
  rw [ite_eq_left (by norm_num)]
  exact hL hT

/-- SPL-NK from SPL-NU and SPL-S. -/
theorem stationaryLeadingSharp_of (hU : SplKernelCapStatement) : StationaryLeadingSharpStatement := by
  intro g g₁ g₂ g₃ lam hg hlam
  obtain ⟨τ, -, hτ⟩ := OscInt.API.stationaryLeading g g₁ g₂ g₃ lam hg hlam
  refine hτ.trans ?_
  have h0 : 0 ≤ ∫ t, ‖g₃ t‖ := integral_nonneg fun _ => norm_nonneg _
  have h1 : 0 ≤ lam ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hlam.le _
  have := hU τ
  gcongr

/-- SPL-NC from SPL-NL, SPL-A and the positivity part. -/
theorem stationaryLeadingSharpness_of (hL : SplKernelLowerStatement) (hP : SplnThirdPosFacts) :
    StationaryLeadingSharpnessStatement := by
  intro c hc hall
  set k := ‖splKernel (8123 / 5000)‖ with hk
  have hck : c < k := lt_of_le_of_lt hc hL
  obtain ⟨g, g₁, g₂, g₃, hg, hsm, hcs, hne, hA⟩ :=
    OscInt.API.stationaryLeadingAttained (8123 / 5000) ((k - c) / 2) (by norm_num) (by linarith)
  have hpos := hP g g₁ g₂ g₃ hg hsm hcs hne
  have hub := hall g g₁ g₂ g₃ 1 hg one_pos
  rw [Real.one_rpow, mul_one] at hub
  have : (k - (k - c) / 2) * (∫ t, ‖g₃ t‖) ≤ c * (∫ t, ‖g₃ t‖) := hA.trans hub
  nlinarith

end OscInt.SPLNAux
