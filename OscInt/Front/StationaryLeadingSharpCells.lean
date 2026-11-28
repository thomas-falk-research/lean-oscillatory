/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.StationaryLeadingSharpInterp
import OscInt.Front.StationaryLeadingSharpThird
import OscInt.Front.StationaryLeadingSharpCellsData

/-!
# Batch SPL-N: the parts of agent C (N5, N3 + N6 + N7, N9, N10)

Route `docs/proof-SPLN.md`, section 2. The four blueprint propositions of agent C:

* `splnInterp : SplnInterpFacts` (**N5**, scalar trick; `StationaryLeadingSharpInterp.lean`);
* `splnCells : SplnCellsFacts` (**N3**, **N6**, **N7**: the 40 cells of the packet's certificate for
  `q = 360987/500000`, checked by the kernel, with generic cell soundness and coverage of `[1/2, 4]`;
  `StationaryLeadingSharpCellsCore.lean`, `StationaryLeadingSharpCellsData.lean`);
* `splnLower : SplnLowerFacts` (**N9**, midpoint `(s₀ + s₁)/2`);
* `splnThirdPos : SplnThirdPosFacts` (assembly paragraph of the route; `StationaryLeadingSharpThird.lean`).
-/

namespace OscInt.SPLNAux

open OscInt.Statements OscInt.Blueprint.SPLN

/-- **N5** Vector interpolation. -/
theorem splnInterp : OscInt.Blueprint.SPLN.SplnInterpFacts := splnC_interp

/-- **N3 + N6 + N7** The 40 cells: `‖κ₊‖ ≤ 360987/500000` on `[1/2, 4]`. -/
theorem splnCells : OscInt.Blueprint.SPLN.SplnCellsFacts := by
  intro hT hS hI x hx1 hx4
  have hc := splnC_check_true
  simp only [splnC_check, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨p, hp, h1, h2⟩ := splnC_chain_sound _ _ _ hc.2 x (by push_cast; linarith) (by push_cast; linarith)
  have h := splnC_cell hT hS hI _ p (hc.1 p hp) x h1 h2
  rwa [show ((splnC_q : ℚ) : ℝ) = 360987 / 500000 by norm_num [splnC_q]] at h

/-- **N9** The lower point: `‖κ₊(8123/5000)‖ > 72197399/10⁸`. -/
theorem splnLower : OscInt.Blueprint.SPLN.SplnLowerFacts := fun hT => splnC_lower_of hT splnC_lowOK_true

/-- **N10** A nonzero smooth compactly supported amplitude has `‖g₃‖₁ > 0`. -/
theorem splnThirdPos : OscInt.Blueprint.SPLN.SplnThirdPosFacts := splnC_thirdPos

end OscInt.SPLNAux
