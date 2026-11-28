/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.StationaryLeadingSharpAssembly
import OscInt.Front.StationaryLeadingSharpTaylor
import OscInt.Front.StationaryLeadingSharpTail
import OscInt.Front.StationaryLeadingSharpCells

/-!
# Batch SPL-N: the final theorems

Route `docs/proof-SPLN.md`; blueprint `Blueprint/StationaryLeadingSharp.lean`; the lead's assembly
`OscInt/Front/StationaryLeadingSharpAssembly.lean`. Parts by proof agents: `StationaryLeadingSharpTaylor.lean`
(N1, N2, N4 and the small branch), `StationaryLeadingSharpTail.lean` (the branch `x ≥ 4`),
`StationaryLeadingSharpInterp.lean` (N5), `StationaryLeadingSharpCellsCore.lean`, `StationaryLeadingSharpCellsData.lean`
and `StationaryLeadingSharpCells.lean` (N3, N6, N7, N9: the 40-cell certificate by kernel computation, the lower
point), `StationaryLeadingSharpThird.lean` (N10).
-/

namespace OscInt.API

open OscInt.Statements OscInt.SPLNAux

/-- **SPL-NU** `|κ(τ)| ≤ 360987/500000` for every real τ. -/
theorem splKernelCap : SplKernelCapStatement :=
  splKernelCap_of splnTaylor splnSecond splnInterp ⟨splnSmall, splnTail⟩ splnCells

/-- **SPL-NL** `|κ(8123/5000)| > 72197399/10⁸`. -/
theorem splKernelLower : SplKernelLowerStatement := splKernelLower_of splnTaylor splnLower

/-- **SPL-NK** the remainder of the quadratic-phase leading term is at most `(360987/500000) ‖g‴‖₁ λ^{−3/2}`. -/
theorem stationaryLeadingSharp : StationaryLeadingSharpStatement := stationaryLeadingSharp_of splKernelCap

/-- **SPL-NC** no constant `c ≤ 72197399/10⁸` bounds the remainder. -/
theorem stationaryLeadingSharpness : StationaryLeadingSharpnessStatement :=
  stationaryLeadingSharpness_of splKernelLower splnThirdPos

end OscInt.API
