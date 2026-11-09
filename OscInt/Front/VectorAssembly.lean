/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Vector
import OscInt.Front.GlobalFinal

/-!
# Batch VT: the lead's assembly against the blueprint (route `docs/proof-VT.md`)

Each vector statement from the proved scalar statement (batch GD) and P-transfer, with `θ = m(Ψ + L)` and the same
constant. Compiled before the part was proved.
-/

namespace OscInt.VectorAux

open OscInt.Statements OscInt.Blueprint

theorem theta_cont (Ψ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (hΨ : ContDiffOn ℝ 4 Ψ U) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ) :
    ContinuousOn (fun k => m * (Ψ k + L k)) U :=
  continuousOn_const.mul (hΨ.continuousOn.add L.continuous.continuousOn)

theorem gdcv_of (hT : VecTransferFacts) : GlobalDecayCritVecStatement := by
  intro Ψ K U K' D hK hU hKU hDU hK' hΨ hcl
  obtain ⟨C, hC⟩ := OscInt.API.globalDecayCrit Ψ K U K' D hK hU hKU hDU hK' hΨ hcl
  exact ⟨C, fun E _ _ _ A M L m hA hs hM hL hm => hT K U _ (fun M => C * M * m ^ (-(2 : ℝ) / 3)) hK hU hKU
    (theta_cont Ψ U hΨ L m) (fun A' M' hA' hs' hM' => hC A' M' L m hA' hs' hM' hL hm) E A M hA hs hM⟩

theorem gdv_of (hT : VecTransferFacts) : GlobalDecayVecStatement := by
  intro Ψ K U D hK hU hKU hDU hΨ hcl
  obtain ⟨C, hC⟩ := OscInt.API.globalDecay Ψ K U D hK hU hKU hDU hΨ hcl
  exact ⟨C, fun E _ _ _ A M L m hA hs hM hm => hT K U _ (fun M => C * M * m ^ (-(2 : ℝ) / 3)) hK hU hKU
    (theta_cont Ψ U hΨ L m) (fun A' M' hA' hs' hM' => hC A' M' L m hA' hs' hM' hm) E A M hA hs hM⟩

theorem gdfv_of (hT : VecTransferFacts) : GlobalFoldVecStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  obtain ⟨C, hC⟩ := OscInt.API.globalFold Ψ K U hK hU hKU hΨ hcl
  exact ⟨C, fun E _ _ _ A M L m hA hs hM hm => hT K U _ (fun M => C * M * m ^ (-(5 : ℝ) / 6)) hK hU hKU
    (theta_cont Ψ U hΨ L m) (fun A' M' hA' hs' hM' => hC A' M' L m hA' hs' hM' hm) E A M hA hs hM⟩

theorem gdnv_of (hT : VecTransferFacts) : GlobalNondegVecStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  obtain ⟨C, hC⟩ := OscInt.API.globalNondeg Ψ K U hK hU hKU hΨ hcl
  exact ⟨C, fun E _ _ _ A M L m hA hs hM hm => hT K U _ (fun M => C * M / m) hK hU hKU
    (theta_cont Ψ U hΨ L m) (fun A' M' hA' hs' hM' => hC A' M' L m hA' hs' hM' hm) E A M hA hs hM⟩

end OscInt.VectorAux
