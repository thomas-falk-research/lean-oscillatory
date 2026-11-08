/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Vector
import OscInt.Front.GlobalSanity

/-! # Sanity theorems through the batch-VT statement constants

Each theorem takes a frozen statement of `OscInt/Statements/Vector.lean` as its only statement hypothesis (lessons 33).
* The specialisation `E = ℂ` of each vector statement is the frozen scalar statement of batch GD, word for word
  (`•` is `*` on `ℂ`): a plant that strengthens a hypothesis or weakens the conclusion of a vector statement relative to
  its scalar counterpart is detected here.
* Matrix-valued data: GD-N-V with `E = Fin 2 → Fin 2 → ℂ` (sup norm) on `x² + 3xy + 5y²`, `K = B̄(0, 1)`, `U = B(0, 2)`.
* GD-F-V and GD-V with `E = ℂ × ℂ` on the fold `x³ + y²` and the elliptic umbilic `x³ − 3xy²` (the data of batch GD).
Structural limit as before: a plant that weakens a hypothesis, strengthens the conclusion or lets `C` depend on `E`
(moving `∃ C` after `∀ E`, a weakening) is not detected and rests on the blind reviews.
-/

namespace OscInt.API.VectorSanity

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.ConvertSanity
open scoped ContDiff

theorem globalDecayCrit_of_vec (h : GlobalDecayCritVecStatement) : GlobalDecayCritStatement := by
  intro Ψ K U K' D hK hU hKU hDU hK' hΨ hcl
  obtain ⟨C, hC⟩ := h Ψ K U K' D hK hU hKU hDU hK' hΨ hcl
  exact ⟨C, fun A M L m hA hs hM hL hm => by simpa [smul_eq_mul] using hC ℂ A M L m hA hs hM hL hm⟩

theorem globalDecay_of_vec (h : GlobalDecayVecStatement) : GlobalDecayStatement := by
  intro Ψ K U D hK hU hKU hDU hΨ hcl
  obtain ⟨C, hC⟩ := h Ψ K U D hK hU hKU hDU hΨ hcl
  exact ⟨C, fun A M L m hA hs hM hm => by simpa [smul_eq_mul] using hC ℂ A M L m hA hs hM hm⟩

theorem globalFold_of_vec (h : GlobalFoldVecStatement) : GlobalFoldStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  obtain ⟨C, hC⟩ := h Ψ K U hK hU hKU hΨ hcl
  exact ⟨C, fun A M L m hA hs hM hm => by simpa [smul_eq_mul] using hC ℂ A M L m hA hs hM hm⟩

theorem globalNondeg_of_vec (h : GlobalNondegVecStatement) : GlobalNondegStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  obtain ⟨C, hC⟩ := h Ψ K U hK hU hKU hΨ hcl
  exact ⟨C, fun A M L m hA hs hM hm => by simpa [smul_eq_mul] using hC ℂ A M L m hA hs hM hm⟩

/-- **GD-N-V on matrix-valued amplitudes** (`E = Fin 2 → Fin 2 → ℂ`), `Ψ = x² + 3xy + 5y²`. -/
theorem globalNondeg_matrix (h : GlobalNondegVecStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (quadPhase k + L k)) * Complex.I) • A k‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := h quadPhase (Metric.closedBall 0 1) (Metric.ball 0 2)
    (isCompact_closedBall _ _) Metric.isOpen_ball (Metric.closedBall_subset_ball (by norm_num))
    (by unfold quadPhase; fun_prop : ContDiff ℝ 4 quadPhase).contDiffOn
    (fun k _ => by unfold quadPhase; rw [(hessian_mixed k).2]; norm_num)
  exact ⟨C, fun A M L m => hC (Fin 2 → Fin 2 → ℂ) A M L m⟩

/-- **GD-F-V on `ℂ²`-valued amplitudes**, the fold `x³ + y²`. -/
theorem globalFold_pair (h : GlobalFoldVecStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ × ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (foldPhase k + L k)) * Complex.I) • A k‖ ≤
        C * M * m ^ (-(5 : ℝ) / 6) := by
  obtain ⟨C, hC⟩ := h foldPhase (Metric.closedBall 0 1) Set.univ (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (by unfold foldPhase; fun_prop) (fun k _ => foldOrNondegMatrix_fold k)
  exact ⟨C, fun A M L m => hC (ℂ × ℂ) A M L m⟩

/-- **GD-V on `ℂ²`-valued amplitudes**, the elliptic umbilic `x³ − 3xy²` with its D4 point at `0`. -/
theorem globalDecay_pair (h : GlobalDecayVecStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ × ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (ellPhase k + L k)) * Complex.I) • A k‖ ≤
        C * M * m ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C, hC⟩ := h ellPhase (Metric.closedBall 0 1) Set.univ {0} (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (Set.subset_univ _) ellPhase_contDiff.contDiffOn ell_classified
  exact ⟨C, fun A M L m => hC (ℂ × ℂ) A M L m⟩

end OscInt.API.VectorSanity
