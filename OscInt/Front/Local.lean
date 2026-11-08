/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.Family
import OscInt.Front.Cutoff
import OscInt.Front.Convert

/-!
# Front-end batch 3: Mathlib-idiom bridges with local smoothness (FE-S2.1L, FE-S2.2L, FE-S3L, FE-S4.1′L, FE-S2.1l,
FE-S2.2l, FE-S3l)

Statements: `OscInt/Statements/Family.lean` (stamp `stamps/20261108T002603Z-9d03130c8f3a`; reviews stamped
`stamps/20261108T010546Z-7bb457958327` before any proof). Route: `docs/proof-API3.md` (P3). Each bridge multiplies the
phase by a cut-off equal to 1 near `K` and supported in `U` (`OscInt/Front/Cutoff.lean`, agent P2) and applies the
frozen S2.1, the re-assembled S2.2F/S3c (`OscInt/Front/Family.lean`) or FE-S4.1′, with C3, C7, C8 for the hypotheses.
-/

namespace OscInt.API.LocalAux

open OscInt.Statements OscInt.API.ConvertAux OscInt.API.CutoffAux

/-- Integrands agree when the phases agree on a set containing the amplitude's support. -/
theorem integral_congr_on {Φ Ψ : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {K : Set (ℝ × ℝ)} (hsupp : tsupport A ⊆ K)
    (h : ∀ k ∈ K, Φ k = Ψ k) (g : ℝ → ℝ × ℝ → ℝ) :
    ∫ k : ℝ × ℝ, Complex.exp (↑(g (Ψ k) k) * Complex.I) * A k =
      ∫ k : ℝ × ℝ, Complex.exp (↑(g (Φ k) k) * Complex.I) * A k := by
  congr 1; funext k
  by_cases hk : A k = 0
  · simp [hk]
  · rw [h k (hsupp (subset_tsupport _ hk))]

/-- A single phase smooth on `U` as a constant family in `σ ∈ ℝ`, smooth on `univ ×ˢ U`. -/
theorem contDiffOn_const_family {n : ℕ} {Ψ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hΨ : ContDiffOn ℝ n Ψ U) :
    ContDiffOn ℝ n (Function.uncurry fun (_ : ℝ) (k : ℝ × ℝ) => Ψ k) (Set.univ ×ˢ U) :=
  hΨ.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)

/-- The cut-off family and its agreement with `Ψ` near `K`, in one package. -/
theorem cutoff_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) {Ψ : E → ℝ × ℝ → ℝ}
    {S V : Set E} {K U : Set (ℝ × ℝ)} (hV : IsOpen V) (hSV : S ⊆ V) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hΨ : ContDiffOn ℝ n (Function.uncurry Ψ) (V ×ˢ U)) :
    ∃ Φ : S → ℝ × ℝ → ℝ, FamilyCk n Φ ∧ (∀ σ : S, ∀ k ∈ K, Φ σ =ᶠ[nhds k] Ψ σ) ∧
      ∀ σ : S, ∀ k ∈ K, Φ σ k = Ψ σ k := by
  obtain ⟨χ, hχ, hχU, W, hW, hKW, hχ1⟩ := exists_cutoff hK hU hKU
  refine ⟨fun σ k => χ k * Ψ σ k, familyCk_cutoff hV hU hSV hΨ (hχ n) hχU,
    fun σ k hk => cutoff_eventuallyEq hW hχ1 (hKW hk), fun σ k hk => ?_⟩
  simp [hχ1 k (hKW hk)]

end OscInt.API.LocalAux

namespace OscInt.API

open OscInt.Statements ConvertAux LocalAux

/-- **FE-S2.1L** -/
theorem nonStationaryLocal : NonStationaryLocalStatement := by
  intro E _ _ N Ψ S V K U c hS hV hSV hK hU hKU hΨ hc
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨Φ, hΦ, hev, heq⟩ := cutoff_family (N + 1) hV hSV hK hU hKU (by exact_mod_cast hΨ)
  obtain ⟨C, hC⟩ := OscInt.nonStationary S N Φ K (c / Real.sqrt 2) hΦ hK (by positivity)
  refine ⟨C, fun A M σ L m hσ hA hsupp hbd hgrad hm => ?_⟩
  have hdiff : ∀ k, DifferentiableAt ℝ (Φ ⟨σ, hσ⟩) k := fun k =>
    ((hΦ.1 ⟨σ, hσ⟩).differentiable (by simp)) k
  have hG : ∀ k ∈ K, GradLower (Φ ⟨σ, hσ⟩) (vecOf L) k (c / Real.sqrt 2) := by
    intro k hk
    refine ((gradLower_iff (Φ ⟨σ, hσ⟩) (vecOf L) k c (hdiff k) hc.le).2.2) ?_
    rw [vecOf, NormAux.fderiv_add_lin (hdiff k), (hev ⟨σ, hσ⟩ k hk).fderiv_eq]; exact hgrad k hk
  rw [integral_congr_on hsupp (heq ⟨σ, hσ⟩) (fun x k => m * (x + L k)), integral_eq_oscInt2]
  exact hC A M ⟨σ, hσ⟩ (vecOf L) m ⟨hA, hsupp, hbd⟩ hG hm

/-- The critical-point condition and the Hessian transfer from `Ψ σ` to the cut-off family at `k ∈ K`. -/
theorem LocalAux.transfer {Φ Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hev : Φ =ᶠ[nhds k] Ψ) (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    (IsCritical Φ (vecOf L) k ↔ fderiv ℝ Ψ k + L = 0) ∧ hessianMatrix Φ k = hessianMatrix Ψ k ∧
      iteratedFDeriv ℝ 3 Φ k = iteratedFDeriv ℝ 3 Ψ k := by
  refine ⟨by rw [isCritical_iff, hev.fderiv_eq], ?_, (hev.iteratedFDeriv ℝ 3).eq_of_nhds⟩
  simp only [hessianMatrix, (hev.iteratedFDeriv ℝ 2).eq_of_nhds]

/-- **FE-S2.2L** -/
theorem stationaryPhaseLocal : StationaryPhaseLocalStatement := by
  intro E _ _ Ψ S V K U K' hS hV hSV hK hU hKU hK' hΨ hcrit
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨Φ, hΦ, hev, heq⟩ := cutoff_family 4 hV hSV hK hU hKU (by exact_mod_cast hΨ)
  obtain ⟨C, hC⟩ := stationaryPhaseFamily S Φ K (vecOf '' K') hΦ hK (hK'.image continuous_vecOf) (by
    rintro σ _ ⟨L, hL, rfl⟩ k hk hcr
    obtain ⟨h1, h2, -⟩ := LocalAux.transfer (hev σ k hk) L
    rw [hessDet_eq_det _ k ((hΦ.1 σ).contDiffAt.of_le (by norm_num)), h2]
    exact hcrit σ σ.2 L hL k hk (h1.1 hcr))
  refine ⟨C, fun A M σ L m hσ hA hsupp hbd hL hm => ?_⟩
  rw [integral_congr_on hsupp (heq ⟨σ, hσ⟩) (fun x k => m * (x + L k)), integral_eq_oscInt2]
  exact hC A M ⟨σ, hσ⟩ (vecOf L) m ⟨hA, hsupp, hbd⟩ ⟨L, hL, rfl⟩ hm

/-- **FE-S3L** -/
theorem foldLocal : FoldLocalStatement := by
  intro E _ _ Ψ S V K U K' hS hV hSV hK hU hKU hK' hΨ hfold
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨Φ, hΦ, hev, heq⟩ := cutoff_family 4 hV hSV hK hU hKU (by exact_mod_cast hΨ)
  obtain ⟨C, hC⟩ := foldCrit S Φ K (vecOf '' K') hΦ hK (hK'.image continuous_vecOf) (by
    rintro σ _ ⟨L, hL, rfl⟩ k hk hcr
    obtain ⟨h1, h2, h3⟩ := LocalAux.transfer (hev σ k hk) L
    refine ((foldOrNondeg_iff (Φ σ) k ((hΦ.1 σ).contDiffAt.of_le (by norm_num))).1).2 ?_
    have := hfold σ σ.2 L hL k hk (h1.1 hcr)
    unfold FoldOrNondegMatrix at this ⊢
    rw [h2, h3]; exact this)
  refine ⟨C, fun A M σ L m hσ hA hsupp hbd hL hm => ?_⟩
  rw [integral_congr_on hsupp (heq ⟨σ, hσ⟩) (fun x k => m * (x + L k)), integral_eq_oscInt2]
  exact hC A M ⟨σ, hσ⟩ (vecOf L) m ⟨hA, hsupp, hbd⟩ ⟨L, hL, rfl⟩ hm

/-- **FE-S2.1l** -/
theorem nonStationaryOn : NonStationaryOnStatement := by
  intro N Ψ K U c hK hU hKU hΨ hc
  obtain ⟨C, hC⟩ := nonStationaryLocal ℝ N (fun _ => Ψ) {0} Set.univ K U c isCompact_singleton isOpen_univ
    (Set.subset_univ _) hK hU hKU (contDiffOn_const_family (by exact_mod_cast hΨ)) hc
  exact ⟨C, fun A M L m hA hsupp hbd hgrad hm => hC A M 0 L m rfl hA hsupp hbd hgrad hm⟩

/-- **FE-S2.2l** -/
theorem stationaryPhaseOn : StationaryPhaseOnStatement := by
  intro Ψ K U K' hK hU hKU hK' hΨ hcrit
  obtain ⟨C, hC⟩ := stationaryPhaseLocal ℝ (fun _ => Ψ) {0} Set.univ K U K' isCompact_singleton isOpen_univ
    (Set.subset_univ _) hK hU hKU hK' (contDiffOn_const_family (by exact_mod_cast hΨ))
    (fun _ _ L hL k hk h => hcrit L hL k hk h)
  exact ⟨C, fun A M L m hA hsupp hbd hL hm => hC A M 0 L m rfl hA hsupp hbd hL hm⟩

/-- **FE-S3l** -/
theorem foldOn : FoldOnStatement := by
  intro Ψ K U K' hK hU hKU hK' hΨ hfold
  obtain ⟨C, hC⟩ := foldLocal ℝ (fun _ => Ψ) {0} Set.univ K U K' isCompact_singleton isOpen_univ
    (Set.subset_univ _) hK hU hKU hK' (contDiffOn_const_family (by exact_mod_cast hΨ))
    (fun _ _ L hL k hk h => hfold L hL k hk h)
  exact ⟨C, fun A M L m hA hsupp hbd hL hm => hC A M 0 L m rfl hA hsupp hbd hL hm⟩

end OscInt.API

namespace OscInt.API

open OscInt.Statements ConvertAux LocalAux CutoffAux

/-- **FE-S4.1′L** -/
theorem d4BoundLocal : D4BoundLocalStatement := by
  intro φ U a b c d hU h0 hφ h2 h3 hdisc
  obtain ⟨χ, hχ, hχU, W, hW, h0W, hχ1⟩ :=
    exists_cutoff (isCompact_singleton (x := (0 : ℝ × ℝ))) hU (Set.singleton_subset_iff.mpr h0)
  have hW0 : (0 : ℝ × ℝ) ∈ W := h0W rfl
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW 0 hW0
  have hφ' : ContDiff ℝ 4 (fun k => χ k * φ k) := by
    have := (familyCk_cutoff (n := 4) (Ψ := fun _ : ℝ => φ) (S := {(0 : ℝ)}) isOpen_univ hU
      (Set.subset_univ _) (contDiffOn_const_family (by exact_mod_cast hφ)) (hχ 4) hχU).1 ⟨0, rfl⟩
    exact_mod_cast this
  have hev : (fun k => χ k * φ k) =ᶠ[nhds 0] φ := cutoff_eventuallyEq hW hχ1 hW0
  obtain ⟨δ, hδ, C, hC⟩ := d4BoundFE (fun k => χ k * φ k) a b c d hφ'
    (by rw [(hev.iteratedFDeriv ℝ 2).eq_of_nhds]; exact h2)
    (by intro x y; rw [(hev.iteratedFDeriv ℝ 3).eq_of_nhds]; exact h3 x y) hdisc
  refine ⟨min δ (r / 2), lt_min hδ (by positivity), C, fun A M L t hA hsupp hbd ht => ?_⟩
  have hsub : Metric.closedBall (0 : ℝ × ℝ) (min δ (r / 2)) ⊆ W := fun k hk =>
    hrW (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hk)
      (lt_of_le_of_lt (min_le_right _ _) (by linarith))))
  have heq : ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) (min δ (r / 2)), χ k * φ k = φ k := fun k hk => by
    simp [hχ1 k (hsub hk)]
  rw [integral_congr_on hsupp heq (fun x k => t * x + L k)]
  exact hC A M L t hA (hsupp.trans (Metric.closedBall_subset_closedBall (min_le_left _ _))) hbd ht

end OscInt.API
