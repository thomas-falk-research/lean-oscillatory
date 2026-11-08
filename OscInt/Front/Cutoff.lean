/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Family

/-!
# Cut-off functions for the front end (API3, agent P2)

* `exists_cutoff`: a smooth cut-off `χ` with `tsupport χ ⊆ U` that equals `1` on an open neighbourhood of a compact `K`.
* `familyCk_cutoff`: multiplying a family smooth on `V ×ˢ U` by such a cut-off gives a `FamilyCk` family on `S ⊆ V`.
  The parameter space `E` may be infinite-dimensional; no bump function on `E` is used (germ argument instead).
* `cutoff_eventuallyEq`: the cut-off phase agrees with the phase near every point of `W`.
-/

open scoped ContDiff
open Filter Topology

namespace OscInt.API.CutoffAux

/-- A smooth cut-off: `χ` is `Cⁿ` for every `n`, `tsupport χ ⊆ U`, and `χ = 1` on an open `W ⊇ K`. -/
theorem exists_cutoff {K U : Set (ℝ × ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℝ × ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ tsupport χ ⊆ U ∧
      ∃ W : Set (ℝ × ℝ), IsOpen W ∧ K ⊆ W ∧ ∀ k ∈ W, χ k = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hex : ∃ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 ∧
      Function.support f = Metric.thickening (δ / 2) K ∧
      ∀ x, x ∈ Metric.cthickening (δ / 4) K ↔ f x = 1 :=
    exists_contDiff_support_eq_eq_one_iff Metric.isOpen_thickening Metric.isClosed_cthickening
      (Metric.cthickening_subset_thickening' (by linarith) (by linarith) K)
  obtain ⟨χ, hχ, -, hsupp, hone⟩ := hex
  refine ⟨χ, fun n => hχ.of_le (by exact_mod_cast le_top), ?_, Metric.thickening (δ / 4) K,
    Metric.isOpen_thickening, Metric.self_subset_thickening (by linarith) K, fun k hk => ?_⟩
  · calc tsupport χ = closure (Metric.thickening (δ / 2) K) := by rw [tsupport, hsupp]
      _ ⊆ Metric.cthickening (δ / 2) K := Metric.closure_thickening_subset_cthickening _ _
      _ ⊆ Metric.cthickening δ K := Metric.cthickening_mono (by linarith) K
      _ ⊆ U := hδU
  · exact (hone k).1 (Metric.thickening_subset_cthickening_of_le le_rfl K hk)

/-- Local slice identity: for `G` of class `Cⁿ` on the open product `V ×ˢ U`, the `j`-th derivative of the slice
`k ↦ G (σ, k)` at `k ∈ U` (`σ ∈ V`) is the `j`-th derivative of `G` restricted to the second factor. -/
theorem iteratedFDeriv_slice_of_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {G : E × (ℝ × ℝ) → ℝ} {V : Set E} {U : Set (ℝ × ℝ)} (hV : IsOpen V) (hU : IsOpen U)
    (hG : ContDiffOn ℝ n G (V ×ˢ U)) {σ : E} (hσ : σ ∈ V) {k : ℝ × ℝ} (hk : k ∈ U) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun k' => G (σ, k')) k =
      (iteratedFDeriv ℝ j G (σ, k)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ E (ℝ × ℝ)) := by
  set a : E × (ℝ × ℝ) := (σ, 0) with ha
  set T : Set (E × (ℝ × ℝ)) := (fun z => z + a) ⁻¹' (V ×ˢ U) with hTdef
  have hT : IsOpen T := (hV.prod hU).preimage (continuous_id.add continuous_const)
  have hGT : ContDiffOn ℝ n (fun z => G (z + a)) T :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hpre : (ContinuousLinearMap.inr ℝ E (ℝ × ℝ)) ⁻¹' T = U := by
    ext k'; simp [hTdef, ha, hσ]
  have hkT : ContinuousLinearMap.inr ℝ E (ℝ × ℝ) k ∈ T := by simp [hTdef, ha, hσ, hk]
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inr ℝ E (ℝ × ℝ))
    hGT hT.uniqueDiffOn (hpre ▸ hU.uniqueDiffOn) hkT (i := j) (by exact_mod_cast hj)
  rw [hpre] at key
  have h1 : (fun k' => G (σ, k')) = (fun z => G (z + a)) ∘ ContinuousLinearMap.inr ℝ E (ℝ × ℝ) := by
    ext k'; simp [ha]
  rw [h1, ← iteratedFDerivWithin_of_isOpen j hU hk, key, iteratedFDerivWithin_of_isOpen j hT hkT,
    iteratedFDeriv_comp_add_right]
  simp [ha]

/-- Away from `tsupport χ`, every derivative of `k ↦ χ k * f k` vanishes. -/
theorem iteratedFDeriv_mul_eq_zero {χ f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hk : k ∉ tsupport χ) (j : ℕ) :
    iteratedFDeriv ℝ j (fun k' => χ k' * f k') k = 0 := by
  have h : (fun k' => χ k' * f k') =ᶠ[𝓝 k] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hk] with x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [(h.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

/-- A family `Cⁿ` on the open product `V ×ˢ U`, multiplied by a `Cⁿ` cut-off with `tsupport χ ⊆ U`, is
`FamilyCk n` on `S ⊆ V`. -/
theorem familyCk_cutoff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {Ψ : E → ℝ × ℝ → ℝ} {S V : Set E} {U : Set (ℝ × ℝ)} {χ : ℝ × ℝ → ℝ}
    (hV : IsOpen V) (hU : IsOpen U) (hSV : S ⊆ V) (hΨ : ContDiffOn ℝ n (Function.uncurry Ψ) (V ×ˢ U))
    (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U) :
    OscInt.Statements.FamilyCk n (fun σ : S => fun k => χ k * Ψ σ k) := by
  set G : E × (ℝ × ℝ) → ℝ := fun p => χ p.2 * Function.uncurry Ψ p with hGdef
  have hG : ContDiffOn ℝ n G (V ×ˢ U) := (hχ.comp contDiff_snd).contDiffOn.mul hΨ
  have hO : IsOpen (V ×ˢ U) := hV.prod hU
  refine ⟨fun σ => ?_, fun j hj => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro k
    by_cases hk : k ∈ U
    · have hΨσ : ContDiffOn ℝ n (Ψ σ) U :=
        hΨ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun k' hk' => ⟨hSV σ.2, hk'⟩)
      exact hχ.contDiffAt.mul (hΨσ.contDiffAt (hU.mem_nhds hk))
    · have hk' : k ∉ tsupport χ := fun h => hk (hχU h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hk'] with x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  · rw [continuous_iff_continuousAt]
    rintro ⟨σ, k⟩
    by_cases hk : k ∈ U
    · have hev : (fun q : S × (ℝ × ℝ) =>
            ContinuousMultilinearMap.compContinuousLinearMapL
              (fun _ : Fin j => ContinuousLinearMap.inr ℝ E (ℝ × ℝ)) (iteratedFDeriv ℝ j G ((q.1 : E), q.2)))
          =ᶠ[𝓝 (σ, k)] fun q => iteratedFDeriv ℝ j (fun k' => χ k' * Ψ q.1 k') q.2 := by
        filter_upwards [(continuous_snd.isOpen_preimage U hU).mem_nhds hk] with q hq
        rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
        exact (iteratedFDeriv_slice_of_contDiffOn hV hU hG (hSV q.1.2) hq hj).symm
      refine ContinuousAt.congr ?_ hev
      refine (ContinuousLinearMap.continuous _).continuousAt.comp ?_
      have hc : ContinuousOn (iteratedFDeriv ℝ j G) (V ×ˢ U) :=
        (hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hO.uniqueDiffOn).congr
          (fun x hx => (iteratedFDerivWithin_of_isOpen j hO hx).symm)
      exact (hc.continuousAt (hO.mem_nhds ⟨hSV σ.2, hk⟩)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
    · have hk' : k ∉ tsupport χ := fun h => hk (hχU h)
      have hev : (fun _ : S × (ℝ × ℝ) => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ × ℝ) ℝ))
          =ᶠ[𝓝 (σ, k)] fun q => iteratedFDeriv ℝ j (fun k' => χ k' * Ψ q.1 k') q.2 := by
        filter_upwards [(continuous_snd.isOpen_preimage _ (isClosed_tsupport χ).isOpen_compl).mem_nhds hk']
          with q hq
        exact (iteratedFDeriv_mul_eq_zero hq j).symm
      exact continuousAt_const.congr hev

/-- Where the cut-off equals `1` on an open set, the cut-off phase has the germ of the phase. -/
theorem cutoff_eventuallyEq {Ψ : ℝ × ℝ → ℝ} {χ : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hχ : ∀ k ∈ W, χ k = 1) {k : ℝ × ℝ} (hk : k ∈ W) :
    (fun k => χ k * Ψ k) =ᶠ[nhds k] Ψ := by
  filter_upwards [hW.mem_nhds hk] with x hx
  simp [hχ x hx]

end OscInt.API.CutoffAux
