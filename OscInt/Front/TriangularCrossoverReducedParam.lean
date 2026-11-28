/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriangularCrossoverReducedParamData
import OscInt.Front.TriangularDecayLocal
import OscInt.Front.TriangularDecayChart
import OscInt.Front.TriangularDecayCore

/-!
# Batch A5U, part B1: K2-L uniformly in a parameter (`ReducedOrderBoundParamFacts`)

Route `docs/proof-A5U.md`, section 5 (B1). A clone of `OscInt.K2.reducedOrderBound_of` in which every
constant is chosen at the base parameter `α₀`:
* the chart `κ = k₀ + L k` of K2's P3 (`OscInt.K2.chart`) at `Ψ α₀`, the same `L` for every `α`;
* the family `Φ α k = Ψ α (k₀ + L k) − Ψ α k₀ − DΨ α (k₀) (L k)`, jointly `C^∞` (`a5uB_family_smooth`), with
  `Φ α₀` a normal point of order `m`;
* near tilts `|q| ≤ q₀`: the uniform data `a5uB_paramData` and K2's P1 (`OscInt.K2.coreEstimateM`);
* far tilts: `OscInt.Cusp.transverseNonStat` on a box where `|∂_s Φ α| ≤ q₀/2` and `|∂²_s Φ α| ≤ D'` for all
  `|α − α₀| ≤ r` (continuity at `(α₀, 0)`, `a5uB_farData`).
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.StationaryPhase
open OscInt.Cusp.AssemblyAux OscInt.K2.LocalAux
open scoped ContDiff

/-- The chart family `Φ α k = Ψ α (k₀ + L k) − Ψ α k₀ − DΨ α (k₀) (L k)` is jointly `C^∞`. -/
theorem a5uB_family_smooth {Ψ : ℝ → ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)) (k₀ : ℝ × ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ContDiff ℝ ∞ (Function.uncurry fun (α : ℝ) (k : ℝ × ℝ) =>
      Ψ α (k₀ + L k) - Ψ α k₀ - fderiv ℝ (Ψ α) k₀ (L k)) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ p.1 (k₀ + L p.2)) :=
    hΨ.comp (contDiff_fst.prodMk (contDiff_const.add (L.contDiff.comp contDiff_snd)))
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ p.1 k₀) := hΨ.comp (contDiff_fst.prodMk contDiff_const)
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (x : ℝ × (ℝ × ℝ)) (z : ℝ × ℝ) => Ψ x.1 z) :=
    hΨ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have h4 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (Ψ p.1) k₀ (L p.2)) :=
    h3.fderiv_apply contDiff_const (L.contDiff.comp contDiff_snd) (by simp)
  exact (h1.sub h2).sub h4

/-- The far-tilt box: for `|α − α₀| ≤ r` and `|x|, |y| ≤ r`, `|∂_s Φ α| ≤ q₀/2` and `|∂²_s Φ α| ≤ D'`. -/
theorem a5uB_farData {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) {α₀ q₀ : ℝ}
    (h0 : fderiv ℝ (Φ α₀) 0 (0, 1) = 0) (hq₀ : 0 < q₀) :
    ∃ r > 0, ∃ D' : ℝ, ∀ α : ℝ, |α - α₀| ≤ r → ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r,
      |fderiv ℝ (Φ α) k (0, 1)| ≤ q₀ / 2 ∧ |dd (Φ α) k (0, 1) (0, 1)| ≤ D' := by
  have ev : ∀ᶠ p in nhds ((α₀, 0) : ℝ × (ℝ × ℝ)), |fderiv ℝ (Φ p.1) p.2 (0, 1)| < q₀ / 2 ∧
      |dd (Φ p.1) p.2 (0, 1) (0, 1) - dd (Φ α₀) 0 (0, 1) (0, 1)| < 1 := by
    filter_upwards [ImplicitAux.eventually_abs_sub_lt
        (a5uB_contDiff_fderiv hΦ (0, 1)).continuous.continuousAt (half_pos hq₀),
      ImplicitAux.eventually_abs_sub_lt (a5uB_contDiff_dd hΦ (0, 1) (0, 1)).continuous.continuousAt
        one_pos] with p h1 h2
    exact ⟨by simpa [h0] using h1, h2⟩
  obtain ⟨r, hr, H⟩ := a5uB_box ev
  refine ⟨r, hr, |dd (Φ α₀) 0 (0, 1) (0, 1)| + 1, fun α hα k hk => ?_⟩
  obtain ⟨h1, h2⟩ := H α k.1 k.2 hα (abs_le.mpr ⟨hk.1.1, hk.1.2⟩) (abs_le.mpr ⟨hk.2.1, hk.2.2⟩)
  refine ⟨h1.le, ?_⟩
  have := abs_sub_abs_le_abs_sub (dd (Φ α) k (0, 1) (0, 1)) (dd (Φ α₀) 0 (0, 1) (0, 1))
  linarith

/-- Far tilts in the chart: one integration by parts in the transverse variable. -/
theorem a5uB_farBound {F : ℝ × ℝ → ℝ} (hF2 : ContDiff ℝ 2 F) {q₀ r D' C₄ : ℝ}
    (hfar : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, |fderiv ℝ F k (0, 1)| ≤ q₀ / 2 ∧ |dd F k (0, 1) (0, 1)| ≤ D')
    (hC₄ : ∀ (Φ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m : ℝ), ContDiff ℝ 2 Φ →
      (∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D') →
      AmpBound 1 (Icc (-r) r ×ˢ Icc (-r) r) A M → 1 ≤ m → ‖oscInt2 (fun k => m * Φ k) A‖ ≤ C₄ * M / m)
    {A' : ℝ × ℝ → ℂ} {M' p q t : ℝ} (hA' : AmpBound 2 (Icc (-r) r ×ˢ Icc (-r) r) A' M') (ht : 1 ≤ t)
    (hqs : q₀ < |q|) :
    ‖oscInt2 (fun k => t * ((F k + q * k.2) + p * k.1)) A'‖ ≤ C₄ * M' / t := by
  let Φ : ℝ × ℝ → ℝ := fun k => F k + lin (p, q) k
  have hΦeq : (fun k => t * ((F k + q * k.2) + p * k.1)) = fun k => t * Φ k := by
    funext k; simp only [Φ, lin]; ring
  have hΦ2 : ContDiff ℝ 2 Φ := hF2.add (FamilyAux.contDiff_lin _)
  have hgrad : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r,
      q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D' := by
    intro k hk
    have hd : fderiv ℝ Φ k (0, 1) = fderiv ℝ F k (0, 1) + q := by
      simpa using fderiv_add_lin (hF2.differentiable (by norm_num)) (p, q) k (0, 1)
    refine ⟨?_, ?_⟩
    · rw [hd]
      have := (hfar k hk).1
      have h1 : |q| - |fderiv ℝ F k (0, 1)| ≤ |fderiv ℝ F k (0, 1) + q| := by
        have := abs_sub_abs_le_abs_sub q (-(fderiv ℝ F k (0, 1)))
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        exact this
      linarith
    · rw [show Φ = fun k => F k + lin (p, q) k from rfl, dd_add_lin hF2 (p, q)]
      exact (hfar k hk).2
  have hAb : AmpBound 1 (Icc (-r) r ×ˢ Icc (-r) r) A' M' :=
    ⟨hA'.1.of_le (by norm_num), hA'.2.1, fun j hj => hA'.2.2 j (hj.trans (by norm_num))⟩
  rw [hΦeq]
  exact hC₄ Φ A' M' t hΦ2 hgrad hAb ht

/-- The bound in the chart for one member `F` of the family, near and far tilts (the `hmain` step of K2-L). -/
theorem a5uB_chartBound {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {m : ℕ} (hm : 2 ≤ m)
    {q₀ a b μ ν D r D' C₂ C₄ : ℝ} {ys : ℝ → ℝ → ℝ}
    (hys : ∀ q : ℝ, |q| ≤ q₀ → CoreHypsM m a b μ ν D (fun k => F k + q * k.2) (ys q))
    (hC₂ : ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M t p : ℝ),
      CoreHypsM m a b μ ν D Q ys → AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (Q k + p * k.1)) A‖ ≤ C₂ * M * t ^ (-(1 / 2 + 1 / (m : ℝ))))
    (hfar : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, |fderiv ℝ F k (0, 1)| ≤ q₀ / 2 ∧ |dd F k (0, 1) (0, 1)| ≤ D')
    (hC₄ : ∀ (Φ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m : ℝ), ContDiff ℝ 2 Φ →
      (∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D') →
      AmpBound 1 (Icc (-r) r ×ˢ Icc (-r) r) A M → 1 ≤ m → ‖oscInt2 (fun k => m * Φ k) A‖ ≤ C₄ * M / m)
    {A' : ℝ × ℝ → ℂ} {M' : ℝ}
    (hA' : AmpBound 2 (Icc (-min (min a b) r) (min (min a b) r) ×ˢ
      Icc (-min (min a b) r) (min (min a b) r)) A' M') (p q t : ℝ) (ht : 1 ≤ t) :
    ‖oscInt2 (fun k => t * ((F k + q * k.2) + p * k.1)) A'‖ ≤
      max (max C₂ 0) (max C₄ 0) * M' * t ^ (-(1 / 2 + 1 / (m : ℝ))) := by
  have hM' : 0 ≤ M' := (norm_nonneg _).trans (hA'.2.2 0 (by norm_num) 0)
  have ht0 : 0 < t := by linarith
  set e : ℝ := -(1 / 2 + 1 / (m : ℝ)) with he
  have htpos : 0 < t ^ e := Real.rpow_pos_of_pos ht0 _
  set s := min (min a b) r with hsdef
  by_cases hqs : |q| ≤ q₀
  · have hAb : AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A' M' :=
      LocalCritAux.ampBound_mono hA' (prod_mono
        (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))
        (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef])))
    refine (hC₂ (fun k => F k + q * k.2) (ys q) A' M' t p (hys q hqs) hAb ht).trans ?_
    gcongr
    exact (le_max_left _ _).trans (le_max_left _ _)
  · push Not at hqs
    have hsr : s ≤ r := min_le_right _ _
    have hA2 : AmpBound 2 (Icc (-r) r ×ˢ Icc (-r) r) A' M' := LocalCritAux.ampBound_mono hA' (prod_mono
      (Icc_subset_Icc (neg_le_neg hsr) hsr) (Icc_subset_Icc (neg_le_neg hsr) hsr))
    refine (a5uB_farBound (hF.of_le (by simp)) hfar hC₄ hA2 ht hqs).trans ?_
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hexp : (-1 : ℝ) ≤ e := by
      rw [he]
      have : 1 / (m : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have h1 : 1 / t ≤ t ^ e := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le ht hexp
    calc C₄ * M' / t ≤ max C₄ 0 * M' / t := by gcongr; exact le_max_left _ _
      _ = max C₄ 0 * M' * (1 / t) := by ring
      _ ≤ max C₄ 0 * M' * t ^ e := by gcongr
      _ ≤ max (max C₂ 0) (max C₄ 0) * M' * t ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM') htpos.le

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.StationaryPhase
open OscInt.Cusp.AssemblyAux OscInt.K2.LocalAux
open scoped ContDiff

/-- **B1** K2-L uniformly in a parameter. -/
theorem reducedOrderBoundParam : OscInt.Blueprint.A5U.ReducedOrderBoundParamFacts := by
  intro Ψ α₀ k₀ v w ε h m hΨ hm hspan hww hε hh hdm
  have hΨ' : ContDiff ℝ ∞ (Function.uncurry Ψ) := hΨ
  have hΨα : ∀ α, ContDiff ℝ ∞ (Ψ α) := fun α => hΨ'.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨L, -, hNP⟩ := OscInt.K2.chart (Ψ α₀) k₀ v w ε h m (hΨα α₀) (by omega) hspan hww hε hh hdm
  set Φ : ℝ → ℝ × ℝ → ℝ := fun α k => Ψ α (k₀ + L k) - Ψ α k₀ - fderiv ℝ (Ψ α) k₀ (L k) with hΦdef
  have hΦ : ContDiff ℝ ∞ (Function.uncurry Φ) := a5uB_family_smooth hΨ' k₀ L
  obtain ⟨ρ₁, hρ₁, q₀, hq₀, a, b, μ, ν, D, ha, hb, hμ, hν, ys, hys⟩ := a5uB_paramData hΦ hm hNP
  obtain ⟨C₂, hC₂⟩ := OscInt.K2.coreEstimateM m hm a b μ ν D ha hb hμ hν
  obtain ⟨r, hr, D', hfar⟩ := a5uB_farData hΦ hNP.2.1 hq₀
  obtain ⟨C₄, hC₄⟩ := OscInt.Cusp.transverseNonStat r r (q₀ / 2) D' hr hr (by positivity)
  set s := min (min a b) r with hsdef
  have hs : 0 < s := lt_min (lt_min ha hb) hr
  set nL := ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  refine ⟨s / (nL + 1), by positivity, min ρ₁ r, lt_min hρ₁ hr,
    |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * max (max C₂ 0) (max C₄ 0) *
      max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2, ?_⟩
  intro α hα A M y t hA ht
  have ht0 : 0 < t := by linarith
  have hsub : (fun k => k₀ + L k) ⁻¹' Metric.closedBall k₀ (s / (nL + 1)) ⊆
      Icc (-s) s ×ˢ Icc (-s) s :=
    LocalCritAux.preimage_ball_subset_box L k₀ (a := s) (b := s) (δ := s / (nL + 1))
      (by positivity) (by rw [div_mul_cancel₀ _ (by positivity), min_self])
  have hA' := LocalCritAux.ampBound_mono (ampBoundAffine 2 _ A M k₀ L hA) hsub
  set p := fderiv ℝ (Ψ α) k₀ (L (1, 0)) + lin y (L (1, 0)) / t
  set q := fderiv ℝ (Ψ α) k₀ (L (0, 1)) + lin y (L (0, 1)) / t
  have hphase : (fun k => t * Ψ α (k₀ + L k) + lin y (k₀ + L k)) =
      fun k => (t * Ψ α k₀ + lin y k₀) + t * ((Φ α k + q * k.2) + p * k.1) := by
    funext k; exact phase_eq_at (Ψ α) k₀ L y ht0.ne' k
  rw [affineChange (fun κ => t * Ψ α κ + lin y κ) A k₀ L, norm_mul, hphase, norm_oscInt2_const_add]
  have hdet : ‖((|LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| : ℝ) : ℂ)‖ =
      |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [hdet]
  have hmain := a5uB_chartBound (F := Φ α) (hΦ.comp (contDiff_const.prodMk contDiff_id)) hm (fun q hq => hys α (hα.trans (min_le_left _ _)) q hq) hC₂
    (hfar α (hα.trans (min_le_right _ _))) hC₄ hA' p q t ht
  calc |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * ‖oscInt2 (fun k => t * ((Φ α k + q * k.2) + p * k.1))
        (fun k => A (k₀ + L k))‖
      ≤ |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * (max (max C₂ 0) (max C₄ 0) *
        (max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 * M) * t ^ (-(1 / 2 + 1 / (m : ℝ)))) := by gcongr
    _ = _ := by ring

end OscInt.A5UAux
