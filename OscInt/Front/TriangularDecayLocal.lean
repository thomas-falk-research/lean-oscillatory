/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Cusp.Assembly

/-!
# Batch K2: the local bound of order m (K2-L) assembled against the blueprint interfaces

Route `docs/proof-K2.md`, section 1 and section 8 (N1). A clone of `OscInt.Cusp.cuspBoundGen_of` at a base point `k₀`
and order m: the chart of P3, the normalised data of P2 for `|q| ≤ q₀`, the core estimate P1, and for `|q| > q₀` one
integration by parts in the transverse variable (`TransverseNonStatFacts`, proved as `OscInt.Cusp.transverseNonStat`).
-/

namespace OscInt.K2.LocalAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase OscInt.Cusp.AssemblyAux
open scoped ContDiff

/-- The phase after `κ = k₀ + L k`: a constant plus `t (F + q y + p x)` with `F` the phase minus its tangent plane. -/
theorem phase_eq_at (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ) {t : ℝ} (ht : t ≠ 0)
    (k : ℝ × ℝ) :
    t * Ψ (k₀ + L k) + lin y (k₀ + L k) =
      (t * Ψ k₀ + lin y k₀) + t * (((Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k)) +
        (fderiv ℝ Ψ k₀ (L (0, 1)) + lin y (L (0, 1)) / t) * k.2) +
        (fderiv ℝ Ψ k₀ (L (1, 0)) + lin y (L (1, 0)) / t) * k.1) := by
  have h1 := clm_apply_coords ((fderiv ℝ Ψ k₀).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) k
  have h2 := clm_apply_coords ((linCLM y).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) k
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    linCLM_apply] at h1 h2
  have hlin : lin y (k₀ + L k) = lin y k₀ + lin y (L k) := by simp only [lin, Prod.fst_add, Prod.snd_add]; ring
  rw [hlin, h2, h1]
  field_simp
  ring

end OscInt.K2.LocalAux

namespace OscInt.K2

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.StationaryPhase
open OscInt.Cusp.AssemblyAux LocalAux
open scoped ContDiff

/-- **K2-L** from P1, P2, P3 and the transverse non-stationary estimate. -/
theorem reducedOrderBound_of (hCE : CoreEstimateMFacts) (hND : NormalizedDataMFacts) (hCh : ChartFacts)
    (hNS : TransverseNonStatFacts) : ReducedOrderBoundStatement := by
  intro Ψ k₀ v w ε h m hΨ hm hspan hww hε hh hdm
  obtain ⟨L, hLdef, hNP⟩ := hCh Ψ k₀ v w ε h m hΨ (by omega) hspan hww hε hh hdm
  set F : ℝ × ℝ → ℝ := fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k) with hFdef
  have hF : ContDiff ℝ ∞ F := hNP.1
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  obtain ⟨q₀, hq₀, a, b, μ, ν, D, ha, hb, hμ, hν, ys, hys⟩ := hND m F ε h hm hNP
  obtain ⟨C₂, hC₂⟩ := hCE m hm a b μ ν D ha hb hμ hν
  -- the transverse derivative is small near `0`
  have hFy0 : fderiv ℝ F 0 (0, 1) = 0 := hNP.2.1
  have hcontFy : Continuous (fun k => fderiv ℝ F k (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨r₀, hr₀, hr₀b⟩ := Metric.continuousAt_iff.mp hcontFy.continuousAt (q₀ / 2) (by positivity)
  set r := r₀ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hFy : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, |fderiv ℝ F k (0, 1)| ≤ q₀ / 2 := by
    intro k hk
    have hk' : dist k 0 < r₀ := by
      rw [dist_zero_right]
      have h1 : |k.1| ≤ r := abs_le.mpr ⟨hk.1.1, hk.1.2⟩
      have h2 : |k.2| ≤ r := abs_le.mpr ⟨hk.2.1, hk.2.2⟩
      calc ‖k‖ = max ‖k.1‖ ‖k.2‖ := rfl
        _ ≤ r := max_le (by simpa using h1) (by simpa using h2)
        _ < r₀ := by rw [hrdef]; linarith
    have := hr₀b hk'
    rw [Real.dist_eq, hFy0, sub_zero] at this
    exact this.le
  have hbox : IsCompact (Icc (-r) r ×ˢ Icc (-r) r) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D', hD'⟩ := hbox.exists_bound_of_continuousOn (f := fun k => dd F k (0, 1) (0, 1))
    ((ImplicitAux.contDiff_dd (n := 0) (by exact_mod_cast hF2) (0, 1) (0, 1)).continuous.continuousOn)
  obtain ⟨C₄, hC₄⟩ := hNS r r (q₀ / 2) D' hr hr (by positivity)
  set s := min (min a b) r with hsdef
  have hs : 0 < s := lt_min (lt_min ha hb) hr
  set nL := ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  refine ⟨s / (nL + 1), by positivity,
    |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * max (max C₂ 0) (max C₄ 0) *
      max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2, ?_⟩
  intro A M y t hA ht
  have ht0 : 0 < t := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (by norm_num) 0)
  have hsub : (fun k => k₀ + L k) ⁻¹' Metric.closedBall k₀ (s / (nL + 1)) ⊆
      Icc (-s) s ×ˢ Icc (-s) s :=
    LocalCritAux.preimage_ball_subset_box L k₀ (a := s) (b := s) (δ := s / (nL + 1))
      (by positivity) (by rw [div_mul_cancel₀ _ (by positivity), min_self])
  set M' := max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 * M
  have hA' := ampBoundAffine 2 _ A M k₀ L hA
  set A' : ℝ × ℝ → ℂ := fun k => A (k₀ + L k)
  set p := fderiv ℝ Ψ k₀ (L (1, 0)) + lin y (L (1, 0)) / t
  set q := fderiv ℝ Ψ k₀ (L (0, 1)) + lin y (L (0, 1)) / t
  have hchange := affineChange (fun κ => t * Ψ κ + lin y κ) A k₀ L
  have hphase : (fun k => t * Ψ (k₀ + L k) + lin y (k₀ + L k)) =
      fun k => (t * Ψ k₀ + lin y k₀) + t * ((F k + q * k.2) + p * k.1) := by
    funext k; exact phase_eq_at Ψ k₀ L y ht0.ne' k
  rw [hchange, norm_mul, hphase, norm_oscInt2_const_add]
  have hdet : ‖((|LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| : ℝ) : ℂ)‖ =
      |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [hdet]
  set e : ℝ := -(1 / 2 + 1 / (m : ℝ)) with he
  have htpos : 0 < t ^ e := Real.rpow_pos_of_pos ht0 _
  have hmain : ‖oscInt2 (fun k => t * ((F k + q * k.2) + p * k.1)) A'‖ ≤
      max (max C₂ 0) (max C₄ 0) * M' * t ^ e := by
    have hM' : 0 ≤ M' := by positivity
    by_cases hqs : |q| ≤ q₀
    · -- near: the core estimate of order m
      have hAb : AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A' M' :=
        LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
          (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))
          (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))))
      refine (hC₂ (fun k => F k + q * k.2) (ys q) A' M' t p (hys q hqs) hAb ht).trans ?_
      gcongr
      exact (le_max_left _ _).trans (le_max_left _ _)
    · -- far: one integration by parts in the second variable
      push Not at hqs
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
          have := hFy k hk
          have h1 : |q| - |fderiv ℝ F k (0, 1)| ≤ |fderiv ℝ F k (0, 1) + q| := by
            have := abs_sub_abs_le_abs_sub q (-(fderiv ℝ F k (0, 1)))
            rw [abs_neg, sub_neg_eq_add, add_comm] at this
            exact this
          linarith
        · rw [show Φ = fun k => F k + lin (p, q) k from rfl, dd_add_lin hF2 (p, q)]
          simpa [Real.norm_eq_abs] using hD' k hk
      have hAb : AmpBound 1 (Icc (-r) r ×ˢ Icc (-r) r) A' M' := by
        have hsr : s ≤ r := min_le_right _ _
        have h2 := LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
          (Icc_subset_Icc (neg_le_neg hsr) hsr) (Icc_subset_Icc (neg_le_neg hsr) hsr)))
        exact ⟨h2.1.of_le (by norm_num), h2.2.1, fun j hj => h2.2.2 j (hj.trans (by norm_num))⟩
      rw [hΦeq]
      refine (hC₄ Φ A' M' t hΦ2 hgrad hAb ht).trans ?_
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
  calc |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * ‖oscInt2 (fun k => t * ((F k + q * k.2) + p * k.1)) A'‖
      ≤ |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * (max (max C₂ 0) (max C₄ 0) * M' * t ^ e) := by gcongr
    _ = _ := by simp only [M']; ring

end OscInt.K2
