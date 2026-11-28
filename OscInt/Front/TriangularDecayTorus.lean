/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay

/-!
# Batch K2, part P14: the torus expansion (`TorusExpansionFacts`)

Route: `docs/proof-K2.md`, section 8, item 2 (finding M2 of route referee R).

The function `a = χ e^{iδ·k}` vanishes outside the compact set `tsupport χ ⊆ (−π, π)²`, so
`G y = a (2π rep (y 0), 2π rep (y 1))`, with `rep` the representative in `[−1/2, 1/2)`, is continuous on the
unit torus `UnitAddTorus (Fin 2)`. Its Fourier coefficients are `(4π²)⁻¹ c_j(δ)` (rescaling 2π ↦ 1 and
`mFourierCoeff_eq_integral`), so the summability hypothesis gives pointwise convergence of the Fourier series
(`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`) on the box; multiplying by the continuous g and
integrating term by term (`hasSum_integral_of_summable_integral_norm`) gives the identity.
-/

namespace OscInt.K2.TorusExpansionAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint
open scoped ContDiff

/-- The representative in `[−1/2, 1/2)` of a point of the unit circle. -/
noncomputable def rep (y : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) (-1 / 2) y : ℝ)

lemma rep_mem (y : UnitAddCircle) : rep y ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  obtain ⟨h1, h2⟩ := (AddCircle.equivIco (1 : ℝ) (-1 / 2) y).2
  exact ⟨h1, by unfold rep; linarith⟩

lemma coe_rep (y : UnitAddCircle) : ((rep y : ℝ) : UnitAddCircle) = y := AddCircle.coe_equivIco

lemma rep_coe {s : ℝ} (hs : s ∈ Ico (-1 / 2 : ℝ) (1 / 2)) : rep (s : UnitAddCircle) = s := by
  have e : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  exact AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -1 / 2) (by rw [e]; exact hs)

lemma rep_half : rep ((1 / 2 : ℝ) : UnitAddCircle) = -1 / 2 := by
  have h := AddCircle.coe_add_period (1 : ℝ) (-1 / 2 : ℝ)
  have e : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e] at h
  rw [h]
  exact rep_coe (by norm_num)

lemma rep_cases {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    rep (s : UnitAddCircle) = s ∨ (s = 1 / 2 ∧ rep (s : UnitAddCircle) = -1 / 2) := by
  rcases eq_or_lt_of_le hs.2 with h | h
  · right
    subst h
    exact ⟨rfl, rep_half⟩
  · left
    exact rep_coe ⟨hs.1, h⟩

/-- The amplitude `χ e^{iδ·k}`. -/
noncomputable def amp (χ : ℝ × ℝ → ℂ) (δ : ℝ × ℝ) (k : ℝ × ℝ) : ℂ :=
  χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I)

/-- The lift of the amplitude to the unit torus. -/
noncomputable def lift (χ : ℝ × ℝ → ℂ) (δ : ℝ × ℝ) (y : UnitAddTorus (Fin 2)) : ℂ :=
  amp χ δ (2 * Real.pi * rep (y 0), 2 * Real.pi * rep (y 1))

/-- A margin: the amplitude vanishes where a coordinate exceeds some `r < π` in absolute value. -/
lemma exists_margin (χ : ℝ × ℝ → ℂ)
    (hsupp : tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi) (δ : ℝ × ℝ) :
    ∃ r : ℝ, r < Real.pi ∧ ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0 := by
  have hK : IsCompact (tsupport χ) :=
    IsCompact.of_isClosed_subset ((isCompact_Icc (a := -Real.pi) (b := Real.pi)).prod isCompact_Icc)
      (isClosed_tsupport _) (hsupp.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
  by_cases hne : (tsupport χ).Nonempty
  · obtain ⟨k, hk, hmax⟩ := hK.exists_isMaxOn hne (f := fun p : ℝ × ℝ => ‖p‖) continuous_norm.continuousOn
    refine ⟨‖k‖, ?_, ?_⟩
    · have h := hsupp hk
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt (abs_lt.2 h.1) (abs_lt.2 h.2)
    · intro p hp
      have hpK : p ∉ tsupport χ := by
        intro hpK
        have h1 : ‖p‖ ≤ ‖k‖ := hmax hpK
        have h2 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
        have h3 : |p.2| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_snd_le p
        rcases hp with hp | hp <;> linarith
      simp [amp, image_eq_zero_of_notMem_tsupport hpK]
  · refine ⟨0, Real.pi_pos, fun p _ => ?_⟩
    have hpK : p ∉ tsupport χ := fun h => hne ⟨p, h⟩
    simp [amp, image_eq_zero_of_notMem_tsupport hpK]

section

variable {χ : ℝ × ℝ → ℂ} {δ : ℝ × ℝ} {r : ℝ}

lemma lift_zero (hr : ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0) (y : UnitAddTorus (Fin 2))
    (i : Fin 2) (hy : y i ∉ (fun s : ℝ => (s : UnitAddCircle)) '' Icc (-(r / (2 * Real.pi))) (r / (2 * Real.pi))) :
    lift χ δ y = 0 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hlt : r / (2 * Real.pi) < |rep (y i)| := by
    by_contra hle
    have hle := not_lt.1 hle
    exact hy ⟨rep (y i), abs_le.1 hle, coe_rep _⟩
  have hlt' : r < |2 * Real.pi * rep (y i)| := by
    rw [abs_mul, abs_of_pos hpi]
    rw [div_lt_iff₀ hpi] at hlt
    linarith
  apply hr
  fin_cases i
  · exact Or.inl hlt'
  · exact Or.inr hlt'

lemma continuous_lift (hχ : Continuous χ) (hrπ : r < Real.pi)
    (hr : ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0) : Continuous (lift χ δ) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  set c := r / (2 * Real.pi) with hc
  have hc2 : c < 1 / 2 := by
    rw [hc, div_lt_iff₀ hpi]; linarith
  set C := (fun s : ℝ => (s : UnitAddCircle)) '' Icc (-c) c with hC
  have hCc : IsClosed C := ((isCompact_Icc).image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hamp : Continuous (amp χ δ) := by
    unfold amp; fun_prop
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ∃ i, x i ∉ C
  · obtain ⟨i, hi⟩ := hx
    have hU : (fun y : UnitAddTorus (Fin 2) => y i) ⁻¹' Cᶜ ∈ nhds x :=
      (hCc.isOpen_compl.preimage (continuous_apply i)).mem_nhds hi
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hU] with y hy
    exact (lift_zero hr y i hy).symm
  · simp only [not_exists, not_not] at hx
    have hne : ∀ i, x i ≠ ((-1 / 2 : ℝ) : UnitAddCircle) := by
      intro i h
      obtain ⟨s, hs, hs'⟩ := hx i
      rw [h] at hs'
      change ((s : ℝ) : UnitAddCircle) = _ at hs'
      have h1 : rep (s : UnitAddCircle) = s := rep_coe ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h2 : rep ((-1 / 2 : ℝ) : UnitAddCircle) = -1 / 2 := rep_coe (by norm_num)
      rw [hs'] at h1
      linarith [hs.1]
    have hrep : ∀ i, ContinuousAt (fun y : UnitAddTorus (Fin 2) => rep (y i)) x := by
      intro i
      have h : ContinuousAt (fun y : UnitAddTorus (Fin 2) => AddCircle.equivIco (1 : ℝ) (-1 / 2) (y i)) x :=
        (AddCircle.continuousAt_equivIco (1 : ℝ) (-1 / 2) (hne i)).comp
          (f := fun y : UnitAddTorus (Fin 2) => y i) (continuous_apply i).continuousAt
      exact continuous_subtype_val.continuousAt.comp h
    exact hamp.continuousAt.comp (((continuousAt_const.mul (hrep 0))).prodMk (continuousAt_const.mul (hrep 1)))

end

lemma div_mem_Icc {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi) :
    t / (2 * Real.pi) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  constructor
  · rw [le_div_iff₀ hpi]; linarith [ht.1]
  · rw [div_le_iff₀ hpi]; linarith [ht.2]

lemma div_mem_Ioc {t : ℝ} (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    t / (2 * Real.pi) ∈ Ioc (-1 / 2 : ℝ) (1 / 2) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  constructor
  · rw [lt_div_iff₀ hpi]; linarith [ht.1]
  · rw [div_le_iff₀ hpi]; linarith [ht.2]

lemma mFourier_eval (n : Fin 2 → ℤ) (v : Fin 2 → ℝ) :
    UnitAddTorus.mFourier n (fun i => (v i : UnitAddCircle)) =
      Complex.exp (↑(2 * Real.pi * ((n 0 : ℝ) * v 0 + (n 1 : ℝ) * v 1)) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two, fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier coefficients `c_j(δ)` of the blueprint. -/
noncomputable def coef (χ : ℝ × ℝ → ℂ) (δ : ℝ × ℝ) (j : ℤ × ℤ) : ℂ :=
  ∫ k in torusBox, χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)

section

variable {χ : ℝ × ℝ → ℂ} {δ : ℝ × ℝ} {r : ℝ}

lemma lift_coe (hrπ : r < Real.pi) (hr : ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0)
    (v : Fin 2 → ℝ) (h0 : v 0 ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (h1 : v 1 ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    lift χ δ (fun i => (v i : UnitAddCircle)) = amp χ δ (2 * Real.pi * v 0, 2 * Real.pi * v 1) := by
  have e1 : |2 * Real.pi * (1 / 2)| = Real.pi := by
    rw [abs_of_pos (by positivity)]; ring
  have e2 : |2 * Real.pi * (-1 / 2)| = Real.pi := by
    rw [abs_of_neg (by linarith [Real.pi_pos])]; ring
  unfold lift
  dsimp only
  rcases rep_cases h0 with ha | ⟨ha, ha'⟩ <;> rcases rep_cases h1 with hb | ⟨hb, hb'⟩
  · rw [ha, hb]
  · rw [hr _ (Or.inr (by rw [hb']; linarith)), hr _ (Or.inr (by rw [hb]; linarith))]
  · rw [hr _ (Or.inl (by rw [ha']; linarith)), hr _ (Or.inl (by rw [ha]; linarith))]
  · rw [hr _ (Or.inl (by rw [ha']; linarith)), hr _ (Or.inl (by rw [ha]; linarith))]

lemma amp_vanish (hsupp : tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi) (j : ℤ × ℤ)
    (k : ℝ × ℝ) (hk : k ∉ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi) :
    χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I) = 0 := by
  rw [image_eq_zero_of_notMem_tsupport (fun h => hk (hsupp h)), zero_mul]

lemma mFourierCoeff_lift (hsupp : tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi)
    (hrπ : r < Real.pi) (hr : ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0) (j : ℤ × ℤ) :
    UnitAddTorus.mFourierCoeff (lift χ δ) ![j.1, j.2] = ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * coef χ δ j := by
  have hpi : 0 < 2 * Real.pi := by positivity
  set h : ℝ × ℝ → ℂ :=
    fun k => χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I) with hh
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => (-1 / 2 : ℝ))]
  have hS : {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin 2 => (-1 / 2 : ℝ)) i)
      ((fun _ : Fin 2 => (-1 / 2 : ℝ)) i + 1)} =
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
        (Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2)) := by
    ext x
    simp only [mem_ofPred_eq, Fin.forall_fin_two, mem_preimage, MeasurableEquiv.finTwoArrow_apply, mem_prod]
    norm_num
  rw [hS, setIntegral_congr_fun (MeasurableEquiv.finTwoArrow.measurable
      (measurableSet_Ioc.prod measurableSet_Ioc))
      (g := fun x => h ((2 * Real.pi) • (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) x)) ?_]
  · rw [(volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
      MeasurableEquiv.finTwoArrow.measurableEmbedding (fun y => h ((2 * Real.pi) • y)),
      Measure.setIntegral_comp_smul_of_pos _ _ _ hpi,
      setIntegral_eq_integral_of_forall_compl_eq_zero ?_, coef,
      setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · simp only [Module.finrank_prod, Module.finrank_self]
      rw [Complex.real_smul]
      congr 1
      push_cast
      ring
    · intro k hk
      apply amp_vanish hsupp j k
      intro hk'
      exact hk ⟨Ioo_subset_Icc_self hk'.1, Ioo_subset_Icc_self hk'.2⟩
    · intro k hk
      apply amp_vanish hsupp j k
      intro hk'
      apply hk
      rw [mem_smul_set_iff_inv_smul_mem₀ hpi.ne']
      have e1 := div_mem_Ioc hk'.1
      have e2 := div_mem_Ioc hk'.2
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mem_prod]
      rw [inv_mul_eq_div, inv_mul_eq_div]
      exact ⟨e1, e2⟩
  · intro x hx
    simp only [mem_preimage, MeasurableEquiv.finTwoArrow_apply, mem_prod] at hx
    dsimp only
    rw [mFourier_eval, lift_coe hrπ hr x (Ioc_subset_Icc_self hx.1) (Ioc_subset_Icc_self hx.2)]
    simp only [hh, amp, smul_eq_mul, MeasurableEquiv.finTwoArrow_apply, Prod.smul_mk, Pi.neg_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 3
    push_cast
    ring

end

/-- Pointwise Fourier inversion on the box. -/
lemma hasSum_amp {χ : ℝ × ℝ → ℂ} {δ : ℝ × ℝ} {r : ℝ} (hχ : Continuous χ)
    (hsupp : tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi)
    (hrπ : r < Real.pi) (hr : ∀ p : ℝ × ℝ, r < |p.1| ∨ r < |p.2| → amp χ δ p = 0)
    (hc : Summable fun j : ℤ × ℤ => ‖coef χ δ j‖) {k : ℝ × ℝ} (hk : k ∈ torusBox) :
    HasSum (fun j : ℤ × ℤ => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * coef χ δ j *
      Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I)) (amp χ δ k) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let F : C(UnitAddTorus (Fin 2), ℂ) := ⟨lift χ δ, continuous_lift hχ hrπ hr⟩
  have hcoef : ∀ j : ℤ × ℤ, UnitAddTorus.mFourierCoeff F ((finTwoArrowEquiv ℤ).symm j) =
      ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * coef χ δ j := fun j => by
    rw [finTwoArrowEquiv_symm_apply]
    exact mFourierCoeff_lift hsupp hrπ hr j
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    rw [← (finTwoArrowEquiv ℤ).symm.summable_iff]
    have e : (UnitAddTorus.mFourierCoeff F ∘ (finTwoArrowEquiv ℤ).symm) =
        fun j => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * coef χ δ j := funext hcoef
    rw [e]
    exact (Summable.of_norm hc).mul_left _
  let v : Fin 2 → ℝ := ![k.1 / (2 * Real.pi), k.2 / (2 * Real.pi)]
  have H := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum (fun i => (v i : UnitAddCircle))
  rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at H
  have hv : F (fun i => (v i : UnitAddCircle)) = amp χ δ k := by
    change lift χ δ (fun i => (v i : UnitAddCircle)) = amp χ δ k
    rw [lift_coe hrπ hr v (div_mem_Icc hk.1) (div_mem_Icc hk.2)]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  rw [hv] at H
  convert H using 1
  funext j
  simp only [Function.comp_apply, hcoef, smul_eq_mul, mFourier_eval]
  congr 3
  simp only [finTwoArrowEquiv_symm_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

end OscInt.K2.TorusExpansionAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.K2.TorusExpansionAux in
/-- **P14** (batch K2): the torus expansion. -/
theorem OscInt.K2.torusExpansion : OscInt.Blueprint.K2.TorusExpansionFacts := by
  intro χ hχ hsupp δ hc g hg
  obtain ⟨r, hrπ, hr⟩ := exists_margin χ hsupp δ
  have hbox : IsCompact torusBox := isCompact_Icc.prod isCompact_Icc
  have hc' : Summable fun j : ℤ × ℤ => ‖coef χ δ j‖ := hc
  set F : ℤ × ℤ → ℝ × ℝ → ℂ := fun j k => (((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * coef χ δ j) *
    (Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k) with hF
  have hint : ∀ j, Integrable (F j) (volume.restrict torusBox) := by
    intro j
    have : Continuous (F j) := by
      simp only [hF]
      fun_prop
    exact this.continuousOn.integrableOn_compact hbox
  have hnorm : ∀ j, ∫ k in torusBox, ‖F j k‖ =
      ‖((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ)‖ * ‖coef χ δ j‖ * ∫ k in torusBox, ‖g k‖ := by
    intro j
    simp only [hF, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact integral_const_mul _ _
  have hsum : Summable fun j => ∫ k in torusBox, ‖F j k‖ := by
    simp_rw [hnorm]
    exact (hc'.mul_left _).mul_right _
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  have hlim : ∫ k in torusBox, ∑' j, F j k =
      ∫ k in torusBox, χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) * g k := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro k hk
    have := (hasSum_amp hχ.continuous hsupp hrπ hr hc' hk).mul_right (g k)
    simp only [hF, ← mul_assoc]
    exact this.tsum_eq
  rw [hlim] at H
  convert H using 1
  funext j
  simp only [hF]
  rw [integral_const_mul]
  rfl

