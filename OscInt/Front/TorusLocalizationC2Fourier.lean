/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.TorusLocalizationC2
import OscInt.Front.TriangularDecayTorus

/-!
# Batch LOC2 (K2-FQ), parts Q2, Q3, Q4 and Q6: Bessel, the shell sum, the combination and the expansion

Route: `docs/proof-LOC2.md`.

* Q6 `locExpansion`: K2's torus expansion (P14), whose proof uses only continuity of χ and summability.
* Q3 `locShell`: `((1 + a² + b²)²)⁻¹ ≤ (1 + a²)⁻¹ (1 + b²)⁻¹`, and `Σ_{n ∈ ℤ} (1 + n²)⁻¹ ≤ 1 + 2 · 7/6 = 10/3` by
  telescoping `(1 + m²)⁻¹ ≤ (m − 1/2)⁻¹ − (m + 1/2)⁻¹` from `m = 2` on; `(10/3)² ≤ 13`.
* Q2 `locBessel`: Parseval on `UnitAddTorus (Fin 2)` (`hasSum_sq_mFourierCoeff`) for the bounded measurable lift
  `y ↦ g (2π x(y))`, `x(y) ∈ (−1/2, 1/2]²` the representative (`measurableEquivPiIoc`); the box `(−π, π]²` and
  `[−π, π]²` differ by a null set.
* Q4 `locCombine`: `|c_j| = (1 + |j|²)⁻¹ |ĝ_j|` and `8 X w a ≤ X² w² + 16 a²` with `X = 4π² ‖g‖`, so
  `Σ |c_j| ≤ (29/8) X ≤ 4 X`.
-/

namespace OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2

/-! ### Q3: the shell sum -/

/-- The weight `(1 + n²)⁻¹`. -/
noncomputable def loc2B_w (n : ℤ) : ℝ := (1 + (n : ℝ) ^ 2)⁻¹

lemma loc2B_w_nonneg (n : ℤ) : 0 ≤ loc2B_w n := by
  unfold loc2B_w; positivity

lemma loc2B_partial (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), loc2B_w ((i : ℤ) + 1) ≤ 7 / 6 - 1 / ((n : ℝ) + 3 / 2) := by
  induction n with
  | zero => norm_num [loc2B_w]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have key : loc2B_w (((m + 1 : ℕ) : ℤ) + 1) ≤
        1 / ((m : ℝ) + 3 / 2) - 1 / ((m : ℝ) + 1 + 3 / 2) := by
      unfold loc2B_w
      push_cast
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

lemma loc2B_partial_le (n : ℕ) : ∑ i ∈ Finset.range n, loc2B_w ((i : ℤ) + 1) ≤ 7 / 6 := by
  rcases n with _ | m
  · norm_num
  · have h := loc2B_partial m
    have : 0 < 1 / ((m : ℝ) + 3 / 2) := by positivity
    linarith

lemma loc2B_hasSum_w : ∃ a : ℝ, a ≤ 7 / 6 ∧ HasSum loc2B_w (a + 1 + a) := by
  have hnn : ∀ n : ℕ, 0 ≤ loc2B_w ((n : ℤ) + 1) := fun n => loc2B_w_nonneg _
  have hs := summable_of_sum_range_le hnn loc2B_partial_le
  refine ⟨∑' n : ℕ, loc2B_w ((n : ℤ) + 1), Real.tsum_le_of_sum_range_le hnn loc2B_partial_le, ?_⟩
  have h0 : loc2B_w 0 = 1 := by norm_num [loc2B_w]
  have hneg : (fun n : ℕ => loc2B_w (-((n : ℤ) + 1))) = fun n : ℕ => loc2B_w ((n : ℤ) + 1) := by
    funext n
    unfold loc2B_w
    push_cast
    ring
  have H := HasSum.of_add_one_of_neg_add_one hs.hasSum (by rw [hneg]; exact hs.hasSum)
  rwa [h0] at H

lemma loc2B_shell_le (j : ℤ × ℤ) :
    ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹ ≤ loc2B_w j.1 * loc2B_w j.2 := by
  unfold loc2B_w
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg ((j.1 : ℝ) ^ 2), sq_nonneg ((j.2 : ℝ) ^ 2), sq_nonneg ((j.1 : ℝ) * j.2)]

end OscInt.LOC2Aux

open OscInt.LOC2Aux in
/-- **Q3** The shell sum `Σ_{j ∈ ℤ²} (1 + |j|²)^{−2} ≤ 13`. -/
theorem OscInt.LOC2Aux.locShell : OscInt.Blueprint.LOC2.LocShellFacts := by
  obtain ⟨a, ha, H⟩ := loc2B_hasSum_w
  have hn : Summable fun n : ℤ => ‖loc2B_w n‖ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (loc2B_w_nonneg _)]
    exact H.summable
  have hP : Summable fun z : ℤ × ℤ => loc2B_w z.1 * loc2B_w z.2 := summable_mul_of_summable_norm hn hn
  have hnn : ∀ j : ℤ × ℤ, 0 ≤ ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹ := fun j => by positivity
  have hS := Summable.of_nonneg_of_le hnn loc2B_shell_le hP
  refine ⟨hS, ?_⟩
  have ha0 : 0 ≤ a + 1 + a := H.nonneg fun n => loc2B_w_nonneg n
  calc ∑' j : ℤ × ℤ, ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹
      ≤ ∑' z : ℤ × ℤ, loc2B_w z.1 * loc2B_w z.2 := hS.tsum_le_tsum loc2B_shell_le hP
    _ = (∑' n : ℤ, loc2B_w n) * ∑' n : ℤ, loc2B_w n := (tsum_mul_tsum_of_summable_norm hn hn).symm
    _ = (a + 1 + a) * (a + 1 + a) := by rw [H.tsum_eq]
    _ ≤ 13 := by nlinarith

open Set MeasureTheory OscInt.Statements OscInt.K2.TorusExpansionAux in
/-- **Q6** The torus expansion for a continuous cutoff (K2's P14 proof, which uses only continuity). -/
theorem OscInt.LOC2Aux.locExpansion : OscInt.Blueprint.LOC2.LocExpansionFacts := by
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
    have := (hasSum_amp hχ hsupp hrπ hr hc' hk).mul_right (g k)
    simp only [hF, ← mul_assoc]
    exact this.tsum_eq
  rw [hlim] at H
  convert H using 1
  funext j
  simp only [hF]
  rw [integral_const_mul]
  rfl

namespace OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2
open scoped Pointwise

/-! ### Q2: Bessel's inequality on the box -/

/-- The base point `(−1/2, −1/2)` of the fundamental domain `(−1/2, 1/2]²`. -/
noncomputable def loc2B_base : Fin 2 → ℝ := fun _ => -1 / 2

lemma loc2B_mem_Ioc (t : ℝ) :
    (2 * Real.pi)⁻¹ * t ∈ Ioc (-1 / 2 : ℝ) (1 / 2) ↔ t ∈ Ioc (-Real.pi) Real.pi := by
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div]
  simp only [mem_Ioc, lt_div_iff₀ hpi, div_le_iff₀ hpi]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma loc2B_smul_box :
    (2 * Real.pi) • (Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2)) =
      Ioc (-Real.pi) Real.pi ×ˢ Ioc (-Real.pi) Real.pi := by
  have hpi : 0 < 2 * Real.pi := by positivity
  ext k
  rw [mem_smul_set_iff_inv_smul_mem₀ hpi.ne']
  simp only [mem_prod, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, loc2B_mem_Ioc]

/-- Change of variables from the fundamental domain `(−1/2, 1/2]²` to the box. -/
lemma loc2B_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × ℝ → E) :
    ∫ x : Fin 2 → ℝ in {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc (loc2B_base i) (loc2B_base i + 1)},
      F (2 * Real.pi * x 0, 2 * Real.pi * x 1) = (4 * Real.pi ^ 2)⁻¹ • ∫ k in torusBox, F k := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hS : {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc (loc2B_base i) (loc2B_base i + 1)} =
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
        (Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2)) := by
    ext x
    simp only [loc2B_base, mem_ofPred_eq, Fin.forall_fin_two, mem_preimage,
      MeasurableEquiv.finTwoArrow_apply, mem_prod]
    norm_num
  have hae : (Ioc (-Real.pi) Real.pi ×ˢ Ioc (-Real.pi) Real.pi : Set (ℝ × ℝ)) =ᵐ[volume] torusBox := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioc_ae_eq_Icc
  calc ∫ x : Fin 2 → ℝ in {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc (loc2B_base i) (loc2B_base i + 1)},
        F (2 * Real.pi * x 0, 2 * Real.pi * x 1)
      = ∫ x : Fin 2 → ℝ in (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
          (Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2)),
          (fun y : ℝ × ℝ => F ((2 * Real.pi) • y)) (MeasurableEquiv.finTwoArrow x) := by
        rw [hS]; rfl
    _ = ∫ y in Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2), F ((2 * Real.pi) • y) :=
        (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
          MeasurableEquiv.finTwoArrow.measurableEmbedding (fun y : ℝ × ℝ => F ((2 * Real.pi) • y))
          (Ioc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioc (-1 / 2 : ℝ) (1 / 2))
    _ = ((2 * Real.pi) ^ 2)⁻¹ • ∫ k in Ioc (-Real.pi) Real.pi ×ˢ Ioc (-Real.pi) Real.pi, F k := by
        rw [Measure.setIntegral_comp_smul_of_pos _ _ _ hpi, loc2B_smul_box]
        simp only [Module.finrank_prod, Module.finrank_self]
    _ = (4 * Real.pi ^ 2)⁻¹ • ∫ k in torusBox, F k := by
        rw [setIntegral_congr_set hae]
        congr 2
        ring

/-- The lift of `g` to the unit torus through the representatives in `(−1/2, 1/2]²`. -/
noncomputable def loc2B_lift (g : ℝ × ℝ → ℂ) (y : UnitAddTorus (Fin 2)) : ℂ :=
  g (2 * Real.pi * (UnitAddTorus.measurableEquivPiIoc loc2B_base y).1 0,
    2 * Real.pi * (UnitAddTorus.measurableEquivPiIoc loc2B_base y).1 1)

lemma loc2B_lift_coe (g : ℝ × ℝ → ℂ) (x : Fin 2 → ℝ)
    (hx : x ∈ {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc (loc2B_base i) (loc2B_base i + 1)}) :
    loc2B_lift g (fun i => (x i : UnitAddCircle)) = g (2 * Real.pi * x 0, 2 * Real.pi * x 1) := by
  simp only [loc2B_lift, UnitAddTorus.coe_measurableEquivPiIoc_apply]
  rw [AddCircle.equivIoc_coe_of_mem (hx 0), AddCircle.equivIoc_coe_of_mem (hx 1)]

lemma loc2B_measurable_lift {g : ℝ × ℝ → ℂ} (hg : Continuous g) : Measurable (loc2B_lift g) := by
  have he : Measurable fun y : UnitAddTorus (Fin 2) =>
      ((UnitAddTorus.measurableEquivPiIoc loc2B_base y).1 : Fin 2 → ℝ) :=
    measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc loc2B_base).measurable
  exact hg.measurable.comp ((((measurable_pi_apply 0).comp he).const_mul _).prodMk
    (((measurable_pi_apply 1).comp he).const_mul _))

lemma loc2B_lift_mem (y : UnitAddTorus (Fin 2)) :
    (2 * Real.pi * (UnitAddTorus.measurableEquivPiIoc loc2B_base y).1 0,
      2 * Real.pi * (UnitAddTorus.measurableEquivPiIoc loc2B_base y).1 1) ∈ torusBox := by
  have key : ∀ u : ℝ, -1 / 2 < u → u ≤ -1 / 2 + 1 →
      -Real.pi ≤ 2 * Real.pi * u ∧ 2 * Real.pi * u ≤ Real.pi := by
    intro u a b
    constructor <;> nlinarith [Real.pi_pos]
  have h := (UnitAddTorus.measurableEquivPiIoc loc2B_base y).2
  exact ⟨key _ (h 0).1 (h 0).2, key _ (h 1).1 (h 1).2⟩

lemma loc2B_measurableSet :
    MeasurableSet {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc (loc2B_base i) (loc2B_base i + 1)} :=
  MeasurableSet.univ_pi' fun _ => measurableSet_Ioc

/-- The Fourier coefficients of the lift are the normalised box coefficients. -/
lemma loc2B_coeff (g : ℝ × ℝ → ℂ) (j : ℤ × ℤ) :
    UnitAddTorus.mFourierCoeff (loc2B_lift g) ![j.1, j.2] =
      (((4 * Real.pi ^ 2)⁻¹ : ℝ) : ℂ) * ∫ k in torusBox, g k * charNeg j k := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ loc2B_base,
    setIntegral_congr_fun loc2B_measurableSet
      (g := fun x => (fun k => g k * charNeg j k) (2 * Real.pi * x 0, 2 * Real.pi * x 1)),
    loc2B_box (fun k => g k * charNeg j k), Complex.real_smul]
  intro x hx
  dsimp only
  rw [OscInt.K2.TorusExpansionAux.mFourier_eval, loc2B_lift_coe g x hx, smul_eq_mul, mul_comm]
  congr 1
  unfold charNeg
  congr 3
  simp only [Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- The probability Haar measure of the unit torus (Mathlib's measure on `UnitAddTorus`). -/
noncomputable abbrev loc2B_mu : Measure (UnitAddTorus (Fin 2)) := Measure.pi fun _ => AddCircle.haarAddCircle

/-- The squared norm of the lift is the normalised squared norm on the box. -/
lemma loc2B_normSq (g : ℝ × ℝ → ℂ) :
    ∫ y, ‖loc2B_lift g y‖ ^ 2 ∂loc2B_mu = (4 * Real.pi ^ 2)⁻¹ * ∫ k in torusBox, ‖g k‖ ^ 2 := by
  refine (UnitAddTorus.integral_preimage _ loc2B_base).trans ?_
  rw [setIntegral_congr_fun loc2B_measurableSet
      (g := fun x => (fun k => ‖g k‖ ^ 2) (2 * Real.pi * x 0, 2 * Real.pi * x 1)),
    loc2B_box (fun k => ‖g k‖ ^ 2), smul_eq_mul]
  intro x hx
  dsimp only
  rw [loc2B_lift_coe g x hx]

end OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2 OscInt.LOC2Aux in
/-- **Q2** Bessel's inequality (indeed Parseval) on the box for continuous `g`. -/
theorem OscInt.LOC2Aux.locBessel : OscInt.Blueprint.LOC2.LocBesselFacts := by
  intro g hg
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have hbox : IsCompact torusBox := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hbox.exists_bound_of_continuousOn hg.continuousOn
  have hG : MemLp (loc2B_lift g) 2 loc2B_mu :=
    MemLp.of_bound (loc2B_measurable_lift hg).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => hC _ (loc2B_lift_mem y))
  have H := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin 2) (hG.toLp (loc2B_lift g))
  have hcoef : UnitAddTorus.mFourierCoeff (⇑(hG.toLp (loc2B_lift g))) =
      UnitAddTorus.mFourierCoeff (loc2B_lift g) := by
    funext n
    unfold UnitAddTorus.mFourierCoeff
    exact integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with t ht; rw [ht])
  have hint : ∫ t, ‖(hG.toLp (loc2B_lift g)) t‖ ^ 2 ∂loc2B_mu = ∫ t, ‖loc2B_lift g t‖ ^ 2 ∂loc2B_mu :=
    integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with t ht; rw [ht])
  rw [hcoef] at H
  have H2 : HasSum (fun n => ‖UnitAddTorus.mFourierCoeff (loc2B_lift g) n‖ ^ 2)
      ((4 * Real.pi ^ 2)⁻¹ * ∫ k in torusBox, ‖g k‖ ^ 2) := by
    convert H using 1
    exact (hint.trans (loc2B_normSq g)).symm
  rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at H2
  have H3 : HasSum (fun j : ℤ × ℤ => ((4 * Real.pi ^ 2)⁻¹) ^ 2 * ‖∫ k in torusBox, g k * charNeg j k‖ ^ 2)
      ((4 * Real.pi ^ 2)⁻¹ * ∫ k in torusBox, ‖g k‖ ^ 2) := by
    convert H2 using 1
    funext j
    simp only [Function.comp_apply, finTwoArrowEquiv_symm_apply]
    rw [loc2B_coeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpi), mul_pow]
  have H4 := H3.mul_left ((4 * Real.pi ^ 2) ^ 2)
  have H5 : HasSum (fun j : ℤ × ℤ => ‖∫ k in torusBox, g k * charNeg j k‖ ^ 2)
      (4 * Real.pi ^ 2 * ∫ k in torusBox, ‖g k‖ ^ 2) := by
    convert H4 using 1
    · funext j
      field_simp
    · field_simp
  exact ⟨H5.summable, H5.tsum_eq.le⟩

namespace OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2

/-! ### Q4: the Cauchy–Schwarz combination -/

/-- Weighted Cauchy–Schwarz with the explicit constants: `Σ w² ≤ 13`, `Σ a² ≤ X²` give `Σ w a ≤ 4 X`. -/
lemma loc2B_cs {w a : ℤ × ℤ → ℝ} {X : ℝ} (hw : ∀ j, 0 ≤ w j) (ha : ∀ j, 0 ≤ a j) (hX : 0 ≤ X)
    (hw2 : Summable fun j => w j ^ 2) (hw13 : ∑' j, w j ^ 2 ≤ 13)
    (ha2 : Summable fun j => a j ^ 2) (haX : ∑' j, a j ^ 2 ≤ X ^ 2) :
    Summable (fun j => w j * a j) ∧ ∑' j, w j * a j ≤ 4 * X := by
  have hle : ∀ j, w j * a j ≤ (w j ^ 2 + a j ^ 2) / 2 := fun j => by
    nlinarith [sq_nonneg (w j - a j)]
  have hsum : Summable fun j => w j * a j :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (ha j)) hle ((hw2.add ha2).div_const 2)
  refine ⟨hsum, ?_⟩
  rcases eq_or_lt_of_le hX with h0 | hpos
  · have hz : ∀ j, a j = 0 := by
      intro j
      have h1 : a j ^ 2 ≤ ∑' i, a i ^ 2 := ha2.le_tsum j (fun i _ => sq_nonneg _)
      rw [← h0] at haX
      have h2 : a j ^ 2 ≤ 0 := by nlinarith
      nlinarith [ha j, sq_nonneg (a j)]
    simp [hz, ← h0]
  · have hpt : ∀ j, 8 * X * (w j * a j) ≤ X ^ 2 * w j ^ 2 + 16 * a j ^ 2 :=
      fun j => by nlinarith [sq_nonneg (X * w j - 4 * a j)]
    have h1 : ∑' j, 8 * X * (w j * a j) ≤ ∑' j, (X ^ 2 * w j ^ 2 + 16 * a j ^ 2) :=
      (hsum.mul_left _).tsum_le_tsum hpt ((hw2.mul_left _).add (ha2.mul_left _))
    rw [tsum_mul_left, Summable.tsum_add (hw2.mul_left _) (ha2.mul_left _), tsum_mul_left,
      tsum_mul_left] at h1
    have h2 : X ^ 2 * ∑' j, w j ^ 2 ≤ X ^ 2 * 13 := mul_le_mul_of_nonneg_left hw13 (sq_nonneg X)
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hpos]

/-- `c_j(δ) = ∫ h e^{−ij·k}` with `h = χ e^{iδ·k}`. -/
lemma loc2B_coef_eq (χ : ℝ × ℝ → ℂ) (δ : ℝ × ℝ) (j : ℤ × ℤ) :
    (∫ k in torusBox, χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)) =
      ∫ k in torusBox, (χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I)) * charNeg j k := by
  congr 1
  funext k
  unfold charNeg
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `|c_j| = (1 + |j|²)⁻¹ |ĝ_j|` from the integration by parts identity. -/
lemma loc2B_norm_eq {u v : ℂ} (j : ℤ × ℤ)
    (e : ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2 : ℝ) : ℂ) * u = v) :
    ‖u‖ = (1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2)⁻¹ * ‖v‖ := by
  have hp : 0 < 1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2 := by positivity
  rw [← e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, ← mul_assoc,
    inv_mul_cancel₀ hp.ne', one_mul]

end OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2 OscInt.LOC2Aux in
/-- **Q4** The combination: Q1, Q2, Q3 and Q5 give the explicit coefficient bound. -/
theorem OscInt.LOC2Aux.locCombine : OscInt.Blueprint.LOC2.LocCombineFacts := by
  intro hI hB hS hL χ hχ hsupp δ hδ1 hδ2
  have hL' := hL χ hχ hsupp δ hδ1 hδ2
  dsimp only at hL'
  set h : ℝ × ℝ → ℂ := fun k => χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) with hhdef
  obtain ⟨hh, hhs, hgc, hgL⟩ := hL'
  have hBg := hB _ hgc
  obtain ⟨ha2, haX⟩ := hBg
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  set w : ℤ × ℤ → ℝ := fun j => (1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2)⁻¹ with hw
  set a : ℤ × ℤ → ℝ := fun j => ‖∫ k in torusBox, (h k - boxLaplacian h k) * charNeg j k‖ with ha
  set X : ℝ := 4 * Real.pi ^ 2 * boxL2 (fun k => h k - boxLaplacian h k) with hX
  have hc : ∀ j : ℤ × ℤ, ‖∫ k in torusBox, χ k *
      Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖ = w j * a j := by
    intro j
    rw [loc2B_coef_eq]
    exact loc2B_norm_eq j (hI h hh hhs j)
  have hI0 : 0 ≤ ∫ k in torusBox, ‖h k - boxLaplacian h k‖ ^ 2 := integral_nonneg fun k => sq_nonneg _
  have hX2 : X ^ 2 = 4 * Real.pi ^ 2 * ∫ k in torusBox, ‖h k - boxLaplacian h k‖ ^ 2 := by
    rw [hX, mul_pow, boxL2, Real.sq_sqrt (mul_nonneg (by positivity) hI0)]
    field_simp
  have hw2 : (fun j => w j ^ 2) = fun j : ℤ × ℤ => ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹ := by
    funext j
    simp only [hw, inv_pow]
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg hpi.le (Real.sqrt_nonneg _)
  obtain ⟨hsum, hle⟩ := loc2B_cs (w := w) (a := a) (X := X) (fun j => by positivity)
    (fun j => norm_nonneg _) hX0 (by rw [hw2]; exact hS.1) (by rw [hw2]; exact hS.2) ha2
    (by rw [hX2]; exact haX)
  simp_rw [hc]
  refine ⟨hsum, hle.trans ?_⟩
  have hb := mul_le_mul_of_nonneg_left hgL hpi.le
  rw [hX, locConstC2]
  linarith
