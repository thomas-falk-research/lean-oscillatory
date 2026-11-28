/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Front.TriangularAnisoFinal
import OscInt.Front.ReducedBridge
import OscInt.Front.TriangularDecaySanity
import OscInt.Front.TriDeriv

/-!
# Batch K2, assembly AD: the global lower bound K2-D from the parts

Route: `docs/proof-K2.md`, section 5, with section 8, items 3 and 4 (m5). From P5 (`ReducedCurveExistsFacts`), P6
(`ReducedOrderTwoFacts`), P11 (`ProductNormalFormFacts`), P12 (`SquareNormalFormFacts`), K2-F
(`TorusLocalizationStatement`) and K2-ML (`MonomialLowerStatement`), with TRI-Q, TRI-W and the bridge:

1. the witness: `(π/2, π/2)` with `v = (1, −1)`, `w = (1, 1)` and `m = 4` for `α ≠ 0`, `|α| ≠ a*`; the A5 point of
   TRI-W with `m = 6` for `|α| = a*`; `(π/2, π/2)` with P12 for `α = 0`;
2. the exact product normal form of P11 (or P12) with a cutoff supported in a ball inside `(−π, π)²`;
3. K2-ML on both factors: `|L(t)| ≥ c₀ t^{−(1/2 + 1/m)}` for large `t`;
4. K2-F: if every lattice coefficient were below `c₀/(|D| + 1) · t^{−β}`, the localised integral would be below
   `c₀ t^{−β}`.
-/

namespace OscInt.K2.TriDecayLowerOfAux

open Set MeasureTheory Filter OscInt.Statements OscInt.Blueprint.K2
open scoped ContDiff

/-- The open box `(−π, π)²`. -/
abbrev openBox : Set (ℝ × ℝ) := Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi

theorem triPhase_smooth (α : ℝ) : ContDiff ℝ ∞ (triPhase α) := by
  unfold triPhase; fun_prop

theorem triPhase_continuous (α : ℝ) : Continuous (triPhase α) := by
  unfold triPhase; fun_prop

theorem triPhase_per₁ (α : ℝ) (k : ℝ × ℝ) : triPhase α (k.1 + 2 * Real.pi, k.2) = triPhase α k := by
  simp only [triPhase]
  rw [show k.1 + 2 * Real.pi + k.2 = (k.1 + k.2) + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.cos_add_two_pi]

theorem triPhase_per₂ (α : ℝ) (k : ℝ × ℝ) : triPhase α (k.1, k.2 + 2 * Real.pi) = triPhase α k := by
  simp only [triPhase]
  rw [show k.1 + (k.2 + 2 * Real.pi) = (k.1 + k.2) + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.cos_add_two_pi]

theorem exists_closedBall_subset {k₀ : ℝ × ℝ} (hk : k₀ ∈ openBox) :
    ∃ δ > 0, Metric.closedBall k₀ δ ⊆ openBox := by
  have ho : IsOpen openBox := isOpen_Ioo.prod isOpen_Ioo
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp ho k₀ hk
  exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hsub⟩

theorem openBox_subset : openBox ⊆ torusBox :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem setIntegral_torusBox (χ : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (hχ : tsupport χ ⊆ torusBox) :
    ∫ k in torusBox, (χ k : ℂ) * f k = ∫ k, (χ k : ℂ) * f k := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun k hk => ?_)
  have : χ k = 0 := image_eq_zero_of_notMem_tsupport (fun h => hk (hχ h))
  simp [this]

/-- Step 4: a lower bound on one localised integral gives a lower bound at some lattice site (via K2-F). -/
theorem lower_of_local (hF : TorusLocalizationStatement) (α β : ℝ) (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ openBox) (p : ℝ × ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hL : ∀ᶠ t in atTop, c₀ * t ^ (-β) ≤
      ‖∫ k in torusBox, (χ k : ℂ) * Complex.exp (↑(t * (triPhase α k + lin p k)) * Complex.I)‖) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-β) ≤ ‖triKernel α t n‖ := by
  have hχc : ContDiff ℝ ∞ (fun k => (χ k : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hsc : tsupport (fun k => (χ k : ℂ)) ⊆ openBox :=
    (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero χ).trans hsupp
  obtain ⟨D, hD⟩ := hF (fun k => (χ k : ℂ)) hχc hsc
  refine ⟨c₀ / (|D| + 1), by positivity, ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hL.and (eventually_gt_atTop 0))
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hLt, htpos⟩ := hT t ht
  by_contra hne
  simp only [not_exists, not_le] at hne
  have htb : 0 < t ^ (-β) := Real.rpow_pos_of_pos htpos _
  have hB := hD (triPhase α) t p (c₀ / (|D| + 1) * t ^ (-β)) (triPhase_continuous α) (triPhase_per₁ α)
    (triPhase_per₂ α) (fun n => (hne n).le)
  have hBn : 0 ≤ c₀ / (|D| + 1) * t ^ (-β) := by positivity
  have h1 : D * (c₀ / (|D| + 1) * t ^ (-β)) ≤ |D| * (c₀ / (|D| + 1) * t ^ (-β)) :=
    mul_le_mul_of_nonneg_right (le_abs_self D) hBn
  have h2 : |D| * (c₀ / (|D| + 1)) < c₀ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg D]
  have h3 : |D| * (c₀ / (|D| + 1) * t ^ (-β)) < c₀ * t ^ (-β) := by
    rw [← mul_assoc]; exact mul_lt_mul_of_pos_right h2 htb
  linarith

/-- For `m ≥ 2` the threshold `96 r^{1−m} ≤ t^{1−1/m}` of K2-ML holds for all large `t`. -/
theorem eventually_threshold (m : ℕ) (hm : 2 ≤ m) (r : ℝ) :
    ∀ᶠ t in atTop, 96 * r ^ (1 - (m : ℝ)) ≤ t ^ (1 - 1 / (m : ℝ)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < 1 - 1 / (m : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  exact (tendsto_rpow_atTop hpos).eventually_ge_atTop _

/-- Step 3: K2-ML on both factors of the product normal form. -/
theorem product_lower (hML : MonomialLowerStatement) (m : ℕ) (hm : 2 ≤ m) (σ ε J r₁ r₂ c : ℝ)
    (b₁ b₂ : ℝ → ℝ) (hσ : σ = 1 ∨ σ = -1) (hε : ε = 1 ∨ ε = -1) (hJ : 0 < J) (hb₁ : PlateauCutoff b₁ r₁)
    (hb₂ : PlateauCutoff b₂ r₂) :
    ∀ᶠ t in atTop, J⁻¹ / (24 * (m : ℝ) * 48) * t ^ (-(1 / 2 + 1 / (m : ℝ))) ≤
      ‖(J⁻¹ : ℂ) * Complex.exp (↑(t * c) * Complex.I) *
          (∫ z : ℝ, (b₁ z : ℂ) * Complex.exp (↑(t * σ * z ^ m) * Complex.I)) *
          (∫ y : ℝ, (b₂ y : ℂ) * Complex.exp (↑(t * ε * y ^ 2) * Complex.I))‖ := by
  filter_upwards [eventually_threshold m hm r₁, eventually_threshold 2 le_rfl r₂, eventually_gt_atTop 0]
    with t h₁ h₂ ht
  have e₁ := hML m σ b₁ r₁ t hm hσ hb₁ ht h₁
  have e₂ := hML 2 ε b₂ r₂ t le_rfl hε hb₂ ht h₂
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hexp : t ^ (-(1 / 2 + 1 / (m : ℝ))) = t ^ (-(1 : ℝ) / (m : ℝ)) * t ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add ht]; congr 1; push_cast; ring
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, hexp]
  have hJn : ‖(J⁻¹ : ℂ)‖ = J⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hJ.le]
  rw [hJn, mul_one]
  have a₁ : 0 ≤ t ^ (-(1 : ℝ) / (m : ℝ)) / (24 * (m : ℝ)) := by positivity
  have a₂ : 0 ≤ t ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)) / (24 * ((2 : ℕ) : ℝ)) := by positivity
  have := mul_le_mul e₁ e₂ a₂ (a₁.trans e₁)
  have hJi : 0 ≤ J⁻¹ := (inv_pos.mpr hJ).le
  calc J⁻¹ / (24 * (m : ℝ) * 48) * (t ^ (-(1 : ℝ) / (m : ℝ)) * t ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)))
      = J⁻¹ * (t ^ (-(1 : ℝ) / (m : ℝ)) / (24 * (m : ℝ)) *
          (t ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)) / (24 * ((2 : ℕ) : ℝ)))) := by
        push_cast; field_simp; ring
    _ ≤ J⁻¹ * (‖∫ z : ℝ, (b₁ z : ℂ) * Complex.exp (↑(t * σ * z ^ m) * Complex.I)‖ *
          ‖∫ y : ℝ, (b₂ y : ℂ) * Complex.exp (↑(t * ε * y ^ 2) * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left this hJi
    _ = _ := by ring

/-- Step 3 at `α = 0`: K2-ML for the cubic factor, squared. -/
theorem square_lower (hML : MonomialLowerStatement) (r c : ℝ) (b : ℝ → ℝ) (hb : PlateauCutoff b r) :
    ∀ᶠ t in atTop, (1 / 72) ^ 2 * t ^ (-(2 / 3 : ℝ)) ≤
      ‖Complex.exp (↑(t * c) * Complex.I) *
          (∫ z : ℝ, (b z : ℂ) * Complex.exp (↑(t * z ^ 3) * Complex.I)) ^ 2‖ := by
  filter_upwards [eventually_threshold 3 (by norm_num) r, eventually_gt_atTop 0] with t h₁ ht
  have e₁ := hML 3 1 b r t (by norm_num) (Or.inl rfl) hb ht h₁
  simp only [mul_one] at e₁
  have hexp : t ^ (-(2 / 3 : ℝ)) = t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) * t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add ht]; congr 1; push_cast; ring
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow, hexp]
  have a₁ : 0 ≤ t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) / (24 * ((3 : ℕ) : ℝ)) := by positivity
  have := mul_le_mul e₁ e₁ a₁ (a₁.trans e₁)
  calc (1 / 72) ^ 2 * (t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) * t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)))
      = t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) / (24 * ((3 : ℕ) : ℝ)) *
          (t ^ (-(1 : ℝ) / ((3 : ℕ) : ℝ)) / (24 * ((3 : ℕ) : ℝ))) := by
        push_cast; ring
    _ ≤ _ := this
    _ = _ := by ring

/-- `DΨ(k₀) k = −lin p k` for `p = −∇Ψ(k₀)`. -/
theorem fderiv_eq_lin (L : ℝ × ℝ →L[ℝ] ℝ) (k : ℝ × ℝ) :
    L k = -lin (-L (1, 0), -L (0, 1)) k := by
  have hk : k = k.1 • ((1 : ℝ), (0 : ℝ)) + k.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hk]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, lin]
  ring

/-- Steps 2 to 4 at a witness of order m (P11). -/
theorem case_product (h11 : ProductNormalFormFacts) (hF : TorusLocalizationStatement)
    (hML : MonomialLowerStatement) (α : ℝ) (k₀ v w : ℝ × ℝ) (ε₀ : ℝ) (h : ℝ → ℝ) (m : ℕ) (β : ℝ)
    (hk₀ : k₀ ∈ openBox) (hm : 2 ≤ m) (hspan : v.1 * w.2 - v.2 * w.1 ≠ 0)
    (hww : iteratedFDeriv ℝ 2 (triPhase α) k₀ ![w, w] ≠ 0) (hε₀ : 0 < ε₀)
    (hred : ReducedCurve (triPhase α) k₀ v w ε₀ h)
    (hlow : ∀ j ∈ Finset.Icc 1 (m - 1), iteratedDeriv j (reducedFn (triPhase α) k₀ v w h) 0 = 0)
    (hne : iteratedDeriv m (reducedFn (triPhase α) k₀ v w h) 0 ≠ 0) (hβ : 1 / 2 + 1 / (m : ℝ) = β) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-β) ≤ ‖triKernel α t n‖ := by
  obtain ⟨δ, hδ, hball⟩ := exists_closedBall_subset hk₀
  obtain ⟨χ, hχ, hsupp, c, σ, ε, J, r₁, r₂, b₁, b₂, hσ, hε, hJ, hb₁, hb₂, -, -, hid⟩ :=
    h11 (triPhase α) k₀ v w ε₀ h m δ (triPhase_smooth α) hm hspan hww hε₀ hred hlow hne hδ
  have hs : tsupport χ ⊆ openBox := hsupp.trans hball
  set L := fderiv ℝ (triPhase α) k₀
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine lower_of_local hF α β χ hχ hs (-L (1, 0), -L (0, 1)) (J⁻¹ / (24 * (m : ℝ) * 48))
    (by have := inv_pos.mpr hJ; positivity) ?_
  filter_upwards [product_lower hML m hm σ ε J r₁ r₂ c b₁ b₂ hσ hε hJ hb₁ hb₂] with t ht
  rw [← hβ]
  refine ht.trans (le_of_eq ?_)
  rw [← hid t, setIntegral_torusBox χ _ (hs.trans openBox_subset)]
  congr 2
  funext k
  rw [fderiv_eq_lin L k]
  ring_nf

/-- Steps 2 to 4 at `α = 0` (P12). -/
theorem case_square (h12 : SquareNormalFormFacts) (hF : TorusLocalizationStatement)
    (hML : MonomialLowerStatement) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-(2 / 3 : ℝ)) ≤ ‖triKernel 0 t n‖ := by
  have hk₀ : ((Real.pi / 2, Real.pi / 2) : ℝ × ℝ) ∈ openBox := by
    have := Real.pi_pos
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨δ, hδ, hball⟩ := exists_closedBall_subset hk₀
  obtain ⟨χ, hχ, hsupp, c, r, b, hb, -, hid⟩ := h12 δ hδ
  have hs : tsupport χ ⊆ openBox := hsupp.trans hball
  refine lower_of_local hF 0 (2 / 3) χ hχ hs (1, 1) ((1 / 72) ^ 2) (by norm_num) ?_
  filter_upwards [square_lower hML r c b hb] with t ht
  refine ht.trans (le_of_eq ?_)
  rw [← hid t, setIntegral_torusBox χ _ (hs.trans openBox_subset)]
  congr 2
  funext k
  simp only [lin]
  ring_nf

end OscInt.K2.TriDecayLowerOfAux

namespace OscInt.K2

open Set OscInt.Statements OscInt.Blueprint.K2 OscInt.K2.TriDecayLowerOfAux
open scoped ContDiff

/-- **K2-D** (assembly AD): the global lower bound from P5, P6, P11, P12, K2-F and K2-ML. -/
theorem triDecayLower_of (h5 : OscInt.Blueprint.K2.ReducedCurveExistsFacts)
    (h6 : OscInt.Blueprint.K2.ReducedOrderTwoFacts) (h11 : OscInt.Blueprint.K2.ProductNormalFormFacts)
    (h12 : OscInt.Blueprint.K2.SquareNormalFormFacts) (hF : OscInt.Statements.TorusLocalizationStatement)
    (hML : OscInt.Statements.MonomialLowerStatement) : OscInt.Statements.TriDecayLowerStatement := by
  intro α
  by_cases h0 : α = 0
  · subst h0
    have hr : triRate 0 = 2 / 3 := by simp [triRate]
    rw [hr]
    exact case_square h12 hF hML
  by_cases hA : |α| = triExceptional
  · -- the A5 point of TRI-W, `m = 6`
    have hr : triRate α = 2 / 3 := by simp [triRate, hA]
    rw [hr]
    obtain ⟨hA5, -, -⟩ := OscInt.API.triA5Witness α hA
    obtain ⟨v, w, -, -, hww, ε, hε, h, hred, hlow, hne⟩ := hA5
    have hspan := OscInt.API.TriangularDecaySanity.span_of_hyps _ _ v w ε h 6 (triPhase_smooth α)
      (by norm_num) hww hε hred hne
    have ha2 : triExceptional ^ 2 = 1 / 8 := by
      rw [triExceptional, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have ha0 : 0 ≤ triExceptional := by rw [← hA]; exact abs_nonneg α
    have hlt : α < 1 / 2 := by
      have : triExceptional < 1 / 2 := by nlinarith
      linarith [le_abs_self α]
    have hθ0 := Real.arccos_nonneg (-2 * α)
    have hθπ : Real.arccos (-2 * α) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    have hk₀ : ((Real.arccos (-2 * α), -Real.arccos (-2 * α)) : ℝ × ℝ) ∈ openBox := by
      have := Real.pi_pos
      exact ⟨⟨by linarith, hθπ⟩, ⟨by linarith, by linarith⟩⟩
    exact case_product h11 hF hML α _ v w ε h 6 (2 / 3) hk₀ (by norm_num) hspan hww hε hred hlow hne
      (by norm_num)
  · -- `(π/2, π/2)` with `v = (1, −1)`, `w = (1, 1)`, `m = 4`
    have hr : triRate α = 3 / 4 := by simp [triRate, h0, hA]
    rw [hr]
    obtain ⟨⟨hker, hcub, hq⟩, -⟩ := OscInt.API.triQuartic α h0
    set k₀ : ℝ × ℝ := (Real.pi / 2, Real.pi / 2) with hk₀def
    have hD2 : iteratedFDeriv ℝ 2 (triPhase α) k₀ ![(1, 1), (1, 1)] = 4 * α := by
      rw [OscInt.API.TriDeriv.triD2_mixed]
      simp only [hk₀def, Real.cos_pi_div_two, add_halves, Real.cos_pi]
      ring
    have hww : iteratedFDeriv ℝ 2 (triPhase α) k₀ ![(1, 1), (1, 1)] ≠ 0 := by
      rw [hD2]; exact mul_ne_zero four_ne_zero h0
    obtain ⟨ε, hε, h, hred⟩ := h5 (triPhase α) k₀ (1, -1) (1, 1) (triPhase_smooth α) hww
    obtain ⟨h3, h4⟩ := OscInt.API.ReducedBridge.bridge (triPhase α) k₀ (1, -1) (1, 1) ε h (triPhase_smooth α)
      hker hww hε hred
    have h2 := h6 (triPhase α) k₀ (1, -1) (1, 1) ε h (triPhase_smooth α) hww hε hred
    have h1 : iteratedDeriv 1 (reducedFn (triPhase α) k₀ (1, -1) (1, 1) h) 0 = 0 := by
      rw [iteratedDeriv_one, (OscInt.API.ReducedBridge.hasDerivAt_reducedFn (triPhase_smooth α) hred.1 hred
        (u := 0) (by simpa using hε)).deriv, OscInt.API.ReducedBridge.jet_zero hred.2.1,
        iteratedFDeriv_one_apply]
      simp
    have hk₀ : k₀ ∈ openBox := by
      have := Real.pi_pos
      rw [hk₀def]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    refine case_product h11 hF hML α k₀ (1, -1) (1, 1) ε h 4 (3 / 4) hk₀ (by norm_num) (by norm_num) hww hε
      hred ?_ ?_ (by norm_num)
    · intro j hj
      have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by
        simp only [Finset.mem_Icc] at hj; omega
      rcases hj' with rfl | rfl | rfl
      · exact h1
      · rw [h2, hker, hker]; simp
      · rw [h3, hcub]
    · rw [h4, OscInt.API.TriBlueprint.qinv, hq, hD2]
      exact div_ne_zero (by norm_num) (mul_ne_zero four_ne_zero h0)

end OscInt.K2

