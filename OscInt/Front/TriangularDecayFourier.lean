/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay

/-!
# Batch K2, part P13: `FourierDecayFacts`

Route: `docs/proof-K2.md`, section 4 ("P13") in the cheaper form of section 8, item 4 (N4). The coefficient
`c_j(δ)` is the transform `F χ ξ = ∫ χ(k) e^{iξ·k} dk` of χ at `ξ = δ − j`. Integration by parts on the whole plane
(χ has compact support; `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) gives `(iξᵥ) F g = −F (∂ᵥ g)`, hence
`(1 + ξ₁²)(1 + ξ₂²) ‖F χ ξ‖ ≤ A := ∫‖χ‖ + ∫‖∂₁²χ‖ + ∫‖∂₂²χ‖ + ∫‖∂₁²∂₂²χ‖`. With `1 + j² ≤ 4 (1 + (δ − j)²)` for
`δ ∈ [0, 1]` the coefficients are bounded by `16 A / ((1 + j₁²)(1 + j₂²))`, which is summable over `ℤ × ℤ`.
-/

namespace OscInt.K2.FourierDecayAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.K2
open scoped ContDiff

/-- The plane wave `e^{iξ·k}`. -/
noncomputable def wave (ξ k : ℝ × ℝ) : ℂ := Complex.exp (↑(ξ.1 * k.1 + ξ.2 * k.2) * Complex.I)

/-- The transform `∫ g(k) e^{iξ·k} dk` over the whole plane. -/
noncomputable def F (g : ℝ × ℝ → ℂ) (ξ : ℝ × ℝ) : ℂ := ∫ k, g k * wave ξ k

/-- The directional derivative `∂ᵥ g`. -/
noncomputable def D (v : ℝ × ℝ) (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun k => fderiv ℝ g k v

/-- Smooth with compact support. -/
def Good (g : ℝ × ℝ → ℂ) : Prop := ContDiff ℝ ∞ g ∧ HasCompactSupport g

theorem Good.D {g : ℝ × ℝ → ℂ} (h : Good g) (v : ℝ × ℝ) : Good (D v g) := by
  refine ⟨?_, h.2.fderiv_apply (𝕜 := ℝ) v⟩
  have h' := (contDiff_infty_iff_fderiv.mp h.1).2
  exact h'.clm_apply contDiff_const

theorem continuous_wave (ξ : ℝ × ℝ) : Continuous (wave ξ) := by
  unfold wave; fun_prop

theorem norm_wave (ξ k : ℝ × ℝ) : ‖wave ξ k‖ = 1 := by
  unfold wave; exact Complex.norm_exp_ofReal_mul_I _

theorem hasFDerivAt_wave (ξ k : ℝ × ℝ) :
    HasFDerivAt (wave ξ) (wave ξ k • ((Complex.ofRealCLM.comp
      (ξ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ξ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)).smulRight Complex.I)) k := by
  have h1 : HasFDerivAt (fun k : ℝ × ℝ => ξ.1 * k.1 + ξ.2 * k.2)
      (ξ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ξ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) k :=
    ((hasFDerivAt_fst).const_smul ξ.1).add ((hasFDerivAt_snd).const_smul ξ.2)
  have h2 := (Complex.ofRealCLM.hasFDerivAt.comp k h1).smul_const Complex.I
  exact h2.cexp

theorem fderiv_wave_apply (ξ k v : ℝ × ℝ) :
    fderiv ℝ (wave ξ) k v = wave ξ k * (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I) := by
  rw [(hasFDerivAt_wave ξ k).fderiv]
  simp

theorem Good.integrable_mul_wave {g : ℝ × ℝ → ℂ} (h : Good g) (ξ : ℝ × ℝ) :
    Integrable (fun k => g k * wave ξ k) :=
  (h.1.continuous.mul (continuous_wave ξ)).integrable_of_hasCompactSupport (h.2.mul_right)

/-- Integration by parts: `(iξ·v) F g = −F (∂ᵥ g)`. -/
theorem ibp {g : ℝ × ℝ → ℂ} (h : Good g) (ξ v : ℝ × ℝ) :
    (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I) * F g ξ = - F (D v g) ξ := by
  have hd : Differentiable ℝ g := h.1.differentiable (by simp)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (ℝ × ℝ)))
    (f := g) (g := wave ξ) (v := v) ((h.D v).integrable_mul_wave ξ) ?_ (h.integrable_mul_wave ξ)
    (fun x _ => hd x) (fun x _ => (hasFDerivAt_wave ξ x).differentiableAt)
  · simp only [fderiv_wave_apply] at key
    unfold F D
    rw [← key, ← integral_const_mul]
    congr 1; ext k; ring
  · simp only [fderiv_wave_apply]
    have := (h.integrable_mul_wave ξ).mul_const (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I)
    refine this.congr (Filter.Eventually.of_forall fun k => ?_)
    simp only; ring

theorem norm_F_le (g : ℝ × ℝ → ℂ) (ξ : ℝ × ℝ) : ‖F g ξ‖ ≤ ∫ k, ‖g k‖ := by
  unfold F
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1; ext k; rw [norm_mul, norm_wave, mul_one]

theorem sq_one {g : ℝ × ℝ → ℂ} (h : Good g) (ξ : ℝ × ℝ) :
    ξ.1 ^ 2 * ‖F g ξ‖ = ‖F (D (1, 0) (D (1, 0) g)) ξ‖ := by
  have h1 := ibp h ξ (1, 0)
  have h2 := ibp (h.D (1, 0)) ξ (1, 0)
  have : (↑(ξ.1 * (1, 0).1 + ξ.2 * (1, 0).2) * Complex.I) ^ 2 * F g ξ = F (D (1, 0) (D (1, 0) g)) ξ := by
    rw [pow_two, mul_assoc, h1, mul_neg, h2, neg_neg]
  rw [← this, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp [sq_abs]

theorem sq_two {g : ℝ × ℝ → ℂ} (h : Good g) (ξ : ℝ × ℝ) :
    ξ.2 ^ 2 * ‖F g ξ‖ = ‖F (D (0, 1) (D (0, 1) g)) ξ‖ := by
  have h1 := ibp h ξ (0, 1)
  have h2 := ibp (h.D (0, 1)) ξ (0, 1)
  have : (↑(ξ.1 * (0, 1).1 + ξ.2 * (0, 1).2) * Complex.I) ^ 2 * F g ξ = F (D (0, 1) (D (0, 1) g)) ξ := by
    rw [pow_two, mul_assoc, h1, mul_neg, h2, neg_neg]
  rw [← this, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp [sq_abs]

/-- The constant `A` of the decay bound. -/
noncomputable def A (g : ℝ × ℝ → ℂ) : ℝ :=
  (∫ k, ‖g k‖) + (∫ k, ‖D (1, 0) (D (1, 0) g) k‖) + (∫ k, ‖D (0, 1) (D (0, 1) g) k‖) +
    ∫ k, ‖D (1, 0) (D (1, 0) (D (0, 1) (D (0, 1) g))) k‖

theorem decay {g : ℝ × ℝ → ℂ} (h : Good g) (ξ : ℝ × ℝ) :
    (1 + ξ.1 ^ 2) * (1 + ξ.2 ^ 2) * ‖F g ξ‖ ≤ A g := by
  have e1 := sq_one h ξ
  have e2 := sq_two h ξ
  have e3 := sq_one ((h.D (0, 1)).D (0, 1)) ξ
  have : (1 + ξ.1 ^ 2) * (1 + ξ.2 ^ 2) * ‖F g ξ‖ =
      ‖F g ξ‖ + ξ.1 ^ 2 * ‖F g ξ‖ + ξ.2 ^ 2 * ‖F g ξ‖ + ξ.1 ^ 2 * (ξ.2 ^ 2 * ‖F g ξ‖) := by ring
  rw [this, e1, e2, e3]
  unfold A
  gcongr <;> exact norm_F_le _ _

theorem one_add_sq_le (d : ℝ) (j : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    1 + j ^ 2 ≤ 4 * (1 + (d - j) ^ 2) := by
  nlinarith [sq_nonneg (j - 2 * d), sq_nonneg (d - j), mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The one-variable weight `1/(1 + n²)`. -/
noncomputable def u (n : ℤ) : ℝ := 1 / (1 + (n : ℝ) ^ 2)

theorem u_nonneg (n : ℤ) : 0 ≤ u n := by unfold u; positivity

theorem summable_u : Summable u := by
  have hs : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2 + if n = 0 then (1 : ℝ) else 0) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine hs.of_nonneg_of_le u_nonneg fun n => ?_
  unfold u
  by_cases hn : n = 0
  · subst hn; simp
  · have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      positivity
    simp only [hn, ite_false, add_zero]
    exact one_div_le_one_div_of_le hpos (by linarith)

end OscInt.K2.FourierDecayAux

namespace OscInt.K2

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.K2 OscInt.K2.FourierDecayAux
open scoped ContDiff

theorem fourierDecay : FourierDecayFacts := by
  intro χ hχ hsupp
  have hbox : Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ torusBox :=
    Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  have hgood : Good χ := ⟨hχ, IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc)
    (isClosed_tsupport χ) (hsupp.trans hbox)⟩
  have hset : ∀ ξ : ℝ × ℝ, ∫ k in torusBox, χ k * wave ξ k = F χ ξ := by
    intro ξ
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_
    have : χ k = 0 := image_eq_zero_of_notMem_tsupport fun hk' => hk (hbox (hsupp hk'))
    rw [this, zero_mul]
  set b : ℤ × ℤ → ℝ := fun j => 16 * A χ * (u j.1 * u j.2) with hb
  have hA : 0 ≤ A χ := le_trans (by positivity) (decay hgood 0)
  have hbs : Summable b := by
    refine (summable_mul_of_summable_norm (f := u) (g := u) ?_ ?_).mul_left (16 * A χ)
    · simpa [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using summable_u
    · simpa [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using summable_u
  refine ⟨∑' j, b j, fun δ hδ => ?_⟩
  have hδ1 : 0 ≤ δ.1 ∧ δ.1 ≤ 1 := ⟨hδ.1.1, hδ.2.1⟩
  have hδ2 : 0 ≤ δ.2 ∧ δ.2 ≤ 1 := ⟨hδ.1.2, hδ.2.2⟩
  have hle : ∀ j : ℤ × ℤ, ‖∫ k in torusBox, χ k *
      Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖ ≤ b j := by
    intro j
    rw [show (∫ k in torusBox, χ k *
      Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)) =
        F χ (δ.1 - j.1, δ.2 - j.2) from hset (δ.1 - j.1, δ.2 - j.2)]
    have hd := decay hgood (δ.1 - j.1, δ.2 - j.2)
    have q1 := one_add_sq_le δ.1 (j.1 : ℝ) hδ1.1 hδ1.2
    have q2 := one_add_sq_le δ.2 (j.2 : ℝ) hδ2.1 hδ2.2
    have hN := norm_nonneg (F χ (δ.1 - j.1, δ.2 - j.2))
    have p1 : (0 : ℝ) < 1 + (j.1 : ℝ) ^ 2 := by positivity
    have p2 : (0 : ℝ) < 1 + (j.2 : ℝ) ^ 2 := by positivity
    simp only [hb, u]
    rw [show 16 * A χ * (1 / (1 + (j.1 : ℝ) ^ 2) * (1 / (1 + (j.2 : ℝ) ^ 2))) =
      16 * A χ / ((1 + (j.1 : ℝ) ^ 2) * (1 + (j.2 : ℝ) ^ 2)) by field_simp]
    rw [le_div_iff₀ (mul_pos p1 p2)]
    simp only at hd
    calc ‖F χ (δ.1 - j.1, δ.2 - j.2)‖ * ((1 + (j.1 : ℝ) ^ 2) * (1 + (j.2 : ℝ) ^ 2))
        ≤ ‖F χ (δ.1 - j.1, δ.2 - j.2)‖ * ((4 * (1 + (δ.1 - j.1) ^ 2)) * (4 * (1 + (δ.2 - j.2) ^ 2))) := by
          gcongr
      _ = 16 * ((1 + (δ.1 - j.1) ^ 2) * (1 + (δ.2 - j.2) ^ 2) * ‖F χ (δ.1 - j.1, δ.2 - j.2)‖) := by ring
      _ ≤ 16 * A χ := by gcongr
  have hs : Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, χ k *
      Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖) :=
    hbs.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  exact ⟨hs, hs.tsum_le_tsum hle hbs⟩

end OscInt.K2

