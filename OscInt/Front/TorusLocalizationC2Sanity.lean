/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TorusLocalizationC2
import OscInt.Front.TriangularDecaySanity
import OscInt.Front.TriangularDecayFinal

/-! # Sanity theorems for batch LOC2 (K2-FQ `TorusLocalizationC2Statement`, `boxL2`, `boxPartial₁`, `boxPartial₂`,
`boxLaplacian`, `locConstC2`)

Draft, written before the statement is stamped; no proof of K2-FQ exists in this file or is used by it, and no lemma
of a planned proof of K2-FQ (Fourier series of `χ e^{iθ·k}`, Parseval, integration by parts) is proved here. The
proved batch-K2 theorem `OscInt.API.triDecayUpper` (from `OscInt.Front.TriangularDecayFinal`) is used only as data,
in `loc2_nontrivial`. Two forms (`docs/lessons.md`, rules 8 and 9).

A. Unconditional, through the definitions of `OscInt/Statements/TorusLocalizationC2.lean`:
* `boxL2`: nonnegative; `boxL2 c = ‖c‖` for a constant (the normalisation `(2π)^{−2}` makes the box mass `1`), so
  `boxL2 (1 + 2i) = √5` and `boxL2 0 = 0`.
* `boxPartial₁`, `boxPartial₂`, `boxLaplacian` of a constant are `0`; so `locConstC2 c = 6 ‖c‖`.
* On the linear datum `ℓ(k) = 2k₁ + 7k₂`: `∂₁ℓ = 2`, `∂₂ℓ = 7` (distinct, so a swap of the unit vectors shows); on the
  quadratic datum `q(k) = k₁² + 3k₂²`: `Δq(0) = 2 + 6 = 8`, while `2 ∂₁²q(0) = 4` and `2 ∂₂²q(0) = 12`.
* The hypotheses: `χ₁` (batch K2's `ContDiffBump` of outer radius `1`) is `C²` with support inside `(−π, π)²`;
  bites: `χ_π` (`C²`, support closure reaching `(π, 0)`), the constant `1` (`C²`, support the plane), and the
  indicator of the closed unit ball (support inside the box, not continuous, so not `C²`).
* The zero phase: every lattice coefficient is at most `(2π)²`; the trivial bound
  `‖∫ χ₁ e^{i·}‖ ≤ ∫ χ₁` for every real phase.

B. Conditional, the statement constant as the only statement hypothesis (one theorem also uses K2-U): K2-FQ with
`χ₁` for every phase; at the zero phase; `0 < locConstC2 χ₁` (so the factor `4` cannot be `0`); K2-FQ implies K2-F;
K2-FQ with K2-U gives the localised decay at `triRate α`; and, with the proved K2-U, a datum (`χ₁`, phase
`triPhase 0`, large `t`) where `locConstC2 χ₁ · B` is below the trivial bound `∫ χ₁` (`loc2_nontrivial`).

Planted copies: `plants-loc2/README.md` of the scratch work directory of the sanity agent (not in the repository).
-/

namespace OscInt.API.TorusLocalizationC2Sanity

open OscInt.Statements OscInt.API.Poly OscInt.API.CuspSanity OscInt.API.TriangularDecaySanity MeasureTheory
open scoped ContDiff

/-! ## A. The normalised norm and the derivatives -/

theorem loc2_boxL2_nonneg (f : ℝ × ℝ → ℂ) : 0 ≤ boxL2 f := Real.sqrt_nonneg _

/-- The box has mass `1` for the normalised norm: `boxL2 c = ‖c‖`. -/
theorem loc2_boxL2_const (c : ℂ) : boxL2 (fun _ => c) = ‖c‖ := by
  rw [boxL2, setIntegral_const, volume_real_torusBox, smul_eq_mul,
    show 1 / (4 * Real.pi ^ 2) * ((2 * Real.pi) ^ 2 * ‖c‖ ^ 2) = ‖c‖ ^ 2 by field_simp; ring]
  exact Real.sqrt_sq (norm_nonneg c)

theorem loc2_boxL2_zero : boxL2 0 = 0 := by
  rw [show (0 : ℝ × ℝ → ℂ) = fun _ => (0 : ℂ) from rfl, loc2_boxL2_const, norm_zero]

/-- A generic constant: `boxL2 (1 + 2i) = √5`. -/
theorem loc2_boxL2_one_two : boxL2 (fun _ => (1 + 2 * Complex.I : ℂ)) = Real.sqrt 5 := by
  rw [loc2_boxL2_const, Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  norm_num

theorem loc2_boxPartial₁_const (c : ℂ) : boxPartial₁ (fun _ => c) = 0 := by
  funext k
  simp [boxPartial₁]

theorem loc2_boxPartial₂_const (c : ℂ) : boxPartial₂ (fun _ => c) = 0 := by
  funext k
  simp [boxPartial₂]

theorem loc2_boxLaplacian_const (c : ℂ) : boxLaplacian (fun _ => c) = 0 := by
  funext k
  simp [boxLaplacian, iteratedFDeriv_const_of_ne (show (2 : ℕ) ≠ 0 by norm_num)]

/-- `locConstC2 c = 4 · (3/2) ‖c‖ = 6 ‖c‖` for a constant. -/
theorem loc2_locConstC2_const (c : ℂ) : locConstC2 (fun _ => c) = 6 * ‖c‖ := by
  rw [locConstC2, loc2_boxPartial₁_const, loc2_boxPartial₂_const, loc2_boxLaplacian_const, loc2_boxL2_const,
    loc2_boxL2_zero]
  ring

theorem loc2_locConstC2_nonneg (χ : ℝ × ℝ → ℂ) : 0 ≤ locConstC2 χ := by
  unfold locConstC2
  have := loc2_boxL2_nonneg χ
  have := loc2_boxL2_nonneg (boxPartial₁ χ)
  have := loc2_boxL2_nonneg (boxPartial₂ χ)
  have := loc2_boxL2_nonneg (boxLaplacian χ)
  positivity

/-- The linear datum `ℓ(k) = 2k₁ + 7k₂` (complex valued). -/
noncomputable def loc2Lin (k : ℝ × ℝ) : ℂ := ((2 * k.1 + 7 * k.2 : ℝ) : ℂ)

theorem loc2_lin_hasFDerivAt (x : ℝ × ℝ) :
    HasFDerivAt loc2Lin (Complex.ofRealCLM.comp
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (7 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have h1 := ((hasFDerivAt_fst (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)).const_mul (2 : ℝ)).add
    ((hasFDerivAt_snd (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)).const_mul (7 : ℝ))
  exact Complex.ofRealCLM.hasFDerivAt.comp x h1

/-- `∂₁ℓ = 2` everywhere. -/
theorem loc2_lin_partial₁ (k : ℝ × ℝ) : boxPartial₁ loc2Lin k = 2 := by
  rw [boxPartial₁, (loc2_lin_hasFDerivAt k).fderiv]
  simp

/-- `∂₂ℓ = 7` everywhere. -/
theorem loc2_lin_partial₂ (k : ℝ × ℝ) : boxPartial₂ loc2Lin k = 7 := by
  rw [boxPartial₂, (loc2_lin_hasFDerivAt k).fderiv]
  simp

/-- The quadratic datum `q(k) = k₁² + 3k₂²`, real part. -/
noncomputable def loc2QuadR (k : ℝ × ℝ) : ℝ := k.1 ^ 2 + 3 * k.2 ^ 2

/-- The quadratic datum, complex valued. -/
noncomputable def loc2Quad (k : ℝ × ℝ) : ℂ := (loc2QuadR k : ℂ)

theorem loc2_quadR_contDiff : ContDiff ℝ ∞ loc2QuadR := by unfold loc2QuadR; fun_prop

/-- Second derivatives of the complex datum are those of its real part. -/
theorem loc2_quad_d2 (k : ℝ × ℝ) (m : Fin 2 → ℝ × ℝ) :
    iteratedFDeriv ℝ 2 loc2Quad k m = (iteratedFDeriv ℝ 2 loc2QuadR k m : ℂ) := by
  have e : loc2Quad = Complex.ofRealCLM ∘ loc2QuadR := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ loc2_quadR_contDiff.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem loc2_quad_d11 : iteratedFDeriv ℝ 2 loc2Quad 0 ![(1, 0), (1, 0)] = 2 := by
  rw [loc2_quad_d2, vec2_const, iteratedFDeriv_diag_eq (loc2_quadR_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]
  have e : (fun t : ℝ => loc2QuadR (0 + t • ((1 : ℝ), (0 : ℝ)))) = fun t => t ^ 2 := by
    funext t; simp [loc2QuadR]
  rw [e, iteratedDeriv_fun_pow_zero]
  norm_num

theorem loc2_quad_d22 : iteratedFDeriv ℝ 2 loc2Quad 0 ![(0, 1), (0, 1)] = 6 := by
  rw [loc2_quad_d2, vec2_const, iteratedFDeriv_diag_eq (loc2_quadR_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]
  have e : (fun t : ℝ => loc2QuadR (0 + t • ((0 : ℝ), (1 : ℝ)))) = fun t => (3 : ℝ) * t ^ 2 := by
    funext t; simp [loc2QuadR]
  rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  norm_num

/-- `Δq(0) = 2 + 6 = 8` (the two terms of the Laplacian are distinct on this datum). -/
theorem loc2_quad_laplacian : boxLaplacian loc2Quad 0 = 8 := by
  rw [boxLaplacian, loc2_quad_d11, loc2_quad_d22]
  norm_num

/-! ## A. The hypotheses: data and bites -/

theorem loc2_chi1_contDiff : ContDiff ℝ 2 chi1 := chi1_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)

/-- **K2-FQ's hypotheses on `χ` hold** for `χ₁`. -/
theorem loc2_chi1_hyps : ContDiff ℝ 2 chi1 ∧
    tsupport chi1 ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi :=
  ⟨loc2_chi1_contDiff, chi1_tsupport⟩

/-- **Bite (support)**: `χ_π` is `C²` and its support closure reaches `(π, 0)`. -/
theorem loc2_chiPi_bite : ContDiff ℝ 2 chiPi ∧
    ¬ tsupport chiPi ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi :=
  ⟨chiPi_bite.1.of_le (WithTop.coe_le_coe.mpr le_top), chiPi_bite.2⟩

/-- **Bite (support)**: the constant `1` is `C²`, with support closure the plane. -/
theorem loc2_const_one_bite : ContDiff ℝ 2 (fun _ : ℝ × ℝ => (1 : ℂ)) ∧
    ¬ tsupport (fun _ : ℝ × ℝ => (1 : ℂ)) ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi :=
  ⟨contDiff_const, const_one_bite.2⟩

/-- The indicator of the closed unit ball (sup norm), real valued. -/
noncomputable def loc2IndR (k : ℝ × ℝ) : ℝ := (Metric.closedBall (0 : ℝ × ℝ) 1).indicator (fun _ => (1 : ℝ)) k

/-- The indicator of the closed unit ball, complex valued. -/
noncomputable def loc2Ind (k : ℝ × ℝ) : ℂ := (loc2IndR k : ℂ)

theorem loc2_indR_not_continuous : ¬ Continuous loc2IndR := by
  intro hc
  have hpre : loc2IndR ⁻¹' Set.Ioi (1 / 2) = Metric.closedBall (0 : ℝ × ℝ) 1 := by
    ext k
    by_cases hk : k ∈ Metric.closedBall (0 : ℝ × ℝ) 1
    · simp only [Set.mem_preimage, Set.mem_Ioi, loc2IndR, Set.indicator_of_mem hk, hk, iff_true]
      norm_num
    · simp only [Set.mem_preimage, Set.mem_Ioi, loc2IndR, Set.indicator_of_notMem hk, hk, iff_false]
      norm_num
  have hopen : IsOpen (Metric.closedBall (0 : ℝ × ℝ) 1) := hpre ▸ isOpen_Ioi.preimage hc
  have hclopen : IsClopen (Metric.closedBall (0 : ℝ × ℝ) 1) := ⟨Metric.isClosed_closedBall, hopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have : (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := Metric.mem_closedBall_self zero_le_one
    rw [h] at this
    exact this
  · have : ((2 : ℝ), (0 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by rw [h]; trivial
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
    norm_num at this

/-- **Bite (regularity)**: the indicator of the closed unit ball has support closure inside the box, but it is not
continuous, so not `C²`. -/
theorem loc2_ind_bite : tsupport loc2Ind ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi ∧
    ¬ ContDiff ℝ 2 loc2Ind := by
  refine ⟨fun k hk => ?_, fun hd => loc2_indR_not_continuous ?_⟩
  · change k ∈ tsupport (fun k => ((loc2IndR k : ℝ) : ℂ)) at hk
    rw [tsupport_ofReal_comp] at hk
    have hsub : tsupport loc2IndR ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 :=
      closure_minimal (Set.support_indicator_subset) Metric.isClosed_closedBall
    have hk' : ‖k‖ ≤ 1 := by simpa using hsub hk
    rw [Prod.norm_def] at hk'
    have h1 : |k.1| ≤ 1 := (le_max_left _ _).trans hk'
    have h2 : |k.2| ≤ 1 := (le_max_right _ _).trans hk'
    have hpi := Real.pi_gt_three
    rw [abs_le] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · have : loc2IndR = fun k => (loc2Ind k).re := by funext k; simp [loc2Ind]
    rw [this]
    exact Complex.continuous_re.comp hd.continuous

/-! ## A. The zero phase and the trivial bound -/

/-- Every lattice coefficient of the zero phase is at most `(2π)²` (`(2π)²` at `n = 0`, `0` otherwise). -/
theorem loc2_zero_phase_coeff (t : ℝ) (n : ℤ × ℤ) :
    ‖∫ k in torusBox, Complex.exp (↑(t * (fun _ : ℝ × ℝ => (0 : ℝ)) k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) *
      Complex.I)‖ ≤ (2 * Real.pi) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp only [mul_zero, Int.cast_zero, zero_mul, add_zero, Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero,
      Complex.exp_zero, setIntegral_const, volume_real_torusBox, Complex.real_smul, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact le_of_eq (abs_of_pos (by positivity))
  · rw [lattice_coeff_zero_phase t n hn, norm_zero]
    positivity

theorem loc2_integral_bump1 : ∫ k in torusBox, (bump1 k : ℝ) = ∫ k, bump1 k := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro k hk
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hk
  have h' : k ∈ tsupport chi1 := by
    change k ∈ tsupport (fun k => ((bump1 k : ℝ) : ℂ))
    rw [tsupport_ofReal_comp]
    exact h
  exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self (chi1_tsupport h')

/-- The trivial bound: `‖∫ χ₁ e^{iφ}‖ ≤ ∫ χ₁` for every real phase `φ`. -/
theorem loc2_trivial_bound (φ : ℝ × ℝ → ℝ) :
    ‖∫ k in torusBox, chi1 k * Complex.exp (↑(φ k) * Complex.I)‖ ≤ ∫ k, bump1 k := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← loc2_integral_bump1]
  congr 1
  funext k
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, chi1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bump1.nonneg)]

/-! ## B. Conditional: K2-FQ as the hypothesis -/

/-- **K2-FQ** with `χ₁`: the constant `locConstC2 χ₁` for every continuous biperiodic phase, time and velocity. -/
theorem loc2_chi1 (h : TorusLocalizationC2Statement) :
    ∀ (Ψ : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) (B : ℝ), Continuous Ψ →
      (∀ k : ℝ × ℝ, Ψ (k.1 + 2 * Real.pi, k.2) = Ψ k) → (∀ k : ℝ × ℝ, Ψ (k.1, k.2 + 2 * Real.pi) = Ψ k) →
      (∀ n : ℤ × ℤ, ‖∫ k in torusBox,
          Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤ B) →
        ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)‖ ≤ locConstC2 chi1 * B :=
  h chi1 loc2_chi1_contDiff chi1_tsupport

/-- **K2-FQ** with `χ₁` and the zero phase: `‖∫ χ₁ e^{it p·k}‖ ≤ locConstC2 χ₁ (2π)²`. -/
theorem loc2_chi1_zero_phase (h : TorusLocalizationC2Statement) (t : ℝ) (p : ℝ × ℝ) :
    ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * ((fun _ : ℝ × ℝ => (0 : ℝ)) k + lin p k)) * Complex.I)‖ ≤
      locConstC2 chi1 * (2 * Real.pi) ^ 2 :=
  loc2_chi1 h _ t p _ continuous_const (fun _ => rfl) (fun _ => rfl) (loc2_zero_phase_coeff t)

/-- **K2-FQ** at `t = 0`: `‖∫ χ₁‖ ≤ locConstC2 χ₁ (2π)²`. -/
theorem loc2_chi1_time_zero (h : TorusLocalizationC2Statement) :
    ‖∫ k in torusBox, chi1 k‖ ≤ locConstC2 chi1 * (2 * Real.pi) ^ 2 := by
  have := loc2_chi1_zero_phase h 0 0
  simpa using this

/-- **K2-FQ forces `0 < locConstC2 χ₁`** (`∫ χ₁ ≠ 0`): the constant cannot vanish on a cutoff with nonzero mass. -/
theorem loc2_locConst_chi1_pos (h : TorusLocalizationC2Statement) : 0 < locConstC2 chi1 := by
  have h1 := loc2_chi1_time_zero h
  have h2 : 0 < ‖∫ k in torusBox, chi1 k‖ := norm_pos_iff.mpr integral_chi1_ne_zero
  by_contra hn
  have : locConstC2 chi1 * (2 * Real.pi) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) (by positivity)
  linarith

/-- **K2-FQ implies K2-F** (prose, item 3), with `D = locConstC2 χ`. -/
theorem loc2_implies_K2F (h : TorusLocalizationC2Statement) : TorusLocalizationStatement :=
  fun χ hχ hs => ⟨locConstC2 χ, fun Ψ t p B hΨ h1 h2 hB =>
    h χ (hχ.of_le (WithTop.coe_le_coe.mpr le_top)) hs Ψ t p B hΨ h1 h2 hB⟩

/-- **K2-FQ with K2-U**: for a `C²` cutoff supported in the box, the localised `triPhase α` integral at every real
velocity is at most `locConstC2 χ · C t^{−triRate α}`. -/
theorem loc2_triU (h : TorusLocalizationC2Statement) (hU : TriDecayUpperStatement) (χ : ℝ × ℝ → ℂ)
    (hχ : ContDiff ℝ 2 χ) (hs : tsupport χ ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi) (α : ℝ) :
    ∃ C : ℝ, ∀ (t : ℝ) (p : ℝ × ℝ), 1 ≤ t →
      ‖∫ k in torusBox, χ k * Complex.exp (↑(t * (triPhase α k + lin p k)) * Complex.I)‖ ≤
        locConstC2 χ * (C * t ^ (-triRate α)) := by
  obtain ⟨C, hC⟩ := hU α
  obtain ⟨h1, h2, h3⟩ := triPhase_periodic α
  exact ⟨C, fun t p ht => h χ hχ hs _ t p _ h1 h2 h3 fun n => hC t n ht⟩

/-- **K2-FQ in the non-trivial regime** (lessons 47), with the proved K2-U at `α = 0`: for `χ₁` and the phase
`triPhase 0` there are `t ≥ 1` and a valid coefficient bound `B` with `locConstC2 χ₁ · B < ∫ χ₁`, the trivial bound
(`loc2_trivial_bound`); K2-FQ then bounds the localised integral at every velocity by `locConstC2 χ₁ · B`. -/
theorem loc2_nontrivial (h : TorusLocalizationC2Statement) :
    ∃ t B : ℝ, 1 ≤ t ∧ (∀ n : ℤ × ℤ, ‖triKernel 0 t n‖ ≤ B) ∧ locConstC2 chi1 * B < ∫ k, bump1 k ∧
      ∀ p : ℝ × ℝ,
        ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * (triPhase 0 k + lin p k)) * Complex.I)‖ ≤
          locConstC2 chi1 * B := by
  obtain ⟨C, hC⟩ := OscInt.API.triDecayUpper 0
  rw [triRate_zero] at hC
  have hI : 0 < ∫ k, bump1 k := bump1.integral_pos
  obtain ⟨t, -, ht1, hlt⟩ := rate_separation 0 (2 / 3) (∫ k, bump1 k) (locConstC2 chi1 * C) 1 (by norm_num) hI
  rw [neg_zero, Real.rpow_zero, mul_one] at hlt
  obtain ⟨h1, h2, h3⟩ := triPhase_periodic 0
  refine ⟨t, C * t ^ (-(2 / 3 : ℝ)), ht1, fun n => hC t n ht1, by rw [← mul_assoc]; exact hlt,
    fun p => loc2_chi1 h _ t p _ h1 h2 h3 fun n => hC t n ht1⟩

end OscInt.API.TorusLocalizationC2Sanity
