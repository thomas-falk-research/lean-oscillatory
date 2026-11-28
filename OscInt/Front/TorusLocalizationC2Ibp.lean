/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.TorusLocalizationC2
import OscInt.Front.TriangularDecayFourier

/-!
# Batch LOC2, parts Q1 and Q5: `LocIbpFacts` and `LocLaplaceFacts`

Route: `docs/proof-LOC2.md`. Q1: a `C²` function `h` with support inside the open box has compact support, so its
box integrals are whole-plane integrals and two integrations by parts per coordinate
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, as in K2's `ibp`, here for `C¹`) give
`(1 + |j|²) ∫ h e^{−ij·k} = ∫ (h − Δh) e^{−ij·k}`. Q5: the product rule gives
`h − Δh = e^{iδ·k} ((1 + |δ|²) χ − 2iδ₁ ∂₁χ − 2iδ₂ ∂₂χ − Δχ)` for `h = χ e^{iδ·k}`; pointwise
`|h − Δh| ≤ (3/2)|χ| + |∂₁χ| + |∂₂χ| + |Δχ|` for `|δᵢ| ≤ 1/2`, and Minkowski's inequality (from Hölder's) on the box
gives the `L²` bound.
-/

namespace OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2 OscInt.K2.FourierDecayAux
open scoped ContDiff

/-! ### Derivatives -/

theorem loc2A_two {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ (1 + 1) f := by
  rw [one_add_one_eq_two]; exact hf

theorem loc2A_D_C1 {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (v : ℝ × ℝ) : ContDiff ℝ 1 (D v f) :=
  (contDiff_succ_iff_fderiv.mp (loc2A_two hf)).2.2.clm_apply contDiff_const

theorem loc2A_D_cont {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) (v : ℝ × ℝ) : Continuous (D v f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem loc2A_DD_cont {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (v : ℝ × ℝ) : Continuous (D v (D v f)) :=
  loc2A_D_cont (loc2A_D_C1 hf v) v

/-- `∂ᵥ²f = D²f(v, v)`. -/
theorem loc2A_iter2 {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (k v : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 f k ![v, v] = D v (D v f) k := by
  rw [iteratedFDeriv_two_apply]
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp (loc2A_two hf)).2.2.differentiable one_ne_zero
  unfold D
  rw [fderiv_clm_apply (hd k) (differentiableAt_const v)]
  simp

theorem loc2A_lap {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (k : ℝ × ℝ) :
    boxLaplacian f k = D (1, 0) (D (1, 0) f) k + D (0, 1) (D (0, 1) f) k := by
  unfold boxLaplacian; rw [loc2A_iter2 hf, loc2A_iter2 hf]

theorem loc2A_lap_cont {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) : Continuous (boxLaplacian f) := by
  rw [show boxLaplacian f = fun k => D (1, 0) (D (1, 0) f) k + D (0, 1) (D (0, 1) f) k from
    funext (loc2A_lap hf)]
  exact (loc2A_DD_cont hf _).add (loc2A_DD_cont hf _)

/-! ### Q1: integration by parts -/

theorem loc2A_hasCompactSupport {h : ℝ × ℝ → ℂ}
    (hs : tsupport h ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi) : HasCompactSupport h :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport h)
    (hs.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))

theorem loc2A_integrable {g : ℝ × ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (ξ : ℝ × ℝ) :
    Integrable (fun k => g k * wave ξ k) :=
  (hg.mul (continuous_wave ξ)).integrable_of_hasCompactSupport hc.mul_right

/-- Integration by parts for `C¹` with compact support: `(iξ·v) F g = −F (∂ᵥ g)`. -/
theorem loc2A_ibp {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ξ v : ℝ × ℝ) :
    (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I) * F g ξ = - F (D v g) ξ := by
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hI : Integrable (fun k => g k * wave ξ k) := loc2A_integrable hg.continuous hc ξ
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (ℝ × ℝ)))
    (f := g) (g := wave ξ) (v := v)
    (loc2A_integrable (loc2A_D_cont hg v) (hc.fderiv_apply (𝕜 := ℝ) v) ξ) ?_ hI
    (fun x _ => hd x) (fun x _ => (hasFDerivAt_wave ξ x).differentiableAt)
  · simp only [fderiv_wave_apply] at key
    unfold F D
    rw [← key, ← integral_const_mul]
    congr 1; ext k; ring
  · simp only [fderiv_wave_apply]
    have := hI.mul_const (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I)
    refine this.congr (Filter.Eventually.of_forall fun k => ?_)
    simp only; ring

theorem loc2A_ibp2 {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (ξ v : ℝ × ℝ) :
    (↑(ξ.1 * v.1 + ξ.2 * v.2) * Complex.I) ^ 2 * F g ξ = F (D v (D v g)) ξ := by
  have h1 := loc2A_ibp (hg.of_le (by norm_num)) hc ξ v
  have h2 := loc2A_ibp (loc2A_D_C1 hg v) (hc.fderiv_apply (𝕜 := ℝ) v) ξ v
  rw [pow_two, mul_assoc, h1, mul_neg, h2, neg_neg]

theorem loc2A_box_eq {f : ℝ × ℝ → ℂ} (hf : ∀ k ∉ torusBox, f k = 0) (j : ℤ × ℤ) :
    ∫ k in torusBox, f k * charNeg j k = F f (-(j.1 : ℝ), -(j.2 : ℝ)) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun k hk => by rw [hf k hk, zero_mul])]
  unfold F
  congr 1; ext k
  unfold charNeg wave
  congr 3
  push_cast; ring

theorem loc2A_F_split {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 2 h) (hc : HasCompactSupport h) (ξ : ℝ × ℝ) :
    F (fun k => h k - boxLaplacian h k) ξ =
      F h ξ - F (D (1, 0) (D (1, 0) h)) ξ - F (D (0, 1) (D (0, 1) h)) ξ := by
  have hI : ∀ v : ℝ × ℝ, Integrable (fun k => D v (D v h) k * wave ξ k) := fun v =>
    loc2A_integrable (loc2A_DD_cont hh v)
      ((hc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v) ξ
  have hI0 : Integrable (fun k => h k * wave ξ k) := loc2A_integrable hh.continuous hc ξ
  have he : (fun k => (h k - boxLaplacian h k) * wave ξ k) = fun k =>
      (h k * wave ξ k - D (1, 0) (D (1, 0) h) k * wave ξ k) - D (0, 1) (D (0, 1) h) k * wave ξ k := by
    ext k; rw [loc2A_lap hh]; ring
  unfold F
  rw [he, integral_sub (f := fun k => h k * wave ξ k - D (1, 0) (D (1, 0) h) k * wave ξ k)
    (hI0.sub (hI _)) (hI _), integral_sub hI0 (hI _)]

/-- **Q1** `LocIbpFacts`. -/
theorem locIbp : LocIbpFacts := by
  intro h hh hs j
  have hc := loc2A_hasCompactSupport hs
  have hout : ∀ k ∉ torusBox, k ∉ tsupport h := fun k hk hk' =>
    hk (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self (hs hk'))
  have h0 : ∀ k ∉ torusBox, h k = 0 := fun k hk => image_eq_zero_of_notMem_tsupport (hout k hk)
  have hL0 : ∀ k ∉ torusBox, boxLaplacian h k = 0 := by
    intro k hk
    have : iteratedFDeriv ℝ 2 h k = 0 := by
      by_contra hne; exact hout k hk (support_iteratedFDeriv_subset 2 hne)
    simp [boxLaplacian, this]
  rw [loc2A_box_eq h0 j, loc2A_box_eq (fun k hk => by rw [h0 k hk, hL0 k hk, sub_zero]) j,
    loc2A_F_split hh hc, ← loc2A_ibp2 hh hc _ (1, 0), ← loc2A_ibp2 hh hc _ (0, 1)]
  push_cast
  linear_combination ((j.1 : ℂ) ^ 2 + (j.2 : ℂ) ^ 2) * F h (-(j.1 : ℝ), -(j.2 : ℝ)) * Complex.I_sq

/-! ### Q5: the Laplacian of `χ e^{iδ·k}` -/

theorem loc2A_contDiff_wave (δ : ℝ × ℝ) : ContDiff ℝ 2 (wave δ) := by
  have h1 : ContDiff ℝ 2 (fun k : ℝ × ℝ => δ.1 * k.1 + δ.2 * k.2) := by fun_prop
  have h2 : ContDiff ℝ 2 (fun k : ℝ × ℝ => ((δ.1 * k.1 + δ.2 * k.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact Complex.contDiff_exp.comp (h2.mul contDiff_const)

theorem loc2A_D_mul_wave {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (δ v : ℝ × ℝ) :
    D v (fun k => f k * wave δ k) =
      fun k => (D v f k + (↑(δ.1 * v.1 + δ.2 * v.2) * Complex.I) * f k) * wave δ k := by
  funext k
  unfold D
  rw [show (fun k => f k * wave δ k) = f * wave δ from rfl,
    fderiv_mul (hf k) (hasFDerivAt_wave δ k).differentiableAt]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fderiv_wave_apply]
  ring

theorem loc2A_D_add {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (c : ℂ)
    (v : ℝ × ℝ) : D v (fun k => f k + c * g k) = fun k => D v f k + c * D v g k := by
  funext k
  unfold D
  show fderiv ℝ (f + fun y => c * g y) k v = _
  rw [fderiv_add (hf k) ((hg k).const_mul c), fderiv_const_mul (hg k) c]
  simp

theorem loc2A_DD_mul_wave {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ 2 χ) (δ v : ℝ × ℝ) :
    D v (D v (fun k => χ k * wave δ k)) = fun k =>
      (D v (D v χ) k + 2 * (↑(δ.1 * v.1 + δ.2 * v.2) * Complex.I) * D v χ k +
        (↑(δ.1 * v.1 + δ.2 * v.2) * Complex.I) ^ 2 * χ k) * wave δ k := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hdD : Differentiable ℝ (D v χ) := (loc2A_D_C1 hχ v).differentiable one_ne_zero
  rw [loc2A_D_mul_wave hd, loc2A_D_mul_wave
    (f := fun k => D v χ k + (↑(δ.1 * v.1 + δ.2 * v.2) * Complex.I) * χ k) (hdD.add (hd.const_mul _)), loc2A_D_add hdD hd]
  funext k; ring

/-- The product rule: `h − Δh = ((1 + |δ|²) χ − 2iδ₁ ∂₁χ − 2iδ₂ ∂₂χ − Δχ) e^{iδ·k}`. -/
theorem loc2A_sub_lap {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ 2 χ) (δ k : ℝ × ℝ) :
    χ k * wave δ k - boxLaplacian (fun k => χ k * wave δ k) k =
      (((1 + δ.1 ^ 2 + δ.2 ^ 2 : ℝ) : ℂ) * χ k - 2 * ((δ.1 : ℂ) * Complex.I) * D (1, 0) χ k -
        2 * ((δ.2 : ℂ) * Complex.I) * D (0, 1) χ k - boxLaplacian χ k) * wave δ k := by
  rw [loc2A_lap (hχ.mul (loc2A_contDiff_wave δ)), loc2A_lap hχ, loc2A_DD_mul_wave hχ,
    loc2A_DD_mul_wave hχ]
  push_cast
  linear_combination (-((δ.1 : ℂ) ^ 2 + (δ.2 : ℂ) ^ 2) * χ k * wave δ k) * Complex.I_sq

theorem loc2A_sq_le {d : ℝ} (hd : |d| ≤ 1 / 2) : d ^ 2 ≤ 1 / 4 := by
  rw [← sq_abs]; nlinarith [abs_nonneg d]

theorem loc2A_norm_two_mul {d : ℝ} (hd : |d| ≤ 1 / 2) (z : ℂ) :
    ‖2 * ((d : ℂ) * Complex.I) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, Complex.norm_two]
  nlinarith [norm_nonneg z]

/-- The pointwise bound `|h − Δh| ≤ (3/2)|χ| + |∂₁χ| + |∂₂χ| + |Δχ|`. -/
theorem loc2A_pointwise {χ : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ 2 χ) {δ : ℝ × ℝ} (h1 : |δ.1| ≤ 1 / 2)
    (h2 : |δ.2| ≤ 1 / 2) (k : ℝ × ℝ) :
    ‖χ k * wave δ k - boxLaplacian (fun k => χ k * wave δ k) k‖ ≤
      3 / 2 * ‖χ k‖ + ‖D (1, 0) χ k‖ + ‖D (0, 1) χ k‖ + ‖boxLaplacian χ k‖ := by
  rw [loc2A_sub_lap hχ, norm_mul, norm_wave, mul_one]
  have n0 : ‖((1 + δ.1 ^ 2 + δ.2 ^ 2 : ℝ) : ℂ) * χ k‖ ≤ 3 / 2 * ‖χ k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := loc2A_sq_le h1; have := loc2A_sq_le h2
    nlinarith [norm_nonneg (χ k)]
  have n1 := loc2A_norm_two_mul h1 (D (1, 0) χ k)
  have n2 := loc2A_norm_two_mul h2 (D (0, 1) χ k)
  have t1 := norm_sub_le (((1 + δ.1 ^ 2 + δ.2 ^ 2 : ℝ) : ℂ) * χ k - 2 * ((δ.1 : ℂ) * Complex.I) * D (1, 0) χ k -
    2 * ((δ.2 : ℂ) * Complex.I) * D (0, 1) χ k) (boxLaplacian χ k)
  have t2 := norm_sub_le (((1 + δ.1 ^ 2 + δ.2 ^ 2 : ℝ) : ℂ) * χ k - 2 * ((δ.1 : ℂ) * Complex.I) * D (1, 0) χ k)
    (2 * ((δ.2 : ℂ) * Complex.I) * D (0, 1) χ k)
  have t3 := norm_sub_le (((1 + δ.1 ^ 2 + δ.2 ^ 2 : ℝ) : ℂ) * χ k) (2 * ((δ.1 : ℂ) * Complex.I) * D (1, 0) χ k)
  linarith

/-! ### Minkowski on the box -/

/-- The normalised `L²` norm on the box of a real function; `boxL2 f = loc2A_N ‖f‖`. -/
noncomputable def loc2A_N (f : ℝ × ℝ → ℝ) : ℝ :=
  Real.sqrt ((1 / (4 * Real.pi ^ 2)) * ∫ k in torusBox, f k ^ 2)

theorem loc2A_compact : IsCompact torusBox := isCompact_Icc.prod isCompact_Icc

theorem loc2A_measurable : MeasurableSet torusBox := measurableSet_Icc.prod measurableSet_Icc

theorem loc2A_intOn {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f torusBox :=
  hf.continuousOn.integrableOn_compact loc2A_compact

theorem loc2A_N_mono {f g : ℝ × ℝ → ℝ} (hg : Continuous g) (hf : Continuous f) (h0 : ∀ k, 0 ≤ f k)
    (hle : ∀ k, f k ≤ g k) : loc2A_N f ≤ loc2A_N g := by
  unfold loc2A_N
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact setIntegral_mono_on (loc2A_intOn (hf.pow 2)) (loc2A_intOn (hg.pow 2)) loc2A_measurable
    (fun k _ => pow_le_pow_left₀ (h0 k) (hle k) 2)

theorem loc2A_N_smul (f : ℝ × ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    loc2A_N (fun k => c * f k) = c * loc2A_N f := by
  unfold loc2A_N
  simp_rw [mul_pow]
  rw [integral_const_mul, mul_left_comm, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Cauchy–Schwarz on the box (Hölder with `p = q = 2`). -/
theorem loc2A_cs {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ k, 0 ≤ f k)
    (hg0 : ∀ k, 0 ≤ g k) :
    ∫ k in torusBox, f k * g k ≤
      Real.sqrt (∫ k in torusBox, f k ^ 2) * Real.sqrt (∫ k in torusBox, g k ^ 2) := by
  have hm : ∀ u : ℝ × ℝ → ℝ, Continuous u →
      MemLp u (ENNReal.ofReal 2) (volume.restrict torusBox) := fun u hu => by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr (loc2A_intOn (hu.pow 2))
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict torusBox) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) (hm f hf) (hm g hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at this
  exact this

/-- Minkowski on the box for nonnegative continuous functions. -/
theorem loc2A_N_add {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ k, 0 ≤ f k)
    (hg0 : ∀ k, 0 ≤ g k) : loc2A_N (fun k => f k + g k) ≤ loc2A_N f + loc2A_N g := by
  have hcs := loc2A_cs hf hg hf0 hg0
  have hexp : ∫ k in torusBox, (f k + g k) ^ 2 =
      (∫ k in torusBox, f k ^ 2) + 2 * (∫ k in torusBox, f k * g k) + ∫ k in torusBox, g k ^ 2 := by
    have e : (fun k => (f k + g k) ^ 2) = fun k => (f k ^ 2 + 2 * (f k * g k)) + g k ^ 2 := by
      ext k; ring
    have i1 : IntegrableOn (fun k => f k ^ 2 + 2 * (f k * g k)) torusBox := loc2A_intOn (by fun_prop)
    have i2 : IntegrableOn (fun k => g k ^ 2) torusBox := loc2A_intOn (by fun_prop)
    have i3 : IntegrableOn (fun k => f k ^ 2) torusBox := loc2A_intOn (by fun_prop)
    have i4 : IntegrableOn (fun k => 2 * (f k * g k)) torusBox := loc2A_intOn (by fun_prop)
    rw [e, integral_add i1 i2, integral_add i3 i4, integral_const_mul]
  have hF : 0 ≤ ∫ k in torusBox, f k ^ 2 := setIntegral_nonneg loc2A_measurable fun k _ => sq_nonneg _
  have hG : 0 ≤ ∫ k in torusBox, g k ^ 2 := setIntegral_nonneg loc2A_measurable fun k _ => sq_nonneg _
  have hc : (0 : ℝ) < 1 / (4 * Real.pi ^ 2) := by positivity
  unfold loc2A_N
  rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sqrt_mul hc.le, Real.sqrt_mul hc.le, hexp]
  have hsc := Real.mul_self_sqrt hc.le
  have : 2 * (√(1 / (4 * Real.pi ^ 2)) * √(∫ k in torusBox, f k ^ 2)) *
      (√(1 / (4 * Real.pi ^ 2)) * √(∫ k in torusBox, g k ^ 2)) =
      (1 / (4 * Real.pi ^ 2)) * (2 * (√(∫ k in torusBox, f k ^ 2) * √(∫ k in torusBox, g k ^ 2))) := by
    rw [show 2 * (√(1 / (4 * Real.pi ^ 2)) * √(∫ k in torusBox, f k ^ 2)) *
      (√(1 / (4 * Real.pi ^ 2)) * √(∫ k in torusBox, g k ^ 2)) =
      (√(1 / (4 * Real.pi ^ 2)) * √(1 / (4 * Real.pi ^ 2))) *
        (2 * (√(∫ k in torusBox, f k ^ 2) * √(∫ k in torusBox, g k ^ 2))) by ring, hsc]
  nlinarith [mul_le_mul_of_nonneg_left hcs hc.le]

theorem loc2A_N_four {a b c e : ℝ × ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (he : Continuous e) (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (hc0 : ∀ k, 0 ≤ c k)
    (he0 : ∀ k, 0 ≤ e k) :
    loc2A_N (fun k => 3 / 2 * a k + b k + c k + e k) ≤
      3 / 2 * loc2A_N a + loc2A_N b + loc2A_N c + loc2A_N e := by
  have ha' : Continuous fun k => 3 / 2 * a k := continuous_const.mul ha
  have ha0' : ∀ k, 0 ≤ 3 / 2 * a k := fun k => by have := ha0 k; positivity
  have s1 := loc2A_N_add (f := fun k => 3 / 2 * a k) ha' hb ha0' hb0
  have s2 := loc2A_N_add (f := fun k => 3 / 2 * a k + b k) (ha'.add hb) hc
    (fun k => add_nonneg (ha0' k) (hb0 k)) hc0
  have s3 := loc2A_N_add (f := fun k => 3 / 2 * a k + b k + c k) ((ha'.add hb).add hc) he
    (fun k => add_nonneg (add_nonneg (ha0' k) (hb0 k)) (hc0 k)) he0
  rw [loc2A_N_smul a (by norm_num)] at s1
  linarith

/-- **Q5** `LocLaplaceFacts`. -/
theorem locLaplace : LocLaplaceFacts := by
  intro χ hχ hs δ h1 h2 h
  have hh : h = fun k => χ k * wave δ k := rfl
  clear_value h; subst hh
  have hC : ContDiff ℝ 2 (fun k => χ k * wave δ k) := hχ.mul (loc2A_contDiff_wave δ)
  have hcont : Continuous (fun k => χ k * wave δ k - boxLaplacian (fun k => χ k * wave δ k) k) :=
    hC.continuous.sub (loc2A_lap_cont hC)
  refine ⟨hC, tsupport_mul_subset_left.trans hs, hcont, ?_⟩
  have c1 : Continuous (boxPartial₁ χ) := loc2A_D_cont (hχ.of_le (by norm_num)) (1, 0)
  have c2 : Continuous (boxPartial₂ χ) := loc2A_D_cont (hχ.of_le (by norm_num)) (0, 1)
  calc boxL2 (fun k => χ k * wave δ k - boxLaplacian (fun k => χ k * wave δ k) k)
      = loc2A_N (fun k => ‖χ k * wave δ k - boxLaplacian (fun k => χ k * wave δ k) k‖) := rfl
    _ ≤ loc2A_N (fun k => 3 / 2 * ‖χ k‖ + ‖boxPartial₁ χ k‖ + ‖boxPartial₂ χ k‖ + ‖boxLaplacian χ k‖) :=
        loc2A_N_mono ((((continuous_const.mul hχ.continuous.norm).add c1.norm).add c2.norm).add
          (loc2A_lap_cont hχ).norm) hcont.norm (fun k => norm_nonneg _) (loc2A_pointwise hχ h1 h2)
    _ ≤ 3 / 2 * loc2A_N (fun k => ‖χ k‖) + loc2A_N (fun k => ‖boxPartial₁ χ k‖) +
          loc2A_N (fun k => ‖boxPartial₂ χ k‖) + loc2A_N (fun k => ‖boxLaplacian χ k‖) :=
        loc2A_N_four hχ.continuous.norm c1.norm c2.norm (loc2A_lap_cont hχ).norm
          (fun k => norm_nonneg _) (fun k => norm_nonneg _) (fun k => norm_nonneg _) (fun k => norm_nonneg _)
    _ = _ := rfl

end OscInt.LOC2Aux
