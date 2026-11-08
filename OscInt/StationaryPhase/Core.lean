/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase
import OscInt.VanDerCorput.Final

/-!
# S2/S3 analytic core: the core estimate (L6)

`coreEstimate : OscInt.Blueprint.CoreEstimateFacts`: under `CoreHyps j a b μ ν D Q ys` (`j = 2, 3`) and
`AmpBound 2 ([-a, a] × [-b, b]) A M`, `|I(mQ, A)| ≤ C M m^{-(1/2 + 1/j)}` with `C = C(j, a, b, μ, ν, D)`.

Route: `docs/proof-S2S3.md` (L5), (L6) with revision items 4, 5, simplified as follows (no decomposition
`B = B(x, ys) + (y - ys) E` and no cutoff `θ` are needed).
1. Fubini (`oscInt2_eq_iterated`): `I(mQ, A) = ∫_{-a}^{a} e^{im g(x)} F(x) dx` with
   `F(x) = ∫_{-2b}^{2b} e^{im(Q(x,t) - g(x))} A(x, t) dt`, `g(x) = Q(x, ys x)` (`ys` clamped to `[-a, a]`
   outside, so that everything is continuous).
2. `|F| ≤ 8 (mμ)^{-1/2} (1 + 4b) M` by S1.2 in `t` (`slice_F_bound`).
3. `F' = ∫ e^{im(Q - g)} (im (∂_xQ(x,t) - ∂_xQ(x, ys x)) A + ∂_xA) dt` (differentiation under the integral sign,
   `hasDerivAt_inner`, using `g' = ∂_xQ(x, ys x)`). Hadamard (`avg`, `sub_eq_mul_avg`):
   `∂_yQ = (t - ys) h`, `∂_xQ - ∂_xQ(x, ys) = (t - ys) K`, with `h, K` and their first two `t`-derivatives given by
   parametric integrals over `s ∈ [0, 1]` (`hasDerivAt_avg`) and `|h| ≥ μ` (`abs_avg_ge`). One integration by
   parts in `t` with the weight `w = (K / h) A` (`hadamard_weight`, `ibp_phase`) and S1.2 give
   `|F'| ≤ 8 (mμ)^{-1/2} (1 + 24 β⁶)(1 + 4b) M`, `β = max 1 (max D μ⁻¹)` (`yStep`, `slice_F'_bound`).
4. S1.2 (`j = 2`) or S1.3 (`j = 3`) in `x` with phase `m g` and amplitude `F` (`core_reduction`,
   `coreEstimate`); `m^{-1/2} · m^{-1/j}` gives the rate.
Only `t`-derivatives of `h, K` are used; fourth derivatives of `Q` enter through `∂²_t K`.
The bounds on `ys'`, `ys''` in `CoreHyps` are not needed.
-/

open Set MeasureTheory OscInt.Statements Complex

namespace OscInt.StationaryPhase.CoreAux


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional derivative `∂_v f`. -/
noncomputable def pd (v : ℝ × ℝ) (f : ℝ × ℝ → E) : ℝ × ℝ → E := fun k => fderiv ℝ f k v

theorem contDiff_pd {n : ℕ} {f : ℝ × ℝ → E} (hf : ContDiff ℝ (n + 1) f) (v : ℝ × ℝ) :
    ContDiff ℝ n (pd v f) := by
  have h1 : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  exact h1.clm_apply contDiff_const

theorem norm_apply_clm_le (v : ℝ × ℝ) :
    ‖ContinuousLinearMap.apply ℝ E v‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L => by
    simpa [mul_comm] using L.le_opNorm v

/-- `‖Dⁱ ∂_v f‖ ≤ ‖Dⁱ⁺¹ f‖` for `‖v‖ ≤ 1`. -/
theorem norm_iteratedFDeriv_pd_le {n i : ℕ} {f : ℝ × ℝ → E} (hf : ContDiff ℝ (n + 1) f) (hi : i ≤ n)
    {v : ℝ × ℝ} (hv : ‖v‖ ≤ 1) (k : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (pd v f) k‖ ≤ ‖iteratedFDeriv ℝ (i + 1) f k‖ := by
  have h1 : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  have : pd v f = (ContinuousLinearMap.apply ℝ E v) ∘ fderiv ℝ f := rfl
  rw [this, ← norm_iteratedFDeriv_fderiv]
  calc _ ≤ ‖ContinuousLinearMap.apply ℝ E v‖ * ‖iteratedFDeriv ℝ i (fderiv ℝ f) k‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ h1.contDiffAt (by exact_mod_cast hi)
    _ ≤ 1 * ‖iteratedFDeriv ℝ i (fderiv ℝ f) k‖ := by
        gcongr; exact (norm_apply_clm_le v).trans hv
    _ = _ := one_mul _


/-- Slice in the second variable. -/
theorem hasDerivAt_slice2 {f : ℝ × ℝ → E} (hf : Differentiable ℝ f) (x t : ℝ) :
    HasDerivAt (fun t => f (x, t)) (pd (0, 1) f (x, t)) t := by
  have h : HasDerivAt (fun t : ℝ => ((x, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (hf (x, t)).hasFDerivAt.comp_hasDerivAt t h

/-- Slice in the first variable. -/
theorem hasDerivAt_slice1 {f : ℝ × ℝ → E} (hf : Differentiable ℝ f) (x t : ℝ) :
    HasDerivAt (fun x => f (x, t)) (pd (1, 0) f (x, t)) x := by
  have h : HasDerivAt (fun x : ℝ => ((x, t) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  exact (hf (x, t)).hasFDerivAt.comp_hasDerivAt x h



/-- Weighted average of `φ` along the segment from `c` to `y`: `∫₀¹ sᵏ φ(c + s(y - c)) ds`. -/
noncomputable def avg (k : ℕ) (φ : ℝ → ℝ) (c y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ k * φ (c + s * (y - c))

theorem mem_uIcc_segment {c y s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : c + s * (y - c) ∈ uIcc c y := by
  rcases le_total c y with h | h
  · rw [uIcc_of_le h]; constructor <;> nlinarith [hs.1, hs.2]
  · rw [uIcc_of_ge h]; constructor <;> nlinarith [hs.1, hs.2]

/-- Hadamard: `f y - f c = (y - c) ∫₀¹ f'(c + s(y - c)) ds`. -/
theorem sub_eq_mul_avg {f f1 : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : Continuous f1) (c y : ℝ) :
    f y - f c = (y - c) * avg 0 f1 c y := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => f (c + s * (y - c))) ((y - c) * f1 (c + s * (y - c))) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => c + s * (y - c)) (y - c) s := by
      simpa using ((hasDerivAt_id s).mul_const (y - c)).const_add c
    exact ((hf _).comp s h1).congr_deriv (by ring)
  have hi : IntervalIntegrable (fun s => (y - c) * f1 (c + s * (y - c))) volume 0 1 :=
    (by fun_prop : Continuous fun s => (y - c) * f1 (c + s * (y - c))).intervalIntegrable _ _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at this
  simp only [avg, pow_zero, one_mul]
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at this
  linarith

theorem continuous_avg (k : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ) (c : ℝ) : Continuous (avg k φ c) := by
  unfold avg
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y s => s ^ k * φ (c + s * (y - c))) (by fun_prop) 0 1

/-- Differentiation of `avg` under the integral sign. -/
theorem hasDerivAt_avg (k : ℕ) {φ φ' : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ')
    (c y : ℝ) : HasDerivAt (avg k φ c) (avg (k + 1) φ' c y) y := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(2 * |c| + |y| + 1)) (b := 2 * |c| + |y| + 1)).exists_bound_of_continuousOn
    hφ'.continuousOn
  have hcont : Continuous fun q : ℝ × ℝ => q.2 ^ k * φ (c + q.2 * (q.1 - c)) := by
    have : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
    fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 1)
    (𝕜 := ℝ) (x₀ := y) (s := Metric.ball y 1) (bound := fun _ => B)
    (F := fun z s => s ^ k * φ (c + s * (z - c))) (F' := fun z s => s ^ (k + 1) * φ' (c + s * (z - c)))
    (Metric.ball_mem_nhds y one_pos)
    (Filter.Eventually.of_forall fun z => (hcont.comp (by fun_prop : Continuous fun s : ℝ => (z, s))).aestronglyMeasurable)
    ((hcont.comp (by fun_prop : Continuous fun s : ℝ => (y, s))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s : ℝ => s ^ (k + 1) * φ' (c + s * (y - c))).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun t ht z hz => ?_
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc] using ht
    have hz' : |z - y| < 1 := by simpa [Real.dist_eq] using hz
    rw [norm_mul, norm_pow]
    have h1 : ‖t‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos ht'.1]; exact ht'.2)
    have h2 : ‖φ' (c + t * (z - c))‖ ≤ B := by
      apply hB
      have : |c + t * (z - c)| ≤ 2 * |c| + |y| + 1 := by
        have : |t * (z - c)| ≤ |z - c| := by
          rw [abs_mul, abs_of_pos ht'.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht'.2
        have h3 := abs_add_le c (t * (z - c))
        have h4 := abs_sub z c
        have h5 := abs_sub_abs_le_abs_sub z y
        linarith
      exact abs_le.1 this
    calc _ ≤ 1 * B := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  · refine Filter.Eventually.of_forall fun t _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℝ => c + t * (z - c)) t z := by
      simpa using (((hasDerivAt_id z).sub_const c).const_mul t).const_add c
    exact (((hφ _).comp z h1).const_mul (t ^ k)).congr_deriv (by ring)

theorem abs_avg_le (k : ℕ) {φ : ℝ → ℝ} {c y B : ℝ} (hB : ∀ t ∈ uIcc c y, |φ t| ≤ B) :
    |avg k φ c y| ≤ B := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun s => s ^ k * φ (c + s * (y - c))) (fun s hs => by
      have hs' : s ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc] using hs
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs'.1]
      have h1 : s ^ k ≤ 1 := pow_le_one₀ hs'.1.le hs'.2
      have h2 := hB _ (mem_uIcc_segment ⟨hs'.1.le, hs'.2⟩)
      calc s ^ k * |φ (c + s * (y - c))| ≤ 1 * B :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = B := one_mul B)
  simpa [avg] using this

/-- A continuous function with `μ ≤ |φ|` on a preconnected set has constant sign there. -/
theorem sign_of_abs_ge {φ : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S) (hφ : ContinuousOn φ S) {μ : ℝ}
    (hμ : 0 < μ) (h : ∀ t ∈ S, μ ≤ |φ t|) : (∀ t ∈ S, μ ≤ φ t) ∨ (∀ t ∈ S, φ t ≤ -μ) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨t1, ht1, h1⟩, ⟨t2, ht2, h2⟩⟩ := hc
  have h1' : φ t1 ≤ -μ := by
    rcases le_abs'.1 (h t1 ht1) with h' | h'
    · linarith
    · linarith
  have h2' : μ ≤ φ t2 := by
    rcases le_abs'.1 (h t2 ht2) with h' | h'
    · linarith
    · exact h'
  obtain ⟨t, ht, h0⟩ := hS.intermediate_value ht1 ht2 hφ
    (show (0 : ℝ) ∈ Icc (φ t1) (φ t2) from ⟨by linarith, by linarith⟩)
  have := h t ht
  rw [h0, abs_zero] at this
  linarith

theorem abs_avg_ge {φ : ℝ → ℝ} (hφ : Continuous φ) {c y μ : ℝ} (hμ : 0 < μ)
    (h : ∀ t ∈ uIcc c y, μ ≤ |φ t|) : μ ≤ |avg 0 φ c y| := by
  have hint : IntervalIntegrable (fun s : ℝ => s ^ 0 * φ (c + s * (y - c))) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => s ^ 0 * φ (c + s * (y - c))).intervalIntegrable _ _
  rcases sign_of_abs_ge isPreconnected_uIcc hφ.continuousOn hμ h with hp | hn
  · have := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one intervalIntegrable_const hint
      (f := fun _ => μ) (fun s hs => by simpa using hp _ (mem_uIcc_segment hs))
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at this
    exact this.trans (le_abs_self _)
  · have := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one hint intervalIntegrable_const
      (g := fun _ => -μ) (fun s hs => by simpa using hn _ (mem_uIcc_segment hs))
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at this
    rw [abs_of_neg (by unfold avg; linarith)]
    unfold avg; linarith



/-- The constant `max 1 (max D μ⁻¹)` controlling the quotient `K / h`. -/
noncomputable def beta (D μ : ℝ) : ℝ := max 1 (max D μ⁻¹)

theorem one_le_beta (D μ : ℝ) : 1 ≤ beta D μ := le_max_left _ _
theorem D_le_beta (D μ : ℝ) : D ≤ beta D μ := (le_max_left _ _).trans (le_max_right _ _)
theorem inv_le_beta (D μ : ℝ) : μ⁻¹ ≤ beta D μ := (le_max_right _ _).trans (le_max_right _ _)

/-- Derivatives of `1 / h`. -/
theorem hasDerivAt_inv_chain {h h1 h2 : ℝ → ℝ} {t : ℝ} (hh : ∀ t, HasDerivAt h (h1 t) t)
    (hh1 : HasDerivAt h1 (h2 t) t) (ht : h t ≠ 0) :
    HasDerivAt (fun t => (h t)⁻¹) (-(h1 t) * (h t)⁻¹ ^ 2) t ∧
    HasDerivAt (fun t => -(h1 t) * (h t)⁻¹ ^ 2)
      (-(h2 t) * (h t)⁻¹ ^ 2 + 2 * h1 t ^ 2 * (h t)⁻¹ ^ 3) t := by
  have hi : HasDerivAt (fun t => (h t)⁻¹) (-(h1 t) * (h t)⁻¹ ^ 2) t :=
    ((hh t).inv ht).congr_deriv (by field_simp)
  refine ⟨hi, ?_⟩
  have := (hh1.fun_neg).fun_mul (hi.fun_pow 2)
  exact this.congr_deriv (by simp; field_simp)

theorem bound_r2 {β k2 k1 k0 h1 h2 i : ℝ} (hβ : 1 ≤ β) (hk2 : |k2| ≤ β) (hk1 : |k1| ≤ β) (hk0 : |k0| ≤ β)
    (hh1 : |h1| ≤ β) (hh2 : |h2| ≤ β) (hi : |i| ≤ β) :
    |k2 * i + 2 * (k1 * (-h1 * i ^ 2)) + k0 * (-h2 * i ^ 2 + 2 * h1 ^ 2 * i ^ 3)| ≤ 6 * β ^ 6 := by
  have e1 : |k2 * i| ≤ β * β := by rw [abs_mul]; gcongr
  have e2 : |2 * (k1 * (-h1 * i ^ 2))| ≤ 2 * (β * (β * β ^ 2)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_two]; gcongr
  have e3 : |k0 * (-h2 * i ^ 2 + 2 * h1 ^ 2 * i ^ 3)| ≤ β * (β * β ^ 2 + 2 * β ^ 2 * β ^ 3) := by
    rw [abs_mul]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_pow, abs_pow, abs_two]
    gcongr
  have p2 : β ^ 2 ≤ β ^ 6 := pow_le_pow_right₀ hβ (by norm_num)
  have p4 : β ^ 4 ≤ β ^ 6 := pow_le_pow_right₀ hβ (by norm_num)
  calc _ ≤ |k2 * i| + |2 * (k1 * (-h1 * i ^ 2))| + |k0 * (-h2 * i ^ 2 + 2 * h1 ^ 2 * i ^ 3)| :=
        abs_add_three _ _ _
    _ ≤ β * β + 2 * (β * (β * β ^ 2)) + β * (β * β ^ 2 + 2 * β ^ 2 * β ^ 3) := by gcongr
    _ ≤ 6 * β ^ 6 := by ring_nf; nlinarith

theorem bound_r1 {β k1 k0 h1 i : ℝ} (hβ : 1 ≤ β) (hk1 : |k1| ≤ β) (hk0 : |k0| ≤ β)
    (hh1 : |h1| ≤ β) (hi : |i| ≤ β) :
    |k1 * i + k0 * (-h1 * i ^ 2)| ≤ 6 * β ^ 6 := by
  have e1 : |k1 * i| ≤ β * β := by rw [abs_mul]; gcongr
  have e2 : |k0 * (-h1 * i ^ 2)| ≤ β * (β * β ^ 2) := by
    rw [abs_mul, abs_mul, abs_neg, abs_pow]; gcongr
  have p2 : β ^ 2 ≤ β ^ 6 := pow_le_pow_right₀ hβ (by norm_num)
  have p4 : β ^ 4 ≤ β ^ 6 := pow_le_pow_right₀ hβ (by norm_num)
  calc _ ≤ |k1 * i| + |k0 * (-h1 * i ^ 2)| := abs_add_le _ _
    _ ≤ β * β + β * (β * β ^ 2) := by gcongr
    _ ≤ 6 * β ^ 6 := by ring_nf; nlinarith

theorem bound_r0 {β k0 i : ℝ} (hβ : 1 ≤ β) (hk0 : |k0| ≤ β) (hi : |i| ≤ β) :
    |k0 * i| ≤ 6 * β ^ 6 := by
  have p2 : β ^ 2 ≤ β ^ 6 := pow_le_pow_right₀ hβ (by norm_num)
  calc _ ≤ β * β := by rw [abs_mul]; gcongr
    _ ≤ 6 * β ^ 6 := by nlinarith


/-- The quotient `r = K / h` with two derivatives and the bound `6 β⁶` (`β = max 1 (max D μ⁻¹)`), on a set
where `|h| ≥ μ` and `h', h'', K, K', K''` are bounded by `D`. -/
theorem quot_data {h h1 h2 K K1 K2 : ℝ → ℝ} {S : Set ℝ} {μ D : ℝ}
    (hh : ∀ t, HasDerivAt h (h1 t) t) (hh1 : ∀ t, HasDerivAt h1 (h2 t) t) (hh2 : Continuous h2)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t) (hK2 : Continuous K2)
    (hμ : 0 < μ) (hlow : ∀ t ∈ S, μ ≤ |h t|)
    (hbd : ∀ t ∈ S, |h1 t| ≤ D ∧ |h2 t| ≤ D ∧ |K t| ≤ D ∧ |K1 t| ≤ D ∧ |K2 t| ≤ D) :
    ∃ r r1 r2 : ℝ → ℝ, (∀ t ∈ S, HasDerivAt r (r1 t) t) ∧ (∀ t ∈ S, HasDerivAt r1 (r2 t) t) ∧
      ContinuousOn r2 S ∧ (∀ t ∈ S, r t * h t = K t) ∧
      ∀ t ∈ S, |r t| ≤ 6 * beta D μ ^ 6 ∧ |r1 t| ≤ 6 * beta D μ ^ 6 ∧ |r2 t| ≤ 6 * beta D μ ^ 6 := by
  have hne : ∀ t ∈ S, h t ≠ 0 := fun t ht h0 => by
    have := hlow t ht; rw [h0, abs_zero] at this; linarith
  refine ⟨fun t => K t * (h t)⁻¹, fun t => K1 t * (h t)⁻¹ + K t * (-(h1 t) * (h t)⁻¹ ^ 2),
    fun t => K2 t * (h t)⁻¹ + 2 * (K1 t * (-(h1 t) * (h t)⁻¹ ^ 2)) +
      K t * (-(h2 t) * (h t)⁻¹ ^ 2 + 2 * h1 t ^ 2 * (h t)⁻¹ ^ 3), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ((hK t).fun_mul (hasDerivAt_inv_chain hh (hh1 t) (hne t ht)).1).congr_deriv (by ring)
  · intro t ht
    obtain ⟨i1, i2⟩ := hasDerivAt_inv_chain hh (hh1 t) (hne t ht)
    exact (((hK1 t).fun_mul i1).fun_add ((hK t).fun_mul i2)).congr_deriv (by ring)
  · have cK : Continuous K := continuous_iff_continuousAt.2 fun t => (hK t).continuousAt
    have cK1 : Continuous K1 := continuous_iff_continuousAt.2 fun t => (hK1 t).continuousAt
    have ch : Continuous h := continuous_iff_continuousAt.2 fun t => (hh t).continuousAt
    have ch1 : Continuous h1 := continuous_iff_continuousAt.2 fun t => (hh1 t).continuousAt
    have ci : ContinuousOn (fun t => (h t)⁻¹) S := ch.continuousOn.inv₀ hne
    fun_prop
  · intro t ht
    simp only
    field_simp [hne t ht]
  · intro t ht
    obtain ⟨b1, b2, b3, b4, b5⟩ := hbd t ht
    have hβ := one_le_beta D μ
    have hD := D_le_beta D μ
    have hi : |(h t)⁻¹| ≤ beta D μ := by
      rw [abs_inv]
      exact (inv_anti₀ hμ (hlow t ht)).trans (inv_le_beta D μ)
    exact ⟨bound_r0 hβ (b3.trans hD) hi, bound_r1 hβ (b4.trans hD) (b3.trans hD) (b1.trans hD) hi,
      bound_r2 hβ (b5.trans hD) (b4.trans hD) (b3.trans hD) (b1.trans hD) (b2.trans hD) hi⟩



/-- Two derivatives of `r · a` (`r` real, `a` complex) with uniform bounds. -/
theorem prod_data {r r1 r2 : ℝ → ℝ} {a a1 a2 : ℝ → ℂ} {S : Set ℝ} {R M : ℝ}
    (hr : ∀ t ∈ S, HasDerivAt r (r1 t) t) (hr1 : ∀ t ∈ S, HasDerivAt r1 (r2 t) t) (hr2 : ContinuousOn r2 S)
    (ha : ∀ t, HasDerivAt a (a1 t) t) (ha1 : ∀ t, HasDerivAt a1 (a2 t) t) (ha2 : Continuous a2)
    (hR : ∀ t ∈ S, |r t| ≤ R ∧ |r1 t| ≤ R ∧ |r2 t| ≤ R)
    (hM : ∀ t ∈ S, ‖a t‖ ≤ M ∧ ‖a1 t‖ ≤ M ∧ ‖a2 t‖ ≤ M) :
    (∀ t ∈ S, HasDerivAt (fun t => (r t : ℂ) * a t) ((r1 t : ℂ) * a t + (r t : ℂ) * a1 t) t) ∧
    (∀ t ∈ S, HasDerivAt (fun t => (r1 t : ℂ) * a t + (r t : ℂ) * a1 t)
      ((r2 t : ℂ) * a t + 2 * ((r1 t : ℂ) * a1 t) + (r t : ℂ) * a2 t) t) ∧
    ContinuousOn (fun t => (r2 t : ℂ) * a t + 2 * ((r1 t : ℂ) * a1 t) + (r t : ℂ) * a2 t) S ∧
    (∀ t ∈ S, ‖(r1 t : ℂ) * a t + (r t : ℂ) * a1 t‖ ≤ 2 * R * M) ∧
    (∀ t ∈ S, ‖(r2 t : ℂ) * a t + 2 * ((r1 t : ℂ) * a1 t) + (r t : ℂ) * a2 t‖ ≤ 4 * R * M) := by
  refine ⟨fun t ht => ((hr t ht).ofReal_comp.fun_mul (ha t)).congr_deriv (by ring),
    fun t ht => ((((hr1 t ht).ofReal_comp.fun_mul (ha t)).fun_add
      ((hr t ht).ofReal_comp.fun_mul (ha1 t)))).congr_deriv (by ring), ?_, ?_, ?_⟩
  · have c0 : ContinuousOn r S := fun t ht => (hr t ht).continuousAt.continuousWithinAt
    have c1 : ContinuousOn r1 S := fun t ht => (hr1 t ht).continuousAt.continuousWithinAt
    have ca : Continuous a := continuous_iff_continuousAt.2 fun t => (ha t).continuousAt
    have ca1 : Continuous a1 := continuous_iff_continuousAt.2 fun t => (ha1 t).continuousAt
    have c0' : ContinuousOn (fun t => (r t : ℂ)) S := continuous_ofReal.comp_continuousOn c0
    have c1' : ContinuousOn (fun t => (r1 t : ℂ)) S := continuous_ofReal.comp_continuousOn c1
    have c2' : ContinuousOn (fun t => (r2 t : ℂ)) S := continuous_ofReal.comp_continuousOn hr2
    fun_prop
  · intro t ht
    obtain ⟨b0, b1, -⟩ := hR t ht
    obtain ⟨m0, m1, -⟩ := hM t ht
    have hR0 : 0 ≤ R := (abs_nonneg _).trans b0
    calc _ ≤ ‖(r1 t : ℂ) * a t‖ + ‖(r t : ℂ) * a1 t‖ := norm_add_le _ _
      _ ≤ R * M + R * M := by
          rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
      _ = 2 * R * M := by ring
  · intro t ht
    obtain ⟨b0, b1, b2⟩ := hR t ht
    obtain ⟨m0, m1, m2⟩ := hM t ht
    have hR0 : 0 ≤ R := (abs_nonneg _).trans b0
    calc _ ≤ ‖(r2 t : ℂ) * a t‖ + ‖2 * ((r1 t : ℂ) * a1 t)‖ + ‖(r t : ℂ) * a2 t‖ := norm_add₃_le
      _ ≤ R * M + 2 * (R * M) + R * M := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_real, norm_real, norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_two]
          gcongr
      _ = 4 * R * M := by ring

theorem hasDerivAt_expPhase {φ q : ℝ → ℝ} {m : ℝ} (hφ : ∀ t, HasDerivAt φ (m * q t) t) (t : ℝ) :
    HasDerivAt (fun t => exp (↑(φ t) * I)) (exp (↑(φ t) * I) * (↑(m * q t) * I)) t := by
  have h0 : HasDerivAt (fun y => ((φ y : ℝ) : ℂ)) ((m * q t : ℝ) : ℂ) t := (hφ t).ofReal_comp
  have h1 : HasDerivAt (fun y => ((φ y : ℝ) : ℂ) * I) (((m * q t : ℝ) : ℂ) * I) t := h0.mul_const I
  exact h1.cexp

/-- One integration by parts against `e^{iφ}` with `φ' = m q`: if `w (m q) i = G` on `[lo, hi]` and `w`
vanishes at the endpoints, then `∫ e^{iφ} G = -∫ e^{iφ} w'`. -/
theorem ibp_phase {φ q : ℝ → ℝ} {m lo hi : ℝ} {w w1 G : ℝ → ℂ} (hle : lo ≤ hi)
    (hφ : ∀ t, HasDerivAt φ (m * q t) t) (hq : Continuous q)
    (hw : ∀ t ∈ Icc lo hi, HasDerivAt w (w1 t) t) (hw1 : ContinuousOn w1 (Icc lo hi))
    (hlo : w lo = 0) (hhi : w hi = 0) (hG : ∀ t ∈ Icc lo hi, w t * (↑(m * q t) * I) = G t) :
    ∫ t in lo..hi, exp (↑(φ t) * I) * G t = -∫ t in lo..hi, exp (↑(φ t) * I) * w1 t := by
  have cφ : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hcv : Continuous fun t => Complex.exp ((φ t : ℂ) * I) * (((m * q t : ℝ) : ℂ) * I) := by
    have : Continuous fun t => ((m * q t : ℝ) : ℂ) := continuous_ofReal.comp (continuous_const.mul hq)
    have : Continuous fun t => ((φ t : ℝ) : ℂ) := continuous_ofReal.comp cφ
    fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (A := ℂ) (a := lo) (b := hi) (u := w) (u' := w1)
    (v := fun t => Complex.exp ((φ t : ℂ) * I))
    (v' := fun t => Complex.exp ((φ t : ℂ) * I) * (((m * q t : ℝ) : ℂ) * I))
    (fun t ht => hw t (by rwa [uIcc_of_le hle] at ht)) (fun t _ => hasDerivAt_expPhase hφ t)
    ((show ContinuousOn w1 (uIcc lo hi) by rwa [uIcc_of_le hle]).intervalIntegrable) (hcv.intervalIntegrable _ _)
  rw [hlo, hhi, zero_mul, zero_mul, sub_zero, zero_sub] at key
  have h1 : ∫ t in lo..hi, Complex.exp ((φ t : ℂ) * I) * G t =
      ∫ t in lo..hi, w t * (Complex.exp ((φ t : ℂ) * I) * (((m * q t : ℝ) : ℂ) * I)) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hle] at ht
      rw [← hG t ht]; ring
  rw [h1, key]
  congr 1
  exact intervalIntegral.integral_congr fun t _ => mul_comm _ _

/-- S1.2 (`vanDerCorput_two`) with derivatives everywhere and uniform amplitude bounds. -/
theorem vdc2_wrap {φ φ1 φ2 : ℝ → ℝ} {ψ ψ1 : ℝ → ℂ} {lo hi μ N : ℝ} (hle : lo ≤ hi) (hμ : 0 < μ)
    (hφ : ∀ t, HasDerivAt φ (φ1 t) t) (hφ1 : ∀ t, HasDerivAt φ1 (φ2 t) t)
    (hlow : ∀ t ∈ Icc lo hi, μ ≤ |φ2 t|) (hψ : ∀ t ∈ Icc lo hi, HasDerivAt ψ (ψ1 t) t)
    (hψ1 : ContinuousOn ψ1 (Icc lo hi)) (hN : ∀ t ∈ Icc lo hi, ‖ψ t‖ ≤ N ∧ ‖ψ1 t‖ ≤ N) :
    ‖∫ t in lo..hi, exp (↑(φ t) * I) * ψ t‖ ≤ 8 / √μ * (N + (hi - lo) * N) := by
  have h := OscInt.vanDerCorput_two φ φ1 φ2 ψ ψ1 lo hi μ 0 hle hμ
    ⟨fun t _ => (hφ t).continuousAt.continuousWithinAt, fun t _ => hφ t⟩
    ⟨fun t _ => (hφ1 t).continuousAt.continuousWithinAt, fun t _ => hφ1 t⟩
    (fun t ht => hlow t (Ioo_subset_Icc_self ht))
    ⟨fun t ht => (hψ t ht).continuousAt.continuousWithinAt, fun t ht => hψ t (Ioo_subset_Icc_self ht),
      (show ContinuousOn ψ1 (uIcc lo hi) by rwa [uIcc_of_le hle]).intervalIntegrable⟩
  have e : oscInt (fun x => φ x + 0 * x) ψ lo hi = ∫ t in lo..hi, exp (↑(φ t) * I) * ψ t := by
    simp [oscInt]
  rw [e] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  unfold ampNorm
  have hb := (hN hi ⟨hle, le_rfl⟩).1
  have hi' : ∫ t in lo..hi, ‖ψ1 t‖ ≤ ∫ _ in lo..hi, N :=
    intervalIntegral.integral_mono_on hle
      ((by rwa [uIcc_of_le hle] : ContinuousOn ψ1 (uIcc lo hi)).norm.intervalIntegrable)
      intervalIntegrable_const (fun t ht => (hN t ht).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi'
  linarith


/-- The integration-by-parts weight of (L6b)(ii): with `q = (t - c) h`, `p - p c = (t - c) K` (Hadamard), the
function `w = (K / h) a` satisfies `w · (m q) i = m (p - p c) i a` on `[-B, B]`, vanishes at `±B`, and its first two
derivatives are bounded by `12 β⁶ M` and `24 β⁶ M`. -/
theorem hadamard_weight {q q1 q2 q3 p p1 p2 p3 : ℝ → ℝ} {a a1 a2 : ℝ → ℂ} {m μ D M c B : ℝ}
    (hμ : 0 < μ)
    (hq : ∀ t, HasDerivAt q (q1 t) t) (hq1 : ∀ t, HasDerivAt q1 (q2 t) t)
    (hq2 : ∀ t, HasDerivAt q2 (q3 t) t) (hq3 : Continuous q3)
    (hp : ∀ t, HasDerivAt p (p1 t) t) (hp1 : ∀ t, HasDerivAt p1 (p2 t) t)
    (hp2 : ∀ t, HasDerivAt p2 (p3 t) t) (hp3 : Continuous p3)
    (ha : ∀ t, HasDerivAt a (a1 t) t) (ha1 : ∀ t, HasDerivAt a1 (a2 t) t) (ha2 : Continuous a2)
    (hc : c ∈ Icc (-B) B) (hqc : q c = 0) (hlow : ∀ t ∈ Icc (-B) B, μ ≤ |q1 t|)
    (hD : ∀ t ∈ Icc (-B) B, |q2 t| ≤ D ∧ |q3 t| ≤ D ∧ |p1 t| ≤ D ∧ |p2 t| ≤ D ∧ |p3 t| ≤ D)
    (hMb : ∀ t ∈ Icc (-B) B, ‖a t‖ ≤ M ∧ ‖a1 t‖ ≤ M ∧ ‖a2 t‖ ≤ M)
    (ha0 : a (-B) = 0) (haB : a B = 0) :
    ∃ w w1 w2 : ℝ → ℂ, (∀ t ∈ Icc (-B) B, HasDerivAt w (w1 t) t) ∧
      (∀ t ∈ Icc (-B) B, HasDerivAt w1 (w2 t) t) ∧ ContinuousOn w2 (Icc (-B) B) ∧ w (-B) = 0 ∧ w B = 0 ∧
      (∀ t ∈ Icc (-B) B, w t * (((m * q t : ℝ) : ℂ) * I) = ((m * (p t - p c) : ℝ) : ℂ) * I * a t) ∧
      (∀ t ∈ Icc (-B) B, ‖w1 t‖ ≤ 2 * (6 * beta D μ ^ 6) * M) ∧
      (∀ t ∈ Icc (-B) B, ‖w2 t‖ ≤ 4 * (6 * beta D μ ^ 6) * M) := by
  have cont : ∀ {f f1 : ℝ → ℝ}, (∀ t, HasDerivAt f (f1 t) t) → Continuous f := fun hf =>
    continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hseg : ∀ t ∈ Icc (-B) B, uIcc c t ⊆ Icc (-B) B := fun t ht => uIcc_subset_Icc hc ht
  obtain ⟨r, r1, r2, hr, hr1, hr2, hrK, hrb⟩ := quot_data (h := avg 0 q1 c) (h1 := avg 1 q2 c)
    (h2 := avg 2 q3 c) (K := avg 0 p1 c) (K1 := avg 1 p2 c) (K2 := avg 2 p3 c) (S := Icc (-B) B) (D := D)
    (fun t => hasDerivAt_avg 0 hq1 (cont hq2) c t) (fun t => hasDerivAt_avg 1 hq2 hq3 c t)
    (continuous_avg 2 hq3 c) (fun t => hasDerivAt_avg 0 hp1 (cont hp2) c t)
    (fun t => hasDerivAt_avg 1 hp2 hp3 c t) (continuous_avg 2 hp3 c) hμ
    (fun t ht => abs_avg_ge (cont hq1) hμ fun s hs => hlow s (hseg t ht hs))
    (fun t ht => ⟨abs_avg_le 1 fun s hs => (hD s (hseg t ht hs)).1,
      abs_avg_le 2 fun s hs => (hD s (hseg t ht hs)).2.1,
      abs_avg_le 0 fun s hs => (hD s (hseg t ht hs)).2.2.1,
      abs_avg_le 1 fun s hs => (hD s (hseg t ht hs)).2.2.2.1,
      abs_avg_le 2 fun s hs => (hD s (hseg t ht hs)).2.2.2.2⟩)
  have hqf : ∀ t, q t = (t - c) * avg 0 q1 c t := fun t => by
    have := sub_eq_mul_avg hq (cont hq1) c t; rw [hqc, sub_zero] at this; exact this
  have hpf : ∀ t, p t - p c = (t - c) * avg 0 p1 c t := fun t => sub_eq_mul_avg hp (cont hp1) c t
  obtain ⟨hw, hw1, hw2, bw1, bw2⟩ := prod_data (M := M) hr hr1 hr2 ha ha1 ha2 hrb hMb
  refine ⟨fun t => (r t : ℂ) * a t, _, _, hw, hw1, hw2, by simp [ha0], by simp [haB], fun t ht => ?_, bw1, bw2⟩
  simp only
  rw [hqf t, hpf t, ← hrK t ht]; push_cast; ring

/-- The `y`-step (L6b)(ii) for one `x`: with `q = ∂_yQ(x, ·)` vanishing at `c`, `p = ∂_xQ(x, ·)`, the phase
`φ` with `φ' = m q`, amplitude `a = A(x, ·)` vanishing at `±B` and `e = ∂_xA(x, ·)`,
`|∫ e^{iφ} (i m (p - p c) a + e)| ≤ 8 (mμ)^{-1/2} (1 + 24 β⁶) M (1 + 2B)`. Proof: one integration by parts with
the weight of `hadamard_weight`, then S1.2. -/
theorem yStep {q q1 q2 q3 p p1 p2 p3 φ : ℝ → ℝ} {a a1 a2 e e1 : ℝ → ℂ} {m μ D M c B : ℝ}
    (hB : 0 < B) (hm : 0 < m) (hμ : 0 < μ) (hM : 0 ≤ M)
    (hq : ∀ t, HasDerivAt q (q1 t) t) (hq1 : ∀ t, HasDerivAt q1 (q2 t) t)
    (hq2 : ∀ t, HasDerivAt q2 (q3 t) t) (hq3 : Continuous q3)
    (hp : ∀ t, HasDerivAt p (p1 t) t) (hp1 : ∀ t, HasDerivAt p1 (p2 t) t)
    (hp2 : ∀ t, HasDerivAt p2 (p3 t) t) (hp3 : Continuous p3)
    (hφ : ∀ t, HasDerivAt φ (m * q t) t)
    (ha : ∀ t, HasDerivAt a (a1 t) t) (ha1 : ∀ t, HasDerivAt a1 (a2 t) t) (ha2 : Continuous a2)
    (he : ∀ t, HasDerivAt e (e1 t) t) (he1 : Continuous e1)
    (hc : c ∈ Icc (-B) B) (hqc : q c = 0) (hlow : ∀ t ∈ Icc (-B) B, μ ≤ |q1 t|)
    (hD : ∀ t ∈ Icc (-B) B, |q2 t| ≤ D ∧ |q3 t| ≤ D ∧ |p1 t| ≤ D ∧ |p2 t| ≤ D ∧ |p3 t| ≤ D)
    (hMb : ∀ t ∈ Icc (-B) B, ‖a t‖ ≤ M ∧ ‖a1 t‖ ≤ M ∧ ‖a2 t‖ ≤ M ∧ ‖e t‖ ≤ M ∧ ‖e1 t‖ ≤ M)
    (ha0 : a (-B) = 0) (haB : a B = 0) :
    ‖∫ t in (-B)..B, Complex.exp ((φ t : ℂ) * I) * (((m * (p t - p c) : ℝ) : ℂ) * I * a t + e t)‖ ≤
      8 / √(m * μ) * ((1 + 24 * beta D μ ^ 6) * M * (1 + 2 * B)) := by
  set S := Icc (-B) B
  have hle : -B ≤ B := by linarith
  have cont : ∀ {f f1 : ℝ → ℝ}, (∀ t, HasDerivAt f (f1 t) t) → Continuous f := fun hf =>
    continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have contC : ∀ {f f1 : ℝ → ℂ}, (∀ t, HasDerivAt f (f1 t) t) → Continuous f := fun hf =>
    continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  obtain ⟨w, w1, w2, hw, hw1, hw2, hw0, hwB, hwid, bw1, bw2⟩ := hadamard_weight (m := m) hμ hq hq1 hq2 hq3
    hp hp1 hp2 hp3 ha ha1 ha2 hc hqc hlow hD (fun t ht => ⟨(hMb t ht).1, (hMb t ht).2.1, (hMb t ht).2.2.1⟩)
    ha0 haB
  set E : ℝ → ℂ := fun t => Complex.exp ((φ t : ℂ) * I)
  have cE : Continuous E := by
    have : Continuous fun t => ((φ t : ℝ) : ℂ) := continuous_ofReal.comp (cont hφ)
    fun_prop
  have cw1 : ContinuousOn w1 S := fun t ht => (hw1 t ht).continuousAt.continuousWithinAt
  have hibp := ibp_phase (G := fun t => ((m * (p t - p c) : ℝ) : ℂ) * I * a t) hle hφ (cont hq) hw cw1
    hw0 hwB hwid
  have iE : ∀ {f : ℝ → ℂ}, ContinuousOn f S → IntervalIntegrable (fun t => E t * f t) volume (-B) B :=
    fun hf => ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hle]; exact cE.continuousOn.mul hf)
  have cG : ContinuousOn (fun t => ((m * (p t - p c) : ℝ) : ℂ) * I * a t) S := by
    have : Continuous fun t => ((m * (p t - p c) : ℝ) : ℂ) :=
      continuous_ofReal.comp (continuous_const.mul ((cont hp).sub continuous_const))
    exact (this.mul continuous_const |>.mul (contC ha)).continuousOn
  have hsplit : ∫ t in (-B)..B, E t * (((m * (p t - p c) : ℝ) : ℂ) * I * a t + e t) =
      ∫ t in (-B)..B, E t * (e t - w1 t) := by
    have e1 : ∀ t, E t * (((m * (p t - p c) : ℝ) : ℂ) * I * a t + e t) =
        E t * (((m * (p t - p c) : ℝ) : ℂ) * I * a t) + E t * e t := fun t => mul_add _ _ _
    have e2 : ∀ t, E t * (e t - w1 t) = E t * e t - E t * w1 t := fun t => mul_sub _ _ _
    simp only [e1, e2]
    rw [intervalIntegral.integral_add (iE cG) (iE (contC he).continuousOn),
      intervalIntegral.integral_sub (iE (contC he).continuousOn) (iE cw1), hibp]
    ring
  rw [hsplit]
  have hβ : 0 ≤ 6 * beta D μ ^ 6 := by positivity
  refine (vdc2_wrap (φ1 := fun t => m * q t) (φ2 := fun t => m * q1 t) (ψ1 := fun t => e1 t - w2 t)
    (N := (1 + 24 * beta D μ ^ 6) * M) hle (mul_pos hm hμ) hφ (fun t => (hq t).const_mul m)
    (fun t ht => by rw [abs_mul, abs_of_pos hm]; exact mul_le_mul_of_nonneg_left (hlow t ht) hm.le)
    (fun t ht => (he t).sub (hw1 t ht)) (he1.continuousOn.sub hw2) (fun t ht => ⟨?_, ?_⟩)).trans
    (le_of_eq (by ring))
  · calc ‖e t - w1 t‖ ≤ ‖e t‖ + ‖w1 t‖ := norm_sub_le _ _
      _ ≤ M + 2 * (6 * beta D μ ^ 6) * M := add_le_add (hMb t ht).2.2.2.1 (bw1 t ht)
      _ ≤ (1 + 24 * beta D μ ^ 6) * M := by nlinarith [mul_nonneg hβ hM]
  · calc ‖e1 t - w2 t‖ ≤ ‖e1 t‖ + ‖w2 t‖ := norm_sub_le _ _
      _ ≤ M + 4 * (6 * beta D μ ^ 6) * M := add_le_add (hMb t ht).2.2.2.2 (bw2 t ht)
      _ ≤ (1 + 24 * beta D μ ^ 6) * M := by nlinarith [mul_nonneg hβ hM]

section TwoD

theorem norm_pd_le (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) (f : ℝ × ℝ → E) (k : ℝ × ℝ) :
    ‖pd v f k‖ ≤ ‖iteratedFDeriv ℝ 1 f k‖ := by
  rw [norm_iteratedFDeriv_one]
  calc ‖fderiv ℝ f k v‖ ≤ ‖fderiv ℝ f k‖ * ‖v‖ := (fderiv ℝ f k).le_opNorm v
    _ ≤ ‖fderiv ℝ f k‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem norm_pd2_le {f : ℝ × ℝ → E} (hf : ContDiff ℝ 2 f) {v w : ℝ × ℝ} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (k : ℝ × ℝ) : ‖pd w (pd v f) k‖ ≤ ‖iteratedFDeriv ℝ 2 f k‖ :=
  (norm_pd_le w hw _ k).trans (norm_iteratedFDeriv_pd_le (n := 1) hf le_rfl hv k)

theorem norm_pd3_le {f : ℝ × ℝ → E} (hf : ContDiff ℝ 3 f) {u v w : ℝ × ℝ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (k : ℝ × ℝ) : ‖pd u (pd w (pd v f)) k‖ ≤ ‖iteratedFDeriv ℝ 3 f k‖ :=
  (norm_pd_le u hu _ k).trans ((norm_iteratedFDeriv_pd_le (n := 1) (contDiff_pd (n := 2) hf v) le_rfl hw k).trans
    (norm_iteratedFDeriv_pd_le (n := 2) hf (by norm_num) hv k))

theorem norm_pd4_le {f : ℝ × ℝ → E} (hf : ContDiff ℝ 4 f) {u u' v w : ℝ × ℝ} (hu' : ‖u'‖ ≤ 1)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℝ × ℝ) :
    ‖pd u' (pd u (pd w (pd v f))) k‖ ≤ ‖iteratedFDeriv ℝ 4 f k‖ :=
  (norm_pd_le u' hu' _ k).trans
    ((norm_iteratedFDeriv_pd_le (n := 1) (contDiff_pd (n := 2) (contDiff_pd (n := 3) hf v) w) le_rfl hu k).trans
    ((norm_iteratedFDeriv_pd_le (n := 2) (contDiff_pd (n := 3) hf v) (by norm_num) hw k).trans
    (norm_iteratedFDeriv_pd_le (n := 3) hf (by norm_num) hv k)))

end TwoD



section Slices

/-- Notation-free unit vectors. -/
abbrev e₁ : ℝ × ℝ := (1, 0)
abbrev e₂ : ℝ × ℝ := (0, 1)

theorem norm_e₁ : ‖e₁‖ ≤ 1 := by simp [Prod.norm_def]
theorem norm_e₂ : ‖e₂‖ ≤ 1 := by simp [Prod.norm_def]

/-- Bound for the inner integral `F(x) = ∫ e^{im(Q(x,t) - γ)} A(x, t) dt` by S1.2 in `t`. -/
theorem slice_F_bound {Q : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {m μ b M x γ : ℝ} (hQ : ContDiff ℝ 4 Q)
    (hA : ContDiff ℝ 2 A) (hb : 0 < b) (hm : 0 < m) (hμ : 0 < μ)
    (hlow : ∀ t ∈ Icc (-(2 * b)) (2 * b), μ ≤ |dd Q (x, t) e₂ e₂|)
    (hM : ∀ k, ‖A k‖ ≤ M ∧ ‖pd e₂ A k‖ ≤ M) :
    ‖∫ t in (-(2 * b))..(2 * b), Complex.exp (((m * (Q (x, t) - γ) : ℝ) : ℂ) * I) * A (x, t)‖ ≤
      8 / √(m * μ) * (M + (2 * b - -(2 * b)) * M) := by
  have dQ : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have dQ2 : Differentiable ℝ (pd e₂ Q) := (contDiff_pd (n := 3) hQ e₂).differentiable (by norm_num)
  have dA : Differentiable ℝ A := hA.differentiable (by norm_num)
  have cA2 : Continuous (pd e₂ A) := (contDiff_pd (n := 1) hA e₂).continuous
  refine vdc2_wrap (φ1 := fun t => m * pd e₂ Q (x, t)) (φ2 := fun t => m * pd e₂ (pd e₂ Q) (x, t))
    (ψ1 := fun t => pd e₂ A (x, t)) (by linarith) (mul_pos hm hμ)
    (fun t => (((hasDerivAt_slice2 dQ x t).sub_const γ).const_mul m))
    (fun t => (hasDerivAt_slice2 dQ2 x t).const_mul m)
    (fun t ht => by
      rw [abs_mul, abs_of_pos hm]; exact mul_le_mul_of_nonneg_left (hlow t ht) hm.le)
    (fun t _ => hasDerivAt_slice2 dA x t) (by fun_prop) (fun t _ => hM (x, t))


/-- The `y`-slices of the derivatives of `Q` used in `yStep` are bounded by `D`. -/
theorem slice_Q_bounds {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 4 Q) {D x : ℝ} {T : Set ℝ}
    (hD : ∀ i ≤ 4, ∀ t ∈ T, ‖iteratedFDeriv ℝ i Q (x, t)‖ ≤ D) (t : ℝ) (ht : t ∈ T) :
    |pd e₂ (pd e₂ (pd e₂ Q)) (x, t)| ≤ D ∧ |pd e₂ (pd e₂ (pd e₂ (pd e₂ Q))) (x, t)| ≤ D ∧
      |pd e₂ (pd e₁ Q) (x, t)| ≤ D ∧ |pd e₂ (pd e₂ (pd e₁ Q)) (x, t)| ≤ D ∧
      |pd e₂ (pd e₂ (pd e₂ (pd e₁ Q))) (x, t)| ≤ D := by
  have h2 : ContDiff ℝ 2 Q := hQ.of_le (by norm_num)
  have h3 : ContDiff ℝ 3 Q := hQ.of_le (by norm_num)
  exact ⟨(norm_pd3_le h3 norm_e₂ norm_e₂ norm_e₂ _).trans (hD 3 (by norm_num) t ht),
    (norm_pd4_le hQ norm_e₂ norm_e₂ norm_e₂ norm_e₂ _).trans (hD 4 (by norm_num) t ht),
    (norm_pd2_le h2 norm_e₁ norm_e₂ _).trans (hD 2 (by norm_num) t ht),
    (norm_pd3_le h3 norm_e₂ norm_e₁ norm_e₂ _).trans (hD 3 (by norm_num) t ht),
    (norm_pd4_le hQ norm_e₂ norm_e₂ norm_e₁ norm_e₂ _).trans (hD 4 (by norm_num) t ht)⟩

/-- The derivatives of `A` used in `yStep` are bounded by `M`. -/
theorem A_bounds {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 2 A) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ k, ‖iteratedFDeriv ℝ i A k‖ ≤ M) (k : ℝ × ℝ) :
    ‖A k‖ ≤ M ∧ ‖pd e₂ A k‖ ≤ M ∧ ‖pd e₂ (pd e₂ A) k‖ ≤ M ∧ ‖pd e₁ A k‖ ≤ M ∧
      ‖pd e₂ (pd e₁ A) k‖ ≤ M :=
  ⟨by simpa using hM 0 (by norm_num) k, (norm_pd_le e₂ norm_e₂ A k).trans (hM 1 (by norm_num) k),
    (norm_pd2_le hA norm_e₂ norm_e₂ k).trans (hM 2 (by norm_num) k),
    (norm_pd_le e₁ norm_e₁ A k).trans (hM 1 (by norm_num) k),
    (norm_pd2_le hA norm_e₁ norm_e₂ k).trans (hM 2 (by norm_num) k)⟩

/-- Bound for the derivative integrand of `F` by `yStep`. -/
theorem slice_F'_bound {Q : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {m μ b M D x γ c : ℝ} (hQ : ContDiff ℝ 4 Q)
    (hA : ContDiff ℝ 2 A) (hb : 0 < b) (hm : 0 < m) (hμ : 0 < μ) (hM0 : 0 ≤ M)
    (hc : c ∈ Icc (-(2 * b)) (2 * b)) (hqc : pd e₂ Q (x, c) = 0)
    (hlow : ∀ t ∈ Icc (-(2 * b)) (2 * b), μ ≤ |dd Q (x, t) e₂ e₂|)
    (hD : ∀ i ≤ 4, ∀ t ∈ Icc (-(2 * b)) (2 * b), ‖iteratedFDeriv ℝ i Q (x, t)‖ ≤ D)
    (hM : ∀ i ≤ 2, ∀ k, ‖iteratedFDeriv ℝ i A k‖ ≤ M)
    (ha0 : A (x, -(2 * b)) = 0) (haB : A (x, 2 * b) = 0) :
    ‖∫ t in (-(2 * b))..(2 * b), Complex.exp (((m * (Q (x, t) - γ) : ℝ) : ℂ) * I) *
        (((m * (pd e₁ Q (x, t) - pd e₁ Q (x, c)) : ℝ) : ℂ) * I * A (x, t) + pd e₁ A (x, t))‖ ≤
      8 / √(m * μ) * ((1 + 24 * beta D μ ^ 6) * M * (1 + 2 * (2 * b))) := by
  have c1 : ∀ v w u, ContDiff ℝ 1 (pd u (pd w (pd v Q))) := fun v w u =>
    contDiff_pd (n := 1) (contDiff_pd (n := 2) (contDiff_pd (n := 3) hQ v) w) u
  have dQ : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have d3 : ∀ v, Differentiable ℝ (pd v Q) := fun v => (contDiff_pd (n := 3) hQ v).differentiable (by norm_num)
  have d2 : ∀ v w, Differentiable ℝ (pd w (pd v Q)) := fun v w =>
    (contDiff_pd (n := 2) (contDiff_pd (n := 3) hQ v) w).differentiable (by norm_num)
  have d1 : ∀ v w u, Differentiable ℝ (pd u (pd w (pd v Q))) :=
    fun v w u => (c1 v w u).differentiable (by norm_num)
  have c0 : ∀ v w u u', Continuous (pd u' (pd u (pd w (pd v Q)))) :=
    fun v w u u' => (contDiff_pd (n := 0) (c1 v w u) u').continuous
  have cA1 : ∀ v, ContDiff ℝ 1 (pd v A) := fun v => contDiff_pd (n := 1) hA v
  have dA : Differentiable ℝ A := hA.differentiable (by norm_num)
  have dA1 : ∀ v, Differentiable ℝ (pd v A) := fun v => (cA1 v).differentiable (by norm_num)
  have cA0 : ∀ v w, Continuous (pd w (pd v A)) := fun v w => (contDiff_pd (n := 0) (cA1 v) w).continuous
  exact yStep (q := fun t => pd e₂ Q (x, t)) (q1 := fun t => pd e₂ (pd e₂ Q) (x, t))
    (q2 := fun t => pd e₂ (pd e₂ (pd e₂ Q)) (x, t)) (q3 := fun t => pd e₂ (pd e₂ (pd e₂ (pd e₂ Q))) (x, t))
    (p := fun t => pd e₁ Q (x, t)) (p1 := fun t => pd e₂ (pd e₁ Q) (x, t))
    (p2 := fun t => pd e₂ (pd e₂ (pd e₁ Q)) (x, t)) (p3 := fun t => pd e₂ (pd e₂ (pd e₂ (pd e₁ Q))) (x, t))
    (φ := fun t => m * (Q (x, t) - γ)) (a := fun t => A (x, t)) (a1 := fun t => pd e₂ A (x, t))
    (a2 := fun t => pd e₂ (pd e₂ A) (x, t)) (e := fun t => pd e₁ A (x, t))
    (e1 := fun t => pd e₂ (pd e₁ A) (x, t)) (by linarith) hm hμ hM0
    (fun t => hasDerivAt_slice2 (d3 e₂) x t) (fun t => hasDerivAt_slice2 (d2 e₂ e₂) x t)
    (fun t => hasDerivAt_slice2 (d1 e₂ e₂ e₂) x t) (by have := c0 e₂ e₂ e₂ e₂; fun_prop)
    (fun t => hasDerivAt_slice2 (d3 e₁) x t) (fun t => hasDerivAt_slice2 (d2 e₁ e₂) x t)
    (fun t => hasDerivAt_slice2 (d1 e₁ e₂ e₂) x t) (by have := c0 e₁ e₂ e₂ e₂; fun_prop)
    (fun t => ((hasDerivAt_slice2 dQ x t).sub_const γ).const_mul m)
    (fun t => hasDerivAt_slice2 dA x t) (fun t => hasDerivAt_slice2 (dA1 e₂) x t)
    (by have := cA0 e₂ e₂; fun_prop) (fun t => hasDerivAt_slice2 (dA1 e₁) x t)
    (by have := cA0 e₁ e₂; fun_prop) hc hqc hlow (slice_Q_bounds hQ hD) (fun t _ => A_bounds hA hM (x, t))
    ha0 haB

end Slices


section XStep

/-- Fubini on the rectangle: `I(mQ, A) = ∫_{-a}^{a} e^{im γ(x)} ∫_{-2b}^{2b} e^{im(Q(x,t) - γ(x))} A(x, t) dt dx`
for any `γ`, when `tsupport A ⊆ [-a, a] × [-b, b]`. -/
theorem oscInt2_eq_iterated {Q : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {a b m : ℝ} (γ : ℝ → ℝ)
    (hQ : Continuous Q) (hA : Continuous A) (hsupp : tsupport A ⊆ Icc (-a) a ×ˢ Icc (-b) b)
    (ha : 0 < a) (hb : 0 < b) :
    oscInt2 (fun k => m * Q k) A = ∫ x in (-a)..a, Complex.exp (((m * γ x : ℝ) : ℂ) * I) *
      ∫ t in (-(2 * b))..(2 * b), Complex.exp (((m * (Q (x, t) - γ x) : ℝ) : ℂ) * I) * A (x, t) := by
  have hcs : HasCompactSupport A :=
    IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) (isClosed_tsupport A) hsupp
  have hzero : ∀ x y, (x ∉ Icc (-a) a ∨ y ∉ Icc (-b) b) → A (x, y) = 0 := fun x y h =>
    image_eq_zero_of_notMem_tsupport fun hk => by
      have := hsupp hk; rcases h with h | h; exacts [h this.1, h this.2]
  have hint : Integrable (fun k : ℝ × ℝ => Complex.exp (((m * Q k : ℝ) : ℂ) * I) * A k)
      (volume.prod volume) := by
    have hc : Continuous fun k : ℝ × ℝ => Complex.exp (((m * Q k : ℝ) : ℂ) * I) * A k := by
      have : Continuous fun k => ((m * Q k : ℝ) : ℂ) := continuous_ofReal.comp (continuous_const.mul hQ)
      fun_prop
    exact hc.integrable_of_hasCompactSupport (hcs.mul_left (f := fun k => Complex.exp (((m * Q k : ℝ) : ℂ) * I)))
  unfold oscInt2
  rw [Measure.volume_eq_prod, integral_prod _ hint, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1; ext x
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_const_mul]
    · congr 1; ext y
      rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    · intro y hy
      rw [hzero x y (Or.inr fun h => hy ⟨by linarith [h.1], by linarith [h.2]⟩), mul_zero]
  · intro x hx
    simp [hzero x _ (Or.inl hx)]

theorem hasDerivAt_cexp_mul_I {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (((f x : ℝ) : ℂ) * I)) (Complex.exp (((f x : ℝ) : ℂ) * I) * ((f' : ℂ) * I)) x := by
  have h0 : HasDerivAt (fun y => ((f y : ℝ) : ℂ)) ((f' : ℝ) : ℂ) x := hf.ofReal_comp
  have h1 : HasDerivAt (fun y => ((f y : ℝ) : ℂ) * I) (((f' : ℝ) : ℂ) * I) x := h0.mul_const I
  exact h1.cexp

/-- Differentiation of the inner integral in `x` under the integral sign. -/
theorem hasDerivAt_inner {Q : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {γ ys : ℝ → ℝ} {m a lo hi x : ℝ}
    (hle : lo ≤ hi) (dQ : Differentiable ℝ Q) (cQ1 : Continuous (pd e₁ Q)) (dA : Differentiable ℝ A)
    (cA1 : Continuous (pd e₁ A)) (cγ : Continuous γ) (cys : Continuous ys)
    (hγ : ∀ x ∈ Ioo (-a) a, HasDerivAt γ (pd e₁ Q (x, ys x)) x) (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun x => ∫ t in lo..hi, Complex.exp (((m * (Q (x, t) - γ x) : ℝ) : ℂ) * I) * A (x, t))
      (∫ t in lo..hi, Complex.exp (((m * (Q (x, t) - γ x) : ℝ) : ℂ) * I) *
        (((m * (pd e₁ Q (x, t) - pd e₁ Q (x, ys x)) : ℝ) : ℂ) * I * A (x, t) + pd e₁ A (x, t))) x := by
  have cQ : Continuous Q := dQ.continuous
  have cA : Continuous A := dA.continuous
  set G : ℝ × ℝ → ℂ := fun z => Complex.exp (((m * (Q (z.1, z.2) - γ z.1) : ℝ) : ℂ) * I) *
    (((m * (pd e₁ Q (z.1, z.2) - pd e₁ Q (z.1, ys z.1)) : ℝ) : ℂ) * I * A (z.1, z.2) + pd e₁ A (z.1, z.2))
  have cG : Continuous G := by
    have h1 : Continuous fun z : ℝ × ℝ => ((m * (Q (z.1, z.2) - γ z.1) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    have h2 : Continuous fun z : ℝ × ℝ => ((m * (pd e₁ Q (z.1, z.2) - pd e₁ Q (z.1, ys z.1)) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    fun_prop
  have cF : Continuous fun z : ℝ × ℝ => Complex.exp (((m * (Q (z.1, z.2) - γ z.1) : ℝ) : ℂ) * I) * A (z.1, z.2) := by
    have h1 : Continuous fun z : ℝ × ℝ => ((m * (Q (z.1, z.2) - γ z.1) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    fun_prop
  obtain ⟨G0, hG0⟩ := (isCompact_Icc (a := -a) (b := a) |>.prod (isCompact_Icc (a := lo) (b := hi))).exists_bound_of_continuousOn
    cG.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := lo) (b := hi)
    (𝕜 := ℝ) (x₀ := x) (s := Ioo (-a) a) (bound := fun _ => G0)
    (F := fun x t => Complex.exp (((m * (Q (x, t) - γ x) : ℝ) : ℂ) * I) * A (x, t))
    (F' := fun x t => G (x, t)) (isOpen_Ioo.mem_nhds hx)
    (Filter.Eventually.of_forall fun z => (cF.comp (by fun_prop : Continuous fun t : ℝ => (z, t))).aestronglyMeasurable)
    ((cF.comp (by fun_prop : Continuous fun t : ℝ => (x, t))).intervalIntegrable _ _)
    ((cG.comp (by fun_prop : Continuous fun t : ℝ => (x, t))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht z hz => hG0 (z, t) ⟨Ioo_subset_Icc_self hz, by
      rw [uIoc_of_le hle] at ht; exact Ioc_subset_Icc_self ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ z hz => by
      have hψ : HasDerivAt (fun x => m * (Q (x, t) - γ x)) (m * (pd e₁ Q (z, t) - pd e₁ Q (z, ys z))) z :=
        ((hasDerivAt_slice1 dQ z t).sub (hγ z hz)).const_mul m
      exact ((hasDerivAt_cexp_mul_I hψ).mul (hasDerivAt_slice1 dA z t)).congr_deriv (by simp only [G]; ring))
  exact key.2

end XStep


section Phase

theorem hasDerivAt_iteratedDeriv_of_contDiffOn {f : ℝ → ℝ} {n : ℕ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) {i : ℕ} (hi : i < n) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (iteratedDeriv i f) (iteratedDeriv (i + 1) f x) x := by
  have hd := hf.differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hi) hU.uniqueDiffOn
  have hd' : DifferentiableOn ℝ (iteratedDeriv i f) U :=
    hd.congr fun y hy => (iteratedDerivWithin_of_isOpen hU hy).symm
  rw [iteratedDeriv_succ]
  exact (hd'.differentiableAt (hU.mem_nhds hx)).hasDerivAt

/-- Derivative of the reduced phase `g(x) = Q(x, ys x)` at a critical point of `Q(x, ·)`. -/
theorem hasDerivAt_reduced {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {x : ℝ} (dQ : Differentiable ℝ Q)
    (hys : DifferentiableAt ℝ ys x) (hcrit : pd e₂ Q (x, ys x) = 0) :
    HasDerivAt (fun x => Q (x, ys x)) (pd e₁ Q (x, ys x)) x := by
  have h1 : HasDerivAt (fun x => ((x, ys x) : ℝ × ℝ)) ((1 : ℝ), deriv ys x) x :=
    (hasDerivAt_id x).prodMk hys.hasDerivAt
  have := (dQ (x, ys x)).hasFDerivAt.comp_hasDerivAt x h1
  refine this.congr_deriv ?_
  have e : ((1 : ℝ), deriv ys x) = e₁ + deriv ys x • e₂ := by simp [e₁, e₂]
  rw [e, map_add, map_smul]
  simp only [pd] at hcrit ⊢
  rw [hcrit, smul_zero, add_zero]

/-- The clamped curve `ys (max (-a) (min a x))`: continuous, equal to `ys` on `[-a, a]`. -/
noncomputable def clamp (a : ℝ) (ys : ℝ → ℝ) (x : ℝ) : ℝ := ys (max (-a) (min a x))

theorem clamp_eq {a : ℝ} {ys : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (-a) a) : clamp a ys x = ys x := by
  unfold clamp; rw [min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_clamp {a : ℝ} (ha : 0 ≤ a) {ys : ℝ → ℝ} (hys : ContinuousOn ys (Icc (-a) a)) :
    Continuous (clamp a ys) :=
  hys.comp_continuous (by fun_prop) fun x => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

end Phase


section Reduction

theorem phase_facts {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {a m : ℝ} (hQ : ContDiff ℝ 4 Q)
    (hys : ContDiffOn ℝ 3 ys (Ioo (-2 * a) (2 * a))) (ha : 0 < a)
    (hcrit : ∀ x ∈ Icc (-a) a, pd e₂ Q (x, ys x) = 0) :
    Continuous (clamp a ys) ∧
    (∀ x ∈ Ioo (-a) a, HasDerivAt (fun x => Q (x, clamp a ys x)) (pd e₁ Q (x, clamp a ys x)) x) ∧
    HasDerivOn (fun x => m * Q (x, clamp a ys x)) (fun x => m * iteratedDeriv 1 (fun x => Q (x, ys x)) x)
      (-a) a ∧
    HasDerivOn (fun x => m * iteratedDeriv 1 (fun x => Q (x, ys x)) x)
      (fun x => m * iteratedDeriv 2 (fun x => Q (x, ys x)) x) (-a) a ∧
    HasDerivOn (fun x => m * iteratedDeriv 2 (fun x => Q (x, ys x)) x)
      (fun x => m * iteratedDeriv 3 (fun x => Q (x, ys x)) x) (-a) a := by
  have hsub : Icc (-a) a ⊆ Ioo (-2 * a) (2 * a) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have dQ : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have cys := continuous_clamp ha.le (hys.continuousOn.mono hsub)
  have hg : ContDiffOn ℝ 3 (fun x => Q (x, ys x)) (Ioo (-2 * a) (2 * a)) :=
    (hQ.of_le (by norm_num)).comp_contDiffOn (contDiffOn_id.prodMk hys)
  have hdg : ∀ i < 3, ∀ x ∈ Icc (-a) a, HasDerivAt (iteratedDeriv i (fun x => Q (x, ys x)))
      (iteratedDeriv (i + 1) (fun x => Q (x, ys x)) x) x := fun i hi x hx =>
    hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hg (by exact_mod_cast hi) (hsub hx)
  have heq : ∀ x ∈ Ioo (-a) a, (fun x => Q (x, clamp a ys x)) =ᶠ[nhds x] fun x => Q (x, ys x) :=
    fun x hx => Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun y hy => by
      simp only [clamp_eq (Ioo_subset_Icc_self hy)]
  have hd1 : ∀ x ∈ Icc (-a) a, DifferentiableAt ℝ ys x := fun x hx =>
    (hys.differentiableOn (by norm_num) x (hsub hx)).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
  have cont : ∀ i < 3, ContinuousOn (fun x => m * iteratedDeriv i (fun x => Q (x, ys x)) x) (Icc (-a) a) :=
    fun i hi x hx => ((hdg i hi x hx).continuousAt.const_mul m).continuousWithinAt
  refine ⟨cys, fun x hx => ?_, ⟨?_, fun x hx => ?_⟩, ⟨cont 1 (by norm_num), fun x hx => ?_⟩,
    ⟨cont 2 (by norm_num), fun x hx => ?_⟩⟩
  · rw [clamp_eq (Ioo_subset_Icc_self hx)]
    exact (hasDerivAt_reduced dQ (hd1 x (Ioo_subset_Icc_self hx))
      (hcrit x (Ioo_subset_Icc_self hx))).congr_of_eventuallyEq (heq x hx)
  · have : Continuous fun x => m * Q (x, clamp a ys x) := by fun_prop
    exact this.continuousOn
  · have := hdg 0 (by norm_num) x (Ioo_subset_Icc_self hx)
    rw [iteratedDeriv_zero] at this
    exact (this.congr_of_eventuallyEq (heq x hx)).const_mul m
  · exact (hdg 1 (by norm_num) x (Ioo_subset_Icc_self hx)).const_mul m
  · exact (hdg 2 (by norm_num) x (Ioo_subset_Icc_self hx)).const_mul m


/-- The inner integral `F(x) = ∫_{-2b}^{2b} e^{im(Q(x,t) - Q(x, y x))} A(x, t) dt`. -/
noncomputable def innerF (m b : ℝ) (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (y : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ t in (-(2 * b))..(2 * b), Complex.exp (((m * (Q (x, t) - Q (x, y x)) : ℝ) : ℂ) * I) * A (x, t)

/-- Its derivative in `x` when `y x` is a critical point of `Q(x, ·)`. -/
noncomputable def innerF' (m b : ℝ) (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (y : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ t in (-(2 * b))..(2 * b), Complex.exp (((m * (Q (x, t) - Q (x, y x)) : ℝ) : ℂ) * I) *
    (((m * (pd e₁ Q (x, t) - pd e₁ Q (x, y x)) : ℝ) : ℂ) * I * A (x, t) + pd e₁ A (x, t))

/-- Regularity of `F` (S1 amplitude hypothesis on `[-a, a]`) and `ampNorm F F' ≤ 8 (mμ)^{-1/2} (1 + 4b) M
(1 + 2a(1 + 24β⁶))`. -/
theorem amplitude_facts {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {A : ℝ × ℝ → ℂ} {a b m μ D M : ℝ}
    (hQ : ContDiff ℝ 4 Q) (hA : ContDiff ℝ 2 A) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hμ : 0 < μ)
    (hM0 : 0 ≤ M) (cys : Continuous (clamp a ys))
    (hγ : ∀ x ∈ Ioo (-a) a, HasDerivAt (fun x => Q (x, clamp a ys x)) (pd e₁ Q (x, clamp a ys x)) x)
    (hc : ∀ x ∈ Icc (-a) a, clamp a ys x ∈ Icc (-(2 * b)) (2 * b) ∧ pd e₂ Q (x, clamp a ys x) = 0)
    (hlow : ∀ x ∈ Icc (-a) a, ∀ t ∈ Icc (-(2 * b)) (2 * b), μ ≤ |dd Q (x, t) e₂ e₂|)
    (hD : ∀ i ≤ 4, ∀ x ∈ Icc (-a) a, ∀ t ∈ Icc (-(2 * b)) (2 * b), ‖iteratedFDeriv ℝ i Q (x, t)‖ ≤ D)
    (hM : ∀ i ≤ 2, ∀ k, ‖iteratedFDeriv ℝ i A k‖ ≤ M)
    (hsupp : tsupport A ⊆ Icc (-a) a ×ˢ Icc (-b) b) :
    AmplitudeOn (innerF m b Q A (clamp a ys)) (innerF' m b Q A (clamp a ys)) (-a) a ∧
    ampNorm (innerF m b Q A (clamp a ys)) (innerF' m b Q A (clamp a ys)) (-a) a ≤
      8 / √(m * μ) * ((1 + 4 * b) * M * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))) := by
  have dQ : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have cQ : Continuous Q := dQ.continuous
  have cQ1 : Continuous (pd e₁ Q) := (contDiff_pd (n := 3) hQ e₁).continuous
  have dA : Differentiable ℝ A := hA.differentiable (by norm_num)
  have cA : Continuous A := dA.continuous
  have cA1 : Continuous (pd e₁ A) := (contDiff_pd (n := 1) hA e₁).continuous
  have cγ : Continuous fun x => Q (x, clamp a ys x) := by fun_prop
  have hzero : ∀ x, ∀ y ∉ Icc (-b) b, A (x, y) = 0 := fun x y hy =>
    image_eq_zero_of_notMem_tsupport fun hk => hy (hsupp hk).2
  set F' := innerF' m b Q A (clamp a ys)
  have cF' : Continuous F' := by
    have h1 : Continuous fun z : ℝ × ℝ => ((m * (Q (z.1, z.2) - Q (z.1, clamp a ys z.1)) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    have h2 : Continuous fun z : ℝ × ℝ =>
        ((m * (pd e₁ Q (z.1, z.2) - pd e₁ Q (z.1, clamp a ys z.1)) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have cF : Continuous (innerF m b Q A (clamp a ys)) := by
    have h1 : Continuous fun z : ℝ × ℝ => ((m * (Q (z.1, z.2) - Q (z.1, clamp a ys z.1)) : ℝ) : ℂ) :=
      continuous_ofReal.comp (by fun_prop)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have hMA : ∀ k, ‖A k‖ ≤ M ∧ ‖pd e₂ A k‖ ≤ M := fun k =>
    ⟨by simpa using hM 0 (by norm_num) k, (norm_pd_le e₂ norm_e₂ A k).trans (hM 1 (by norm_num) k)⟩
  have hF'b : ∀ x ∈ Icc (-a) a, ‖F' x‖ ≤ 8 / √(m * μ) * ((1 + 24 * beta D μ ^ 6) * M * (1 + 2 * (2 * b))) :=
    fun x hx => slice_F'_bound hQ hA hb hm hμ hM0 (hc x hx).1 (hc x hx).2 (hlow x hx)
      (fun i hi t ht => hD i hi x hx t ht) hM (hzero x _ fun h => by linarith [h.1])
      (hzero x _ fun h => by linarith [h.2])
  refine ⟨⟨cF.continuousOn, fun x hx => hasDerivAt_inner (by linarith) dQ cQ1 dA cA1 cγ cys hγ hx,
    cF'.intervalIntegrable _ _⟩, ?_⟩
  unfold ampNorm
  have h1 := slice_F_bound (x := a) (γ := Q (a, clamp a ys a)) hQ hA hb hm hμ
    (hlow a ⟨by linarith, le_rfl⟩) hMA
  have h2 : ∫ x in (-a)..a, ‖F' x‖ ≤ ∫ _ in (-a)..a,
      8 / √(m * μ) * ((1 + 24 * beta D μ ^ 6) * M * (1 + 2 * (2 * b))) :=
    intervalIntegral.integral_mono_on (by linarith) (cF'.norm.intervalIntegrable _ _) intervalIntegrable_const
      hF'b
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  calc _ ≤ 8 / √(m * μ) * (M + (2 * b - -(2 * b)) * M) +
        (a - -a) * (8 / √(m * μ) * ((1 + 24 * beta D μ ^ 6) * M * (1 + 2 * (2 * b)))) := add_le_add h1 h2
    _ = _ := by ring


theorem arith2 {m μ ν : ℝ} (hm : 0 < m) (hμ : 0 < μ) (hν : 0 < ν) (P : ℝ) :
    8 / √(m * ν) * (8 / √(m * μ) * P) = 64 / (√ν * √μ) * P * m ^ (-(1 / 2 + 1 / ((2 : ℕ) : ℝ))) := by
  have e : -(1 / 2 + 1 / ((2 : ℕ) : ℝ)) = -1 := by norm_num
  rw [e, Real.rpow_neg_one, Real.sqrt_mul hm.le, Real.sqrt_mul hm.le]
  have hsm : 0 < √m := Real.sqrt_pos.2 hm
  have hsμ : 0 < √μ := Real.sqrt_pos.2 hμ
  have hsν : 0 < √ν := Real.sqrt_pos.2 hν
  have hmm : √m * √m = m := Real.mul_self_sqrt hm.le
  field_simp
  rw [Real.sq_sqrt hm.le]; ring

theorem arith3 {m μ ν : ℝ} (hm : 0 < m) (hμ : 0 < μ) (hν : 0 < ν) (P : ℝ) :
    18 * (m * ν) ^ (-(1 : ℝ) / 3) * (8 / √(m * μ) * P) =
      144 * ν ^ (-(1 : ℝ) / 3) / √μ * P * m ^ (-(1 / 2 + 1 / ((3 : ℕ) : ℝ))) := by
  have e : -(1 / 2 + 1 / ((3 : ℕ) : ℝ)) = -(1 / 2) + -(1 : ℝ) / 3 := by norm_num
  rw [e, Real.rpow_add hm, Real.mul_rpow hm.le hν.le, Real.sqrt_mul hm.le, Real.sqrt_eq_rpow m,
    Real.rpow_neg hm.le]
  have hsm : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm _
  have hsμ : 0 < √μ := Real.sqrt_pos.2 hμ
  field_simp
  ring

/-- The common reduction for `j = 2, 3`: `I(mQ, A)` is a one-dimensional oscillatory integral in `x` with
phase `m g`, amplitude `F(x) = ∫ e^{im(Q(x,t) - g(x))} A(x, t) dt` and `ampNorm F F' ≲ M (mμ)^{-1/2}`. -/
theorem core_reduction {j : ℕ} {a b μ ν D : ℝ} (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ)
    {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {A : ℝ × ℝ → ℂ} {M m : ℝ} (hC : Blueprint.CoreHyps j a b μ ν D Q ys)
    (hA : AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M) (hm : 1 ≤ m) :
    ∃ φ φ1 φ2 φ3 : ℝ → ℝ, ∃ F F' : ℝ → ℂ,
      oscInt2 (fun k => m * Q k) A = oscInt (fun x => φ x + 0 * x) F (-a) a ∧
      HasDerivOn φ φ1 (-a) a ∧ HasDerivOn φ1 φ2 (-a) a ∧ HasDerivOn φ2 φ3 (-a) a ∧
      (j = 2 → ∀ x ∈ Ioo (-a) a, m * ν ≤ |φ2 x|) ∧ (j = 3 → ∀ x ∈ Ioo (-a) a, m * ν ≤ |φ3 x|) ∧
      AmplitudeOn F F' (-a) a ∧
      ampNorm F F' (-a) a ≤ 8 / √(m * μ) * ((1 + 4 * b) * M * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))) := by
  obtain ⟨hQ, hys, hcrit, hlow, hD, -, hν⟩ := hC
  obtain ⟨hA2, hsupp, hM⟩ := hA
  have hm0 : 0 < m := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  have e2b : -2 * b = -(2 * b) := by ring
  rw [e2b] at hlow hD
  have hcrit' : ∀ x ∈ Icc (-a) a, pd e₂ Q (x, ys x) = 0 := fun x hx => (hcrit x hx).2
  obtain ⟨cys, hγ, h1, h2, h3⟩ := phase_facts (m := m) hQ hys ha hcrit'
  have hA2' : ContDiff ℝ 2 A := by exact_mod_cast hA2
  obtain ⟨hamp, hnorm⟩ := amplitude_facts (D := D) hQ hA2' ha hb hm0 hμ hM0 cys hγ
    (fun x hx => by
      rw [clamp_eq hx]
      exact ⟨⟨by linarith [(hcrit x hx).1.1], by linarith [(hcrit x hx).1.2]⟩, hcrit' x hx⟩)
    hlow (fun i hi x hx t ht => hD i hi x hx t ht) hM hsupp
  refine ⟨_, _, _, _, _, _, ?_, h1, h2, h3, ?_, ?_, hamp, hnorm⟩
  · rw [oscInt2_eq_iterated (fun x => Q (x, clamp a ys x)) (hQ.continuous) hA2'.continuous hsupp ha hb]
    simp only [oscInt, zero_mul, add_zero, innerF]
  · rintro rfl x hx
    rw [abs_mul, abs_of_pos hm0]
    exact mul_le_mul_of_nonneg_left (hν x (Ioo_subset_Icc_self hx)) hm0.le
  · rintro rfl x hx
    rw [abs_mul, abs_of_pos hm0]
    exact mul_le_mul_of_nonneg_left (hν x (Ioo_subset_Icc_self hx)) hm0.le

end Reduction

end OscInt.StationaryPhase.CoreAux

namespace OscInt.StationaryPhase

open CoreAux

/-- **L6** The core estimate: `|I(mQ, A)| ≤ C M m^{-(1/2 + 1/j)}` for `j ∈ {2, 3}`, with `C` depending only on
`(a, b, μ, ν, D)`. -/
theorem coreEstimate : OscInt.Blueprint.CoreEstimateFacts := by
  intro j hj a b μ ν D ha hb hμ hν
  set Y := (1 + 4 * b) * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))
  rcases hj with rfl | rfl
  · refine ⟨64 / (√ν * √μ) * Y, fun Q ys A M m hC hA hm => ?_⟩
    have hm0 : 0 < m := by linarith
    obtain ⟨φ, φ1, φ2, φ3, F, F', he, h1, h2, -, hν2, -, hamp, hnorm⟩ :=
      core_reduction ha hb hμ hC hA hm
    rw [he]
    refine (OscInt.vanDerCorput_two φ φ1 φ2 F F' (-a) a (m * ν) 0 (by linarith) (by positivity) h1 h2
      (hν2 rfl) hamp).trans ?_
    refine (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_)
    rw [arith2 hm0 hμ hν]; ring
  · refine ⟨144 * ν ^ (-(1 : ℝ) / 3) / √μ * Y, fun Q ys A M m hC hA hm => ?_⟩
    have hm0 : 0 < m := by linarith
    obtain ⟨φ, φ1, φ2, φ3, F, F', he, h1, h2, h3, -, hν3, hamp, hnorm⟩ :=
      core_reduction ha hb hμ hC hA hm
    rw [he]
    refine (OscInt.vanDerCorput_three φ φ1 φ2 φ3 F F' (-a) a (m * ν) 0 (by linarith) (by positivity) h1 h2 h3
      (hν3 rfl) hamp).trans ?_
    refine (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_)
    rw [arith3 hm0 hμ hν]; ring

end OscInt.StationaryPhase
