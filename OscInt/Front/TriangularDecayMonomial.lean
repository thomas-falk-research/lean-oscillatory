/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay

/-!
# Batch K2, parts P10a and P10b: monomial asymptotics (`MonomialPositivityFacts`, `MonomialTailFacts`)

Route: `docs/proof-K2.md`, section 3 (with section 8, N2). Both parts rest on one integration by parts against
`d/dx e^{isx^m} = i s m x^{m−1} e^{isx^m}` on `[a, R]`, `0 < a` (`ibp_bound`).

* P10a. Convergence of `∫₀^R e^{isx^m}` (s = ±1) by the Cauchy criterion from `‖∫_a^R e^{isx^m}‖ ≤ 2/(m a^{m−1})`.
  The lower bound on the real part is proved directly in x, not by the route's substitution `y = x^m` and
  half-period pairing: with `a^m = 2`, `∫₀^a cos(x^m) ≥ ∫₀^a (1 − x^{2m}/2) = a(1 − 2/(2m+1))` and the tail from `a`
  has norm at most `2/(m a^{m−1}) = a/m`, so every partial integral has real part at least
  `1 − 2/(2m+1) − 1/m ≥ 1/(24m)`. The symmetric integral is the sum of two half-line integrals with signs
  `σ` and `σ(−1)^m`.
* P10b. Scaling `x ↦ t^{1/m} x`, then on each side `[r, R]` the integration by parts gives exactly
  `2/(m t r^{m−1})` (b monotone from 1 to 0, `(m − 1)∫_r^R x^{−m} = r^{1−m} − R^{1−m}`), and a limit in R.
-/

namespace OscInt.K2.MonomialPositivityAux

open Set MeasureTheory Filter Topology
open intervalIntegral (integral_congr integral_mul_deriv_eq_deriv_mul)

/-- The phase `e^{i s x^n}`. -/
noncomputable def E (s : ℝ) (n : ℕ) (x : ℝ) : ℂ := Complex.exp (↑(s * x ^ n) * Complex.I)

lemma norm_E (s : ℝ) (n : ℕ) (x : ℝ) : ‖E s n x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma continuous_E (s : ℝ) (n : ℕ) : Continuous (E s n) := by
  unfold E; fun_prop

lemma hasDerivAt_E (s : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (E s (k + 2)) (E s (k + 2) x * (↑(s * ((k + 2 : ℕ) * x ^ (k + 1))) * Complex.I)) x := by
  have h1 : HasDerivAt (fun y : ℝ => s * y ^ (k + 2)) (s * ((k + 2 : ℕ) * x ^ (k + 1))) x := by
    simpa using (hasDerivAt_pow (k + 2) x).const_mul s
  exact (h1.ofReal_comp.mul_const Complex.I).cexp

/-- One integration by parts on `[a, R]`, `0 < a`, with the norm bound it gives. -/
lemma ibp_bound (k : ℕ) (s : ℝ) (hs : s ≠ 0) (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ‖∫ x in a..R, (g x : ℂ) * E s (k + 2) x‖ ≤
      (|g R| / R ^ (k + 1) + |g a| / a ^ (k + 1) +
        ∫ x in a..R, |g' x / x ^ (k + 1) - (k + 1) * g x / x ^ (k + 2)|) / (|s| * (k + 2)) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hpos : ∀ x ∈ uIcc a R, 0 < x := by
    intro x hx; rw [uIcc_of_le haR] at hx; exact lt_of_lt_of_le ha hx.1
  set ψ' : ℝ → ℝ := fun x => g' x / x ^ (k + 1) - (k + 1) * g x / x ^ (k + 2) with hψ'
  set c : ℂ := (s : ℂ)⁻¹ * ((k : ℂ) + 2)⁻¹ * (-Complex.I) with hc
  have hcn : ‖c‖ = 1 / (|s| * (k + 2)) := by
    have : (k : ℂ) + 2 = ((k + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, this, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, norm_neg,
      Complex.norm_I, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < k + 2)]
    field_simp
  set u : ℝ → ℂ := fun x => ((g x / x ^ (k + 1) : ℝ) : ℂ) * c with hu
  set u' : ℝ → ℂ := fun x => ((ψ' x : ℝ) : ℂ) * c with hu'
  set v' : ℝ → ℂ := fun x => E s (k + 2) x * (↑(s * ((k + 2 : ℕ) * x ^ (k + 1))) * Complex.I) with hv'
  have hdu : ∀ x ∈ uIcc a R, HasDerivAt u (u' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    have h1 := ((hg x).div (hasDerivAt_pow (k + 1) x) (pow_ne_zero _ hx0)).ofReal_comp.mul_const c
    refine h1.congr_deriv ?_
    simp only [hu', hψ']
    congr 2
    field_simp
    push_cast
    ring
  have hdv : ∀ x ∈ uIcc a R, HasDerivAt (E s (k + 2)) (v' x) x := fun x _ => hasDerivAt_E s k x
  have hψc : ContinuousOn ψ' (uIcc a R) := by
    apply ContinuousOn.sub
    · exact hg'.continuousOn.div (by fun_prop) fun x hx => pow_ne_zero _ (hpos x hx).ne'
    · exact (by fun_prop : Continuous fun x => ((k : ℝ) + 1) * g x).continuousOn.div (by fun_prop)
        fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hu'i : IntervalIntegrable u' volume a R :=
    ((Complex.continuous_ofReal.comp_continuousOn hψc).mul continuousOn_const).intervalIntegrable
  have hv'i : IntervalIntegrable v' volume a R := by
    apply Continuous.intervalIntegrable
    simp only [hv']
    have := continuous_E s (k + 2)
    fun_prop
  have hibp := integral_mul_deriv_eq_deriv_mul hdu hdv hu'i hv'i
  have hcongr : ∫ x in a..R, (g x : ℂ) * E s (k + 2) x = ∫ x in a..R, u x * v' x := by
    apply integral_congr
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    have hkC : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (by positivity : (k : ℝ) + 2 ≠ 0)
    have key : u x * v' x = ↑(g x) * E s (k + 2) x * ((s : ℂ) * (s : ℂ)⁻¹) * (((k : ℂ) + 2) * ((k : ℂ) + 2)⁻¹) *
        ((x : ℂ) ^ (k + 1) * ((x : ℂ) ^ (k + 1))⁻¹) * (-(Complex.I * Complex.I)) := by
      simp only [hu, hv', hc]; push_cast; ring
    show ↑(g x) * E s (k + 2) x = u x * v' x
    rw [key, mul_inv_cancel₀ hsC, mul_inv_cancel₀ hkC, mul_inv_cancel₀ (pow_ne_zero _ hxC), Complex.I_mul_I]
    ring
  rw [hcongr, hibp]
  have hnu : ∀ x, ‖u x * E s (k + 2) x‖ = |g x| / |x ^ (k + 1)| * ‖c‖ := by
    intro x
    simp only [hu, norm_mul, norm_E, Complex.norm_real, Real.norm_eq_abs, abs_div, mul_one]
  have hint : ‖∫ x in a..R, u' x * E s (k + 2) x‖ ≤ (∫ x in a..R, |ψ' x|) * ‖c‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm haR).trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_mul_const]
    apply integral_congr
    intro x _
    simp only [hu', norm_mul, norm_E, Complex.norm_real, Real.norm_eq_abs, mul_one]
  have hR0 : 0 < R := lt_of_lt_of_le ha haR
  calc ‖u R * E s (k + 2) R - u a * E s (k + 2) a - ∫ x in a..R, u' x * E s (k + 2) x‖
      ≤ ‖u R * E s (k + 2) R‖ + ‖u a * E s (k + 2) a‖ + ‖∫ x in a..R, u' x * E s (k + 2) x‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ (|g R| / R ^ (k + 1) + |g a| / a ^ (k + 1) + ∫ x in a..R, |ψ' x|) * ‖c‖ := by
        rw [hnu, hnu, abs_of_pos (pow_pos hR0 _), abs_of_pos (pow_pos ha _)]
        nlinarith [hint]
    _ = _ := by rw [hcn]; ring

lemma hasDerivAt_neg_inv_pow (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / y ^ (k + 1))) ((k + 1) / x ^ (k + 2)) x := by
  have h := ((hasDerivAt_pow (k + 1) x).inv (pow_ne_zero _ hx)).neg
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [one_div])
  field_simp
  push_cast
  ring

/-- `∫_a^R (k+1)/x^{k+2} = a^{-(k+1)} − R^{-(k+1)}`. -/
lemma integral_inv_pow (k : ℕ) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ∫ x in a..R, ((k : ℝ) + 1) / x ^ (k + 2) = 1 / a ^ (k + 1) - 1 / R ^ (k + 1) := by
  have hpos : ∀ x ∈ uIcc a R, 0 < x := by
    intro x hx; rw [uIcc_of_le haR] at hx; exact lt_of_lt_of_le ha hx.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => -(1 / y ^ (k + 1)))
    (fun x hx => hasDerivAt_neg_inv_pow k (hpos x hx).ne')]
  · ring
  · exact (continuousOn_const.div (by fun_prop) fun x hx => pow_ne_zero _ (hpos x hx).ne').intervalIntegrable

/-- The tail from `a` of the plain phase. -/
lemma tail_one (k : ℕ) (s : ℝ) (hs : s ≠ 0) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    ‖∫ x in a..R, E s (k + 2) x‖ ≤ 2 / (a ^ (k + 1) * (|s| * (k + 2))) := by
  have h := ibp_bound k s hs (fun _ => 1) (fun _ => 0) (fun x => hasDerivAt_const x 1) continuous_const ha haR
  simp only [Complex.ofReal_one, one_mul, abs_one] at h
  have hpos : ∀ x ∈ uIcc a R, 0 < x := by
    intro x hx; rw [uIcc_of_le haR] at hx; exact lt_of_lt_of_le ha hx.1
  have hi : ∫ x in a..R, |0 / x ^ (k + 1) - (k + 1) * 1 / x ^ (k + 2)| = 1 / a ^ (k + 1) - 1 / R ^ (k + 1) := by
    rw [← integral_inv_pow k ha haR]
    apply integral_congr
    intro x hx
    have := hpos x hx
    simp only
    rw [zero_div, zero_sub, mul_one, abs_neg, abs_of_pos (by positivity)]
  rw [hi] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

lemma abs_sign {s : ℝ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with rfl | rfl <;> simp

lemma tail_small (k : ℕ) {s : ℝ} (hs : s = 1 ∨ s = -1) {a R : ℝ} (ha : 1 ≤ a) (haR : a ≤ R) :
    ‖∫ x in a..R, E s (k + 2) x‖ ≤ 2 / a := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine (tail_one k s hs0 (by linarith) haR).trans ?_
  rw [abs_sign hs, one_mul]
  have h1 : a ≤ a ^ (k + 1) := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ (k + 1) := pow_le_pow_right₀ ha (by omega)
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
  nlinarith [(by positivity : (0 : ℝ) ≤ k)]

/-- The half-line integral `∫₀^R e^{isx^m}` converges, with real part at least `1/(24m)` in the limit. -/
lemma half_line (k : ℕ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ L : ℂ, Tendsto (fun R => ∫ x in (0 : ℝ)..R, E s (k + 2) x) atTop (𝓝 L) ∧
      1 / (24 * ((k : ℝ) + 2)) ≤ L.re := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hii : ∀ a b : ℝ, IntervalIntegrable (E s (k + 2)) volume a b :=
    fun a b => (continuous_E s (k + 2)).intervalIntegrable a b
  set F : ℝ → ℂ := fun R => ∫ x in (0 : ℝ)..R, E s (k + 2) x with hF
  -- Cauchy criterion
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    refine ⟨max 1 (4 / ε), fun p hp q hq => ?_⟩
    have hp1 : 1 ≤ p := le_trans (le_max_left _ _) hp
    have hq1 : 1 ≤ q := le_trans (le_max_left _ _) hq
    have hsmall : ∀ x, max 1 (4 / ε) ≤ x → 2 / x < ε := by
      intro x hx
      have hx4 : 4 / ε ≤ x := le_trans (le_max_right _ _) hx
      have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hx)
      rw [div_lt_iff₀ hx0]
      rw [div_le_iff₀ hε] at hx4
      linarith
    rw [dist_eq_norm, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
    rcases le_total q p with hqp | hpq
    · exact lt_of_le_of_lt (tail_small k hs hq1 hqp) (hsmall q hq)
    · rw [intervalIntegral.integral_symm, norm_neg]
      exact lt_of_le_of_lt (tail_small k hs hp1 hpq) (hsmall p hp)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, hL, ?_⟩
  -- the lower bound
  set a : ℝ := (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ)⁻¹) with ha_def
  have ha1 : 1 ≤ a := Real.one_le_rpow (by norm_num) (by positivity)
  have ham : a ^ (k + 2) = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have ha0 : 0 < a := by linarith
  have hak : a ^ (k + 1) = 2 / a := by
    rw [eq_div_iff ha0.ne', ← pow_succ]; exact ham
  have hmain : a * (1 - 2 / (2 * k + 5)) ≤ (∫ x in (0 : ℝ)..a, E s (k + 2) x).re := by
    have hre : (∫ x in (0 : ℝ)..a, E s (k + 2) x).re = ∫ x in (0 : ℝ)..a, Real.cos (s * x ^ (k + 2)) := by
      rw [← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re (hii 0 a)]
      apply integral_congr
      intro x _
      simp only [E, RCLike.re_to_complex]; exact Complex.exp_ofReal_mul_I_re _
    rw [hre]
    have hlow : ∫ x in (0 : ℝ)..a, (1 - x ^ (2 * (k + 2)) / 2) ≤ ∫ x in (0 : ℝ)..a, Real.cos (s * x ^ (k + 2)) := by
      apply intervalIntegral.integral_mono_on ha0.le
      · exact (by fun_prop : Continuous fun x : ℝ => 1 - x ^ (2 * (k + 2)) / 2).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun x : ℝ => Real.cos (s * x ^ (k + 2))).intervalIntegrable _ _
      intro x _
      have := Real.one_sub_sq_div_two_le_cos (x := s * x ^ (k + 2))
      have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      calc 1 - x ^ (2 * (k + 2)) / 2 = 1 - (s * x ^ (k + 2)) ^ 2 / 2 := by rw [mul_pow, hs2, ← pow_mul]; ring
        _ ≤ _ := this
    refine le_trans (le_of_eq ?_) hlow
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => x ^ (2 * (k + 2)) / 2).intervalIntegrable _ _),
      intervalIntegral.integral_div, integral_pow, intervalIntegral.integral_const]
    have : a ^ (2 * (k + 2) + 1) = 4 * a := by rw [pow_succ, pow_mul', ham]; ring
    rw [this]
    simp only [smul_eq_mul, sub_zero, mul_one]
    push_cast
    field_simp
    ring
  have hlower : ∀ R, a ≤ R → 1 / (24 * ((k : ℝ) + 2)) ≤ (F R).re := by
    intro R haR
    have hsplit : F R = (∫ x in (0 : ℝ)..a, E s (k + 2) x) + ∫ x in a..R, E s (k + 2) x :=
      (intervalIntegral.integral_add_adjacent_intervals (hii 0 a) (hii a R)).symm
    have htail := tail_one k s hs0 ha0 haR
    rw [abs_sign hs, one_mul, hak] at htail
    have hre_tail : -(2 / (2 / a * (k + 2))) ≤ (∫ x in a..R, E s (k + 2) x).re := by
      have := Complex.abs_re_le_norm (∫ x in a..R, E s (k + 2) x)
      have := neg_abs_le (∫ x in a..R, E s (k + 2) x).re
      linarith
    have heq : 2 / (2 / a * (k + 2)) = a / (k + 2) := by field_simp
    rw [heq] at hre_tail
    rw [hsplit, Complex.add_re]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hD : 1 / (24 * ((k : ℝ) + 2)) ≤ 1 - 2 / (2 * k + 5) - 1 / (k + 2) := by
      rw [div_le_iff₀ (by positivity)]
      have e1 : 2 / (2 * (k : ℝ) + 5) * (24 * (k + 2)) = 48 * (k + 2) / (2 * k + 5) := by ring
      have e2 : 1 / ((k : ℝ) + 2) * (24 * (k + 2)) = 24 := by field_simp
      rw [sub_mul, sub_mul, e1, e2, one_mul]
      rw [show (24 : ℝ) * (k + 2) - 48 * (k + 2) / (2 * k + 5) - 24 = (24 * k + 48 - 24) - 48 * (k + 2) / (2 * k + 5)
        by ring]
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
      nlinarith
    have hDpos : 0 ≤ 1 - 2 / (2 * (k : ℝ) + 5) - 1 / (k + 2) := le_trans (by positivity) hD
    have : 1 - 2 / (2 * (k : ℝ) + 5) - 1 / (k + 2) ≤ a * (1 - 2 / (2 * k + 5)) - a / (k + 2) := by
      have : a * (1 - 2 / (2 * k + 5)) - a / (k + 2) = a * (1 - 2 / (2 * (k : ℝ) + 5) - 1 / (k + 2)) := by ring
      rw [this]
      nlinarith
    linarith
  exact ge_of_tendsto ((Complex.continuous_re.tendsto L).comp hL)
    ((eventually_ge_atTop a).mono fun R hR => hlower R hR)

end OscInt.K2.MonomialPositivityAux

namespace OscInt.K2

open Set MeasureTheory Filter Topology OscInt.K2.MonomialPositivityAux

/-- **P10a** (`MonomialPositivityFacts`). -/
theorem monomialPositivity : OscInt.Blueprint.K2.MonomialPositivityFacts := by
  intro m σ hm hσ
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  set σ' : ℝ := σ * (-1) ^ (k + 2) with hσ'_def
  have hσ' : σ' = 1 ∨ σ' = -1 := by
    rcases neg_one_pow_eq_or ℝ (k + 2) with h | h <;> rcases hσ with rfl | rfl <;> simp [hσ'_def, h]
  obtain ⟨L₁, h₁, hr₁⟩ := half_line k hσ
  obtain ⟨L₂, h₂, hr₂⟩ := half_line k hσ'
  refine ⟨L₁ + L₂, ?_, ?_⟩
  · rw [Complex.add_re]
    have : 1 / (12 * ((k + 2 : ℕ) : ℝ)) = 2 * (1 / (24 * ((k : ℝ) + 2))) := by push_cast; field_simp; ring
    rw [this]; linarith
  · have hfun : (fun R : ℝ => ∫ x in -R..R, Complex.exp (↑(σ * x ^ (k + 2)) * Complex.I)) =
        fun R => (∫ x in (0 : ℝ)..R, E σ (k + 2) x) + ∫ x in (0 : ℝ)..R, E σ' (k + 2) x := by
      funext R
      have hii : ∀ a b : ℝ, IntervalIntegrable (E σ (k + 2)) volume a b :=
        fun a b => (continuous_E σ (k + 2)).intervalIntegrable a b
      change ∫ x in -R..R, E σ (k + 2) x = _
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-R) 0) (hii 0 R), add_comm]
      congr 1
      rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [E, hσ'_def, neg_pow x]
      congr 3
      ring
    rw [hfun]
    exact h₁.add h₂

end OscInt.K2

namespace OscInt.K2.MonomialTailAux

open Set MeasureTheory Filter Topology OscInt.K2.MonomialPositivityAux

/-- One side of the cutoff remainder: `‖∫_r^R (b − 1) e^{isx^m}‖ ≤ 2/(|s| m r^{m−1})`. -/
lemma tail_cutoff (k : ℕ) (s : ℝ) (hs : s ≠ 0) (b b' : ℝ → ℝ) (hb : ∀ x, HasDerivAt b (b' x) x)
    (hb' : Continuous b') {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hbr : b r = 1)
    (hneg : ∀ x ∈ Icc r R, b' x ≤ 0) (hab : ∀ x ∈ Icc r R, |b x - 1| ≤ 1) (hbR : 0 ≤ b R) :
    ‖∫ x in r..R, ((b x - 1 : ℝ) : ℂ) * E s (k + 2) x‖ ≤ 2 / (r ^ (k + 1) * (|s| * (k + 2))) := by
  have h := ibp_bound k s hs (fun x => b x - 1) b' (fun x => (hb x).sub_const 1) hb' hr hrR
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have hpos : ∀ x ∈ uIcc r R, 0 < x := by
    intro x hx; rw [uIcc_of_le hrR] at hx; exact lt_of_lt_of_le hr hx.1
  have hpt : ∀ x ∈ Icc r R, |b' x / x ^ (k + 1) - (k + 1) * (b x - 1) / x ^ (k + 2)| ≤
      -b' x / r ^ (k + 1) + (k + 1) / x ^ (k + 2) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr hx.1
    refine (abs_sub _ _).trans ?_
    have e1 : |b' x / x ^ (k + 1)| ≤ -b' x / r ^ (k + 1) := by
      rw [abs_div, abs_of_nonpos (hneg x hx), abs_of_pos (pow_pos hx0 _)]
      exact div_le_div_of_nonneg_left (by linarith [hneg x hx]) (pow_pos hr _) (pow_le_pow_left₀ hr.le hx.1 _)
    have e2 : |(k + 1) * (b x - 1) / x ^ (k + 2)| ≤ (k + 1) / x ^ (k + 2) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < k + 1), abs_of_pos (pow_pos hx0 _)]
      apply div_le_div_of_nonneg_right _ (pow_pos hx0 _).le
      have := hab x hx
      have hk : (0 : ℝ) < k + 1 := by positivity
      nlinarith
    linarith
  have hcont1 : ContinuousOn (fun x => |b' x / x ^ (k + 1) - (k + 1) * (b x - 1) / x ^ (k + 2)|) (uIcc r R) := by
    apply ContinuousOn.abs
    apply ContinuousOn.sub
    · exact hb'.continuousOn.div (by fun_prop) fun x hx => pow_ne_zero _ (hpos x hx).ne'
    · exact (by fun_prop : Continuous fun x => ((k : ℝ) + 1) * (b x - 1)).continuousOn.div (by fun_prop)
        fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hcont2 : ContinuousOn (fun x => ((k : ℝ) + 1) / x ^ (k + 2)) (uIcc r R) :=
    continuousOn_const.div (by fun_prop) fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hcont3 : Continuous fun x => -b' x / r ^ (k + 1) := by fun_prop
  have hint := intervalIntegral.integral_mono_on (μ := volume) hrR hcont1.intervalIntegrable
    ((hcont3.intervalIntegrable r R).add hcont2.intervalIntegrable) hpt
  have hval : ∫ x in r..R, (-b' x / r ^ (k + 1) + ((k : ℝ) + 1) / x ^ (k + 2)) =
      (b r - b R) / r ^ (k + 1) + (1 / r ^ (k + 1) - 1 / R ^ (k + 1)) := by
    rw [intervalIntegral.integral_add (hcont3.intervalIntegrable r R) hcont2.intervalIntegrable,
      intervalIntegral.integral_div, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hb x) (hb'.intervalIntegrable _ _),
      integral_inv_pow k hr hrR]
    ring
  rw [hval] at hint
  simp only [hbr, sub_self, abs_zero, zero_div, add_zero] at h
  have hRb : |b R - 1| / R ^ (k + 1) ≤ 1 / R ^ (k + 1) :=
    div_le_div_of_nonneg_right (hab R ⟨hrR, le_rfl⟩) (pow_pos (lt_of_lt_of_le hr hrR) _).le
  refine h.trans ?_
  rw [show 2 / (r ^ (k + 1) * (|s| * (k + 2))) = (2 / r ^ (k + 1)) / (|s| * (k + 2)) by rw [div_div]]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ b R / r ^ (k + 1) := div_nonneg hbR (pow_pos hr _).le
  have e : (b r - b R) / r ^ (k + 1) = 1 / r ^ (k + 1) - b R / r ^ (k + 1) := by rw [hbr]; ring
  rw [e] at hint
  have e2 : 2 / r ^ (k + 1) = 1 / r ^ (k + 1) + 1 / r ^ (k + 1) := by ring
  linarith

end OscInt.K2.MonomialTailAux

namespace OscInt.K2

open Set MeasureTheory Filter Topology OscInt.K2.MonomialPositivityAux OscInt.K2.MonomialTailAux

/-- **P10b** (`MonomialTailFacts`). -/
theorem monomialTail : OscInt.Blueprint.K2.MonomialTailFacts := by
  intro m σ C b r t hm hσ hC hb ht
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨hb1, hbcs, hr, heven, hone, hanti⟩ := hb
  obtain ⟨hdiff, hcont⟩ := contDiff_one_iff_deriv.1 hb1
  have hbd : ∀ x, HasDerivAt b (deriv b x) x := fun x => (hdiff x).hasDerivAt
  have hbc : Continuous b := hdiff.continuous
  obtain ⟨R₀, hR₀, hsupp⟩ := hbcs.exists_pos_le_norm
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  -- the cutoff on `[0, ∞)`
  have hb_le : ∀ x, 0 ≤ x → b x ≤ 1 := by
    intro x hx
    have h := hanti (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) (show x ∈ Ici 0 from hx) hx
    rwa [hone 0 (by simp [hr.le])] at h
  have hb_nn : ∀ x, 0 ≤ x → 0 ≤ b x := by
    intro x hx
    have hy : 0 ≤ max x R₀ := le_trans hx (le_max_left _ _)
    have h0 : b (max x R₀) = 0 := hsupp _ (by
      rw [Real.norm_eq_abs, abs_of_nonneg hy]; exact le_max_right _ _)
    have h := hanti (show x ∈ Ici 0 from hx) (show max x R₀ ∈ Ici 0 from hy) (le_max_left _ _)
    linarith
  have habs : ∀ x, 0 ≤ x → |b x - 1| ≤ 1 := fun x hx =>
    abs_le.2 ⟨by linarith [hb_nn x hx], by linarith [hb_le x hx]⟩
  have hneg : ∀ x, 0 < x → deriv b x ≤ 0 := by
    intro x hx
    rw [← derivWithin_of_isOpen isOpen_Ioi hx]
    exact (hanti.mono Ioi_subset_Ici_self).derivWithin_nonpos
  have hbr : b r = 1 := hone r (by rw [abs_of_pos hr])
  -- scaling `x ↦ t^{1/m} x`
  set lam : ℝ := t ^ (((k + 2 : ℕ) : ℝ)⁻¹) with hlam_def
  have hlam : 0 < lam := Real.rpow_pos_of_pos ht _
  have hlamm : lam ^ (k + 2) = t := Real.rpow_inv_natCast_pow ht.le (by omega)
  have hpow : t ^ (-(1 : ℝ) / ((k + 2 : ℕ) : ℝ)) = lam⁻¹ := by
    rw [neg_div, Real.rpow_neg ht.le, one_div]
  rw [hpow]
  have hG : Tendsto (fun R : ℝ => ∫ x in -R..R, E (t * σ) (k + 2) x) atTop (𝓝 (((lam⁻¹ : ℝ) : ℂ) * C)) := by
    have hfun : (fun R : ℝ => ∫ x in -R..R, E (t * σ) (k + 2) x) = fun R => (lam⁻¹ : ℝ) •
        (fun R : ℝ => ∫ x in -R..R, Complex.exp (↑(σ * x ^ (k + 2)) * Complex.I)) (lam * R) := by
      funext R
      have h2 := intervalIntegral.integral_comp_mul_left (a := -R) (b := R)
        (fun y => Complex.exp (↑(σ * y ^ (k + 2)) * Complex.I)) hlam.ne'
      rw [mul_neg] at h2
      rw [← h2]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [E]
      congr 3
      rw [mul_pow, hlamm]; ring
    rw [hfun]
    have := (hC.comp (tendsto_id.const_mul_atTop hlam)).const_smul (lam⁻¹)
    simpa only [Function.comp_def, id, Complex.real_smul] using this
  have hii : ∀ (s : ℝ) (a c : ℝ), IntervalIntegrable (E s (k + 2)) volume a c :=
    fun s a c => (continuous_E s (k + 2)).intervalIntegrable a c
  have hbound : ∀ R, max R₀ r ≤ R → ‖(∫ x, (b x : ℂ) * E (t * σ) (k + 2) x) -
      ∫ x in -R..R, E (t * σ) (k + 2) x‖ ≤ 4 / (((k + 2 : ℕ) : ℝ) * t * r ^ (k + 2 - 1)) := by
    intro R hR
    have hR0 : R₀ ≤ R := le_trans (le_max_left _ _) hR
    have hrR : r ≤ R := le_trans (le_max_right _ _) hR
    have hfull : ∫ x, (b x : ℂ) * E (t * σ) (k + 2) x = ∫ x in -R..R, (b x : ℂ) * E (t * σ) (k + 2) x := by
      rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      have hx' : R ≤ |x| := by
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with hx | hx
        · exact le_abs.2 (Or.inr (by linarith))
        · exact le_abs.2 (Or.inl hx.le)
      rw [hsupp x (by rw [Real.norm_eq_abs]; linarith), Complex.ofReal_zero, zero_mul]
    set h : ℝ → ℂ := fun x => ((b x - 1 : ℝ) : ℂ) * E (t * σ) (k + 2) x with hh
    have hhc : Continuous h := by
      have := continuous_E (t * σ) (k + 2)
      simp only [hh]; fun_prop
    have hbE : Continuous fun x => (b x : ℂ) * E (t * σ) (k + 2) x := by
      have := continuous_E (t * σ) (k + 2)
      fun_prop
    rw [hfull, ← intervalIntegral.integral_sub (hbE.intervalIntegrable _ _) (hii _ _ _)]
    have hsub : ∫ x in -R..R, ((b x : ℂ) * E (t * σ) (k + 2) x - E (t * σ) (k + 2) x) = ∫ x in -R..R, h x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hh]; push_cast; ring
    rw [hsub, ← intervalIntegral.integral_add_adjacent_intervals (hhc.intervalIntegrable (-R) (-r))
      (hhc.intervalIntegrable (-r) R), ← intervalIntegral.integral_add_adjacent_intervals
      (hhc.intervalIntegrable (-r) r) (hhc.intervalIntegrable r R)]
    have hmid : ∫ x in -r..r, h x = 0 := by
      rw [← intervalIntegral.integral_zero (a := -r) (b := r) (μ := volume) (E := ℂ)]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      simp only [hh, hone x (abs_le.2 ⟨hx.1, hx.2⟩), sub_self, Complex.ofReal_zero, zero_mul]
    set σ' : ℝ := t * σ * (-1) ^ (k + 2) with hσ'
    have hleft : ∫ x in -R..-r, h x = ∫ x in r..R, ((b x - 1 : ℝ) : ℂ) * E σ' (k + 2) x := by
      rw [← intervalIntegral.integral_comp_neg]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hh, heven, E, hσ', neg_pow x]
      congr 4
      ring
    rw [hmid, zero_add, hleft]
    have habs' : ∀ x ∈ Icc r R, |b x - 1| ≤ 1 := fun x hx => habs x (by linarith [hx.1])
    have hneg' : ∀ x ∈ Icc r R, deriv b x ≤ 0 := fun x hx => hneg x (by linarith [hx.1])
    have hσ'0 : σ' ≠ 0 := by
      rw [hσ']; exact mul_ne_zero (mul_ne_zero ht.ne' hσ0) (pow_ne_zero _ (by norm_num))
    have hA := tail_cutoff k σ' hσ'0 b (deriv b) hbd hcont hr hrR hbr hneg' habs' (hb_nn R (by linarith))
    have hB := tail_cutoff k (t * σ) (mul_ne_zero ht.ne' hσ0) b (deriv b) hbd hcont hr hrR hbr hneg' habs'
      (hb_nn R (by linarith))
    have hs1 : |t * σ| = t := by rw [abs_mul, abs_sign hσ, abs_of_pos ht, mul_one]
    have hs2 : |σ'| = t := by
      rw [hσ', abs_mul, hs1, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    rw [hs1] at hB
    rw [hs2] at hA
    have hk : k + 2 - 1 = k + 1 := by omega
    rw [hk]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add hA hB).trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  show ‖(∫ x, (b x : ℂ) * E (t * σ) (k + 2) x) - _‖ ≤ _
  exact le_of_tendsto ((tendsto_const_nhds.sub hG).norm) ((eventually_ge_atTop (max R₀ r)).mono hbound)

end OscInt.K2

