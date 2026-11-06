import Blueprint.D4LimitS42

/-!
# S4.2, part E1b: polar reduction

`polarReduction : OscInt.Blueprint.PolarReductionFacts`. For an even continuous cut-off `χ` vanishing outside the
max-norm ball of radius `K₀`:
* evenness: `w ↦ −w` (`integral_neg_eq_self`) and `C(−w) = −C(w)` give `2∫e^{iC}χ_R = ∫(e^{iC} + e^{−iC})χ_R`,
  so the integral is the real number `∫ cos(C(w)) χ(R⁻¹w) dw`;
* polar coordinates (`integral_comp_polarCoord_symm`, target `Ioi 0 ×ˢ Ioo (−π) π`), truncation of `r` at `2K₀R`
  (`‖rω‖ ≥ r/2` in the max norm, since `max(|cos θ|, |sin θ|) ≥ 1/2`), Fubini with `θ` outer
  (`setIntegral_prod_swap`, `setIntegral_prod`, continuity on a compact box), and `C(rω) = r³ circleCubic q θ`.

Route: `docs/proof-S42.md` (E1b) and `review/2026-11-06-S42-proof-route.md` §3.
-/

namespace OscInt.D4.PolarAux

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

theorem cubicForm_neg (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : cubicForm q (-z) = -cubicForm q z := by
  simp only [cubicForm, Prod.fst_neg, Prod.snd_neg]; ring

theorem cubicForm_polar (q : ℝ × ℝ × ℝ × ℝ) (r θ : ℝ) :
    cubicForm q (r * Real.cos θ, r * Real.sin θ) = r ^ 3 * circleCubic q θ := by
  simp only [circleCubic, cubicForm]; ring

theorem half_le_abs_or (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : 1 / 2 ≤ |a| ∨ 1 / 2 ≤ |b| := by
  by_contra hc
  push Not at hc
  have h1 : a ^ 2 < 1 / 4 := by nlinarith [abs_nonneg a, sq_abs a]
  have h2 : b ^ 2 < 1 / 4 := by nlinarith [abs_nonneg b, sq_abs b]
  linarith

/-- The cut-off vanishes at radius `r ≥ 2K₀R` in every direction. -/
theorem chi_polar_eq_zero (χ : ℝ × ℝ → ℝ) (K₀ : ℝ) (hK : 0 < K₀) (hχ : ∀ z, K₀ ≤ ‖z‖ → χ z = 0)
    (R : ℝ) (hR : 0 < R) (r θ : ℝ) (hr : 2 * K₀ * R ≤ r) :
    χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) = 0 := by
  apply hχ
  have hr0 : 0 ≤ R⁻¹ * r := mul_nonneg (inv_nonneg.2 hR.le) (by nlinarith [mul_pos hK hR])
  have hRr : 2 * K₀ ≤ R⁻¹ * r := by
    rw [le_inv_mul_iff₀ hR]; linarith
  rcases half_le_abs_or (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ) with h | h
  · refine le_trans ?_ (norm_fst_le _)
    simp only [Prod.smul_fst, smul_eq_mul, Real.norm_eq_abs, abs_mul, ← mul_assoc,
      abs_of_nonneg hr0]
    nlinarith
  · refine le_trans ?_ (norm_snd_le _)
    simp only [Prod.smul_snd, smul_eq_mul, Real.norm_eq_abs, abs_mul, ← mul_assoc,
      abs_of_nonneg hr0]
    nlinarith


/-- The rescaled cut-off is supported in the max-norm ball of radius `K₀R`. -/
theorem hasCompactSupport_scaled (χ : ℝ × ℝ → ℝ) (K₀ : ℝ) (hχ : ∀ z, K₀ ≤ ‖z‖ → χ z = 0)
    (R : ℝ) (hR : 0 < R) : HasCompactSupport (fun w : ℝ × ℝ => χ (R⁻¹ • w)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (R * K₀)) fun w hw => hχ _ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]
  exact hw.le

theorem exp_add_exp_neg (x : ℝ) :
    Complex.exp (↑x * Complex.I) + Complex.exp (↑(-x) * Complex.I) = 2 * ((Real.cos x : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  ring

/-- Evenness: the integral is real, `∫ cos(C(w)) χ(R⁻¹w) dw`. -/
theorem oscInt2_eq_cos (q : ℝ × ℝ × ℝ × ℝ) (χ : ℝ × ℝ → ℝ) (hc : Continuous χ) (he : ∀ z, χ (-z) = χ z)
    (K₀ : ℝ) (hχ : ∀ z, K₀ ≤ ‖z‖ → χ z = 0) (R : ℝ) (hR : 0 < R) :
    oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ)) =
      (((∫ w, Real.cos (cubicForm q w) * χ (R⁻¹ • w)) : ℝ) : ℂ) := by
  set F : ℝ × ℝ → ℂ := fun w => Complex.exp (↑(cubicForm q w) * Complex.I) * ((χ (R⁻¹ • w) : ℝ) : ℂ)
  have hCc : Continuous (cubicForm q) := by unfold cubicForm; fun_prop
  have hFc : Continuous F := by
    have : Continuous fun w : ℝ × ℝ => χ (R⁻¹ • w) := hc.comp (continuous_const_smul _)
    fun_prop
  have hFs : HasCompactSupport F :=
    (hasCompactSupport_scaled χ K₀ hχ R hR).comp_left (g := fun x : ℝ => ((x : ℝ) : ℂ))
      Complex.ofReal_zero |>.mul_left
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hneg : ∫ w, F (-w) = ∫ w, F w := integral_neg_eq_self F volume
  have hsum : ∀ w, F w + F (-w) = 2 * (((Real.cos (cubicForm q w) * χ (R⁻¹ • w)) : ℝ) : ℂ) := by
    intro w
    simp only [F, cubicForm_neg, smul_neg, he]
    rw [← add_mul, exp_add_exp_neg]; push_cast; ring
  have h2 : 2 * oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ)) =
      2 * (((∫ w, Real.cos (cubicForm q w) * χ (R⁻¹ • w)) : ℝ) : ℂ) := by
    calc 2 * oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ))
        = (∫ w, F w) + ∫ w, F (-w) := by rw [hneg, two_mul]; rfl
      _ = ∫ w, (F w + F (-w)) := (integral_add hFi hFi.comp_neg).symm
      _ = _ := by simp_rw [hsum]; rw [integral_const_mul, integral_complex_ofReal]
  exact mul_left_cancel₀ two_ne_zero h2


/-- Polar coordinates, `θ` outer, for a continuous `G` vanishing at radius `≥ ρ`. -/
theorem integral_polar (G : ℝ × ℝ → ℝ) (hG : Continuous G) (ρ : ℝ) (hρ : 0 < ρ)
    (h0 : ∀ r θ, ρ ≤ r → G (r * Real.cos θ, r * Real.sin θ) = 0) :
    ∫ w, G w = ∫ θ in (-Real.pi)..Real.pi, ∫ r in (0 : ℝ)..ρ,
      r * G (r * Real.cos θ, r * Real.sin θ) := by
  rw [← integral_comp_polarCoord_symm]
  simp only [polarCoord_symm_apply, smul_eq_mul, polarCoord_target]
  set H : ℝ × ℝ → ℝ := fun p => p.1 * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2) with hHdef
  have hH : Continuous H := by
    have : Continuous fun p : ℝ × ℝ => (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by fun_prop
    exact continuous_fst.mul (hG.comp this)
  change ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, H p = _
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioo 0 ρ ×ˢ Ioo (-Real.pi) Real.pi)
    (measurableSet_Ioi.prod measurableSet_Ioo) (prod_mono Ioo_subset_Ioi_self subset_rfl)]
  swap
  · rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    have : ρ ≤ r := by
      by_contra hc
      exact hn ⟨⟨hr, lt_of_not_ge hc⟩, hθ⟩
    simp only [hHdef, h0 r θ this, mul_zero]
  have hint : IntegrableOn (fun z : ℝ × ℝ => H z.swap) (Ioo (-Real.pi) Real.pi ×ˢ Ioo 0 ρ)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hH.comp continuous_swap).continuousOn).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _ hint,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  rw [intervalIntegral.integral_of_le hρ.le, integral_Ioc_eq_integral_Ioo]
  rfl

end OscInt.D4.PolarAux

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint OscInt.D4.PolarAux

/-- **E1b** Polar reduction: the integral is real and equals the iterated polar integral, `θ ∈ (−π, π)` outer,
`r ≤ 2K₀R` inner. -/
theorem polarReduction : PolarReductionFacts := by
  intro q χ hc he K₀ hK hχ R hR
  rw [oscInt2_eq_cos q χ hc he K₀ hχ R hR]
  congr 1
  have hCc : Continuous (cubicForm q) := by unfold cubicForm; fun_prop
  have hG : Continuous fun w : ℝ × ℝ => Real.cos (cubicForm q w) * χ (R⁻¹ • w) :=
    (Real.continuous_cos.comp hCc).mul (hc.comp (continuous_const_smul _))
  rw [integral_polar _ hG (2 * K₀ * R) (by positivity)
    (fun r θ hr => by simp only [chi_polar_eq_zero χ K₀ hK hχ R hR r θ hr, mul_zero])]
  refine intervalIntegral.integral_congr fun θ _ => intervalIntegral.integral_congr fun r _ => ?_
  simp only [cubicForm_polar]
  ring

end OscInt.D4

