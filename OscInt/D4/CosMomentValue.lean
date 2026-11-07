import Blueprint.D4ClosedForm

/-!
# S4.4, part E1: the cosine moment `∫₀^∞ cos u · u^{-1/3} du = Γ(2/3)/2`

`OscInt.D4.cosMomentValue : BetaIoiFacts → CosMomentValueFacts`, route `docs/proof-S44.md`, E1 (with its revision 3).
1. `u^{-1/3} Γ(1/3) = ∫₀^∞ s^{-2/3} e^{-us} ds` (`Real.integral_rpow_mul_exp_neg_mul_Ioi`).
2. Fubini on `(0, R] × (0, ∞)`: `Γ(1/3) · cosMomentPartial R = ∫₀^∞ s^{-2/3} h_R(s) ds` with
   `h_R(s) = (s + e^{-Rs}(sin R − s cos R))/(1 + s²)` (fundamental theorem of calculus).
3. Dominated convergence as `R → ∞` with the bound `s^{-2/3}(2s + 1)/(1 + s²)`.
4. The limit `∫₀^∞ s^{1/3}/(1 + s²) ds = Γ(2/3)Γ(1/3)/2` by `t = s²` and the Beta integral E6a (hypothesis).
5. `limUnder` of the partial integrals is `Γ(2/3)/2`.
-/

namespace OscInt.D4.CosMomentValueAux

open Set MeasureTheory Filter Topology OscInt.Statements

/-- Gamma representation: `∫₀^∞ s^{-2/3} e^{-us} ds = u^{-1/3} Γ(1/3)` for `u > 0`. -/
theorem integral_gammaRep {u : ℝ} (hu : 0 < u) :
    ∫ s in Ioi (0 : ℝ), s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s)) =
      u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 3) (r := u) (by norm_num) hu
  have e : (1 : ℝ) / 3 - 1 = -(2 : ℝ) / 3 := by norm_num
  rw [e] at h
  rw [h, one_div, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
  congr 2
  ring

theorem gamma_third_pos : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)

theorem integrableOn_gammaRep {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun s => s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaRep hu]
  exact (mul_pos (Real.rpow_pos_of_pos hu _) gamma_third_pos).ne'

/-- The antiderivative: `∫₀^R cos u e^{-us} du = (s + e^{-Rs}(sin R − s cos R))/(1 + s²)`. -/
theorem integral_cos_mul_exp (s R : ℝ) :
    ∫ u in (0 : ℝ)..R, Real.cos u * Real.exp (-(u * s)) =
      (s + Real.exp (-(R * s)) * (Real.sin R - s * Real.cos R)) / (1 + s ^ 2) := by
  have hs : (1 + s ^ 2) ≠ 0 := by positivity
  have hd : ∀ x ∈ uIcc 0 R, HasDerivAt
      (fun u => Real.exp (-(u * s)) * (Real.sin u - s * Real.cos u) / (1 + s ^ 2))
      (Real.cos x * Real.exp (-(x * s))) x := by
    intro x _
    have h1 : HasDerivAt (fun u => -(u * s)) (-(1 * s)) x := ((hasDerivAt_id x).mul_const s).neg
    have h2 := (h1.exp.fun_mul ((Real.hasDerivAt_sin x).fun_sub
      ((Real.hasDerivAt_cos x).const_mul s))).div_const (1 + s ^ 2)
    convert h2 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring


/-- The absolute integrand of the Fubini step is integrable on `(0, R] × (0, ∞)`. -/
theorem integrable_fubini (R : ℝ) :
    Integrable (Function.uncurry fun u s : ℝ =>
        Real.cos u * (s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s))))
      ((volume.restrict (Ioc 0 R)).prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (Function.uncurry fun u s : ℝ =>
      Real.cos u * (s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s)))) := by
    unfold Function.uncurry; fun_prop
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (integrableOn_gammaRep hu.1).const_mul (Real.cos u)
  · have hI : IntegrableOn (fun u : ℝ => u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3)) (Ioc 0 R) := by
      rcases le_total 0 R with hR | hR
      · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).mul_const _
      · simp [Ioc_eq_empty_of_le hR]
    refine hI.mono' ?_ ?_
    · exact hm.aestronglyMeasurable.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have : ∫ s in Ioi (0 : ℝ), ‖Function.uncurry (fun u s : ℝ =>
          Real.cos u * (s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s)))) (u, s)‖ =
          |Real.cos u| * (u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3)) := by
        rw [← integral_gammaRep hu.1, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs, Real.abs_exp,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) _)]
      rw [this, Real.norm_eq_abs, abs_of_nonneg (by
        have := (mul_pos (Real.rpow_pos_of_pos hu.1 (-(1 : ℝ) / 3)) gamma_third_pos).le
        positivity)]
      have h0 : 0 ≤ u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3) :=
        (mul_pos (Real.rpow_pos_of_pos hu.1 _) gamma_third_pos).le
      calc |Real.cos u| * (u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3))
          ≤ 1 * (u ^ (-(1 : ℝ) / 3) * Real.Gamma (1 / 3)) :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one u) h0
        _ = _ := one_mul _

/-- Fubini: `Γ(1/3) ∫₀^R cos u u^{-1/3} du = ∫₀^∞ s^{-2/3} h_R(s) ds`. -/
theorem gamma_mul_cosMomentPartial {R : ℝ} (hR : 0 ≤ R) :
    Real.Gamma (1 / 3) * cosMomentPartial R =
      ∫ s in Ioi (0 : ℝ), s ^ (-(2 : ℝ) / 3) *
        ((s + Real.exp (-(R * s)) * (Real.sin R - s * Real.cos R)) / (1 + s ^ 2)) := by
  calc Real.Gamma (1 / 3) * cosMomentPartial R
      = ∫ u in Ioc 0 R, ∫ s in Ioi (0 : ℝ),
          Real.cos u * (s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s))) := by
        rw [cosMomentPartial, intervalIntegral.integral_of_le hR, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
        rw [integral_const_mul, integral_gammaRep hu.1]
        ring
    _ = ∫ s in Ioi (0 : ℝ), ∫ u in Ioc 0 R,
          Real.cos u * (s ^ (-(2 : ℝ) / 3) * Real.exp (-(u * s))) :=
        integral_integral_swap (integrable_fubini R)
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
        rw [← integral_cos_mul_exp, intervalIntegral.integral_of_le hR, ← integral_const_mul]
        congr 1
        ext u
        ring


/-- Arithmetic: `|s + E (x − s y)| ≤ 2s + 1` for `0 ≤ E ≤ 1`, `|x|, |y| ≤ 1`, `s ≥ 0`. -/
theorem abs_hR_num_le {s E x y : ℝ} (hs : 0 ≤ s) (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |s + E * (x - s * y)| ≤ 2 * s + 1 := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have h1 : s * y ≤ s := by nlinarith
  have h2 : -s ≤ s * y := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The dominating function `s^{-2/3}(2s + 1)/(1 + s²)`. -/
noncomputable def bound (s : ℝ) : ℝ := s ^ (-(2 : ℝ) / 3) * ((2 * s + 1) / (1 + s ^ 2))

theorem integrableOn_bound : IntegrableOn bound (Ioi 0) := by
  have hm : Measurable bound := by unfold bound; fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hI : IntegrableOn (fun s : ℝ => 2 * s ^ (-(2 : ℝ) / 3)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _
    refine hI.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hp := Real.rpow_pos_of_pos hs.1 (-(2 : ℝ) / 3)
    have hq : (2 * s + 1) / (1 + s ^ 2) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (s - 1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold bound; have := hs.1; positivity), bound]
    nlinarith
  · have hI : IntegrableOn (fun s : ℝ => 3 * s ^ (-(5 : ℝ) / 3)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    refine hI.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := zero_lt_one.trans hs
    have hp := Real.rpow_pos_of_pos hs0 (-(2 : ℝ) / 3)
    have e : s ^ (-(5 : ℝ) / 3) = s ^ (-(2 : ℝ) / 3) * (1 / s) := by
      rw [show -(5 : ℝ) / 3 = -(2 : ℝ) / 3 - 1 by norm_num, Real.rpow_sub_one hs0.ne']
      ring
    have hq : (2 * s + 1) / (1 + s ^ 2) ≤ 3 * (1 / s) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold bound; positivity), bound, e]
    nlinarith

/-- Dominated convergence as `R → ∞`. -/
theorem tendsto_integral_hR :
    Tendsto (fun R : ℝ => ∫ s in Ioi (0 : ℝ), s ^ (-(2 : ℝ) / 3) *
        ((s + Real.exp (-(R * s)) * (Real.sin R - s * Real.cos R)) / (1 + s ^ 2))) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), s ^ (-(2 : ℝ) / 3) * (s / (1 + s ^ 2)))) := by
  refine tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun R => (by fun_prop : Measurable _).aestronglyMeasurable) ?_
    integrableOn_bound ?_
  · filter_upwards [eventually_ge_atTop 0] with R hR
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hE1 : Real.exp (-(R * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hnum := abs_hR_num_le hs0.le (Real.exp_pos _).le hE1 (Real.abs_sin_le_one R)
      (Real.abs_cos_le_one R)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hs0 _),
      abs_of_pos (by positivity : (0 : ℝ) < 1 + s ^ 2), bound]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hexp : Tendsto (fun R : ℝ => Real.exp (-(R * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hs0))
    have hprod : Tendsto (fun R : ℝ => Real.exp (-(R * s)) * (Real.sin R - s * Real.cos R))
        atTop (𝓝 0) := by
      have h0 := hexp.mul_const (1 + s)
      rw [zero_mul] at h0
      refine squeeze_zero_norm (fun R => ?_) h0
      rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [Real.norm_eq_abs]
      calc |Real.sin R - s * Real.cos R| ≤ |Real.sin R| + |s * Real.cos R| := abs_sub _ _
        _ ≤ 1 + s := by
          rw [abs_mul, abs_of_pos hs0]
          gcongr
          · exact Real.abs_sin_le_one R
          · nlinarith [Real.abs_cos_le_one R]
    have := ((hprod.const_add s).div_const (1 + s ^ 2)).const_mul (s ^ (-(2 : ℝ) / 3))
    simpa using this


/-- `∫₀^∞ s^{-2/3} · s/(1 + s²) ds = Γ(2/3)Γ(1/3)/2` (substitution `t = s²` and E6a). -/
theorem integral_limit (hB : OscInt.Blueprint.BetaIoiFacts) :
    ∫ s in Ioi (0 : ℝ), s ^ (-(2 : ℝ) / 3) * (s / (1 + s ^ 2)) =
      Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / 2 := by
  have hsub := integral_comp_rpow_Ioi_of_pos (p := 2) (g := fun t : ℝ =>
    (1 / 2) * (t ^ ((2 : ℝ) / 3 - 1) * (1 + t) ^ (-((2 : ℝ) / 3 + 1 / 3)))) two_pos
  rw [integral_const_mul, hB _ _ (by norm_num) (by norm_num),
    show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.Gamma_one] at hsub
  rw [show Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / 2 =
    1 / 2 * (Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / 1) by ring, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, ← Real.rpow_mul hx0.le,
    Real.rpow_neg_one, Real.rpow_two,
    show (2 : ℝ) * (2 / 3 - 1) = -(2 : ℝ) / 3 by norm_num]
  field_simp

end OscInt.D4.CosMomentValueAux

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.D4.CosMomentValueAux

/-- **E1** `cosMoment = Γ(2/3)/2`, given the Beta integral E6a. -/
theorem cosMomentValue (hB : OscInt.Blueprint.BetaIoiFacts) :
    OscInt.Blueprint.CosMomentValueFacts := by
  have hG := gamma_third_pos
  have h1 : Tendsto (fun R => Real.Gamma (1 / 3) * cosMomentPartial R) atTop
      (𝓝 (Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / 2)) := by
    rw [← integral_limit hB]
    refine tendsto_integral_hR.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact (gamma_mul_cosMomentPartial hR).symm
  have h2 := h1.const_mul (Real.Gamma (1 / 3))⁻¹
  have e : (Real.Gamma (1 / 3))⁻¹ * (Real.Gamma (2 / 3) * Real.Gamma (1 / 3) / 2) =
      Real.Gamma (2 / 3) / 2 := by field_simp
  rw [e] at h2
  simp only [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul] at h2
  exact h2.limUnder_eq

end OscInt.D4
