import Blueprint.D4Limit

/-!
# S4.3, parts C1 and C2: the cosine moment after one integration by parts

Route `docs/proof-S43.md` (with its route-referee revision).

* `OscInt.D4.cosIBP` (C1): for `R > 0`,
  `∫₀^R cos u · u^{-1/3} du = R^{-1/3} sin R + (1/3) ∫₀^R sin u · u^{-4/3} du`, by the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) for `f u = sin u · u^{-1/3}`, which is continuous on
  `[0, R]` (`|f u| ≤ u^{2/3}`, and `f 0 = 0` in Lean) and differentiable on `(0, R)`; both integrands are dominated
  by `u^{-1/3}` near `0`.
* `OscInt.D4.sinMoment` (C2): `sin u · u^{-4/3}` is integrable on `(0, ∞)` (dominated by `u^{-1/3}` on `(0, 1]` and
  by `u^{-4/3}` on `(1, ∞)`), so `∫₀^R` tends to `S = ∫_{(0,∞)}`. Positivity without any Gamma identity: on each
  period `[2nπ, 2nπ + 2π]` the shift `u ↦ u + π` turns the integral into
  `∫_{2nπ}^{2nπ+π} sin u · (u^{-4/3} - (u + π)^{-4/3}) du > 0`, so `n ↦ ∫₀^{2nπ}` increases and
  `S ≥ ∫₀^{2π} > 0`.
-/

namespace OscInt.D4.CosMomentAux

open Set MeasureTheory Filter Topology

/-- The sine integrand `sin u · u^{-4/3}`. -/
noncomputable def sinInt (u : ℝ) : ℝ := Real.sin u * u ^ (-(4 : ℝ) / 3)

theorem integrableOn_rpow_neg_third_Ioc (R : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ (-(1 : ℝ) / 3)) (Ioc 0 R) := by
  rcases le_total 0 R with hR | hR
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  · simp [Ioc_eq_empty_of_le hR]

theorem rpow_mul_self (u : ℝ) (hu : 0 < u) (p : ℝ) : u * u ^ p = u ^ (1 + p) := by
  rw [Real.rpow_add hu, Real.rpow_one]

theorem abs_sinInt_le {u : ℝ} (hu : 0 < u) : |sinInt u| ≤ u ^ (-(1 : ℝ) / 3) := by
  unfold sinInt
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.le _)]
  calc |Real.sin u| * u ^ (-(4 : ℝ) / 3) ≤ u * u ^ (-(4 : ℝ) / 3) := by
        gcongr; simpa [abs_of_pos hu] using Real.abs_sin_le_abs (x := u)
    _ = u ^ (-(1 : ℝ) / 3) := by rw [rpow_mul_self u hu]; norm_num

theorem measurable_sinInt : Measurable sinInt :=
  Real.continuous_sin.measurable.mul (measurable_id.pow_const _)

theorem integrableOn_sinInt_Ioc (R : ℝ) : IntegrableOn sinInt (Ioc 0 R) := by
  refine Integrable.mono' (integrableOn_rpow_neg_third_Ioc R)
    measurable_sinInt.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs]; exact abs_sinInt_le hu.1

theorem integrableOn_sinInt_Ioi_one : IntegrableOn sinInt (Ioi 1) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -(4 : ℝ) / 3) (by norm_num) one_pos)
    measurable_sinInt.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  rw [Real.norm_eq_abs, sinInt, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  calc |Real.sin u| * u ^ (-(4 : ℝ) / 3) ≤ 1 * u ^ (-(4 : ℝ) / 3) := by
        gcongr; exact Real.abs_sin_le_one u
    _ = u ^ (-(4 : ℝ) / 3) := one_mul _

theorem integrableOn_sinInt_Ioi : IntegrableOn sinInt (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_sinInt_Ioc 1).union integrableOn_sinInt_Ioi_one

theorem intervalIntegrable_sinInt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable sinInt volume a b := by
  rw [intervalIntegrable_iff]
  exact integrableOn_sinInt_Ioi.mono_set fun x hx => lt_of_le_of_lt (le_min ha hb) hx.1

theorem intervalIntegrable_cos_mul_rpow (R : ℝ) (hR : 0 ≤ R) :
    IntervalIntegrable (fun u : ℝ => Real.cos u * u ^ (-(1 : ℝ) / 3)) volume 0 R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
  refine Integrable.mono' (integrableOn_rpow_neg_third_Ioc R)
    (Real.continuous_cos.measurable.mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.1.le _)]
  calc |Real.cos u| * u ^ (-(1 : ℝ) / 3) ≤ 1 * u ^ (-(1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one u) (Real.rpow_nonneg hu.1.le _)
    _ = u ^ (-(1 : ℝ) / 3) := one_mul _

/-- `sin u · u^{-1/3}` is continuous on `[0, ∞)` (at `0` because `|sin u · u^{-1/3}| ≤ u^{2/3}`). -/
theorem continuousOn_sin_mul_rpow :
    ContinuousOn (fun u : ℝ => Real.sin u * u ^ (-(1 : ℝ) / 3)) (Ici 0) := by
  intro u hu
  rcases (mem_Ici.1 hu).eq_or_lt with h0 | hpos
  · subst h0
    have hb : Tendsto (fun v : ℝ => v ^ ((2 : ℝ) / 3)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 ((2 : ℝ) / 3) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at this
      exact this.mono_left nhdsWithin_le_nhds
    show Tendsto _ _ (𝓝 (Real.sin 0 * (0 : ℝ) ^ (-(1 : ℝ) / 3)))
    rw [Real.sin_zero, zero_mul]
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with v hv
    rcases (mem_Ici.1 hv).eq_or_lt with hv0 | hv0
    · subst hv0; simp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
    calc |Real.sin v| * v ^ (-(1 : ℝ) / 3) ≤ v * v ^ (-(1 : ℝ) / 3) := by
          gcongr; simpa [abs_of_pos hv0] using Real.abs_sin_le_abs (x := v)
      _ = v ^ ((2 : ℝ) / 3) := by rw [rpow_mul_self v hv0]; norm_num
  · exact (Real.continuous_sin.continuousAt.mul
      (Real.continuousAt_rpow_const u _ (Or.inl hpos.ne'))).continuousWithinAt

theorem hasDerivAt_sin_mul_rpow {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => Real.sin u * u ^ (-(1 : ℝ) / 3))
      (Real.cos u * u ^ (-(1 : ℝ) / 3) - (1 / 3) * sinInt u) u := by
  have h := (Real.hasDerivAt_sin u).mul (Real.hasDerivAt_rpow_const (p := -(1 : ℝ) / 3) (Or.inl hu.ne'))
  convert h using 1
  unfold sinInt
  have : -(1 : ℝ) / 3 - 1 = -(4 : ℝ) / 3 := by norm_num
  rw [this]; ring

/-- `∫₀^x sin u · u^{-4/3} du`. -/
noncomputable def sinPartial (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, sinInt u

/-- The pointwise pairing of the two humps: positive on `(2nπ, 2nπ + π)`. -/
theorem sinInt_add_sinInt_add_pi_pos (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (n * (2 * Real.pi)) (n * (2 * Real.pi) + Real.pi)) :
    0 < sinInt x + sinInt (x + Real.pi) := by
  have hn : (0 : ℝ) ≤ n * (2 * Real.pi) := by positivity
  have hx0 : 0 < x := lt_of_le_of_lt hn hx.1
  have hs : 0 < Real.sin x := by
    rw [← Real.sin_sub_nat_mul_two_pi x n]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have hr : (x + Real.pi) ^ (-(4 : ℝ) / 3) < x ^ (-(4 : ℝ) / 3) :=
    Real.rpow_lt_rpow_of_neg hx0 (by linarith [Real.pi_pos]) (by norm_num)
  unfold sinInt
  rw [Real.sin_add_pi]
  nlinarith

/-- The integral over one period `[2nπ, 2nπ + 2π]` is positive. -/
theorem integral_period_pos (n : ℕ) :
    0 < ∫ u in (n * (2 * Real.pi))..(n * (2 * Real.pi) + 2 * Real.pi), sinInt u := by
  set a : ℝ := n * (2 * Real.pi) with ha_def
  have ha : 0 ≤ a := by positivity
  have hpi := Real.pi_pos
  have h1 : IntervalIntegrable sinInt volume a (a + Real.pi) :=
    intervalIntegrable_sinInt ha (by linarith)
  have h2 : IntervalIntegrable sinInt volume (a + Real.pi) (a + Real.pi + Real.pi) :=
    intervalIntegrable_sinInt (by linarith) (by linarith)
  have h2' : IntervalIntegrable (fun u => sinInt (u + Real.pi)) volume a (a + Real.pi) := by
    have := h2.comp_add_right Real.pi
    simpa using this
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [← intervalIntegral.integral_comp_add_right sinInt Real.pi,
    ← intervalIntegral.integral_add h1 h2'] at hsplit
  have he : a + Real.pi + Real.pi = a + 2 * Real.pi := by ring
  rw [he] at hsplit
  rw [← hsplit]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (h1.add h2')
    (fun x hx => sinInt_add_sinInt_add_pi_pos n hx) (by linarith)

theorem sinPartial_period_mono : Monotone fun n : ℕ => sinPartial (n * (2 * Real.pi)) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hpi := Real.pi_pos
  have hn : (0 : ℝ) ≤ n * (2 * Real.pi) := by positivity
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_sinInt le_rfl hn)
    (intervalIntegrable_sinInt (b := n * (2 * Real.pi) + 2 * Real.pi) hn (by linarith))
  have he : ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) = n * (2 * Real.pi) + 2 * Real.pi := by push_cast; ring
  simp only [sinPartial]
  rw [he, ← hadd]
  linarith [integral_period_pos n]

theorem sinPartial_two_pi_pos : 0 < sinPartial (2 * Real.pi) := by
  have := integral_period_pos 0
  simpa [sinPartial] using this

end OscInt.D4.CosMomentAux

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint OscInt.D4.CosMomentAux

/-- **C1** One integration by parts for the cosine moment. -/
theorem cosIBP : CosIBPFacts := by
  intro R hR
  have hI1 := intervalIntegrable_cos_mul_rpow R hR.le
  have hI2 : IntervalIntegrable sinInt volume 0 R := intervalIntegrable_sinInt le_rfl hR.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
    (continuousOn_sin_mul_rpow.mono Icc_subset_Ici_self)
    (fun x hx => hasDerivAt_sin_mul_rpow hx.1) (hI1.sub (hI2.const_mul (1 / 3)))
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1 / 3)), intervalIntegral.integral_const_mul,
    Real.sin_zero, zero_mul, sub_zero] at hftc
  unfold cosMomentPartial
  change _ = _ + (1 / 3) * ∫ u in (0 : ℝ)..R, sinInt u
  linarith

/-- **C2** The sine moment converges to a positive number. -/
theorem sinMoment : SinMomentFacts := by
  have hT : Tendsto sinPartial atTop (𝓝 (∫ u in Ioi (0 : ℝ), sinInt u)) :=
    intervalIntegral_tendsto_integral_Ioi 0 integrableOn_sinInt_Ioi tendsto_id
  refine ⟨∫ u in Ioi (0 : ℝ), sinInt u, ?_, hT⟩
  have hseq : Tendsto (fun n : ℕ => sinPartial (n * (2 * Real.pi))) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), sinInt u)) :=
    hT.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  have hle : sinPartial (2 * Real.pi) ≤ ∫ u in Ioi (0 : ℝ), sinInt u := by
    refine ge_of_tendsto hseq ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have := sinPartial_period_mono hn
    simpa using this
  exact lt_of_lt_of_le sinPartial_two_pi_pos hle

end OscInt.D4
