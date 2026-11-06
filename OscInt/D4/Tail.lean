import Blueprint.D4LimitS42

/-!
# S4.2, parts E2 and E3: the inner limit and the dyadic tail

* `innerLimit : OscInt.Blueprint.InnerLimitFacts` (E2). Dominated convergence along `𝓝 0`
  (`tendsto_integral_filter_of_dominated_convergence`): for `|s| ≤ 1` the integrand is bounded by
  `sup‖B‖ · sup{‖A(s•w)‖ : |s| ≤ 1, w ∈ tsupport B}` times the indicator of the compact `tsupport B`; pointwise
  convergence from the joint continuity of `Ψ` and continuity of `A`; the limit is split by `integral_mul_const`.
* `dyadicTail : OscInt.Blueprint.DyadicTailFacts` (E3). `N` is the least index with `δ ≤ 2^N ρ`, `ρ = R t^{-1/3}`
  (`Nat.find`); minimality gives `2^{j+1} ρ < 2δ` for `j < N`. Each term equals `2^{-(j+1)/2} R^{-1/2} t^{-2/3}`
  (rpow algebra), and the geometric sum is at most `1/(√2 − 1) < 3`.

Route: `docs/proof-S42.md` (Steps 2–3) and `review/2026-11-06-S42-proof-route.md` (§2).
-/

namespace OscInt.D4.TailAux

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- Each dyadic term is `2^{-(j+1)/2} R^{-1/2} t^{-2/3}`. -/
theorem term_eq (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (j : ℕ) :
    (2 ^ (j + 1) * (R * t ^ (-(1 : ℝ) / 3))) ^ 2 *
        (t * (2 ^ (j + 1) * (R * t ^ (-(1 : ℝ) / 3))) ^ 3) ^ (-(5 : ℝ) / 6) =
      ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ (j + 1) * (R ^ (-(1 : ℝ) / 2) * t ^ (-(2 : ℝ) / 3)) := by
  have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have htr : 0 < t ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  set a : ℝ := 2 ^ (j + 1)
  set ε := a * (R * t ^ (-(1 : ℝ) / 3)) with hε
  have he : 0 < ε := by positivity
  have h1 : ε ^ 2 * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) = t ^ (-(5 : ℝ) / 6) * ε ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow ht.le (by positivity), ← Real.rpow_natCast ε 3, ← Real.rpow_mul he.le,
      ← Real.rpow_natCast ε 2]
    rw [mul_left_comm, ← Real.rpow_add he]
    norm_num
  rw [h1, hε, Real.mul_rpow h2.le (by positivity), Real.mul_rpow hR.le htr.le, ← Real.rpow_mul ht.le]
  have ha : a ^ (-(1 : ℝ) / 2) = ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ (j + 1) := by
    simp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  rw [ha]
  have ht' : t ^ (-(5 : ℝ) / 6) * t ^ (-(1 : ℝ) / 3 * (-(1 : ℝ) / 2)) = t ^ (-(2 : ℝ) / 3) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [← ht']; ring

/-- `∑_{j<N} 2^{-(j+1)/2} ≤ 1/(√2 − 1) ≤ 3`. -/
theorem geom_le (N : ℕ) :
    ∑ j ∈ Finset.range N, ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ (j + 1) ≤ 3 := by
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = 1 / 2 := by
    simp only [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hr : r ≤ 3 / 4 := by nlinarith
  have hr1 : r < 1 := by linarith
  have hs : ∑ j ∈ Finset.range N, r ^ j ≤ r ^ 0 / (1 - r) := by
    rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hr0 hr1
  have he : ∑ j ∈ Finset.range N, r ^ (j + 1) = r * ∑ j ∈ Finset.range N, r ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => pow_succ' r j
  rw [he]
  calc r * ∑ j ∈ Finset.range N, r ^ j ≤ r * (r ^ 0 / (1 - r)) := mul_le_mul_of_nonneg_left hs hr0
    _ ≤ 3 := by
      rw [pow_zero, ← mul_div_assoc, mul_one, div_le_iff₀ (by linarith)]; linarith

end OscInt.D4.TailAux

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- **E2** The inner limit, by dominated convergence. -/
theorem innerLimit : InnerLimitFacts := by
  intro Ψ hΨ B hB hBc A hA
  set K := tsupport B
  have hK : IsCompact K := hBc
  obtain ⟨CB, hCB⟩ := hB.norm.bddAbove_range_of_hasCompactSupport hBc.norm
  have hKA : IsCompact ((fun p : ℝ × (ℝ × ℝ) => p.1 • p.2) '' (Metric.closedBall (0 : ℝ) 1 ×ˢ K)) :=
    ((isCompact_closedBall 0 1).prod hK).image (continuous_fst.smul continuous_snd)
  obtain ⟨CA, hCA⟩ := hKA.exists_bound_of_continuousOn hA.continuousOn
  have hΨs : ∀ s, Continuous (Ψ s) := fun s => hΨ.comp (Continuous.prodMk_right s)
  have hcont : ∀ s, Continuous fun w => Complex.exp (↑(Ψ s w) * Complex.I) * (B w * A (s • w)) :=
    fun s => (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (hΨs s)).mul
      continuous_const)).mul (hB.mul (hA.comp (continuous_const_smul s)))
  have hlim : oscInt2 (Ψ 0) B * A 0 =
      ∫ w, Complex.exp (↑(Ψ 0 w) * Complex.I) * (B w * A ((0 : ℝ) • w)) := by
    simp only [oscInt2, zero_smul, ← mul_assoc]
    exact (integral_mul_const _ _).symm
  rw [hlim]
  refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => CB * CA)
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with s hs
    refine Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ K
    · rw [indicator_of_mem hw, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
      exact mul_le_mul (hCB ⟨w, rfl⟩) (hCA _ ⟨(s, w), ⟨hs, hw⟩, rfl⟩) (norm_nonneg _)
        ((norm_nonneg _).trans (hCB ⟨w, rfl⟩))
    · rw [indicator_of_notMem hw, image_eq_zero_of_notMem_tsupport hw, zero_mul, mul_zero, norm_zero]
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · refine Eventually.of_forall fun w => ?_
    have h1 : Continuous fun s : ℝ => Ψ s w := hΨ.comp (Continuous.prodMk_left w)
    exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp h1).mul
      continuous_const)).mul (continuous_const.mul (hA.comp (continuous_id.smul
        continuous_const)))).tendsto 0

/-- **E3** The dyadic tail: choice of `N` and the geometric bound. -/
theorem dyadicTail : DyadicTailFacts := by
  intro t R δ ht hR hδ
  set ρ := R * t ^ (-(1 : ℝ) / 3) with hρ
  have hρ0 : 0 < ρ := mul_pos (by linarith) (Real.rpow_pos_of_pos ht _)
  have hex : ∃ N : ℕ, δ ≤ 2 ^ N * ρ := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (δ / ρ) (by norm_num : (1 : ℝ) < 2)
    exact ⟨N, by rw [div_lt_iff₀ hρ0] at hN; linarith⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_, ?_⟩
  · have h := Nat.find_min hex hj
    rw [not_le] at h
    rw [pow_succ]; linarith
  · rw [Finset.sum_congr rfl fun j _ => TailAux.term_eq t R ht (by linarith) j, ← Finset.sum_mul]
    have hpos : 0 ≤ R ^ (-(1 : ℝ) / 2) * t ^ (-(2 : ℝ) / 3) := by positivity
    calc _ ≤ 3 * (R ^ (-(1 : ℝ) / 2) * t ^ (-(2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_right (TailAux.geom_le _) hpos
      _ = _ := by ring

end OscInt.D4
