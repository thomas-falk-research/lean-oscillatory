import Blueprint.D4Limit
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# S4.3, part C4: integrability of `|g|^{-α}` near simple zeros

`OscInt.D4.singularPower : OscInt.Blueprint.SingularPowerFacts`. Route: `docs/proof-S43.md`, C4 with the
revision (3) of the route referee. For a `C¹` function `g` and `0 ≤ α < 1`, `|g|^{-α}` is integrable on a
neighbourhood of every point `x₀` of `[a, b]`:
* if `g x₀ ≠ 0`, then `|g| ≥ |g x₀|/2` near `x₀`, so the integrand is bounded by a constant;
* if `g x₀ = 0` and `g' x₀ ≠ 0`, the mean value inequality applied to `g x - g'(x₀) x` (whose derivative is
  small near `x₀` by continuity of `g'`) gives `|g x| ≥ (|g'(x₀)|/2)|x − x₀|`, so the integrand is dominated by
  `c^{-α} |x − x₀|^{-α}`, which is integrable since `-α > -1` (`intervalIntegrable_rpow'`, after a shift and a
  reflection).
Compactness of `[a, b]` (`LocallyIntegrableOn.integrableOn_isCompact`) assembles the local pieces.
-/

namespace OscInt.D4.SingularPowerAux

open Set MeasureTheory Filter Topology

/-- `|x|^r` is interval integrable on every interval for `-1 < r`. -/
theorem intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ r) volume a b := by
  have hpos : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 c := by
    intro c hc
    have m := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr
    rw [intervalIntegrable_iff, uIoc_of_le hc] at m ⊢
    refine m.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [abs_of_pos hx.1]
  have hall : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · rw [IntervalIntegrable.iff_comp_neg]
      simpa only [abs_neg, neg_zero] using hpos (-c) (by linarith)
  exact (hall a).symm.trans (hall b)

/-- The shifted power `|x - x₀|^r` is interval integrable on `[x₀ - δ, x₀ + δ]` for `-1 < r`. -/
theorem integrableOn_abs_sub_rpow {r : ℝ} (hr : -1 < r) (x₀ δ : ℝ) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => |x - x₀| ^ r) (Icc (x₀ - δ) (x₀ + δ)) volume := by
  have h := (intervalIntegrable_abs_rpow hr (-δ) δ).comp_sub_right x₀
  rw [show -δ + x₀ = x₀ - δ by ring, add_comm δ x₀] at h
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp h

/-- Away from the zeros of a continuous `g`, `|g|^{-α}` is integrable near the point. -/
theorem integrableAt_of_ne {g : ℝ → ℝ} (hg : Continuous g) {x₀ : ℝ} (hx : g x₀ ≠ 0) {α : ℝ}
    (h0 : 0 ≤ α) : IntegrableAtFilter (fun x => |g x| ^ (-α)) (𝓝 x₀) volume := by
  set c := |g x₀| / 2 with hc
  have cpos : 0 < c := by have := abs_pos.mpr hx; positivity
  have hev : ∀ᶠ y in 𝓝 x₀, c < |g y| :=
    hg.abs.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, δpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨Icc (x₀ - δ / 2) (x₀ + δ / 2), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  refine Integrable.mono' (continuous_const (y := c ^ (-α))).integrableOn_Icc
    ((hg.abs.measurable.pow_const (-α)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hd : dist y x₀ < δ := by
    rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hy.1, hy.2]
  exact Real.rpow_le_rpow_of_nonpos cpos (hδ hd).le (by linarith)

/-- Near a simple zero `x₀` of a `C¹` function, `|g x| ≥ (|g'(x₀)|/2) |x - x₀|`. -/
theorem linear_lower_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {x₀ : ℝ} (hx : g x₀ = 0)
    (hd : deriv g x₀ ≠ 0) : ∃ δ > 0, ∀ y ∈ Icc (x₀ - δ) (x₀ + δ),
      |deriv g x₀| / 2 * |y - x₀| ≤ |g y| := by
  set m := |deriv g x₀| with hm
  have mpos : 0 < m := abs_pos.mpr hd
  obtain ⟨δ, δpos, hδ⟩ :=
    Metric.continuous_iff.mp (hg.continuous_deriv le_rfl) x₀ (m / 2) (by positivity)
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  refine ⟨δ / 2, by positivity, fun y hy => ?_⟩
  have hx₀ : x₀ ∈ Icc (x₀ - δ / 2) (x₀ + δ / 2) := ⟨by linarith, by linarith⟩
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => g z - deriv g x₀ * z) (f' := fun z => deriv g z - deriv g x₀ * 1) (C := m / 2)
    (fun z _ => ((hdiff z).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv g x₀))).hasDerivWithinAt)
    (fun z hz => by
      rw [mul_one, Real.norm_eq_abs, ← Real.dist_eq]
      refine (hδ z ?_).le
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hz.1, hz.2])
    (convex_Icc _ _) hx₀ hy
  simp only [Real.norm_eq_abs, hx] at hb
  have e1 : |deriv g x₀ * (y - x₀)| = m * |y - x₀| := abs_mul _ _
  have e2 : |deriv g x₀ * (y - x₀) - g y| = |g y - deriv g x₀ * y - (0 - deriv g x₀ * x₀)| := by
    rw [abs_sub_comm]; ring_nf
  have := abs_sub_abs_le_abs_sub (deriv g x₀ * (y - x₀)) (g y)
  linarith

/-- Near a simple zero of a `C¹` function, `|g|^{-α}` is integrable for `0 ≤ α < 1`. -/
theorem integrableAt_of_deriv_ne {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {x₀ : ℝ} (hx : g x₀ = 0)
    (hd : deriv g x₀ ≠ 0) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    IntegrableAtFilter (fun x => |g x| ^ (-α)) (𝓝 x₀) volume := by
  obtain ⟨δ, δpos, key⟩ := linear_lower_bound hg hx hd
  set m := |deriv g x₀| / 2 with hm
  have mpos : 0 < m := by have := abs_pos.mpr hd; positivity
  refine ⟨Icc (x₀ - δ) (x₀ + δ), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  refine Integrable.mono' ((integrableOn_abs_sub_rpow (r := -α) (by linarith) x₀ δ δpos.le).const_mul
    (m ^ (-α))) ((hg.continuous.abs.measurable.pow_const (-α)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.mul_rpow mpos.le (abs_nonneg _)]
  rcases eq_or_ne y x₀ with rfl | hne
  · simp [hx]
  · have : 0 < |y - x₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (key y hy) (by linarith)

end OscInt.D4.SingularPowerAux

open Set MeasureTheory Filter Topology OscInt.D4.SingularPowerAux in
/-- **C4** For `C¹` `g` with only simple zeros on `[a, b]` and `0 ≤ α < 1`, `|g|^{-α}` is interval integrable
on `[a, b]`: locally integrable at every point of `[a, b]`, hence integrable on the compact `[a, b]`. -/
theorem OscInt.D4.singularPower : OscInt.Blueprint.SingularPowerFacts := by
  intro g hg a b hab hz α h0 h1
  have hloc : LocallyIntegrableOn (fun x => |g x| ^ (-α)) (Icc a b) volume := by
    intro x hx
    refine IntegrableAtFilter.filter_mono nhdsWithin_le_nhds ?_
    by_cases hgx : g x = 0
    · exact integrableAt_of_deriv_ne hg hgx ((hz x hx).resolve_left (not_not.mpr hgx)) h0 h1
    · exact integrableAt_of_ne hg.continuous hgx h0
  apply IntegrableOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hloc.integrableOn_isCompact isCompact_Icc
