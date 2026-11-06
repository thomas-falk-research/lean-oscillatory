import Blueprint.D4Limit
import OscInt.D4.Gauge

/-!
# S4.3, parts C3 and C5: the cubic on the circle

* `circleNondeg : OscInt.Blueprint.CircleNondegFacts` (C3). With `ω = (cos θ, sin θ)`, the derivative of
  `g θ = C(ω)` is `∇C(ω) · ω⊥` (explicit `HasDerivAt`), and Euler gives `∇C(ω) · ω = 3 C(ω)`. If `g θ = g′ θ = 0`
  then `∇C(ω) = 0`, so `H(ω) ω = 2 ∇C(ω) = 0` and `C(ω) = 0`; `OscInt.D4.GaugeAux.disc_eq_zero` with `z = v = ω`
  gives `disc = 0` (the two kernel equations are `linear_combination`s of `g = 0`, `g′ = 0`, `cos² + sin² = 1`).
* `angularPos : OscInt.Blueprint.AngularPosFacts` (C5). `g` does not vanish identically on `(0, 2π)`: otherwise
  `g′(π) = 0 = g(π)`, contradicting C3. By continuity `g ≠ 0` on an open interval inside `(0, 2π)`, where the
  nonnegative integrand `|g|^{-2/3}` is positive; `intervalIntegral.integral_pos_iff_support_of_nonneg_ae`.

Route: `docs/proof-S43.md` (C3, C5, with the route-referee revision (4)).
-/

namespace OscInt.D4.AngularAux

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- The derivative of the cubic on the circle: `g′(θ) = -sin θ · ∂₁C(ω) + cos θ · ∂₂C(ω)`. -/
theorem hasDerivAt_circleCubic (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) :
    HasDerivAt (circleCubic q)
      (-Real.sin θ * (3 * q.1 * Real.cos θ ^ 2 + 2 * q.2.1 * Real.cos θ * Real.sin θ +
          q.2.2.1 * Real.sin θ ^ 2) +
        Real.cos θ * (q.2.1 * Real.cos θ ^ 2 + 2 * q.2.2.1 * Real.cos θ * Real.sin θ +
          3 * q.2.2.2 * Real.sin θ ^ 2)) θ := by
  have hc := Real.hasDerivAt_cos θ
  have hs := Real.hasDerivAt_sin θ
  have h := ((((hc.pow 3).const_mul q.1).fun_add (((hc.pow 2).const_mul q.2.1).fun_mul hs)).fun_add
    ((hc.const_mul q.2.2.1).fun_mul (hs.pow 2))).fun_add ((hs.pow 3).const_mul q.2.2.2)
  convert h using 1
  · ext x; simp only [circleCubic, cubicForm, Pi.pow_apply]
  · simp only [Pi.pow_apply]; push_cast; ring

end OscInt.D4.AngularAux

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint OscInt.D4.AngularAux

/-- **C3** For `disc q ≠ 0`, `g` and `g′` have no common zero on the circle. -/
theorem circleNondeg : CircleNondegFacts := by
  rintro ⟨a, b, c, d⟩ hq θ h0 hd
  rw [(hasDerivAt_circleCubic _ θ).deriv] at hd
  simp only [circleCubic, cubicForm] at h0 hd
  set x := Real.cos θ
  set y := Real.sin θ
  have hp : x ^ 2 + y ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
  have hz : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; push Not at h; rw [h.1, h.2] at hp; norm_num at hp
  refine hq (GaugeAux.disc_eq_zero a b c d x y x y hz hz ?_ ?_ h0)
  · linear_combination 6 * x * h0 - 2 * y * hd -
      2 * (3 * a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * hp
  · linear_combination 6 * y * h0 + 2 * x * hd -
      2 * (b * x ^ 2 + 2 * c * x * y + 3 * d * y ^ 2) * hp

/-- **C5** For `disc q ≠ 0` and an integrable angular integrand, `angularMoment q > 0`. -/
theorem angularPos : AngularPosFacts := by
  intro q hq hint
  have hcont : Continuous (circleCubic q) := (hasDerivAt_circleCubic q · |>.continuousAt) |>
    continuous_iff_continuousAt.2
  have hpi := Real.pi_pos
  obtain ⟨θ₀, hθ₀, hne⟩ : ∃ θ₀ ∈ Ioo 0 (2 * Real.pi), circleCubic q θ₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hev : circleCubic q =ᶠ[𝓝 Real.pi] fun _ => 0 :=
      Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hall
    exact circleNondeg q hq Real.pi (hall _ ⟨hpi, by linarith⟩)
      (by rw [hev.deriv_eq]; simp)
  have hopen : IsOpen ({θ | circleCubic q θ ≠ 0} ∩ Ioo 0 (2 * Real.pi)) :=
    (isOpen_ne_fun hcont continuous_const).inter isOpen_Ioo
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen θ₀ ⟨hne, hθ₀⟩
  show 0 < ∫ θ in (0 : ℝ)..(2 * Real.pi), |circleCubic q θ| ^ (-(2 : ℝ) / 3)
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun θ => Real.rpow_nonneg (abs_nonneg _) _) hint]
  refine ⟨by linarith, ?_⟩
  have hsub : Ioo (θ₀ - ε) (θ₀ + ε) ⊆
      Function.support (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) ∩
        Ioc 0 (2 * Real.pi) := by
    intro θ hθ
    have hm : θ ∈ Metric.ball θ₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hθ.1, hθ.2]
    obtain ⟨h1, h2⟩ := hball hm
    exact ⟨(Real.rpow_pos_of_pos (abs_pos.2 h1) _).ne', Ioo_subset_Ioc_self h2⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

end OscInt.D4
