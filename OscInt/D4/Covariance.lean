import OscInt.D4.CubicComp
import OscInt.D4.PolarLimit
import OscInt.D4.ConstantPosFinal
import OscInt.D4.Polar
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# S4.4, part E3: `GL₂` covariance of the angular integral

`covariance : OscInt.Blueprint.CovarianceFacts`: `J(C ∘ g) = J(C)/|det g|` for `disc C ≠ 0`, `det g ≠ 0`, where
`J(C) = angularMoment q = ∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ`. Route `docs/proof-S44.md`, E3 and its revision 4:
* `lintegral_wt`: with `G(C) = ∫⁻_{ℝ²} exp(-|C(z)|^{2/3}) dz`, `G(C) = J(C)/2`. Polar coordinates
  (`lintegral_comp_polarCoord_symm`, target `Ioi 0 ×ˢ Ioo (-π) π`), Tonelli with `θ` outer
  (`lintegral_prod_symm`), `C(rω) = r³ g(θ)` (`PolarAux.cubicForm_polar`) and `∫₀^∞ r e^{-a r²} dr = (2a)⁻¹`
  (`integral_rpow_mul_exp_neg_mul_rpow`) off the null zero set of `g` (`circleZerosNull`); then periodicity
  (period `2π`) moves `(-π, π)` to `(0, 2π)`, with integrability from S4.3 (`d4ConstantPos`).
* `lintegral_wt_comp`: `G(C ∘ g) = |det g|⁻¹ G(C)` (`lin2 g` as `Matrix.toLin` of `!![g₁, g₂; g₃, g₄]`,
  `map_linearMap_addHaar_eq_smul_addHaar`, `lintegral_map`), with `cubicForm_cubicComp` (E4a).
* `disc_cubicComp` (E4b) gives `disc (C ∘ g) ≠ 0`; injectivity of `ENNReal.ofReal` on `[0, ∞)` concludes.
-/

namespace OscInt.D4.CovarianceAux

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- The angular integrand `θ ↦ |C(cos θ, sin θ)|^{-2/3}`. -/
noncomputable def angInt (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) : ℝ :=
  |cubicForm q (Real.cos θ, Real.sin θ)| ^ (-(2 : ℝ) / 3)

/-- The Gaussian-type weight `z ↦ exp(-|C(z)|^{2/3})` as an `ℝ≥0∞`-valued function. -/
noncomputable def wt (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-|cubicForm q z| ^ ((2 : ℝ) / 3)))

theorem continuous_wt (q : ℝ × ℝ × ℝ × ℝ) : Continuous (wt q) := by
  have hC : Continuous (fun z : ℝ × ℝ => cubicForm q z) := by
    unfold cubicForm; fun_prop
  have h2 : Continuous (fun z : ℝ × ℝ => |cubicForm q z| ^ ((2 : ℝ) / 3)) :=
    hC.abs.rpow_const (fun _ => Or.inr (by norm_num))
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp h2.neg)

/-- `∫₀^∞ r e^{-a r²} dr = (2a)⁻¹` in `lintegral` form. -/
theorem lintegral_radial {a : ℝ} (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * Real.exp (-a * r ^ 2)) = ENNReal.ofReal ((2 * a)⁻¹) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mul_exp_neg_mul_sq ha).integrableOn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr; exact mul_nonneg (le_of_lt hr) (Real.exp_pos _).le)]
  congr 1
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := a) (by norm_num) (by norm_num) ha
  simp only [Real.rpow_one, Real.rpow_two] at h
  rw [h]
  norm_num [Real.rpow_neg_one]

/-- `|C(r cos θ, r sin θ)|^{2/3} = |g θ|^{2/3} r²` for `r > 0`. -/
theorem abs_cubic_polar_rpow (q : ℝ × ℝ × ℝ × ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    |cubicForm q (r * Real.cos θ, r * Real.sin θ)| ^ ((2 : ℝ) / 3) =
      |cubicForm q (Real.cos θ, Real.sin θ)| ^ ((2 : ℝ) / 3) * r ^ 2 := by
  rw [OscInt.D4.PolarAux.cubicForm_polar, abs_mul, abs_of_pos (pow_pos hr 3),
    Real.mul_rpow (pow_pos hr 3).le (abs_nonneg _), mul_comm]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  norm_num


/-- The radial integral at a direction `θ` with `g θ ≠ 0`. -/
theorem lintegral_radial_dir (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) (hθ : circleCubic q θ ≠ 0) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * wt q (r * Real.cos θ, r * Real.sin θ) =
      ENNReal.ofReal (angInt q θ / 2) := by
  set a := |cubicForm q (Real.cos θ, Real.sin θ)| ^ ((2 : ℝ) / 3) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos (abs_pos.2 hθ) _
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (g := fun r => ENNReal.ofReal (r * Real.exp (-a * r ^ 2))) ?_, lintegral_radial ha]
  · congr 1
    rw [angInt, mul_inv, ha_def, ← Real.rpow_neg (abs_nonneg _), neg_div]
    ring
  · intro r hr
    dsimp only
    simp only [wt]
    rw [abs_cubic_polar_rpow q hr, ← ENNReal.ofReal_mul (le_of_lt hr)]
    rw [ha_def, neg_mul]

/-- Polar coordinates: `∫⁻ exp(-|C|^{2/3}) = ∫⁻_{(-π, π)} |g|^{-2/3}/2` for `disc ≠ 0`. -/
theorem lintegral_wt_polar (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    ∫⁻ z, wt q z = ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (angInt q θ / 2) := by
  rw [← lintegral_comp_polarCoord_symm, polarCoord_target]
  simp only [polarCoord_symm_apply, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · have hnull := OscInt.D4.circleZerosNull q hq
    have hae : ∀ᵐ θ ∂(volume : Measure ℝ), circleCubic q θ ≠ 0 := by
      rw [ae_iff]; simpa using hnull
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with θ hθ
    exact lintegral_radial_dir q θ hθ
  · have h1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) :=
      ENNReal.continuous_ofReal.measurable.comp measurable_fst
    have h2 : Measurable (fun p : ℝ × ℝ => wt q (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :=
      ((continuous_wt q).comp (by fun_prop)).measurable
    exact (h1.mul h2).aemeasurable


theorem angInt_periodic (q : ℝ × ℝ × ℝ × ℝ) : Function.Periodic (angInt q) (2 * Real.pi) := by
  intro θ
  simp only [angInt, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- One period: `J(C) = ∫_{(-π, π)} |g|^{-2/3}`, and the integrand is integrable there, for `disc ≠ 0`. -/
theorem angularMoment_Ioo (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    IntegrableOn (angInt q) (Ioo (-Real.pi) Real.pi) ∧
      angularMoment q = ∫ θ in Ioo (-Real.pi) Real.pi, angInt q θ := by
  have hper := angInt_periodic q
  have h02 : IntervalIntegrable (angInt q) volume 0 (0 + 2 * Real.pi) := by
    rw [zero_add]; exact (OscInt.d4ConstantPos.2.2 q hq).1
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hint := hper.intervalIntegrable (by positivity) h02 (-Real.pi) Real.pi
  refine ⟨((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hint).mono_set Ioo_subset_Ioc_self, ?_⟩
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [hpi, zero_add] at h
  rw [angularMoment, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle, h]
  rfl

/-- `∫⁻ exp(-|C|^{2/3}) = J(C)/2` for `disc ≠ 0`. -/
theorem lintegral_wt (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    ∫⁻ z, wt q z = ENNReal.ofReal (angularMoment q / 2) := by
  obtain ⟨hint, hJ⟩ := angularMoment_Ioo q hq
  rw [lintegral_wt_polar q hq, hJ, ← integral_div,
    ofReal_integral_eq_lintegral_ofReal (hint.div_const 2)]
  exact Eventually.of_forall (fun θ => div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num))

/-- Linear change of variables: `∫⁻ exp(-|C ∘ g|^{2/3}) = |det g|⁻¹ ∫⁻ exp(-|C|^{2/3})`. -/
theorem lintegral_wt_comp (q g : ℝ × ℝ × ℝ × ℝ) (hg : det2 g ≠ 0) :
    ∫⁻ z, wt (cubicComp q g) z = ENNReal.ofReal |det2 g|⁻¹ * ∫⁻ z, wt q z := by
  set M : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ := Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![g.1, g.2.1; g.2.2.1, g.2.2.2] with hM_def
  have hM : ∀ z, M z = lin2 g z := fun z => by rw [hM_def, Matrix.toLin_finTwoProd_apply]; rfl
  have hdet : LinearMap.det M = det2 g := by
    rw [hM_def, LinearMap.det_toLin, Matrix.det_fin_two_of]; rfl
  have hcomp : ∀ z, wt (cubicComp q g) z = wt q (M z) := fun z => by
    simp only [wt, OscInt.D4.cubicForm_cubicComp, hM]
  simp_rw [hcomp]
  rw [← lintegral_map (continuous_wt q).measurable (LinearMap.continuous_of_finiteDimensional M).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (hdet ▸ hg), lintegral_smul_measure,
    smul_eq_mul, hdet, abs_inv]

end OscInt.D4.CovarianceAux

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint OscInt.D4.CovarianceAux

/-- **E3** `GL₂` covariance of the angular integral: `J(C ∘ g) = J(C)/|det g|`. -/
theorem covariance : CovarianceFacts := by
  intro q g hq hg
  have hq' : disc (cubicComp q g) ≠ 0 := by
    rw [disc_cubicComp]; exact mul_ne_zero (pow_ne_zero _ hg) hq
  have h := lintegral_wt_comp q g hg
  rw [lintegral_wt _ hq', lintegral_wt _ hq, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _))] at h
  have hJ0 : ∀ p : ℝ × ℝ × ℝ × ℝ, 0 ≤ angularMoment p := fun p =>
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ => Real.rpow_nonneg (abs_nonneg _) _)
  rw [ENNReal.ofReal_eq_ofReal_iff (by linarith [hJ0 (cubicComp q g)])
    (mul_nonneg (inv_nonneg.2 (abs_nonneg _)) (by linarith [hJ0 q]))] at h
  rw [div_eq_inv_mul]
  linarith

end OscInt.D4
