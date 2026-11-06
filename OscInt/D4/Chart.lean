import Blueprint.D4ClosedForm
import OscInt.D4.ConstantPosFinal
import OscInt.D4.Polar
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# S4.4, part E2: the chart `u = tan θ`

`angularLine : OscInt.Blueprint.AngularLineFacts`: for `disc q ≠ 0`,
`∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ = 2 ∫_ℝ |C(1, u)|^{-2/3} du`.
* `C(−z) = −C(z)` (`OscInt.D4.PolarAux.cubicForm_neg`) makes the integrand `π`-periodic, so splitting `[0, 2π]` at
  `π` (interval integrability from S4.3, `OscInt.d4ConstantPos`) and `Function.Periodic.intervalIntegral_add_eq`
  give twice the integral over `[−π/2, π/2]`.
* On `Ioo (−π/2) (π/2) = arctan '' univ`, `integral_image_eq_integral_abs_deriv_smul` (no integrability needed)
  turns it into `∫_ℝ (1 + u²)⁻¹ |C(cos (arctan u), sin (arctan u))|^{-2/3} du`, and
  `C(cos (arctan u), sin (arctan u)) = (1 + u²)^{-3/2} C(1, u)` cancels the Jacobian pointwise.

Route: `docs/proof-S44.md` (E2) and `review/2026-11-06-S44-proof-route.md`.
-/

namespace OscInt.D4.ChartAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

/-- The angular integrand `θ ↦ |C(cos θ, sin θ)|^{-2/3}`. -/
noncomputable def angF (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) : ℝ :=
  |cubicForm q (Real.cos θ, Real.sin θ)| ^ (-(2 : ℝ) / 3)

/-- The angular integrand has period `π`, since `C(−z) = −C(z)`. -/
theorem angF_periodic (q : ℝ × ℝ × ℝ × ℝ) : Function.Periodic (angF q) Real.pi := by
  intro θ
  have h : ((Real.cos (θ + Real.pi), Real.sin (θ + Real.pi)) : ℝ × ℝ) = -(Real.cos θ, Real.sin θ) := by
    simp [Real.cos_add_pi, Real.sin_add_pi]
  simp only [angF, h, OscInt.D4.PolarAux.cubicForm_neg, abs_neg]

/-- `((1/√w)³)^{-2/3} = w` for `w > 0`. -/
theorem rpow_cube_sqrt (w : ℝ) (hw : 0 < w) : ((1 / Real.sqrt w) ^ 3) ^ (-(2 : ℝ) / 3) = w := by
  have ht : 0 < 1 / Real.sqrt w := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show (3 : ℕ) * (-(2 : ℝ) / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast,
    div_pow, Real.sq_sqrt hw.le]
  simp

/-- The Jacobian `(1 + u²)⁻¹` of `arctan` cancels: `(1 + u²)⁻¹ |C(cos (arctan u), sin (arctan u))|^{-2/3} =
|C(1, u)|^{-2/3}`. -/
theorem chart_pointwise (q : ℝ × ℝ × ℝ × ℝ) (u : ℝ) :
    |1 / (1 + u ^ 2)| * angF q (Real.arctan u) = |lineCubic q u| ^ (-(2 : ℝ) / 3) := by
  have hw : 0 < 1 + u ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 hw
  have hC : cubicForm q (1 / Real.sqrt (1 + u ^ 2), u / Real.sqrt (1 + u ^ 2)) =
      (1 / Real.sqrt (1 + u ^ 2)) ^ 3 * lineCubic q u := by
    simp only [cubicForm, lineCubic]; field_simp
  rw [angF, Real.cos_arctan, Real.sin_arctan, hC, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_pos (by positivity : (0:ℝ) < (1 / Real.sqrt (1 + u ^ 2)) ^ 3),
    rpow_cube_sqrt _ hw, abs_of_pos (by positivity : (0:ℝ) < 1 / (1 + u ^ 2)), ← mul_assoc]
  field_simp

/-- `∫_{−π/2}^{π/2} |C(cos θ, sin θ)|^{-2/3} dθ = ∫_ℝ |C(1, u)|^{-2/3} du` (for every `q`). -/
theorem chart_integral (q : ℝ × ℝ × ℝ × ℝ) :
    ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), angF q θ = lineMoment q := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
    ← Real.range_arctan, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_arctan x).hasDerivWithinAt) Real.arctan_injective.injOn,
    Measure.restrict_univ, lineMoment]
  simp only [smul_eq_mul, chart_pointwise]

end OscInt.D4.ChartAux

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint ChartAux

/-- **E2** `angularMoment q = 2 * lineMoment q` for `disc q ≠ 0`. -/
theorem angularLine : AngularLineFacts := by
  intro q hq
  have hI : IntervalIntegrable (angF q) MeasureTheory.volume 0 (2 * Real.pi) :=
    (OscInt.d4ConstantPos.2.2 q hq).1
  have hpi := Real.pi_pos
  have h1 : IntervalIntegrable (angF q) MeasureTheory.volume 0 Real.pi :=
    hI.mono_set (by rw [Set.uIcc_of_le hpi.le, Set.uIcc_of_le (by linarith)]
                    exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable (angF q) MeasureTheory.volume Real.pi (2 * Real.pi) :=
    hI.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
                    exact Set.Icc_subset_Icc hpi.le le_rfl)
  have hP := angF_periodic q
  have e1 := hP.intervalIntegral_add_eq 0 (-(Real.pi / 2))
  have e2 := hP.intervalIntegral_add_eq Real.pi (-(Real.pi / 2))
  have hm : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
  rw [hm, chart_integral] at e1 e2
  rw [zero_add] at e1
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring] at e2
  change ∫ θ in (0 : ℝ)..(2 * Real.pi), angF q θ = _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, e1, e2]
  ring

end OscInt.D4
