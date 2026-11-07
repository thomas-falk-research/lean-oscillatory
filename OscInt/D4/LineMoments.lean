import Blueprint.D4ClosedForm
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# S4.4, part E6c: the line moments of the two normal forms

Given E6a (`BetaIoiFacts`) and E6b (`BetaUnitFacts`) as hypotheses (route `docs/proof-S44.md`, E6c):
* `p₊(u) = 1 + u²`: `integral_comp_abs` gives `2 ∫₀^∞`, then `t = u²` (`integral_comp_rpow_Ioi_of_pos`) and
  E6a with `a = 1/2`, `b = 1/6`, `Real.Gamma_one_half_eq`: `√π Γ(1/6)/Γ(2/3)`.
* `p₋(u) = u + u²`: `ℝ = (−∞, −1] ∪ (−1, 0] ∪ (0, ∞)`. On `(0, ∞)` E6a with `a = b = 1/3`; on `(−∞, −1)` the
  reflection `u ↦ −1 − u` (`integral_image_eq_integral_abs_deriv_smul`) reduces to `(0, ∞)`; on `(−1, 0)`
  `u ↦ −u` and E6b with `a = b = 1/3`. Each piece is integrable because its integral is nonzero
  (`Integrable.of_integral_ne_zero`, `intervalIntegral.intervalIntegrable_of_integral_ne_zero`). Total
  `3 Γ(1/3)²/Γ(2/3)`.
-/

namespace OscInt.D4

open Set MeasureTheory Real OscInt.Blueprint OscInt.Statements

namespace LineMomentsAux

/-- `|u + u²|^{-2/3}`. -/
noncomputable def fm (u : ℝ) : ℝ := |u + u ^ 2| ^ (-(2 : ℝ) / 3)

lemma fm_pos (u : ℝ) (hu : 0 < u) : fm u = u ^ ((1 : ℝ) / 3 - 1) * (1 + u) ^ (-((1 : ℝ) / 3 + 1 / 3)) := by
  rw [fm, show u + u ^ 2 = u * (1 + u) by ring, abs_of_pos (by positivity),
    mul_rpow hu.le (by linarith)]
  norm_num

lemma fm_reflect (x : ℝ) : fm (-1 - x) = fm x := by
  rw [fm, fm, show -1 - x + (-1 - x) ^ 2 = x + x ^ 2 by ring]

lemma fm_neg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    fm (-x) = x ^ ((1 : ℝ) / 3 - 1) * (1 - x) ^ ((1 : ℝ) / 3 - 1) := by
  rw [fm, show -x + (-x) ^ 2 = -(x * (1 - x)) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg h0 (by linarith)), mul_rpow h0 (by linarith)]
  norm_num

lemma gpos : 0 < Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (1 / 3 + 1 / 3) := by
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 3 by norm_num)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 3 + 1 / 3 by norm_num)
  positivity

lemma I1 (hB : BetaIoiFacts) : ∫ u in Ioi (0 : ℝ), fm u =
    Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (1 / 3 + 1 / 3) := by
  rw [← hB (1 / 3) (1 / 3) (by norm_num) (by norm_num)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => fm_pos u hu

lemma I2 (hB : BetaIoiFacts) : ∫ u in Iic (-1 : ℝ), fm u =
    Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (1 / 3 + 1 / 3) := by
  have himg : (fun x : ℝ => -1 - x) '' Ioi 0 = Iio (-1) := by simp
  rw [integral_Iic_eq_integral_Iio, ← himg,
    integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => -1 - x) (f' := fun _ => -1)
      measurableSet_Ioi (fun x _ => ((hasDerivAt_id' x).const_sub (-1)).hasDerivWithinAt)
      (fun x _ y _ h => by simpa using h), ← I1 hB]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp [fm_reflect]

lemma I3 (hU : BetaUnitFacts) : ∫ u in (-1 : ℝ)..0, fm u =
    Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (1 / 3 + 1 / 3) := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (f := fm)
  rw [neg_zero] at h
  rw [← hU (1 / 3) (1 / 3) (by norm_num) (by norm_num), ← h]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  exact fm_neg x hx.1 hx.2

lemma K1pt (x : ℝ) (hx : 0 < x) : (1 + x ^ 2) ^ (-(2 : ℝ) / 3) =
    1 / 2 * (((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      ((x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2 - 1) * (1 + x ^ (2 : ℝ)) ^ (-((1 : ℝ) / 2 + 1 / 6)))) := by
  rw [smul_eq_mul, ← rpow_mul hx.le, rpow_two]
  have h1 : x ^ ((2 : ℝ) - 1) = x := by norm_num
  have h2 : x ^ ((2 : ℝ) * (1 / 2 - 1)) = x⁻¹ := by norm_num; exact rpow_neg_one x
  have h3 : -((1 : ℝ) / 2 + 1 / 6) = -(2 : ℝ) / 3 := by norm_num
  rw [h1, h2, h3]
  field_simp

end LineMomentsAux

open LineMomentsAux

/-- `∫_ℝ (1 + u²)^{-2/3} du = √π Γ(1/6)/Γ(2/3)`. -/
theorem lineMomentPlus (hB : BetaIoiFacts) :
    lineMoment (1, 0, 1, 0) = Real.sqrt Real.pi * Real.Gamma (1 / 6) / Real.Gamma (2 / 3) := by
  have hfun : (fun u => |lineCubic (1, 0, 1, 0) u| ^ (-(2 : ℝ) / 3)) =
      fun u => (fun x : ℝ => (1 + x ^ 2) ^ (-(2 : ℝ) / 3)) |u| := by
    funext u
    have : lineCubic (1, 0, 1, 0) u = 1 + u ^ 2 := by simp [lineCubic, cubicForm]
    simp only [this, sq_abs]
    rw [abs_of_pos (by positivity)]
  have hsub := integral_comp_rpow_Ioi_of_pos (p := 2) (by norm_num)
    (g := fun y : ℝ => y ^ ((1 : ℝ) / 2 - 1) * (1 + y) ^ (-((1 : ℝ) / 2 + 1 / 6)))
  rw [hB (1 / 2) (1 / 6) (by norm_num) (by norm_num)] at hsub
  rw [lineMoment, hfun, integral_comp_abs (f := fun x : ℝ => (1 + x ^ 2) ^ (-(2 : ℝ) / 3)),
    setIntegral_congr_fun measurableSet_Ioi fun x hx => K1pt x hx, integral_const_mul, hsub,
    Real.Gamma_one_half_eq, show (1 : ℝ) / 2 + 1 / 6 = 2 / 3 by norm_num]
  ring

/-- `∫_ℝ |u + u²|^{-2/3} du = 3 Γ(1/3)²/Γ(2/3)`. -/
theorem lineMomentMinus (hB : BetaIoiFacts) (hU : BetaUnitFacts) :
    lineMoment (0, 1, 1, 0) = 3 * Real.Gamma (1 / 3) ^ 2 / Real.Gamma (2 / 3) := by
  have hI1 := I1 hB
  have hI2 := I2 hB
  have hI3 := I3 hU
  have hne := gpos.ne'
  have h1 : IntegrableOn fm (Ioi 0) := Integrable.of_integral_ne_zero (by rw [hI1]; exact hne)
  have h2 : IntegrableOn fm (Iic (-1)) := Integrable.of_integral_ne_zero (by rw [hI2]; exact hne)
  have h3 : IntegrableOn fm (Ioc (-1) 0) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      (intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [hI3]; exact hne))
  have hfun : (fun u => |lineCubic (0, 1, 1, 0) u| ^ (-(2 : ℝ) / 3)) = fm := by
    funext u; simp [lineCubic, cubicForm, fm]
  rw [lineMoment, hfun, ← intervalIntegral.integral_Iic_add_Ioi h2
      (by rw [← Ioc_union_Ioi_eq_Ioi (show (-1 : ℝ) ≤ 0 by norm_num)]; exact h3.union h1),
    ← Ioc_union_Ioi_eq_Ioi (show (-1 : ℝ) ≤ 0 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h3 h1,
    ← intervalIntegral.integral_of_le (by norm_num), hI1, hI2, hI3]
  norm_num
  ring


/-- **E6c** The line moments of the normal forms `x(x² + y²)` and `xy(x + y)`. -/
theorem lineMomentValues (hB : OscInt.Blueprint.BetaIoiFacts) (hU : OscInt.Blueprint.BetaUnitFacts) :
    OscInt.Blueprint.LineMomentValuesFacts :=
  ⟨lineMomentPlus hB, lineMomentMinus hB hU⟩

end OscInt.D4
