import Blueprint.D4ClosedForm
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# S4.4, parts E6a and E6b: the Beta integrals

* `betaUnit` (E6b): `∫₀¹ x^{a-1} (1 − x)^{b-1} dx = Γ(a)Γ(b)/Γ(a+b)` for `a, b > 0`, from Mathlib's complex
  `Complex.Gamma_mul_Gamma_eq_betaIntegral` (with `Complex.ofReal_cpow` on `[0, 1]` and
  `intervalIntegral.integral_ofReal`).
* `betaIoi` (E6a): `∫₀^∞ t^{a-1} (1 + t)^{-(a+b)} dt = Γ(a)Γ(b)/Γ(a+b)`, from E6b by the substitution
  `x = t/(1+t)` (`integral_image_eq_integral_abs_deriv_smul`), which maps `(0, ∞)` onto `(0, 1)` with
  `dx = dt/(1+t)²`. (Route `docs/proof-S44.md`, E6a–b; E6a deviates from the Tonelli sketch there: it is derived
  from E6b in the same file by a change of variables.)
-/

namespace OscInt.D4

open Set MeasureTheory Real

/-- **E6b** The Beta integral on `[0, 1]`. -/
theorem betaUnit : OscInt.Blueprint.BetaUnitFacts := by
  intro a b ha hb
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hB : Complex.betaIntegral a b =
      ((∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have h1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    simp only [Complex.ofReal_mul]
    rw [Complex.ofReal_cpow hx.1, Complex.ofReal_cpow h1]
    push_cast
    rfl
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at h
  have h2 : Real.Gamma a * Real.Gamma b =
      Real.Gamma (a + b) * ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
    exact_mod_cast h
  have hG : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [h2]
  field_simp

namespace BetaAux

/-- `t ↦ t/(1+t)` maps `(0, ∞)` onto `(0, 1)`. -/
lemma img : (fun t : ℝ => t / (1 + t)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht : (0 : ℝ) < t := ht
    exact ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨x / (1 - x), div_pos h0 (by linarith), ?_⟩
    have : (1 : ℝ) - x ≠ 0 := by linarith
    have h2 : 1 + x / (1 - x) = 1 / (1 - x) := by field_simp; ring
    simp only [h2]
    field_simp

lemma injOn' : InjOn (fun t : ℝ => t / (1 + t)) (Ioi 0) := by
  intro s hs t ht h
  have hs : (0 : ℝ) < s := hs
  have ht : (0 : ℝ) < t := ht
  simp only at h
  rw [div_eq_div_iff (by linarith) (by linarith)] at h
  linarith

lemma deriv' (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + t) ^ 2) t := by
  have := (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) (by simp; linarith)
  exact this.congr_deriv (by simp)

/-- The Jacobian identity `|φ'(t)| · B(φ t) = t^{a-1} (1+t)^{-(a+b)}` for `φ t = t/(1+t)`. -/
lemma pointwise (a b t : ℝ) (ht : 0 < t) :
    |1 / (1 + t) ^ 2| • ((t / (1 + t)) ^ (a - 1) * (1 - t / (1 + t)) ^ (b - 1)) =
      t ^ (a - 1) * (1 + t) ^ (-(a + b)) := by
  have hs : 0 < 1 + t := by linarith
  have h1 : 1 - t / (1 + t) = (1 + t)⁻¹ := by field_simp; ring
  have key : (1 + t) ^ (-(a + b)) * ((1 + t) ^ (2 : ℝ) * (1 + t) ^ (a - 1) * (1 + t) ^ (b - 1)) = 1 := by
    rw [← rpow_add hs, ← rpow_add hs, ← rpow_add hs]
    ring_nf
    exact rpow_zero _
  rw [smul_eq_mul, abs_of_pos (by positivity), h1, div_rpow ht.le hs.le, inv_rpow hs.le]
  rw [← rpow_two] at *
  rw [eq_inv_of_mul_eq_one_left key, mul_inv, mul_inv]
  ring

end BetaAux

/-- **E6a** The Beta integral on `(0, ∞)`, by `x = t/(1+t)` from E6b. -/
theorem betaIoi : OscInt.Blueprint.BetaIoiFacts := by
  intro a b ha hb
  rw [← betaUnit a b ha hb, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← BetaAux.img,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t ht => (BetaAux.deriv' t ht).hasDerivWithinAt) BetaAux.injOn']
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => (BetaAux.pointwise a b t ht).symm

end OscInt.D4
