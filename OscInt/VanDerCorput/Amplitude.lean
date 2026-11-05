import Blueprint.VanDerCorput
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# P2: amplitude transfer for oscillatory integrals

Proves `OscInt.VanDerCorput.amplitudeTransfer : OscInt.Blueprint.AmplitudeTransferFacts`: if
`‖∫_a^y e^{iφ}‖ ≤ C` for all `y ∈ [a, b]`, then `‖∫_a^b e^{iφ} ψ‖ ≤ C (‖ψ b‖ + ∫_a^b ‖ψ'‖)`.

Proof: with the primitive `F y = ∫_a^y e^{iφ}` (continuous on `[a, b]`, derivative `e^{iφ}` on `(a, b)` by the
fundamental theorem of calculus), integrate by parts: `∫ e^{iφ} ψ = F(b) ψ(b) - ∫ F ψ'` since `F a = 0`; then
bound both terms by `C`. Only integrability of `ψ'` is needed. Route adapted from J. Roos and M. Praveen,
`roos-j/lean-oscillatory` (Apache-2.0), `norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I`.
-/

namespace OscInt.VanDerCorput.AmplitudeAux

open Set MeasureTheory Complex OscInt.Statements intervalIntegral

/-- The primitive `F y = ∫_a^y e^{iφ}` is continuous on `[a, b]` and has derivative `e^{iφ}` on `(a, b)`. -/
theorem primitive_hasDerivOn (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    ContinuousOn (fun y => ∫ x in a..y, Complex.exp (↑(φ x) * Complex.I)) (Icc a b) ∧
      ∀ x ∈ Ioo a b, HasDerivAt (fun y => ∫ t in a..y, Complex.exp (↑(φ t) * Complex.I))
        (Complex.exp (↑(φ x) * Complex.I)) x := by
  have he : ContinuousOn (fun x => Complex.exp (↑(φ x) * Complex.I)) (Icc a b) :=
    (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const))
  refine ⟨?_, fun x hx => ?_⟩
  · have := continuousOn_primitive_interval (μ := volume) (a := a) (b := b)
      (f := fun x => Complex.exp (↑(φ x) * Complex.I))
      (by rw [uIcc_of_le hab]; exact he.integrableOn_Icc)
    rwa [uIcc_of_le hab] at this
  · have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2.le
    refine integral_hasDerivAt_right ?_ ?_ ?_
    · exact (he.mono hsub).intervalIntegrable_of_Icc hx.1.le
    · exact (he.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    · exact he.continuousAt (Icc_mem_nhds hx.1 hx.2)

end OscInt.VanDerCorput.AmplitudeAux

namespace OscInt.VanDerCorput

open Set MeasureTheory Complex OscInt.Statements intervalIntegral OscInt.VanDerCorput.AmplitudeAux

/-- **P2** (amplitude transfer): a uniform bound `C` on the partial integrals `∫_a^y e^{iφ}` bounds
`‖oscInt φ ψ a b‖` by `C * ampNorm ψ ψ' a b`. -/
theorem amplitudeTransfer : OscInt.Blueprint.AmplitudeTransferFacts := by
  intro φ ψ ψ' a b C hab hC hφ hψ hF
  obtain ⟨hψc, hψd, hψi⟩ := hψ
  set e : ℝ → ℂ := fun x => Complex.exp (↑(φ x) * Complex.I) with he_def
  set F : ℝ → ℂ := fun y => ∫ x in a..y, e x with hF_def
  obtain ⟨hFc, hFd⟩ := primitive_hasDerivOn φ a b hab hφ
  have hec : ContinuousOn e (Icc a b) :=
    (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const))
  have hmin : min a b = a := min_eq_left hab
  have hmax : max a b = b := max_eq_right hab
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := F) (v := ψ) (u' := e) (v' := ψ')
    (by rw [uIcc_of_le hab]; exact hFc) (by rw [uIcc_of_le hab]; exact hψc)
    (by rw [hmin, hmax]; exact hFd) (by rw [hmin, hmax]; exact hψd)
    (hec.intervalIntegrable_of_Icc hab) hψi
  have hFa : F a = 0 := integral_same
  have hosc : oscInt φ ψ a b = F b * ψ b - ∫ x in a..b, F x * ψ' x := by
    simp only [oscInt]
    change (∫ x in a..b, e x * ψ x) = _
    rw [hibp, hFa]; ring
  have hFψ' : IntervalIntegrable (fun x => F x * ψ' x) volume a b :=
    hψi.continuousOn_mul (by rw [uIcc_of_le hab]; exact hFc)
  have hint : ‖∫ x in a..b, F x * ψ' x‖ ≤ C * ∫ x in a..b, ‖ψ' x‖ := by
    calc ‖∫ x in a..b, F x * ψ' x‖ ≤ ∫ x in a..b, ‖F x * ψ' x‖ :=
          norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, C * ‖ψ' x‖ := by
          refine integral_mono_on hab hFψ'.norm (hψi.norm.const_mul C) fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hF x hx) (norm_nonneg _)
      _ = C * ∫ x in a..b, ‖ψ' x‖ := integral_const_mul C _
  have hb : ‖F b * ψ b‖ ≤ C * ‖ψ b‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hF b ⟨hab, le_rfl⟩) (norm_nonneg _)
  rw [hosc, ampNorm, mul_add]
  exact (norm_sub_le _ _).trans (add_le_add hb hint)

end OscInt.VanDerCorput
