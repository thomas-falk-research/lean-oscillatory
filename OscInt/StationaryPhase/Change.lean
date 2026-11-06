import Blueprint.StationaryPhase

/-!
# S2/S3 infrastructure: affine change of variables (F1c) and cut-off amplitudes (F2b)

* `affineChange : AffineChangeFacts`. For an additive Haar measure `μ` on a finite-dimensional real space and a
  continuous linear automorphism `L`, `map L μ = |det L|⁻¹ • μ` (`Measure.map_linearMap_addHaar_eq_smul_addHaar`),
  so `∫ f ∘ L = |det L|⁻¹ ∫ f`; with translation invariance (`integral_add_left_eq_self`) this gives
  `∫ f = |det L| ∫ f (k₀ + L ·)`. No integrability is needed (both sides are Bochner integrals related by a
  measurable equivalence).
* `ampBoundMul : AmpBoundMulFacts`. Leibniz rule `norm_iteratedFDeriv_mul_le` with uniform bounds:
  if all derivatives of order `≤ n` of `χ` and `A` are bounded by `B` and `M`, those of `χ A` are bounded by
  `2ⁿ B M`; `B` exists since `χ` is `Cⁿ` with compact support. Only `χ ∈ Cⁿ` is used.
-/

open Set MeasureTheory OscInt.Statements

namespace OscInt.StationaryPhase.ChangeAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Linear change of variables for an additive Haar measure: `∫ f (L x) dμ = |det L|⁻¹ • ∫ f dμ`. -/
theorem integral_comp_continuousLinearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E)
    (f : E → F) :
    ∫ x, f (L x) ∂μ = |LinearMap.det (L : E →ₗ[ℝ] E)|⁻¹ • ∫ x, f x ∂μ := by
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' (L : E ≃ₗ[ℝ] E)).ne_zero
  have hemb : MeasurableEmbedding (L : E → E) := L.toHomeomorph.measurableEmbedding
  rw [← hemb.integral_map]
  have hmap : Measure.map (L : E → E) μ =
      ENNReal.ofReal |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

/-- Affine change of variables for an additive Haar measure:
`∫ f = |det L| • ∫ f (k₀ + L x) dμ`. -/
theorem integral_eq_abs_det_smul_integral_comp_affine (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E ≃L[ℝ] E) (k₀ : E) (f : E → F) :
    ∫ x, f x ∂μ = |LinearMap.det (L : E →ₗ[ℝ] E)| • ∫ x, f (k₀ + L x) ∂μ := by
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' (L : E ≃ₗ[ℝ] E)).ne_zero
  rw [integral_comp_continuousLinearEquiv μ L (fun y => f (k₀ + y)), integral_add_left_eq_self,
    smul_smul, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_smul]

end OscInt.StationaryPhase.ChangeAux

namespace OscInt.StationaryPhase.ChangeAux

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Leibniz bound with uniform bounds on the factors: if all derivatives of order `≤ n` of `f` and `g` are
bounded by `B` and `M`, then the `n`-th derivative of `f * g` is bounded by `2ⁿ B M`. -/
theorem norm_iteratedFDeriv_mul_le_of_forall_le {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : E → A} {n : ℕ} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) {B M : ℝ}
    (hB : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ B) (hM : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv 𝕜 i g x‖ ≤ M)
    (x : E) : ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖ ≤ 2 ^ n * B * M := by
  calc ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
          ‖iteratedFDeriv 𝕜 (n - i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x le_rfl
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (B * M) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hB i hi' x) (hM (n - i) (Nat.sub_le n i) x)
          (norm_nonneg _) ((norm_nonneg _).trans (hB i hi' x))) (Nat.cast_nonneg _)
    _ = 2 ^ n * B * M := by
        rw [← Finset.sum_mul, mul_assoc]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

/-- A compactly supported `Cⁿ` function has all derivatives of order `≤ n` bounded by one constant. -/
theorem exists_forall_norm_iteratedFDeriv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {n : ℕ} (hf : ContDiff 𝕜 n f) (hcs : HasCompactSupport f) :
    ∃ B, 0 ≤ B ∧ ∀ i ≤ n, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ B := by
  have h : ∀ i : Fin (n + 1), ∃ b, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ b := fun i => by
    obtain ⟨b, hb⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.mp i.2)).norm
      |>.bddAbove_range_of_hasCompactSupport (hcs.iteratedFDeriv i).norm
    exact ⟨b, fun x => hb ⟨x, rfl⟩⟩
  choose b hb using h
  refine ⟨∑ i, max (b i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun i hi x => ?_⟩
  calc ‖iteratedFDeriv 𝕜 i f x‖ ≤ max (b ⟨i, Nat.lt_succ_of_le hi⟩) 0 :=
        (hb ⟨i, Nat.lt_succ_of_le hi⟩ x).trans (le_max_left _ _)
    _ ≤ ∑ i, max (b i) 0 :=
        Finset.single_le_sum (f := fun i => max (b i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ _)

end OscInt.StationaryPhase.ChangeAux

namespace OscInt.StationaryPhase

/-- **F1c** Affine change of variables in `oscInt2`. -/
theorem affineChange : OscInt.Blueprint.AffineChangeFacts := by
  intro Q A k₀ L
  unfold oscInt2
  rw [ChangeAux.integral_eq_abs_det_smul_integral_comp_affine volume L k₀, Complex.real_smul]

/-- **F2b** Cutting off an amplitude by a smooth compactly supported `χ`; the constant is `2ⁿ B` with `B`
bounding all derivatives of order `≤ n` of `χ`. -/
theorem ampBoundMul : OscInt.Blueprint.AmpBoundMulFacts := by
  intro n χ hχ hcs
  set χc : ℝ × ℝ → ℂ := fun k => (χ k : ℂ) with hχc_def
  have hχc : ContDiff ℝ n χc := Complex.ofRealCLM.contDiff.comp (hχ.of_le (by exact_mod_cast le_top))
  have hcsc : HasCompactSupport χc := hcs.comp_left Complex.ofReal_zero
  obtain ⟨B, hB0, hB⟩ := ChangeAux.exists_forall_norm_iteratedFDeriv_le hχc hcsc
  refine ⟨2 ^ n * B, by positivity, fun K A M ⟨hA, hsupp, hbd⟩ => ⟨hχc.mul hA, ?_, fun j hj k => ?_⟩⟩
  · exact subset_inter (tsupport_mul_subset_right.trans hsupp)
      (tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero χ))
  · have hM : 0 ≤ M := (norm_nonneg _).trans (hbd 0 (Nat.zero_le _) k)
    have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
    calc ‖iteratedFDeriv ℝ j (fun k => χc k * A k) k‖ ≤ 2 ^ j * B * M :=
          ChangeAux.norm_iteratedFDeriv_mul_le_of_forall_le (hχc.of_le hjn) (hA.of_le hjn)
            (fun i hi => hB i (hi.trans hj)) (fun i hi => hbd i (hi.trans hj)) k
      _ ≤ 2 ^ n * B * M := by
          gcongr
          · norm_num

end OscInt.StationaryPhase
