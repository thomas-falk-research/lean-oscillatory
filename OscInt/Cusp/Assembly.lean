/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.Cusp
import OscInt.StationaryPhase.Assembly
import OscInt.StationaryPhase.LocalCrit
import OscInt.StationaryPhase.Implicit

/-!
# S5.1′ and S5.1 assembled against the batch-A3 blueprint interfaces

Route: `docs/proof-A3.md`. From the normalisation (A3-P5) `φ(L·) = φ(0) + Dφ(0)(L·) + F`, the family
`q ↦ F + q·y` has a normal point of order 4 at `q = 0`, so (A3-P3) gives `CoreHyps 4` with one set of constants for
`|q| ≤ q₀`. For an amplitude supported in `closedBall 0 δ` and any `y`, `t`, the affine change (F1c, F1d) turns
`I(tφ + y·, A)` into `|det L| e^{itφ(0)} I(t(F + p x + q y), A ∘ L)` with `p, q` real. If `|q| ≤ q₀` the core
estimate of order 4 with an outer linear term (A3-P2) gives `t^{-3/4}`; if `|q| > q₀` then `|∂_y(F + p x + q y)| ≥ q₀/2`
on the support box and one integration by parts in `y` (A3-P4) gives `t^{-1} ≤ t^{-3/4}`.
-/

namespace OscInt.Cusp.AssemblyAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase
open scoped ContDiff

/-- A constant added to the phase does not change the modulus of `oscInt2`. -/
theorem norm_oscInt2_const_add (c : ℝ) (Ψ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) :
    ‖oscInt2 (fun k => c + Ψ k) A‖ = ‖oscInt2 Ψ A‖ := by
  have h : oscInt2 (fun k => c + Ψ k) A = Complex.exp (↑c * Complex.I) * oscInt2 Ψ A := by
    unfold oscInt2
    rw [← integral_const_mul]
    congr 1; funext k
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- A continuous linear functional on `ℝ × ℝ` in coordinates. -/
theorem clm_apply_coords (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (k : ℝ × ℝ) : ℓ k = ℓ (1, 0) * k.1 + ℓ (0, 1) * k.2 := by
  have hk : k = k.1 • ((1 : ℝ), (0 : ℝ)) + k.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hk]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring

/-- `lin y` as a continuous linear functional. -/
noncomputable def linCLM (y : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem linCLM_apply (y k : ℝ × ℝ) : linCLM y k = lin y k := by
  simp [linCLM, lin]

theorem lin_zero_left (k : ℝ × ℝ) : lin (0, 0) k = 0 := by simp [lin]

theorem lin_split (p q : ℝ) (k : ℝ × ℝ) : lin (0, q) k + p * k.1 = lin (p, q) k := by
  simp only [lin]; ring

/-- The phase after the change of variables `κ = L k`: a constant plus `t (F + p x + q y)`. -/
theorem phase_eq (φ : ℝ × ℝ → ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ) {t : ℝ} (ht : t ≠ 0) (k : ℝ × ℝ) :
    t * φ (0 + L k) + lin y (0 + L k) =
      t * φ 0 + t * ((φ (L k) - φ 0 - fderiv ℝ φ 0 (L k)) +
        lin (0, fderiv ℝ φ 0 (L (0, 1)) + lin y (L (0, 1)) / t) k +
        (fderiv ℝ φ 0 (L (1, 0)) + lin y (L (1, 0)) / t) * k.1) := by
  have h1 := clm_apply_coords ((fderiv ℝ φ 0).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) k
  have h2 := clm_apply_coords ((linCLM y).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) k
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    linCLM_apply] at h1 h2
  rw [zero_add, h2]
  simp only [lin] at *
  rw [h1]
  field_simp
  ring

end OscInt.Cusp.AssemblyAux

namespace OscInt.Cusp

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase AssemblyAux
open scoped ContDiff

/-- **S5.1′** from the batch-A3 interfaces (`docs/proof-A3.md`). -/
theorem cuspBoundGen_of (hCE : CoreEstimate4Facts) (hND : NormalizedData4Facts) (hNS : TransverseNonStatFacts)
    (hN : A3NormalizeFacts) : CuspBoundGenStatement := by
  intro φ hφ hA3
  obtain ⟨L, hNP⟩ := hN φ hφ hA3
  set F : ℝ × ℝ → ℝ := fun k => φ (L k) - φ 0 - fderiv ℝ φ 0 (L k) with hFdef
  -- smoothness of `F`
  have hLs : ContDiff ℝ ∞ (fun k => L k) := (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).contDiff
  have hF : ContDiff ℝ ∞ F := by
    have h1 : ContDiff ℝ ∞ (fun k => φ (L k)) := hφ.comp hLs
    have h2 : ContDiff ℝ ∞ (fun k => fderiv ℝ φ 0 (L k)) :=
      ((fderiv ℝ φ 0).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))).contDiff
    exact (h1.sub contDiff_const).sub h2
  have hF4 : ContDiff ℝ 4 F := hF.of_le (by simp)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  -- the family `q ↦ F + q y` and its normalized data near `q = 0`
  let Q : ℝ → ℝ × ℝ → ℝ := fun q k => F k + lin (0, q) k
  have hQ : FamilyCk 4 Q := by
    have hlin := familyAddLinear Unit 4 (fun _ : Unit => F) (Set.univ : Set (ℝ × ℝ))
      (sanity_familyCk_const 4 F hF4)
    exact LocalCritAux.familyCk_comp hlin
      (f := fun q : ℝ => ((), (⟨(0, q), Set.mem_univ _⟩ : (Set.univ : Set (ℝ × ℝ)))))
      (by fun_prop)
  have hQ0 : Q 0 = F := by funext k; simp [Q, lin_zero_left]
  have hNP0 : NormalPoint4 (Q 0) := by rw [hQ0]; exact hNP
  obtain ⟨U, hU, a, b, μ, ν, D, ha, hb, hμ, hν, ys, hys⟩ := hND ℝ Q 0 hQ hNP0
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set q₀ := ε / 2 with hq₀def
  have hq₀ : 0 < q₀ := by positivity
  obtain ⟨C₂, hC₂⟩ := hCE a b μ ν D ha hb hμ hν
  -- the transverse derivative is small near `0`
  have hFy0 : fderiv ℝ F 0 (0, 1) = 0 := hNP.1
  have hcontFy : Continuous (fun k => fderiv ℝ F k (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨r₀, hr₀, hr₀b⟩ := Metric.continuousAt_iff.mp hcontFy.continuousAt (q₀ / 2) (by positivity)
  set r := r₀ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hFy : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r, |fderiv ℝ F k (0, 1)| ≤ q₀ / 2 := by
    intro k hk
    have hk' : dist k 0 < r₀ := by
      rw [dist_zero_right]
      have h1 : |k.1| ≤ r := abs_le.mpr ⟨hk.1.1, hk.1.2⟩
      have h2 : |k.2| ≤ r := abs_le.mpr ⟨hk.2.1, hk.2.2⟩
      calc ‖k‖ = max ‖k.1‖ ‖k.2‖ := rfl
        _ ≤ r := max_le (by simpa using h1) (by simpa using h2)
        _ < r₀ := by rw [hrdef]; linarith
    have := hr₀b hk'
    rw [Real.dist_eq, hFy0, sub_zero] at this
    exact this.le
  -- a bound for `∂²_y F` on the box
  have hbox : IsCompact (Icc (-r) r ×ˢ Icc (-r) r) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D', hD'⟩ := hbox.exists_bound_of_continuousOn (f := fun k => dd F k (0, 1) (0, 1))
    ((ImplicitAux.contDiff_dd (n := 0) (by exact_mod_cast hF2) (0, 1) (0, 1)).continuous.continuousOn)
  obtain ⟨C₄, hC₄⟩ := hNS r r (q₀ / 2) D' hr hr (by positivity)
  -- the radius
  set s := min (min a b) r with hsdef
  have hs : 0 < s := lt_min (lt_min ha hb) hr
  set nL := ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  refine ⟨s / (nL + 1), by positivity,
    |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * max (max C₂ 0) (max C₄ 0) *
      max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2, ?_⟩
  intro A M y t hA ht
  have ht0 : 0 < t := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (by norm_num) 0)
  -- change of variables
  have hsub : (fun k => (0 : ℝ × ℝ) + L k) ⁻¹' Metric.closedBall 0 (s / (nL + 1)) ⊆
      Icc (-s) s ×ˢ Icc (-s) s := by
    have := LocalCritAux.preimage_ball_subset_box L 0 (a := s) (b := s) (δ := s / (nL + 1))
      (by positivity) (by rw [div_mul_cancel₀ _ (by positivity), min_self])
    exact this
  set M' := max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 * M
  have hA' := ampBoundAffine 2 _ A M 0 L hA
  set A' : ℝ × ℝ → ℂ := fun k => A (0 + L k)
  set p := fderiv ℝ φ 0 (L (1, 0)) + lin y (L (1, 0)) / t
  set q := fderiv ℝ φ 0 (L (0, 1)) + lin y (L (0, 1)) / t
  have hchange := affineChange (fun κ => t * φ κ + lin y κ) A 0 L
  have hphase : (fun k => t * φ (0 + L k) + lin y (0 + L k)) =
      fun k => t * φ 0 + t * (Q q k + p * k.1) := by
    funext k; exact phase_eq φ L y ht0.ne' k
  rw [hchange, norm_mul, hphase, norm_oscInt2_const_add]
  have hdet : ‖((|LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| : ℝ) : ℂ)‖ =
      |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [hdet]
  have hexp : (-(3 : ℝ) / 4) = -(3 / 4 : ℝ) := by ring
  rw [hexp]
  have htpos : 0 < t ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  -- the bound for the transformed integral
  have hmain : ‖oscInt2 (fun k => t * (Q q k + p * k.1)) A'‖ ≤
      max (max C₂ 0) (max C₄ 0) * M' * t ^ (-(3 / 4 : ℝ)) := by
    have hM' : 0 ≤ M' := by positivity
    by_cases hqs : |q| ≤ q₀
    · -- near: the core estimate of order 4
      have hqU : q ∈ U := hεU (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
      have hAb : AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A' M' :=
        LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
          (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))
          (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))))
      refine (hC₂ (Q q) (ys q) A' M' t p (hys q hqU) hAb ht).trans ?_
      gcongr
      exact (le_max_left _ _).trans (le_max_left _ _)
    · -- far: one integration by parts in `y`
      push Not at hqs
      let Φ : ℝ × ℝ → ℝ := fun k => F k + lin (p, q) k
      have hΦ2 : ContDiff ℝ 2 Φ := hF2.add (FamilyAux.contDiff_lin _)
      have hΦeq : (fun k => t * (Q q k + p * k.1)) = fun k => t * Φ k := by
        funext k; simp only [Q, Φ]; rw [add_assoc, lin_split]
      have hgrad : ∀ k ∈ Icc (-r) r ×ˢ Icc (-r) r,
          q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D' := by
        intro k hk
        have hd : fderiv ℝ Φ k (0, 1) = fderiv ℝ F k (0, 1) + q := by
          simpa using fderiv_add_lin (hF2.differentiable (by norm_num)) (p, q) k (0, 1)
        refine ⟨?_, ?_⟩
        · rw [hd]
          have := hFy k hk
          have h1 : |q| - |fderiv ℝ F k (0, 1)| ≤ |fderiv ℝ F k (0, 1) + q| := by
            have := abs_sub_abs_le_abs_sub q (-(fderiv ℝ F k (0, 1)))
            rw [abs_neg, sub_neg_eq_add, add_comm] at this
            exact this
          linarith
        · rw [show Φ = fun k => F k + lin (p, q) k from rfl, dd_add_lin hF2 (p, q)]
          simpa [Real.norm_eq_abs] using hD' k hk
      have hAb : AmpBound 1 (Icc (-r) r ×ˢ Icc (-r) r) A' M' := by
        have hsr : s ≤ r := min_le_right _ _
        have h2 := LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
          (Icc_subset_Icc (neg_le_neg hsr) hsr) (Icc_subset_Icc (neg_le_neg hsr) hsr)))
        exact ⟨h2.1.of_le (by norm_num), h2.2.1, fun j hj => h2.2.2 j (hj.trans (by norm_num))⟩
      rw [hΦeq]
      refine (hC₄ Φ A' M' t hΦ2 hgrad hAb ht).trans ?_
      have h1 : 1 / t ≤ t ^ (-(3 / 4 : ℝ)) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
      calc C₄ * M' / t ≤ max C₄ 0 * M' / t := by gcongr; exact le_max_left _ _
        _ = max C₄ 0 * M' * (1 / t) := by ring
        _ ≤ max C₄ 0 * M' * t ^ (-(3 / 4 : ℝ)) := by gcongr
        _ ≤ max (max C₂ 0) (max C₄ 0) * M' * t ^ (-(3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM') htpos.le
  calc |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * ‖oscInt2 (fun k => t * (Q q k + p * k.1)) A'‖
      ≤ |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| *
          (max (max C₂ 0) (max C₄ 0) * M' * t ^ (-(3 / 4 : ℝ))) := by gcongr
    _ = _ := by simp only [M']; ring

/-- **S5.1** from S5.1′: a stable A3 point is an A3 point. -/
theorem cuspBound_of_gen (h : CuspBoundGenStatement) : CuspBoundStatement := by
  rintro φ hφ ⟨v, w, h1, h2, h3, h4, -⟩
  exact h φ hφ ⟨v, w, h1, h2, h3, h4⟩

end OscInt.Cusp
