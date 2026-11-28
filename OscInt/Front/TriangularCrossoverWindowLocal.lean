/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayLocal
import OscInt.Front.TriangularDecayChart
import OscInt.Front.TriDeriv
import OscInt.Cusp.Transverse

/-!
# Batch A5U, part A12: the window local bound at the A5 point (`A5WindowLocalFacts`)

Route `stmts/proof-A5U-draft.md`, sections 1 and 4–5. A clone of `OscInt.K2.reducedOrderBound_of` with the fixed
chart `κ = k* + L k`, `L (u, s) = u (1, 1) + s (1, −1)` (`a5uX_chartEquiv`): after `OscInt.K2.LocalAux.phase_eq_at`
the phase is a constant plus `t (Q_{α,q} + p u)`. Near tilts `|q| ≤ q₀` use the core window (A12a's bound). Far tilts
use `OscInt.Cusp.transverseNonStat` on a box chosen at `a₀` only: by the fixed chart (A8) `∂_s F_α = ∂_s F_{a₀}` and
`∂²_s F_α = ∂²_s F_{a₀}` for every `α` (`a5uX_fderiv_s`, `a5uX_dd_s`), and `t^{−1} ≤ W` for `|α − a₀| ≤ 1`
(`a5uX_inv_le_weight`).
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open OscInt.StationaryPhase OscInt.Cusp.AssemblyAux
open scoped ContDiff

/-- The chart `a5L` is a linear automorphism. -/
theorem a5uX_chartEquiv : ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ k, L k = a5L k := by
  obtain ⟨L, hL1, hL2⟩ :=
    OscInt.StationaryPhase.LocalAux.exists_equiv_cols ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (-1 : ℝ)) (by norm_num)
  refine ⟨L, fun k => ?_⟩
  have hk : k = k.1 • ((1 : ℝ), (0 : ℝ)) + k.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hk]
  rw [map_add, map_smul, map_smul, hL1, hL2]
  rfl

/-- A8 as an identity of functions. -/
theorem a5uX_F_eq (h8 : A5FixedChartFacts) (a₀ α : ℝ) :
    a5F a₀ α = fun k => 2 * Real.cos (a5Theta a₀ + k.2) * Real.cos k.1 - 2 * Real.cos (a5Theta a₀) +
      α * (Real.cos (2 * k.1) - 1) + 2 * k.2 * Real.sin (a5Theta a₀) :=
  funext (h8 a₀ α)

/-- The chart phase is smooth. -/
theorem a5uX_F_smooth (h8 : A5FixedChartFacts) (a₀ α : ℝ) : ContDiff ℝ ∞ (a5F a₀ α) := by
  rw [a5uX_F_eq h8]
  fun_prop

/-- `F_α = F_{a₀} + (α − a₀)(cos 2u − 1)`. -/
theorem a5uX_F_split (h8 : A5FixedChartFacts) (a₀ α : ℝ) :
    a5F a₀ α = fun k => a5F a₀ a₀ k + (α - a₀) * (Real.cos (2 * k.1) - 1) := by
  funext k
  rw [h8, h8]
  ring

/-- A function of `u` only has zero derivative in the direction `(0, 1)`. -/
theorem a5uX_fderiv_long_zero (c : ℝ) (k : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => c * (Real.cos (2 * k.1) - 1)) k (0, 1) = 0 := by
  have hg : HasDerivAt (fun x : ℝ => c * (Real.cos (2 * x) - 1)) (c * (-Real.sin (2 * k.1) * 2)) k.1 := by
    have h1 := ((Real.hasDerivAt_cos (2 * k.1)).comp k.1 ((hasDerivAt_id k.1).const_mul 2)).sub_const 1
    have h2 := h1.const_mul c
    simpa using h2
  have hF : HasFDerivAt (fun k : ℝ × ℝ => c * (Real.cos (2 * k.1) - 1))
      ((c * (-Real.sin (2 * k.1) * 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) k :=
    hg.comp_hasFDerivAt k (hasFDerivAt_fst (𝕜 := ℝ) (p := k))
  rw [hF.fderiv]
  simp

/-- `∂_s F_α = ∂_s F_{a₀}`. -/
theorem a5uX_fderiv_s (h8 : A5FixedChartFacts) (a₀ α : ℝ) (k : ℝ × ℝ) :
    fderiv ℝ (a5F a₀ α) k (0, 1) = fderiv ℝ (a5F a₀ a₀) k (0, 1) := by
  rw [a5uX_F_split h8 a₀ α]
  have h1 : DifferentiableAt ℝ (a5F a₀ a₀) k := (a5uX_F_smooth h8 a₀ a₀).differentiable (by simp) k
  have h2 : DifferentiableAt ℝ (fun k : ℝ × ℝ => (α - a₀) * (Real.cos (2 * k.1) - 1)) k := by fun_prop
  rw [fderiv_fun_add h1 h2]
  simp only [add_apply, a5uX_fderiv_long_zero, add_zero]

/-- `∂²_s F_α = ∂²_s F_{a₀}`. -/
theorem a5uX_dd_s (h8 : A5FixedChartFacts) (a₀ α : ℝ) (k : ℝ × ℝ) :
    dd (a5F a₀ α) k (0, 1) (0, 1) = dd (a5F a₀ a₀) k (0, 1) (0, 1) := by
  unfold dd
  rw [show (fun y => fderiv ℝ (a5F a₀ α) y (0, 1)) = fun y => fderiv ℝ (a5F a₀ a₀) y (0, 1) from
    funext (a5uX_fderiv_s h8 a₀ α)]

/-- `∂_s F_{a₀}(0) = 0`: the tangent plane is removed. -/
theorem a5uX_fderiv_zero (a₀ : ℝ) : fderiv ℝ (a5F a₀ a₀) 0 (0, 1) = 0 := by
  obtain ⟨L, hL⟩ := a5uX_chartEquiv
  have hfun : a5F a₀ a₀ = fun k => triPhase a₀ (a5Centre a₀ + (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) k) -
      triPhase a₀ (a5Centre a₀) - fderiv ℝ (triPhase a₀) (a5Centre a₀) ((L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) k) := by
    funext k
    simp only [ContinuousLinearEquiv.coe_coe, hL]
    rfl
  rw [hfun, OscInt.K2.ChartAux.fderiv_F_apply
    ((OscInt.API.TriDeriv.triPhase_smooth a₀).differentiable (by simp))]
  simp

/-- The target weight is nonnegative. -/
theorem a5uX_weight_nonneg (a₀ α : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ crossWeight a₀ α t := by
  unfold crossWeight crossEnvelope
  split_ifs <;> positivity

/-- `t^{−1} ≤ W` for `|α − a₀| ≤ 1`, `t ≥ 1`. -/
theorem a5uX_inv_le_weight {a₀ α t : ℝ} (hε : |α - a₀| ≤ 1) (ht : 1 ≤ t) : t⁻¹ ≤ crossWeight a₀ α t := by
  have ht0 : 0 < t := by linarith
  have h13 : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht0 _
  have hsplit : t ^ (-(2 : ℝ) / 3) * (t ^ ((1 : ℝ) / 3))⁻¹ = t⁻¹ := by
    rw [← Real.rpow_neg ht0.le, ← Real.rpow_add ht0, show -(2 : ℝ) / 3 + -(1 / 3) = -1 by norm_num,
      Real.rpow_neg_one]
  unfold crossWeight crossEnvelope
  split_ifs with h
  · rw [mul_one, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  · push Not at h
    set s := |α - a₀| * t ^ ((1 : ℝ) / 3) with hs
    have hs0 : 0 < s := by linarith
    have hst : s ≤ t ^ ((1 : ℝ) / 3) := by
      rw [hs]; nlinarith [abs_nonneg (α - a₀)]
    have h1 : s⁻¹ ≤ s ^ (-(1 : ℝ) / 4) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
    have h2 : (t ^ ((1 : ℝ) / 3))⁻¹ ≤ s⁻¹ := inv_anti₀ hs0 hst
    rw [← hsplit]
    gcongr
    exact h2.trans h1

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open OscInt.StationaryPhase OscInt.Cusp.AssemblyAux
open scoped ContDiff

/-- The far-tilt box at `a₀`: `|∂_s F_{a₀}| ≤ q₀/2` on `[−ρ, ρ]²` and a bound for `∂²_s F_{a₀}` there. -/
theorem a5uX_farBox (h8 : A5FixedChartFacts) (a₀ q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ ρ > 0, ∃ D' : ℝ, ∀ k ∈ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ,
      |fderiv ℝ (a5F a₀ a₀) k (0, 1)| ≤ q₀ / 2 ∧ ‖dd (a5F a₀ a₀) k (0, 1) (0, 1)‖ ≤ D' := by
  have hF : ContDiff ℝ ∞ (a5F a₀ a₀) := a5uX_F_smooth h8 a₀ a₀
  have hF2 : ContDiff ℝ 2 (a5F a₀ a₀) := hF.of_le (by simp)
  have hcontFy : Continuous (fun k => fderiv ℝ (a5F a₀ a₀) k (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨r₀, hr₀, hr₀b⟩ := Metric.continuousAt_iff.mp hcontFy.continuousAt (q₀ / 2) (by positivity)
  have hr : 0 < r₀ / 2 := by positivity
  have hbox : IsCompact (Icc (-(r₀ / 2)) (r₀ / 2) ×ˢ Icc (-(r₀ / 2)) (r₀ / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨D', hD'⟩ := hbox.exists_bound_of_continuousOn (f := fun k => dd (a5F a₀ a₀) k (0, 1) (0, 1))
    ((ImplicitAux.contDiff_dd (n := 0) (by exact_mod_cast hF2) (0, 1) (0, 1)).continuous.continuousOn)
  refine ⟨r₀ / 2, hr, D', fun k hk => ⟨?_, hD' k hk⟩⟩
  have hk' : dist k 0 < r₀ := by
    rw [dist_zero_right]
    have h1 : |k.1| ≤ r₀ / 2 := abs_le.mpr ⟨hk.1.1, hk.1.2⟩
    have h2 : |k.2| ≤ r₀ / 2 := abs_le.mpr ⟨hk.2.1, hk.2.2⟩
    calc ‖k‖ = max ‖k.1‖ ‖k.2‖ := rfl
      _ ≤ r₀ / 2 := max_le (by simpa using h1) (by simpa using h2)
      _ < r₀ := by linarith
  have := hr₀b hk'
  rw [Real.dist_eq, a5uX_fderiv_zero, sub_zero] at this
  exact this.le

/-- The far branch: for `|q| > q₀` one transverse integration by parts, uniformly in `α`. -/
theorem a5uX_far (h8 : A5FixedChartFacts) {a₀ q₀ ρ D' C₄ : ℝ}
    (hbox : ∀ k ∈ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ,
      |fderiv ℝ (a5F a₀ a₀) k (0, 1)| ≤ q₀ / 2 ∧ ‖dd (a5F a₀ a₀) k (0, 1) (0, 1)‖ ≤ D')
    (hC₄ : ∀ (Φ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m : ℝ), ContDiff ℝ 2 Φ →
      (∀ k ∈ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ, q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D') →
      AmpBound 1 (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ) A M → 1 ≤ m → ‖oscInt2 (fun k => m * Φ k) A‖ ≤ C₄ * M / m)
    {α q p t M : ℝ} {A : ℝ × ℝ → ℂ} (hq : q₀ < |q|) (hε : |α - a₀| ≤ 1) (ht : 1 ≤ t) (hM : 0 ≤ M)
    (hA : AmpBound 1 (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ) A M) :
    ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) A‖ ≤ max C₄ 0 * M * crossWeight a₀ α t := by
  have ht0 : 0 < t := by linarith
  have hF2 : ContDiff ℝ 2 (a5F a₀ α) := (a5uX_F_smooth h8 a₀ α).of_le (by simp)
  let Φ : ℝ × ℝ → ℝ := fun k => a5F a₀ α k + lin (p, q) k
  have hΦeq : (fun k => t * (a5Q a₀ α q k + p * k.1)) = fun k => t * Φ k := by
    funext k; simp only [Φ, lin, a5Q]; ring
  have hΦ2 : ContDiff ℝ 2 Φ := hF2.add (FamilyAux.contDiff_lin _)
  have hgrad : ∀ k ∈ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ,
      q₀ / 2 ≤ |fderiv ℝ Φ k (0, 1)| ∧ |dd Φ k (0, 1) (0, 1)| ≤ D' := by
    intro k hk
    have hd : fderiv ℝ Φ k (0, 1) = fderiv ℝ (a5F a₀ a₀) k (0, 1) + q := by
      rw [← a5uX_fderiv_s h8 a₀ α k]
      simpa using fderiv_add_lin (hF2.differentiable (by norm_num)) (p, q) k (0, 1)
    refine ⟨?_, ?_⟩
    · rw [hd]
      have h0 := (hbox k hk).1
      have h1 : |q| - |fderiv ℝ (a5F a₀ a₀) k (0, 1)| ≤ |fderiv ℝ (a5F a₀ a₀) k (0, 1) + q| := by
        have := abs_sub_abs_le_abs_sub q (-(fderiv ℝ (a5F a₀ a₀) k (0, 1)))
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        exact this
      linarith
    · rw [show Φ = fun k => a5F a₀ α k + lin (p, q) k from rfl, dd_add_lin hF2 (p, q), a5uX_dd_s h8 a₀ α k]
      simpa [Real.norm_eq_abs] using (hbox k hk).2
  rw [hΦeq]
  refine (hC₄ Φ A M t hΦ2 hgrad hA ht).trans ?_
  calc C₄ * M / t ≤ max C₄ 0 * M / t := by gcongr; exact le_max_left _ _
    _ = max C₄ 0 * M * t⁻¹ := by ring
    _ ≤ max C₄ 0 * M * crossWeight a₀ α t := by gcongr; exact a5uX_inv_le_weight hε ht

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open OscInt.StationaryPhase OscInt.Cusp.AssemblyAux
open scoped ContDiff

/-- The chart step: with `κ = k* + L k` the integral is `|det L|` times a chart integral of
`t (Q_{α,q} + p u)` with the transported amplitude. -/
theorem a5uX_chartStep (a₀ α : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (hL : ∀ k, L k = a5L k) (A : ℝ × ℝ → ℂ)
    (y : ℝ × ℝ) {t : ℝ} (ht : 0 < t) :
    ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ =
      |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| *
        ‖oscInt2 (fun k => t * (a5Q a₀ α (fderiv ℝ (triPhase α) (a5Centre a₀) (L (0, 1)) +
          lin y (L (0, 1)) / t) k + (fderiv ℝ (triPhase α) (a5Centre a₀) (L (1, 0)) +
          lin y (L (1, 0)) / t) * k.1)) (fun k => A (a5Centre a₀ + L k))‖ := by
  have hchange := affineChange (fun κ => t * triPhase α κ + lin y κ) A (a5Centre a₀) L
  have hphase : (fun k => t * triPhase α (a5Centre a₀ + L k) + lin y (a5Centre a₀ + L k)) =
      fun k => (t * triPhase α (a5Centre a₀) + lin y (a5Centre a₀)) +
        t * (a5Q a₀ α (fderiv ℝ (triPhase α) (a5Centre a₀) (L (0, 1)) + lin y (L (0, 1)) / t) k +
          (fderiv ℝ (triPhase α) (a5Centre a₀) (L (1, 0)) + lin y (L (1, 0)) / t) * k.1) := by
    funext k
    rw [OscInt.K2.LocalAux.phase_eq_at (triPhase α) (a5Centre a₀) L y ht.ne' k, hL k]
    rfl
  rw [hchange, norm_mul, hphase, norm_oscInt2_const_add, Complex.norm_real, Real.norm_eq_abs, abs_abs]

/-- **A12** The window local bound at `k*`, from A8 and A12a's bound. -/
theorem a5WindowLocal : A5WindowLocalFacts := by
  intro h8 hW a₀ ha₀
  obtain ⟨q₀, hq₀, a, ha, b, hb, r, hr, C, hC⟩ := hW a₀ ha₀
  obtain ⟨L, hL⟩ := a5uX_chartEquiv
  obtain ⟨ρ, hρ, D', hbox⟩ := a5uX_farBox h8 a₀ q₀ hq₀
  obtain ⟨C₄, hC₄⟩ := OscInt.Cusp.transverseNonStat ρ ρ (q₀ / 2) D' hρ hρ (by positivity)
  set s := min (min a b) ρ with hsdef
  have hs : 0 < s := lt_min (lt_min ha hb) hρ
  set nL := ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  refine ⟨s / (nL + 1), by positivity, min r 1, lt_min hr one_pos,
    |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * max (max C 0) (max C₄ 0) *
      max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2, ?_⟩
  intro α hα A M y t hA ht
  have ht0 : 0 < t := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (by norm_num) 0)
  have hsub : (fun k => a5Centre a₀ + L k) ⁻¹' Metric.closedBall (a5Centre a₀) (s / (nL + 1)) ⊆
      Icc (-s) s ×ˢ Icc (-s) s :=
    LocalCritAux.preimage_ball_subset_box L (a5Centre a₀) (a := s) (b := s) (δ := s / (nL + 1))
      (by positivity) (by rw [div_mul_cancel₀ _ (by positivity), min_self])
  set M' := max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 * M
  have hM' : 0 ≤ M' := by positivity
  have hA' := ampBoundAffine 2 _ A M (a5Centre a₀) L hA
  rw [a5uX_chartStep a₀ α L hL A y ht0]
  set p := fderiv ℝ (triPhase α) (a5Centre a₀) (L (1, 0)) + lin y (L (1, 0)) / t
  set q := fderiv ℝ (triPhase α) (a5Centre a₀) (L (0, 1)) + lin y (L (0, 1)) / t
  set W := crossWeight a₀ α t
  have hW0 : 0 ≤ W := a5uX_weight_nonneg a₀ α ht0
  have hmain : ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) (fun k => A (a5Centre a₀ + L k))‖ ≤
      max (max C 0) (max C₄ 0) * M' * W := by
    by_cases hqs : |q| ≤ q₀
    · have hAb : AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) (fun k => A (a5Centre a₀ + L k)) M' :=
        LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
        (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))
        (Icc_subset_Icc (by simp [hsdef]) (by simp [hsdef]))))
      refine (hC α q (hα.trans (min_le_left _ _)) hqs _ M' t p hAb ht).trans ?_
      gcongr
      exact (le_max_left _ _).trans (le_max_left _ _)
    · push Not at hqs
      have hsρ : s ≤ ρ := min_le_right _ _
      have h2 := LocalCritAux.ampBound_mono hA' (hsub.trans (prod_mono
        (Icc_subset_Icc (neg_le_neg hsρ) hsρ) (Icc_subset_Icc (neg_le_neg hsρ) hsρ)))
      have hAb : AmpBound 1 (Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ) (fun k => A (a5Centre a₀ + L k)) M' :=
        ⟨h2.1.of_le (by norm_num), h2.2.1, fun j hj => h2.2.2 j (hj.trans (by norm_num))⟩
      refine (a5uX_far h8 hbox hC₄ hqs (hα.trans (min_le_right _ _)) ht hM' hAb).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM') hW0
  calc |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| *
        ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) (fun k => A (a5Centre a₀ + L k))‖
      ≤ |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * (max (max C 0) (max C₄ 0) * M' * W) := by gcongr
    _ = _ := by simp only [M']; ring

end OscInt.A5UAux
