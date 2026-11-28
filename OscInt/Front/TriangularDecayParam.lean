/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.TriangularDecay

/-!
# Batch K2, part P9: parametric integrals over `[0, 1]` preserve smoothness

Proves `OscInt.K2.paramIntegralSmooth : OscInt.Blueprint.K2.ParamIntegralSmoothFacts`.
Route: `docs/proof-K2.md`, section 5 ("P9"). The general helper is stated for values in a normed space `E`
and proved by induction on finite orders via `contDiff_succ_iff_hasFDerivAt`; the derivative is the
integral of the partial derivative in `x`, by differentiation under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`), with the bound coming from compactness
of `closedBall x₀ 1 ×ˢ [0, 1]`. The case `n = ∞` uses every finite order.
-/

namespace OscInt.K2.ParamIntegralSmoothAux

open Set MeasureTheory Metric
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity of the parametric integral. -/
theorem continuous_integral {f : (ℝ × ℝ) × ℝ → E} (hf : Continuous f) :
    Continuous (fun x : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, f (x, τ)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x τ => f (x, τ)) (μ := volume) hf 0 1

/-- The partial derivative in `x`. -/
noncomputable def partialX (f : (ℝ × ℝ) × ℝ → E) (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) →L[ℝ] E :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)

theorem contDiff_partialX {n : ℕ} {f : (ℝ × ℝ) × ℝ → E} (hf : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f) :
    ContDiff ℝ n (partialX f) :=
  (hf.fderiv_right le_rfl).clm_comp contDiff_const

theorem hasFDerivAt_slice {f : (ℝ × ℝ) × ℝ → E} (hf : ContDiff ℝ 1 f) (x : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => f (y, t)) (partialX f (x, t)) x :=
  ((hf.differentiable one_ne_zero) (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

/-- Differentiation under the integral sign. -/
theorem hasFDerivAt_integral [CompleteSpace E] {f : (ℝ × ℝ) × ℝ → E} (hf : ContDiff ℝ 1 f) (x₀ : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, f (x, τ))
      (∫ τ in (0 : ℝ)..1, partialX f (x₀, τ)) x₀ := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous (partialX f) :=
    (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (f := partialX f) (s := closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1) hgc.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x τ => f (x, τ)) (F' := fun x τ => partialX f (x, τ)) (bound := fun _ => C)
    (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hfc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact (hfc.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (hgc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => hC _ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact ⟨ball_subset_closedBall hx, Ioc_subset_Icc_self ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ x _ => hasFDerivAt_slice hf x t

theorem contDiff_integral_nat (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : (ℝ × ℝ) × ℝ → E), ContDiff ℝ n f →
        ContDiff ℝ n (fun x : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, f (x, τ)) := by
  induction n with
  | zero =>
    intro E _ _ _ f hf
    rw [Nat.cast_zero, contDiff_zero] at hf ⊢
    exact continuous_integral hf
  | succ n ih =>
    intro E _ _ _ f hf
    have hf' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by exact_mod_cast hf
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.succ_ne_zero)
    have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun x : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, f (x, τ)) := by
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun x => ∫ τ in (0 : ℝ)..1, partialX f (x, τ), ?_, fun x => hasFDerivAt_integral h1 x⟩
      exact ih (partialX f) (contDiff_partialX hf')
    exact_mod_cast this

end OscInt.K2.ParamIntegralSmoothAux

namespace OscInt.K2

open OscInt.K2.ParamIntegralSmoothAux

theorem paramIntegralSmooth : OscInt.Blueprint.K2.ParamIntegralSmoothFacts := by
  intro n f hf
  rw [contDiff_iff_forall_nat_le] at hf ⊢
  intro m hm
  exact contDiff_integral_nat m f (hf m hm)

end OscInt.K2

