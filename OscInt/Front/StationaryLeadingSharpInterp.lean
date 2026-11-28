/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.StationaryLeadingSharp
import Mathlib.Analysis.Convex.Deriv

/-!
# Batch SPL-N, part N5: vector interpolation (helper of agent C)

Route `docs/proof-SPLN.md`, section 2, **N5**, by the scalar trick: for `c = f(x)` the real function
`φ = Re(c̄ f)` has `φ″ ≥ −‖c‖M`; adding the parabola `‖c‖M (t − a)(t − b)/2` makes it convex on `[a, b]`, so
`φ(x) ≤ max(φ(a), φ(b)) + ‖c‖M (b − a)²/8`, and `φ(x) = ‖c‖²`, `φ(a) ≤ ‖c‖ ‖f(a)‖`, `φ(b) ≤ ‖c‖ ‖f(b)‖`.
Proves `splnC_interp : SplnInterpFacts`.
-/

namespace OscInt.SPLNAux

open OscInt.Statements OscInt.Blueprint.SPLN

/-- A real function on `[a, b]` with `φ″ ≥ −K` lies below `max(φ(a), φ(b)) + K (b − a)²/8`. -/
theorem splnC_real_interp (φ φ₁ φ₂ : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK0 : 0 ≤ K)
    (h1 : ∀ x ∈ Set.Icc a b, HasDerivAt φ (φ₁ x) x) (h2 : ∀ x ∈ Set.Icc a b, HasDerivAt φ₁ (φ₂ x) x)
    (hK : ∀ x ∈ Set.Icc a b, -K ≤ φ₂ x) :
    ∀ x ∈ Set.Icc a b, φ x ≤ max (φ a) (φ b) + K * (b - a) ^ 2 / 8 := by
  intro x hx
  set ψ : ℝ → ℝ := fun t => φ t + K * ((t - a) * (t - b)) / 2 with hψ
  have hψ1 : ∀ t ∈ Set.Icc a b, HasDerivAt ψ (φ₁ t + K * (2 * t - a - b) / 2) t := by
    intro t ht
    have h := ((((hasDerivAt_id' t).sub_const a).mul ((hasDerivAt_id' t).sub_const b)).const_mul K).div_const 2
    exact ((h1 t ht).add h).congr_deriv (by ring)
  have hψ2 : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => φ₁ t + K * (2 * t - a - b) / 2) (φ₂ t + K) t := by
    intro t ht
    have h := (((((hasDerivAt_id' t).const_mul 2).sub_const a).sub_const b).const_mul K).div_const 2
    exact ((h2 t ht).add h).congr_deriv (by ring)
  have hconv : ConvexOn ℝ (Set.Icc a b) ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (fun t ht => (hψ1 t ht).continuousAt.continuousWithinAt) (f' := fun t => φ₁ t + K * (2 * t - a - b) / 2)
      (f'' := fun t => φ₂ t + K) ?_ ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψ1 t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψ2 t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have := hK t (Set.Ioo_subset_Icc_self ht)
      linarith
  have hle := hconv.le_max_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hx
  have ha : ψ a = φ a := by simp [hψ]
  have hb : ψ b = φ b := by simp [hψ]
  rw [ha, hb] at hle
  have hxψ : ψ x = φ x + K * ((x - a) * (x - b)) / 2 := rfl
  have hq : -((x - a) * (x - b)) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hKq := mul_le_mul_of_nonneg_left hq hK0
  nlinarith

/-- The real part of `c̄ g` has the derivative `Re(c̄ g′)`. -/
theorem splnC_hasDerivAt_re (c : ℂ) (g : ℝ → ℂ) (g' : ℂ) (t : ℝ) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun t => (starRingEnd ℂ c * g t).re) (starRingEnd ℂ c * g').re t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hg.const_mul (starRingEnd ℂ c))
  simpa only [Function.comp_def, Complex.reCLM_apply] using h

/-- `Re(c̄ z) ≤ ‖c‖ ‖z‖`. -/
theorem splnC_re_le (c z : ℂ) : (starRingEnd ℂ c * z).re ≤ ‖c‖ * ‖z‖ := by
  have h := Complex.re_le_norm (starRingEnd ℂ c * z)
  rwa [norm_mul, Complex.norm_conj] at h

/-- **N5** The vector interpolation inequality. -/
theorem splnC_interp : SplnInterpFacts := by
  intro f f₁ f₂ a b M hab h1 h2 hM x hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  have hmax0 : 0 ≤ max ‖f a‖ ‖f b‖ := le_max_of_le_left (norm_nonneg _)
  set c := f x with hc
  rcases eq_or_ne c 0 with hc0 | hc0
  · rw [hc0, norm_zero]; positivity
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have key := splnC_real_interp (fun t => (starRingEnd ℂ c * f t).re) (fun t => (starRingEnd ℂ c * f₁ t).re)
    (fun t => (starRingEnd ℂ c * f₂ t).re) a b (‖c‖ * M) hab (by positivity)
    (fun t ht => splnC_hasDerivAt_re c f (f₁ t) t (h1 t ht))
    (fun t ht => splnC_hasDerivAt_re c f₁ (f₂ t) t (h2 t ht)) (by
      intro t ht
      have h := (abs_le.1 (Complex.abs_re_le_norm (starRingEnd ℂ c * f₂ t))).1
      rw [norm_mul, Complex.norm_conj] at h
      have := mul_le_mul_of_nonneg_left (hM t ht) (norm_nonneg c)
      linarith) x hx
  have hφx : (starRingEnd ℂ c * f x).re = ‖c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hc]
    simp [Complex.mul_re]
  have hA : max (starRingEnd ℂ c * f a).re (starRingEnd ℂ c * f b).re ≤ ‖c‖ * max ‖f a‖ ‖f b‖ := by
    rw [mul_max_of_nonneg _ _ (norm_nonneg c)]
    exact max_le_max (splnC_re_le c (f a)) (splnC_re_le c (f b))
  rw [hφx] at key
  have h3 : ‖c‖ * ‖c‖ ≤ ‖c‖ * (max ‖f a‖ ‖f b‖ + M * (b - a) ^ 2 / 8) := by nlinarith
  exact le_of_mul_le_mul_left h3 hcpos

end OscInt.SPLNAux
