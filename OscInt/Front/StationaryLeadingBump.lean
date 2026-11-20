/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Batch SPL, part P-bump: mollified point masses for the third derivative (route `docs/proof-SPL.md`, sections 6 and 10)

For a mollifier `ψ ≥ 0` of integral 1 vanishing outside `(−w, w)` put
`m(t) = ½[ψ(t − τ) − ψ(t + τ)] − (τ/2T)[ψ(t − T) − ψ(t + T)]` (`splBumpStencil ψ τ T`). The same combination of
translates applied to a triple primitive `P₃` of `ψ` is an amplitude `g` with `g‴ = m`; it has compact support because
the combination annihilates polynomials of degree at most two and `P₃` is such a polynomial on each side of `[−w, w]`.
Then `‖g‴‖₁ ≤ 1 + τ/T` and `|∫ g‴ k − k(τ)| ≤ δ + Mτ/T` for a continuous odd `k` with `|k| ≤ M`, which gives P-bump.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory Set OscInt.Statements OscInt.Blueprint.StationaryLeading
open scoped ContDiff

/-- The combination of translates `D[p](x) = ½[p(x − τ) − p(x + τ)] − (τ/2T)[p(x − T) − p(x + T)]`. -/
noncomputable def splBumpStencil (p : ℝ → ℝ) (τ T : ℝ) (x : ℝ) : ℝ :=
  1 / 2 * (p (x - τ) - p (x + τ)) - τ / (2 * T) * (p (x - T) - p (x + T))

/-- The primitive `x ↦ ∫_a^x f`. -/
noncomputable def splBumpPrim (f : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ := ∫ t in a..x, f t

/-! ### Amplitudes from a chain of real derivatives -/

/-- A real function with compact support and three successive derivatives, the last continuous, is an amplitude. -/
theorem splBump_amplitude_of_chain (G₀ G₁ G₂ G₃ : ℝ → ℝ) (h₀ : ∀ x, HasDerivAt G₀ (G₁ x) x)
    (h₁ : ∀ x, HasDerivAt G₁ (G₂ x) x) (h₂ : ∀ x, HasDerivAt G₂ (G₃ x) x) (h₃ : Continuous G₃)
    (hc : HasCompactSupport G₀) :
    SplAmplitude (fun x => (G₀ x : ℂ)) (fun x => (G₁ x : ℂ)) (fun x => (G₂ x : ℂ)) (fun x => (G₃ x : ℂ)) := by
  have e₁ : deriv G₀ = G₁ := funext fun x => (h₀ x).deriv
  have e₂ : deriv G₁ = G₂ := funext fun x => (h₁ x).deriv
  have e₃ : deriv G₂ = G₃ := funext fun x => (h₂ x).deriv
  have c₁ : HasCompactSupport G₁ := by rw [← e₁]; exact hc.deriv
  have c₂ : HasCompactSupport G₂ := by rw [← e₂]; exact c₁.deriv
  have c₃ : HasCompactSupport G₃ := by rw [← e₃]; exact c₂.deriv
  have k₀ : Continuous G₀ := continuous_iff_continuousAt.2 fun x => (h₀ x).continuousAt
  have k₁ : Continuous G₁ := continuous_iff_continuousAt.2 fun x => (h₁ x).continuousAt
  have k₂ : Continuous G₂ := continuous_iff_continuousAt.2 fun x => (h₂ x).continuousAt
  exact ⟨fun x => (h₀ x).ofReal_comp, fun x => (h₁ x).ofReal_comp, fun x => (h₂ x).ofReal_comp,
    (k₀.integrable_of_hasCompactSupport hc).ofReal, (k₁.integrable_of_hasCompactSupport c₁).ofReal,
    (k₂.integrable_of_hasCompactSupport c₂).ofReal, (h₃.integrable_of_hasCompactSupport c₃).ofReal⟩

/-- A real function whose third derivative is smooth is smooth, and so is its cast to the complex numbers. -/
theorem splBump_contDiff_of_chain (G₀ G₁ G₂ G₃ : ℝ → ℝ) (h₀ : ∀ x, HasDerivAt G₀ (G₁ x) x)
    (h₁ : ∀ x, HasDerivAt G₁ (G₂ x) x) (h₂ : ∀ x, HasDerivAt G₂ (G₃ x) x) (h₃ : ContDiff ℝ ∞ G₃) :
    ContDiff ℝ ∞ (fun x => (G₀ x : ℂ)) := by
  have e₁ : deriv G₀ = G₁ := funext fun x => (h₀ x).deriv
  have e₂ : deriv G₁ = G₂ := funext fun x => (h₁ x).deriv
  have e₃ : deriv G₂ = G₃ := funext fun x => (h₂ x).deriv
  have d₂ : ContDiff ℝ ∞ G₂ :=
    contDiff_infty_iff_deriv.2 ⟨fun x => (h₂ x).differentiableAt, by rw [e₃]; exact h₃⟩
  have d₁ : ContDiff ℝ ∞ G₁ :=
    contDiff_infty_iff_deriv.2 ⟨fun x => (h₁ x).differentiableAt, by rw [e₂]; exact d₂⟩
  have d₀ : ContDiff ℝ ∞ G₀ :=
    contDiff_infty_iff_deriv.2 ⟨fun x => (h₀ x).differentiableAt, by rw [e₁]; exact d₁⟩
  exact Complex.ofRealCLM.contDiff.comp d₀

/-- The derivative of the zero function is zero. -/
theorem splBump_deriv_eq_zero (f f' : ℝ → ℝ) (h : ∀ x, HasDerivAt f (f' x) x) (z : ∀ x, f x = 0) (x : ℝ) :
    f' x = 0 := by
  have hx := h x
  rw [show f = fun _ => (0 : ℝ) from funext z] at hx
  exact hx.unique (hasDerivAt_const x 0)

/-- If the third derivative is not identically zero, neither is the function. -/
theorem splBump_exists_ne_of_chain (G₀ G₁ G₂ G₃ : ℝ → ℝ) (h₀ : ∀ x, HasDerivAt G₀ (G₁ x) x)
    (h₁ : ∀ x, HasDerivAt G₁ (G₂ x) x) (h₂ : ∀ x, HasDerivAt G₂ (G₃ x) x) (x₀ : ℝ) (hx : G₃ x₀ ≠ 0) :
    ∃ x, (G₀ x : ℂ) ≠ 0 := by
  by_contra hne
  have z₀ : ∀ x, G₀ x = 0 := fun x => by
    by_contra h
    exact hne ⟨x, fun hz => h (Complex.ofReal_eq_zero.1 hz)⟩
  have z₁ := splBump_deriv_eq_zero G₀ G₁ h₀ z₀
  have z₂ := splBump_deriv_eq_zero G₁ G₂ h₁ z₁
  exact hx (splBump_deriv_eq_zero G₂ G₃ h₂ z₂ x₀)

/-! ### The combination of translates -/

/-- The combination of translates commutes with differentiation. -/
theorem splBump_stencil_hasDerivAt (p p' : ℝ → ℝ) (τ T : ℝ) (h : ∀ x, HasDerivAt p (p' x) x) (x : ℝ) :
    HasDerivAt (splBumpStencil p τ T) (splBumpStencil p' τ T x) x := by
  have a := (h (x - τ)).comp_sub_const x τ
  have b := (h (x + τ)).comp_add_const x τ
  have c := (h (x - T)).comp_sub_const x T
  have d := (h (x + T)).comp_add_const x T
  exact ((a.sub b).const_mul (1 / 2)).sub ((c.sub d).const_mul (τ / (2 * T)))

/-- The combination of translates of a smooth function is smooth. -/
theorem splBump_stencil_contDiff (ψ : ℝ → ℝ) (τ T : ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (splBumpStencil ψ τ T) := by
  show ContDiff ℝ ∞ (fun x => 1 / 2 * (ψ (x - τ) - ψ (x + τ)) - τ / (2 * T) * (ψ (x - T) - ψ (x + T)))
  fun_prop

/-- The combination vanishes to the left of `−(T + w)` on a function that vanishes to the left of `−w`. -/
theorem splBump_stencil_left (p : ℝ → ℝ) (w τ T x : ℝ) (hl : ∀ y, y ≤ -w → p y = 0) (h0τ : 0 ≤ τ) (hτT : τ ≤ T)
    (hx : x ≤ -(T + w)) : splBumpStencil p τ T x = 0 := by
  unfold splBumpStencil
  rw [hl (x - τ) (by linarith), hl (x + τ) (by linarith), hl (x - T) (by linarith), hl (x + T) (by linarith)]
  ring

/-- The combination annihilates polynomials of degree at most two: it vanishes to the right of `T + w` on a function
that is such a polynomial to the right of `w`. -/
theorem splBump_stencil_right (p : ℝ → ℝ) (w τ T A B C x : ℝ) (hr : ∀ y, w ≤ y → p y = A + B * y + C * y ^ 2)
    (h0τ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 < T) (hx : T + w ≤ x) : splBumpStencil p τ T x = 0 := by
  have h : τ / (2 * T) * T = τ / 2 := by field_simp
  unfold splBumpStencil
  rw [hr (x - τ) (by linarith), hr (x + τ) (by linarith), hr (x - T) (by linarith), hr (x + T) (by linarith)]
  linear_combination (2 * B + 4 * C * x) * h

/-- At `x = τ` only the translate centred at `τ` contributes: `D[ψ](τ) = ψ(0)/2`. -/
theorem splBump_stencil_self (ψ : ℝ → ℝ) (w τ T : ℝ) (hs : ∀ t, w ≤ |t| → ψ t = 0) (hw2 : w ≤ 2 * τ)
    (hwT : w ≤ T - τ) (h0τ : 0 ≤ τ) : splBumpStencil ψ τ T τ = 1 / 2 * ψ 0 := by
  have e : τ - τ = 0 := sub_self τ
  unfold splBumpStencil
  rw [hs (τ + τ) (le_trans (by linarith) (le_abs_self _)), hs (τ - T) (le_trans (by linarith) (neg_le_abs _)),
    hs (τ + T) (le_trans (by linarith) (le_abs_self _)), e]
  ring

/-! ### Primitives -/

/-- A primitive taken from `a` vanishes to the left of `a` if the function does. -/
theorem splBump_prim_eq_zero (f : ℝ → ℝ) (a x : ℝ) (hx : x ≤ a) (hf : ∀ t, t ≤ a → f t = 0) :
    splBumpPrim f a x = 0 := by
  have h : EqOn f (fun _ => (0 : ℝ)) (uIcc a x) := fun t ht => by
    rw [uIcc_of_ge hx] at ht
    exact hf t ht.2
  unfold splBumpPrim
  rw [intervalIntegral.integral_congr h]
  exact intervalIntegral.integral_zero

/-- Two functions with the same derivative on `[w, ∞)` differ by a constant there. -/
theorem splBump_eq_add_of_deriv_eq (f q f' q' : ℝ → ℝ) (w : ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hq : ∀ x, HasDerivAt q (q' x) x) (h : ∀ x, w ≤ x → f' x = q' x) (y : ℝ) (hy : w ≤ y) :
    f y = q y + (f w - q w) := by
  have hc : ContinuousOn (fun x => f x - q x) (Icc w y) := fun x _ =>
    ((hf x).sub (hq x)).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ico w y, HasDerivWithinAt (fun x => f x - q x) 0 (Ici x) x := fun x hx => by
    have hx' := ((hf x).sub (hq x)).hasDerivWithinAt (s := Ici x)
    rw [h x hx.1, sub_self] at hx'
    exact hx'
  have key : f y - q y = f w - q w := constant_of_has_deriv_right_zero hc hd y (right_mem_Icc.2 hy)
  linarith

/-- A triple primitive of a function vanishing on `[w, ∞)` is a polynomial of degree at most two on `[w, ∞)`. -/
theorem splBump_quadratic_right (P₃ P₂ P₁ ψ : ℝ → ℝ) (w : ℝ) (d₃ : ∀ x, HasDerivAt P₃ (P₂ x) x)
    (d₂ : ∀ x, HasDerivAt P₂ (P₁ x) x) (d₁ : ∀ x, HasDerivAt P₁ (ψ x) x) (hz : ∀ x, w ≤ x → ψ x = 0) :
    ∃ A B C : ℝ, ∀ x, w ≤ x → P₃ x = A + B * x + C * x ^ 2 := by
  have e₁ : ∀ y, w ≤ y → P₁ y = P₁ w := fun y hy => by
    have h := splBump_eq_add_of_deriv_eq P₁ (fun _ => 0) ψ (fun _ => 0) w d₁ (fun x => hasDerivAt_const x 0) hz y hy
    simpa using h
  have q₂ : ∀ x, HasDerivAt (fun x : ℝ => P₁ w * x) (P₁ w) x := fun x =>
    ((hasDerivAt_id' x).const_mul (P₁ w)).congr_deriv (mul_one _)
  have e₂ : ∀ y, w ≤ y → P₂ y = P₁ w * y + (P₂ w - P₁ w * w) := fun y hy =>
    splBump_eq_add_of_deriv_eq P₂ (fun x => P₁ w * x) P₁ (fun _ => P₁ w) w d₂ q₂ e₁ y hy
  have q₃ : ∀ x, HasDerivAt (fun x : ℝ => P₁ w / 2 * (x * x) + (P₂ w - P₁ w * w) * x)
      (P₁ w * x + (P₂ w - P₁ w * w)) x := fun x =>
    ((((hasDerivAt_id' x).mul (hasDerivAt_id' x)).const_mul (P₁ w / 2)).add
      ((hasDerivAt_id' x).const_mul (P₂ w - P₁ w * w))).congr_deriv (by ring)
  have e₃ : ∀ y, w ≤ y → P₃ y = P₁ w / 2 * (y * y) + (P₂ w - P₁ w * w) * y +
      (P₃ w - (P₁ w / 2 * (w * w) + (P₂ w - P₁ w * w) * w)) := fun y hy =>
    splBump_eq_add_of_deriv_eq P₃ _ P₂ _ w d₃ q₃ e₂ y hy
  refine ⟨P₃ w - (P₁ w / 2 * (w * w) + (P₂ w - P₁ w * w) * w), P₂ w - P₁ w * w, P₁ w / 2, fun y hy => ?_⟩
  rw [e₃ y hy]
  ring

/-- A continuous `ψ` vanishing outside `(−w, w)` has a triple primitive that vanishes on `(−∞, −w]` and is a
polynomial of degree at most two on `[w, ∞)`. -/
theorem splBump_exists_primitives (ψ : ℝ → ℝ) (w : ℝ) (hψ : Continuous ψ) (hs : ∀ t, w ≤ |t| → ψ t = 0) :
    ∃ P₁ P₂ P₃ : ℝ → ℝ, (∀ x, HasDerivAt P₃ (P₂ x) x) ∧ (∀ x, HasDerivAt P₂ (P₁ x) x) ∧
      (∀ x, HasDerivAt P₁ (ψ x) x) ∧ (∀ x, x ≤ -w → P₃ x = 0) ∧
        ∃ A B C : ℝ, ∀ x, w ≤ x → P₃ x = A + B * x + C * x ^ 2 := by
  have d₁ : ∀ x, HasDerivAt (splBumpPrim ψ (-w)) (ψ x) x := fun x =>
    (hψ.integral_hasStrictDerivAt (-w) x).hasDerivAt
  have c₁ : Continuous (splBumpPrim ψ (-w)) := continuous_iff_continuousAt.2 fun x => (d₁ x).continuousAt
  have d₂ : ∀ x, HasDerivAt (splBumpPrim (splBumpPrim ψ (-w)) (-w)) (splBumpPrim ψ (-w) x) x := fun x =>
    (c₁.integral_hasStrictDerivAt (-w) x).hasDerivAt
  have c₂ : Continuous (splBumpPrim (splBumpPrim ψ (-w)) (-w)) :=
    continuous_iff_continuousAt.2 fun x => (d₂ x).continuousAt
  have d₃ : ∀ x, HasDerivAt (splBumpPrim (splBumpPrim (splBumpPrim ψ (-w)) (-w)) (-w))
      (splBumpPrim (splBumpPrim ψ (-w)) (-w) x) x := fun x =>
    (c₂.integral_hasStrictDerivAt (-w) x).hasDerivAt
  have z₁ : ∀ x, x ≤ -w → splBumpPrim ψ (-w) x = 0 := fun x hx =>
    splBump_prim_eq_zero ψ (-w) x hx fun t ht => hs t (le_trans (by linarith) (neg_le_abs t))
  have z₂ : ∀ x, x ≤ -w → splBumpPrim (splBumpPrim ψ (-w)) (-w) x = 0 := fun x hx =>
    splBump_prim_eq_zero _ (-w) x hx z₁
  have z₃ : ∀ x, x ≤ -w → splBumpPrim (splBumpPrim (splBumpPrim ψ (-w)) (-w)) (-w) x = 0 := fun x hx =>
    splBump_prim_eq_zero _ (-w) x hx z₂
  exact ⟨_, _, _, d₃, d₂, d₁, z₃,
    splBump_quadratic_right _ _ _ ψ w d₃ d₂ d₁ fun x hx => hs x (hx.trans (le_abs_self x))⟩

/-- The amplitude: the combination of translates of a triple primitive of a smooth `ψ` vanishing outside `(−w, w)`
is smooth with compact support, its third derivative is the combination of translates of `ψ`, and it is not
identically zero if that third derivative is not. -/
theorem splBump_exists_amplitude (ψ : ℝ → ℝ) (w τ T : ℝ) (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, w ≤ |t| → ψ t = 0)
    (h0τ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 < T) (x₀ : ℝ) (hne : splBumpStencil ψ τ T x₀ ≠ 0) :
    ∃ g g₁ g₂ : ℝ → ℂ, SplAmplitude g g₁ g₂ (fun t => ((splBumpStencil ψ τ T t : ℝ) : ℂ)) ∧ ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧ ∃ x, g x ≠ 0 := by
  obtain ⟨P₁, P₂, P₃, d₃, d₂, d₁, hl, A, B, C, hr⟩ := splBump_exists_primitives ψ w hψ.continuous hs
  have D₀ := splBump_stencil_hasDerivAt P₃ P₂ τ T d₃
  have D₁ := splBump_stencil_hasDerivAt P₂ P₁ τ T d₂
  have D₂ := splBump_stencil_hasDerivAt P₁ ψ τ T d₁
  have hsm : ContDiff ℝ ∞ (splBumpStencil ψ τ T) := splBump_stencil_contDiff ψ τ T hψ
  have hcs : HasCompactSupport (splBumpStencil P₃ τ T) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(T + w)) (b := T + w)) fun x hx => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact splBump_stencil_left P₃ w τ T x hl h0τ hτT h.le
    · exact splBump_stencil_right P₃ w τ T A B C x hr h0τ hτT hT h.le
  exact ⟨_, _, _, splBump_amplitude_of_chain _ _ _ _ D₀ D₁ D₂ hsm.continuous hcs,
    splBump_contDiff_of_chain _ _ _ _ D₀ D₁ D₂ hsm, hcs.comp_left Complex.ofReal_zero,
    splBump_exists_ne_of_chain _ _ _ _ D₀ D₁ D₂ x₀ hne⟩

/-! ### The mollifier -/

/-- A smooth mollifier: nonnegative, of integral 1, vanishing outside `(−w, w)`, positive at `0`. -/
theorem splBump_exists_bump (w : ℝ) (hw : 0 < w) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 ≤ ψ t) ∧ ∫ t, ψ t = 1 ∧ (∀ t, w ≤ |t| → ψ t = 0) ∧ 0 < ψ 0 := by
  let f : ContDiffBump (0 : ℝ) := ⟨w / 2, w, by linarith, by linarith⟩
  have hsupp : Function.support (f.normed volume) = Metric.ball 0 w := f.support_normed_eq
  refine ⟨f.normed volume, f.contDiff_normed, f.nonneg_normed, f.integral_normed, fun t ht => ?_, ?_⟩
  · by_contra hne
    have hmem : t ∈ Function.support (f.normed volume) := hne
    rw [hsupp, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
    linarith
  · have hmem : (0 : ℝ) ∈ Function.support (f.normed volume) := by
      rw [hsupp]
      exact Metric.mem_ball_self hw
    exact lt_of_le_of_ne (f.nonneg_normed 0) (Ne.symm hmem)

/-- A function with integral 1 is integrable. -/
theorem splBump_integrable_of_integral_one (ψ : ℝ → ℝ) (h1 : ∫ t, ψ t = 1) : Integrable ψ := by
  by_contra hni
  rw [integral_undef hni] at h1
  exact zero_ne_one h1

/-- A translate of the mollifier times a continuous function is integrable. -/
theorem splBump_integrable_shift_mul (ψ : ℝ → ℝ) (w c : ℝ) (k : ℝ → ℂ) (hψ : Continuous ψ)
    (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k) : Integrable (fun t => (ψ (t - c) : ℂ) * k t) := by
  have hcont : Continuous fun t => (ψ (t - c) : ℂ) * k t :=
    (Complex.continuous_ofReal.comp (hψ.comp (continuous_id.sub continuous_const))).mul hk
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := c - w) (b := c + w)) fun t ht => ?_
  have hwt : w ≤ |t - c| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact ht ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hs _ hwt, Complex.ofReal_zero, zero_mul]

/-- The same for a translate to the left. -/
theorem splBump_integrable_shift_add_mul (ψ : ℝ → ℝ) (w c : ℝ) (k : ℝ → ℂ) (hψ : Continuous ψ)
    (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k) : Integrable (fun t => (ψ (t + c) : ℂ) * k t) := by
  have h := splBump_integrable_shift_mul ψ w (-c) k hψ hs hk
  simp only [sub_neg_eq_add] at h
  exact h

/-- The mollifier averages: if `|h| ≤ D` on `(c − w, c + w)` then `|∫ ψ(t − c) h(t) dt| ≤ D`. -/
theorem splBump_norm_integral_shift_mul_le (ψ : ℝ → ℝ) (w c : ℝ) (h : ℝ → ℂ) (D : ℝ) (h0 : ∀ t, 0 ≤ ψ t)
    (h1 : ∫ t, ψ t = 1) (hs : ∀ t, w ≤ |t| → ψ t = 0) (hD : ∀ t, |t - c| < w → ‖h t‖ ≤ D) :
    ‖∫ t, (ψ (t - c) : ℂ) * h t‖ ≤ D := by
  have hint : Integrable ψ := splBump_integrable_of_integral_one ψ h1
  have hg : Integrable (fun t => ψ (t - c) * D) := (hint.comp_sub_right c).mul_const D
  have hle : ∀ t, ‖(ψ (t - c) : ℂ) * h t‖ ≤ ψ (t - c) * D := fun t => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    rcases lt_or_ge |t - c| w with hlt | hge
    · exact mul_le_mul_of_nonneg_left (hD t hlt) (h0 _)
    · rw [hs _ hge, zero_mul, zero_mul]
  calc ‖∫ t, (ψ (t - c) : ℂ) * h t‖ ≤ ∫ t, ψ (t - c) * D := norm_integral_le_of_norm_le hg (ae_of_all _ hle)
    _ = D := by rw [integral_mul_const, integral_sub_right_eq_self ψ c, h1, one_mul]

/-- The mollifier estimate: if `|k − z| ≤ δ` on `(c − w, c + w)` then `|∫ ψ(t − c) k(t) dt − z| ≤ δ`. -/
theorem splBump_mollifier (ψ : ℝ → ℝ) (w c : ℝ) (k : ℝ → ℂ) (z : ℂ) (δ : ℝ) (hψ : Continuous ψ)
    (h0 : ∀ t, 0 ≤ ψ t) (h1 : ∫ t, ψ t = 1) (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k)
    (hc : ∀ t, |t - c| < w → ‖k t - z‖ ≤ δ) : ‖(∫ t, (ψ (t - c) : ℂ) * k t) - z‖ ≤ δ := by
  have hint : Integrable ψ := splBump_integrable_of_integral_one ψ h1
  have ia := splBump_integrable_shift_mul ψ w c k hψ hs hk
  have ib : Integrable (fun t => (ψ (t - c) : ℂ) * z) := ((hint.comp_sub_right c).ofReal).mul_const z
  have e0 : ∫ t, (ψ (t - c) : ℂ) = 1 :=
    (integral_ofReal (𝕜 := ℂ) (f := fun t => ψ (t - c))).trans
      (by rw [integral_sub_right_eq_self ψ c, h1]; exact RCLike.ofReal_one)
  have e1 : ∫ t, (ψ (t - c) : ℂ) * z = z := by rw [integral_mul_const, e0, one_mul]
  have e2 : (fun t => (ψ (t - c) : ℂ) * (k t - z)) = fun t => (ψ (t - c) : ℂ) * k t - (ψ (t - c) : ℂ) * z :=
    funext fun t => mul_sub _ _ _
  have e : ∫ t, (ψ (t - c) : ℂ) * (k t - z) = (∫ t, (ψ (t - c) : ℂ) * k t) - z := by
    rw [e2, integral_sub ia ib, e1]
  rw [← e]
  exact splBump_norm_integral_shift_mul_le ψ w c (fun t => k t - z) δ h0 h1 hs hc

/-! ### The two integrals of the third derivative -/

/-- The triangle inequality for the combination, pointwise. -/
theorem splBump_abs_combination_le (a b c d ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hρ : 0 ≤ ρ) : |1 / 2 * (a - b) - ρ * (c - d)| ≤ 1 / 2 * (a + b) + ρ * (c + d) := by
  have h1 := mul_nonneg hρ hc
  have h2 := mul_nonneg hρ hd
  rw [abs_le]
  constructor <;> nlinarith

/-- `‖g‴‖₁ ≤ 1 + τ/T` for `g‴` the combination of translates of the mollifier. -/
theorem splBump_integral_norm_stencil_le (ψ : ℝ → ℝ) (τ T : ℝ) (h0 : ∀ t, 0 ≤ ψ t) (h1 : ∫ t, ψ t = 1)
    (h0τ : 0 ≤ τ) (hT : 0 < T) : ∫ t, ‖((splBumpStencil ψ τ T t : ℝ) : ℂ)‖ ≤ 1 + 2 * (τ / (2 * T)) := by
  have hint : Integrable ψ := splBump_integrable_of_integral_one ψ h1
  have ha := hint.comp_sub_right τ
  have hb := hint.comp_add_right τ
  have hc := hint.comp_sub_right T
  have hd := hint.comp_add_right T
  have e1 : ∫ t, ψ (t - τ) = 1 := by rw [integral_sub_right_eq_self ψ τ, h1]
  have e2 : ∫ t, ψ (t + τ) = 1 := by rw [integral_add_right_eq_self ψ τ, h1]
  have e3 : ∫ t, ψ (t - T) = 1 := by rw [integral_sub_right_eq_self ψ T, h1]
  have e4 : ∫ t, ψ (t + T) = 1 := by rw [integral_add_right_eq_self ψ T, h1]
  have hr : 0 ≤ τ / (2 * T) := div_nonneg h0τ (by linarith)
  have i1 : Integrable (fun t => 1 / 2 * (ψ (t - τ) + ψ (t + τ))) := (ha.add hb).const_mul _
  have i2 : Integrable (fun t => τ / (2 * T) * (ψ (t - T) + ψ (t + T))) := (hc.add hd).const_mul _
  have hle : ∀ t, ‖((splBumpStencil ψ τ T t : ℝ) : ℂ)‖ ≤
      1 / 2 * (ψ (t - τ) + ψ (t + τ)) + τ / (2 * T) * (ψ (t - T) + ψ (t + T)) := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact splBump_abs_combination_le (ψ (t - τ)) (ψ (t + τ)) (ψ (t - T)) (ψ (t + T)) (τ / (2 * T)) (h0 _) (h0 _)
      (h0 _) (h0 _) hr
  calc ∫ t, ‖((splBumpStencil ψ τ T t : ℝ) : ℂ)‖
      ≤ ∫ t, (1 / 2 * (ψ (t - τ) + ψ (t + τ)) + τ / (2 * T) * (ψ (t - T) + ψ (t + T))) :=
        integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (i1.add i2) (ae_of_all _ hle)
    _ = 1 + 2 * (τ / (2 * T)) := by
        rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_add ha hb, integral_add hc hd,
          e1, e2, e3, e4]
        ring

/-- `∫ g‴ k` as the combination of the four mollified values of `k`. -/
theorem splBump_integral_stencil_mul (ψ : ℝ → ℝ) (w τ T : ℝ) (k : ℝ → ℂ) (hψ : Continuous ψ)
    (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k) :
    ∫ t, ((splBumpStencil ψ τ T t : ℝ) : ℂ) * k t =
      1 / 2 * ((∫ t, (ψ (t - τ) : ℂ) * k t) - ∫ t, (ψ (t + τ) : ℂ) * k t) -
        ((τ / (2 * T) : ℝ) : ℂ) * ((∫ t, (ψ (t - T) : ℂ) * k t) - ∫ t, (ψ (t + T) : ℂ) * k t) := by
  have ia := splBump_integrable_shift_mul ψ w τ k hψ hs hk
  have ib := splBump_integrable_shift_add_mul ψ w τ k hψ hs hk
  have ic := splBump_integrable_shift_mul ψ w T k hψ hs hk
  have id' := splBump_integrable_shift_add_mul ψ w T k hψ hs hk
  have i1 : Integrable (fun t => (1 / 2 : ℂ) * ((ψ (t - τ) : ℂ) * k t - (ψ (t + τ) : ℂ) * k t)) :=
    (ia.sub ib).const_mul _
  have i2 : Integrable (fun t => ((τ / (2 * T) : ℝ) : ℂ) * ((ψ (t - T) : ℂ) * k t - (ψ (t + T) : ℂ) * k t)) :=
    (ic.sub id').const_mul _
  have e : (fun t => ((splBumpStencil ψ τ T t : ℝ) : ℂ) * k t) = fun t =>
      (1 / 2 : ℂ) * ((ψ (t - τ) : ℂ) * k t - (ψ (t + τ) : ℂ) * k t) -
        ((τ / (2 * T) : ℝ) : ℂ) * ((ψ (t - T) : ℂ) * k t - (ψ (t + T) : ℂ) * k t) := by
    funext t
    unfold splBumpStencil
    push_cast
    ring
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_sub ia ib, integral_sub ic id']

/-- A real scalar times a bounded complex number. -/
theorem splBump_norm_real_mul_le (r : ℝ) (z : ℂ) (D : ℝ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ D) : ‖(r : ℂ) * z‖ ≤ r * D := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left hz hr

/-- The triangle inequality for four terms. -/
theorem splBump_norm_four_le (a b c d : ℂ) (A B C D : ℝ) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C)
    (hd : ‖d‖ ≤ D) : ‖a - b - c + d‖ ≤ A + B + C + D := by
  have t1 := norm_add_le (a - b - c) d
  have t2 := norm_sub_le (a - b) c
  have t3 := norm_sub_le a b
  linarith

/-- If `S = ½(I₁ − I₂) − ρ(I₃ − I₄)` with `|I₁ − z| ≤ δ`, `|I₂ + z| ≤ δ` and `|I₃|, |I₄| ≤ M`, then
`|S| ≥ |z| − δ − 2ρM`. -/
theorem splBump_norm_combination (S I₁ I₂ I₃ I₄ z : ℂ) (ρ δ M : ℝ) (hρ : 0 ≤ ρ)
    (hS : S = 1 / 2 * (I₁ - I₂) - (ρ : ℂ) * (I₃ - I₄)) (h1 : ‖I₁ - z‖ ≤ δ) (h2 : ‖I₂ + z‖ ≤ δ) (h3 : ‖I₃‖ ≤ M)
    (h4 : ‖I₄‖ ≤ M) : ‖z‖ - δ - 2 * ρ * M ≤ ‖S‖ := by
  subst hS
  have key : z = 1 / 2 * (I₁ - I₂) - (ρ : ℂ) * (I₃ - I₄) -
      (((1 / 2 : ℝ) : ℂ) * (I₁ - z) - ((1 / 2 : ℝ) : ℂ) * (I₂ + z) - (ρ : ℂ) * I₃ + (ρ : ℂ) * I₄) := by
    push_cast
    ring
  have n1 := splBump_norm_real_mul_le (1 / 2) (I₁ - z) δ (by norm_num) h1
  have n2 := splBump_norm_real_mul_le (1 / 2) (I₂ + z) δ (by norm_num) h2
  have n3 := splBump_norm_real_mul_le ρ I₃ M hρ h3
  have n4 := splBump_norm_real_mul_le ρ I₄ M hρ h4
  have hE := splBump_norm_four_le _ _ _ _ _ _ _ _ n1 n2 n3 n4
  have t0 := norm_sub_le (1 / 2 * (I₁ - I₂) - (ρ : ℂ) * (I₃ - I₄))
    (((1 / 2 : ℝ) : ℂ) * (I₁ - z) - ((1 / 2 : ℝ) : ℂ) * (I₂ + z) - (ρ : ℂ) * I₃ + (ρ : ℂ) * I₄)
  rw [← key] at t0
  linarith

/-- `|∫ g‴ k| ≥ |k(τ)| − δ − Mτ/T` for a continuous odd `k` with `|k| ≤ M` and `|k − k(τ)| ≤ δ` near `τ`. -/
theorem splBump_estimate (ψ : ℝ → ℝ) (w τ T δ M : ℝ) (k : ℝ → ℂ) (hψ : Continuous ψ) (h0 : ∀ t, 0 ≤ ψ t)
    (h1 : ∫ t, ψ t = 1) (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k) (hodd : ∀ t, k (-t) = -k t)
    (hM : ∀ t, ‖k t‖ ≤ M) (h0τ : 0 ≤ τ) (hT : 0 < T) (hc : ∀ t, |t - τ| < w → ‖k t - k τ‖ ≤ δ) :
    ‖k τ‖ - δ - 2 * (τ / (2 * T)) * M ≤ ‖∫ t, ((splBumpStencil ψ τ T t : ℝ) : ℂ) * k t‖ := by
  have hS := splBump_integral_stencil_mul ψ w τ T k hψ hs hk
  have ha := splBump_mollifier ψ w τ k (k τ) δ hψ h0 h1 hs hk hc
  have hc' : ∀ t, |t - -τ| < w → ‖k t - -k τ‖ ≤ δ := fun t ht => by
    have e : k t - -k τ = -(k (-t) - k τ) := by rw [hodd t]; ring
    have e' : -t - τ = -(t - -τ) := by ring
    rw [e, norm_neg]
    apply hc
    rw [e', abs_neg]
    exact ht
  have hb := splBump_mollifier ψ w (-τ) k (-k τ) δ hψ h0 h1 hs hk hc'
  simp only [sub_neg_eq_add] at hb
  have h3 := splBump_norm_integral_shift_mul_le ψ w T k M h0 h1 hs fun t _ => hM t
  have h4 := splBump_norm_integral_shift_mul_le ψ w (-T) k M h0 h1 hs fun t _ => hM t
  simp only [sub_neg_eq_add] at h4
  exact splBump_norm_combination _ _ _ _ _ (k τ) (τ / (2 * T)) δ M (div_nonneg h0τ (by linarith)) hS ha hb h3 h4

/-! ### The inequality and the two cases -/

/-- The final arithmetic: `(N − ε) S ≤ R` from `S ≤ 1 + 2r`, `R ≥ N − ε/2 − 2rM`, `N ≤ M` and `4Mr ≤ ε/2`. -/
theorem splBump_final_arith (N S R M ε r : ℝ) (hS0 : 0 ≤ S) (hS : S ≤ 1 + 2 * r) (hR0 : 0 ≤ R)
    (hR : N - ε / 2 - 2 * r * M ≤ R) (hNM : N ≤ M) (hε : 0 < ε) (hr : 0 ≤ r) (hρ : 4 * M * r ≤ ε / 2) :
    (N - ε) * S ≤ R := by
  rcases le_or_gt (N - ε) 0 with h | h
  · have h1 := mul_nonneg (neg_nonneg.2 h) hS0
    linarith
  · have h1 : (N - ε) * S ≤ (N - ε) * (1 + 2 * r) := mul_le_mul_of_nonneg_left hS h.le
    have h2 : (N - ε) * r ≤ M * r := mul_le_mul_of_nonneg_right (by linarith) hr
    linarith

/-- The inequality of P-bump for the combination of translates of a mollifier. -/
theorem splBump_inequality (ψ : ℝ → ℝ) (w τ T ε M : ℝ) (k : ℝ → ℂ) (hψ : Continuous ψ) (h0 : ∀ t, 0 ≤ ψ t)
    (h1 : ∫ t, ψ t = 1) (hs : ∀ t, w ≤ |t| → ψ t = 0) (hk : Continuous k) (hodd : ∀ t, k (-t) = -k t)
    (hM : ∀ t, ‖k t‖ ≤ M) (h0τ : 0 ≤ τ) (hT : 0 < T) (hε : 0 < ε)
    (hc : ∀ t, |t - τ| < w → ‖k t - k τ‖ ≤ ε / 2) (hρ : 4 * M * (τ / (2 * T)) ≤ ε / 2) :
    (‖k τ‖ - ε) * (∫ t, ‖((splBumpStencil ψ τ T t : ℝ) : ℂ)‖) ≤
      ‖∫ t, ((splBumpStencil ψ τ T t : ℝ) : ℂ) * k t‖ := by
  have hS := splBump_integral_norm_stencil_le ψ τ T h0 h1 h0τ hT
  have hS0 : 0 ≤ ∫ t, ‖((splBumpStencil ψ τ T t : ℝ) : ℂ)‖ := integral_nonneg fun t => norm_nonneg _
  have hR := splBump_estimate ψ w τ T (ε / 2) M k hψ h0 h1 hs hk hodd hM h0τ hT hc
  exact splBump_final_arith _ _ _ M ε (τ / (2 * T)) hS0 hS (norm_nonneg _) hR (hM τ) hε
    (div_nonneg h0τ (by linarith)) hρ

/-- P-bump for `τ > 0`, with the width `w` and the far point `T` given. -/
theorem splBump_pos_core (k : ℝ → ℂ) (M τ ε w T : ℝ) (hk : Continuous k) (hodd : ∀ t, k (-t) = -k t)
    (hM : ∀ t, ‖k t‖ ≤ M) (hτ : 0 < τ) (hε : 0 < ε) (hw : 0 < w) (hw2 : 2 * w ≤ τ) (hT2 : 2 * τ ≤ T)
    (hρ : 4 * M * (τ / (2 * T)) ≤ ε / 2) (hc : ∀ t, |t - τ| < w → ‖k t - k τ‖ ≤ ε / 2) :
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      (‖k τ‖ - ε) * (∫ t, ‖g₃ t‖) ≤ ‖∫ t, g₃ t * k t‖ := by
  obtain ⟨ψ, hψ, h0, h1, hs, hpos⟩ := splBump_exists_bump w hw
  have hT : 0 < T := by linarith
  have hne : splBumpStencil ψ τ T τ ≠ 0 := by
    rw [splBump_stencil_self ψ w τ T hs (by linarith) (by linarith) hτ.le]
    exact (mul_pos (by norm_num) hpos).ne'
  obtain ⟨g, g₁, g₂, hamp, hsm, hcs, hx⟩ :=
    splBump_exists_amplitude ψ w τ T hψ hs hτ.le (by linarith) hT τ hne
  exact ⟨g, g₁, g₂, _, hamp, hsm, hcs, hx,
    splBump_inequality ψ w τ T ε M k hψ.continuous h0 h1 hs hk hodd hM hτ.le hT hε hc hρ⟩

/-- P-bump for `τ > 0`: `w = min(w₀, τ)/2` with `w₀` from the continuity of `k` at `τ`, and `T = 2τ + 4Mτ/ε`. -/
theorem splBump_pos_case (k : ℝ → ℂ) (M τ ε : ℝ) (hk : Continuous k) (hodd : ∀ t, k (-t) = -k t)
    (hM : ∀ t, ‖k t‖ ≤ M) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      (‖k τ‖ - ε) * (∫ t, ‖g₃ t‖) ≤ ‖∫ t, g₃ t * k t‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (k 0)).trans (hM 0)
  obtain ⟨w₀, hw₀, hcont⟩ := Metric.continuousAt_iff.1 (hk.continuousAt (x := τ)) (ε / 2) (by linarith)
  have hmin : 0 < min w₀ τ := lt_min hw₀ hτ
  have hc : ∀ t, |t - τ| < min w₀ τ / 2 → ‖k t - k τ‖ ≤ ε / 2 := fun t ht => by
    have hd : dist t τ < w₀ := by
      rw [Real.dist_eq]
      linarith [min_le_left w₀ τ]
    have h := hcont hd
    rw [dist_eq_norm] at h
    exact h.le
  have h4 : 4 * M * τ / ε * ε = 4 * M * τ := by field_simp
  have hεT : ε * (2 * τ + 4 * M * τ / ε) = 2 * τ * ε + 4 * M * τ := by linear_combination h4
  have hq : 0 ≤ 4 * M * τ / ε := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hτ.le) hε.le
  have hρ : 4 * M * (τ / (2 * (2 * τ + 4 * M * τ / ε))) ≤ ε / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    linarith [mul_pos hτ hε]
  exact splBump_pos_core k M τ ε (min w₀ τ / 2) (2 * τ + 4 * M * τ / ε) hk hodd hM hτ hε (by linarith)
    (by linarith [min_le_right w₀ τ]) (by linarith) hρ hc

/-- P-bump for `τ = 0`: `k(0) = 0`, so any amplitude of the construction serves. -/
theorem splBump_zero_case (k : ℝ → ℂ) (ε : ℝ) (hodd : ∀ t, k (-t) = -k t) (hε : 0 < ε) :
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      (‖k 0‖ - ε) * (∫ t, ‖g₃ t‖) ≤ ‖∫ t, g₃ t * k t‖ := by
  obtain ⟨ψ, hψ, h0, h1, hs, hpos⟩ := splBump_exists_bump (1 / 2) (by norm_num)
  have hne : splBumpStencil ψ 1 2 1 ≠ 0 := by
    rw [splBump_stencil_self ψ (1 / 2) 1 2 hs (by norm_num) (by norm_num) (by norm_num)]
    exact (mul_pos (by norm_num) hpos).ne'
  obtain ⟨g, g₁, g₂, hamp, hsm, hcs, hx⟩ :=
    splBump_exists_amplitude ψ (1 / 2) 1 2 hψ hs (by norm_num) (by norm_num) (by norm_num) 1 hne
  refine ⟨g, g₁, g₂, _, hamp, hsm, hcs, hx, ?_⟩
  show (‖k 0‖ - ε) * (∫ t, ‖((splBumpStencil ψ 1 2 t : ℝ) : ℂ)‖) ≤
    ‖∫ t, ((splBumpStencil ψ 1 2 t : ℝ) : ℂ) * k t‖
  have hk0 : k 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    have h2 : (2 : ℂ) * k 0 = 0 := by linear_combination h
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  have hI : 0 ≤ ∫ t, ‖((splBumpStencil ψ 1 2 t : ℝ) : ℂ)‖ := integral_nonneg fun t => norm_nonneg _
  rw [hk0, norm_zero]
  linarith [norm_nonneg (∫ t, ((splBumpStencil ψ 1 2 t : ℝ) : ℂ) * k t), mul_nonneg hε.le hI]

/-- **P-bump** (`SplBumpFacts`): point masses for the third derivative, mollified. -/
theorem splBumpFacts : SplBumpFacts := by
  intro k M τ ε hk hodd hM h0τ hε
  rcases h0τ.eq_or_lt with h | h
  · subst h
    exact splBump_zero_case k ε hodd hε
  · exact splBump_pos_case k M τ ε hk hodd hM h hε

end OscInt.StationaryLeadingAux
