/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Batch VC2, part V3: a positive arc that starts at the turning point (route `docs/proof-VC2.md`, V3)

`Vdc2HeadFacts` from `Vdc2RootFacts`. With `F = f − f(c)` and `Γ(v) = ∫_0^{√(2v)} sin(w − u²/2) du`, the function
`H(x) = Γ(F(x))/√λ − ∫_c^x sin(w − F)` is continuous on `[c, d]`, vanishes at `c` and has a derivative `≥ 0` inside,
so `∫_c^d sin(w − F) ≤ Γ(F(d))/√λ ≤ Γ(w)/√λ = A(w)/(2√λ)`.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- The integrand `u ↦ sin(w − u²/2)` of the profile is continuous. -/
theorem vdc2H_integrand_continuous (w : ℝ) : Continuous fun u : ℝ => Real.sin (w - u ^ 2 / 2) :=
  Real.continuous_sin.comp (continuous_const.sub ((continuous_pow 2).div_const 2))

/-- `Γ(v) = ∫_0^{√(2v)} sin(w − u²/2) du` is continuous in `v`. -/
theorem vdc2H_gamma_continuous (w : ℝ) :
    Continuous fun v : ℝ => ∫ u in (0 : ℝ)..Real.sqrt (2 * v), Real.sin (w - u ^ 2 / 2) := by
  have h1 : Continuous fun b : ℝ => ∫ u in (0 : ℝ)..b, Real.sin (w - u ^ 2 / 2) :=
    intervalIntegral.continuous_primitive
      (fun a b => (vdc2H_integrand_continuous w).intervalIntegrable a b) 0
  exact h1.comp (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))

/-- For `v > 0`, `Γ` has derivative `sin(w − v)/√(2v)` at `v`. -/
theorem vdc2H_gamma_hasDerivAt (w v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun v : ℝ => ∫ u in (0 : ℝ)..Real.sqrt (2 * v), Real.sin (w - u ^ 2 / 2))
      (Real.sin (w - v) / Real.sqrt (2 * v)) v := by
  have hc := vdc2H_integrand_continuous w
  have h2v : 0 < 2 * v := by linarith
  have hs : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr h2v
  have h1 : HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, Real.sin (w - u ^ 2 / 2))
      (Real.sin (w - Real.sqrt (2 * v) ^ 2 / 2)) (Real.sqrt (2 * v)) :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have h2 : HasDerivAt (fun v : ℝ => Real.sqrt (2 * v)) (2 * 1 / (2 * Real.sqrt (2 * v))) v :=
    ((hasDerivAt_id v).const_mul 2).sqrt h2v.ne'
  have h3 := HasDerivAt.comp v h1 h2
  have he : Real.sin (w - Real.sqrt (2 * v) ^ 2 / 2) * (2 * 1 / (2 * Real.sqrt (2 * v))) =
      Real.sin (w - v) / Real.sqrt (2 * v) := by
    rw [Real.sq_sqrt h2v.le]
    have : 2 * v / 2 = v := by ring
    rw [this]
    field_simp
  rw [he] at h3
  exact h3

/-- `Γ(v) ≤ Γ(w)` for `v ≤ w` and `0 ≤ w ≤ π`: the integrand is nonnegative between `√(2v)` and `√(2w)`. -/
theorem vdc2H_gamma_le (w : ℝ) (hw0 : 0 ≤ w) (hwpi : w ≤ Real.pi) (v : ℝ) (hvw : v ≤ w) :
    (∫ u in (0 : ℝ)..Real.sqrt (2 * v), Real.sin (w - u ^ 2 / 2)) ≤
      ∫ u in (0 : ℝ)..Real.sqrt (2 * w), Real.sin (w - u ^ 2 / 2) := by
  have hc := vdc2H_integrand_continuous w
  have hle : Real.sqrt (2 * v) ≤ Real.sqrt (2 * w) := Real.sqrt_le_sqrt (by linarith)
  have h := intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.sqrt (2 * w)))
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.sqrt (2 * v)))
  have hnn : 0 ≤ ∫ u in Real.sqrt (2 * v)..Real.sqrt (2 * w), Real.sin (w - u ^ 2 / 2) :=
    intervalIntegral.integral_nonneg hle fun u hu => by
      have hu0 : 0 ≤ u := (Real.sqrt_nonneg _).trans hu.1
      have hu2 : u ^ 2 ≤ 2 * w := by
        have := pow_le_pow_left₀ hu0 hu.2 2
        rwa [Real.sq_sqrt (by linarith)] at this
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by nlinarith [sq_nonneg u])
  linarith

/-- **V-head** on one side, from the root inequality on that side. -/
theorem vdc2H_head (f f' : ℝ → ℝ) (c d lam w : ℝ) (hS : Vdc2Side f f' c d lam)
    (hroot : ∀ x ∈ Ioo c d, 2 * lam * (f x - f c) ≤ f' x ^ 2)
    (hw0 : 0 ≤ w) (hwpi : w ≤ Real.pi) (hfw : f d - f c ≤ w) :
    ∫ x in c..d, Real.sin (w - (f x - f c)) ≤ vdc2Profile w / (2 * Real.sqrt lam) := by
  obtain ⟨hcd, hlam, hfc, hfd, -, hpos⟩ := hS
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hc_mem : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hd_mem : d ∈ Icc c d := ⟨hcd, le_rfl⟩
  -- step 1: `f` is strictly increasing on `[c, d]`
  have hmono : StrictMonoOn f (Icc c d) :=
    strictMonoOn_of_deriv_pos (convex_Icc c d) hfc fun x hx => by
      rw [interior_Icc] at hx
      rw [(hfd x hx).deriv]
      exact hpos x hx
  have hFpos : ∀ x ∈ Ioo c d, 0 < f x - f c := fun x hx =>
    sub_pos.mpr (hmono hc_mem ⟨hx.1.le, hx.2.le⟩ hx.1)
  have hFle : ∀ x ∈ Ioo c d, f x - f c ≤ w := fun x hx => by
    have := hmono.monotoneOn ⟨hx.1.le, hx.2.le⟩ hd_mem hx.2.le
    linarith
  -- the integrand in `x`
  have hgc : ContinuousOn (fun x => Real.sin (w - (f x - f c))) (Icc c d) :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.sub (hfc.sub continuousOn_const))
  -- step 2: `Γ`
  have hΓc := vdc2H_gamma_continuous w
  -- step 3: `H` is continuous on `[c, d]` with a nonnegative derivative inside
  have hHc : ContinuousOn (fun x => (∫ u in (0 : ℝ)..Real.sqrt (2 * (f x - f c)), Real.sin (w - u ^ 2 / 2)) /
      Real.sqrt lam - ∫ t in c..x, Real.sin (w - (f t - f c))) (Icc c d) := by
    have hp : ContinuousOn (fun x => ∫ t in c..x, Real.sin (w - (f t - f c))) (Icc c d) := by
      have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume) (a := c) (b := d)
        (f := fun x => Real.sin (w - (f x - f c))) (by rw [uIcc_of_le hcd]; exact hgc.integrableOn_Icc)
      rwa [uIcc_of_le hcd] at this
    exact ((hΓc.comp_continuousOn (hfc.sub continuousOn_const)).div_const _).sub hp
  have hHd : ∀ x ∈ Ioo c d, HasDerivAt
      (fun x => (∫ u in (0 : ℝ)..Real.sqrt (2 * (f x - f c)), Real.sin (w - u ^ 2 / 2)) / Real.sqrt lam -
        ∫ t in c..x, Real.sin (w - (f t - f c)))
      (Real.sin (w - (f x - f c)) / Real.sqrt (2 * (f x - f c)) * f' x / Real.sqrt lam -
        Real.sin (w - (f x - f c))) x := by
    intro x hx
    have h1 := vdc2H_gamma_hasDerivAt w (f x - f c) (hFpos x hx)
    have h2 : HasDerivAt (fun x => f x - f c) (f' x) x := (hfd x hx).sub_const (f c)
    have h3 : HasDerivAt (fun x => ∫ u in (0 : ℝ)..Real.sqrt (2 * (f x - f c)), Real.sin (w - u ^ 2 / 2))
        (Real.sin (w - (f x - f c)) / Real.sqrt (2 * (f x - f c)) * f' x) x := by
      have h := HasDerivAt.comp x h1 h2
      exact h
    have hsub : Icc c x ⊆ Icc c d := Icc_subset_Icc_right hx.2.le
    have h4 : HasDerivAt (fun y => ∫ t in c..y, Real.sin (w - (f t - f c))) (Real.sin (w - (f x - f c))) x :=
      intervalIntegral.integral_hasDerivAt_right ((hgc.mono hsub).intervalIntegrable_of_Icc hx.1.le)
        ((hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hgc.continuousAt (Icc_mem_nhds hx.1 hx.2))
    exact (h3.div_const _).sub h4
  have hHmono := monotoneOn_of_deriv_nonneg (convex_Icc c d) hHc
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hHd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hHd x hx).deriv]
      have hF0 := hFpos x hx
      have hsin : 0 ≤ Real.sin (w - (f x - f c)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hFle x hx]) (by linarith)
      have hf'pos := hpos x hx
      have hsF : 0 < Real.sqrt (2 * (f x - f c)) := Real.sqrt_pos.mpr (by linarith)
      have hle : Real.sqrt (2 * (f x - f c)) * Real.sqrt lam ≤ f' x := by
        rw [← Real.sqrt_mul (by linarith)]
        exact Real.sqrt_le_iff.mpr ⟨hf'pos.le, by nlinarith [hroot x hx]⟩
      have he : Real.sin (w - (f x - f c)) / Real.sqrt (2 * (f x - f c)) * f' x / Real.sqrt lam -
          Real.sin (w - (f x - f c)) = Real.sin (w - (f x - f c)) *
            (f' x - Real.sqrt (2 * (f x - f c)) * Real.sqrt lam) /
            (Real.sqrt (2 * (f x - f c)) * Real.sqrt lam) := by
        field_simp
      rw [he]
      exact div_nonneg (mul_nonneg hsin (sub_nonneg.mpr hle)) (mul_pos hsF hsl).le)
  have hcd' := hHmono hc_mem hd_mem hcd
  simp only [sub_self, mul_zero, Real.sqrt_zero, intervalIntegral.integral_same, zero_div] at hcd'
  -- step 4: `Γ (F d) ≤ Γ w = A(w) / 2`
  have hΓle := vdc2H_gamma_le w hw0 hwpi (f d - f c) hfw
  have hprof : vdc2Profile w / (2 * Real.sqrt lam) =
      (∫ u in (0 : ℝ)..Real.sqrt (2 * w), Real.sin (w - u ^ 2 / 2)) / Real.sqrt lam := by
    rw [vdc2Profile]
    field_simp
  rw [hprof]
  have h5 := div_le_div_of_nonneg_right hΓle hsl.le
  linarith

/-- **V-head** (`Vdc2HeadFacts`) from **V-root** (`Vdc2RootFacts`). -/
theorem vdc2HeadFacts_of (hR : Vdc2RootFacts) : Vdc2HeadFacts := by
  intro f f' c d lam w hS hw0 hwpi hfw
  exact vdc2H_head f f' c d lam w hS (hR f f' c d lam hS) hw0 hwpi hfw

end OscInt.SecondDerivSharpAux
