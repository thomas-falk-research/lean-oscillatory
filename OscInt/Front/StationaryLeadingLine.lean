/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Batch SPL, part Line: P-line from P-kernel (route `docs/proof-SPL.md`, Propositions 3 and 3′; sections 10, 11)

Half-line: on `[0, T]`, three integrations by parts with `E₁′ = e`, `E₂′ = E₁`, `(iκ₊)′ = E₂` give
`∫₀ᵀ g e = [g E₁ − g′ E₂ + g″ iκ₊]₀ᵀ − ∫₀ᵀ g‴ iκ₊`; `g, g′, g″ → 0` at `+∞` and `E₁, E₂, κ₊` are bounded on `[0, ∞)`, so
`∫₀^∞ g e = L g(0) + i g′(0) − i ∫₀^∞ g‴ κ₊` (`E₁(0) = −L`, `E₂(0) = i`, `κ₊(0) = 0`). Line: the same for `g(−·)`, with
`e` even and `κ` odd, and the two half-lines add up to `∫ g e = 2L g(0) − i ∫ g‴ κ`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory Set Filter Topology OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- If `f → 0` at `+∞` and `|h| ≤ M` on `[0, ∞)`, then `f h → 0` at `+∞`. -/
theorem splLine_tendsto_mul_bdd {f h : ℝ → ℂ} {M : ℝ} (hf : Tendsto f atTop (𝓝 0))
    (hh : ∀ u : ℝ, 0 ≤ u → ‖h u‖ ≤ M) : Tendsto (fun T => f T * h T) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun T => ‖f T‖ * M) atTop (𝓝 0) := by
    have := (tendsto_zero_iff_norm_tendsto_zero.1 hf).mul_const M
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hh T hT) (norm_nonneg _)

/-- If `f` is integrable and `h` is continuous with `|h| ≤ M` on `[0, ∞)`, then `f h` is integrable on `(0, ∞)`. -/
theorem splLine_integrableOn_mul {f h : ℝ → ℂ} {M : ℝ} (hf : Integrable f) (hc : Continuous h)
    (hh : ∀ u : ℝ, 0 ≤ u → ‖h u‖ ≤ M) : IntegrableOn (fun u => f u * h u) (Ioi 0) := by
  refine Integrable.mono' (hf.norm.mul_const M).integrableOn
    (hf.aestronglyMeasurable.mul hc.aestronglyMeasurable).restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hh u (le_of_lt hu)) (norm_nonneg _)

/-- `e(u) = e^{iu²/2}` is continuous on the line. -/
theorem splLine_continuous_fresnelE : Continuous fresnelE := by
  unfold fresnelE
  fun_prop

/-- `|e(u)| ≤ 1` (stated on `[0, ∞)`, the shape the half-line lemmas take). -/
theorem splLine_norm_fresnelE_le (u : ℝ) (_hu : 0 ≤ u) : ‖fresnelE u‖ ≤ 1 := by
  unfold fresnelE
  exact (Complex.norm_exp_ofReal_mul_I _).le

/-- `e` is even. -/
theorem splLine_fresnelE_neg (u : ℝ) : fresnelE (-u) = fresnelE u := by
  unfold fresnelE
  rw [neg_sq]

/-- `|iκ₊(u)| ≤ 7/8` for `u ≥ 0`, from the bound of `κ` in P-kernel. -/
theorem splLine_norm_I_mul_kernelPos_le (hK : SplKernelFacts) (u : ℝ) (hu : 0 ≤ u) :
    ‖Complex.I * splKernelPos u‖ ≤ 7 / 8 := by
  have h := hK.2.2.2.2.2.2.2 u
  unfold splKernel at h
  rw [ite_eq_left hu] at h
  simpa using h

/-- `E₁(0) = −L`. -/
theorem splLine_primOne_zero : splPrimOne 0 = -fresnelLimit := by simp [splPrimOne, fresnelPrim]

/-- `E₂(0) = i`. -/
theorem splLine_primTwo_zero : splPrimTwo 0 = Complex.I := by simp [splPrimTwo, fresnelE]

/-- `κ₊(0) = 0`. -/
theorem splLine_kernelPos_zero : splKernelPos 0 = 0 := by simp [splKernelPos, fresnelPrim]

/-- Three integrations by parts on `[0, T]`:
`∫₀ᵀ g e = [g E₁ − g′ E₂ + g″ iκ₊](T) − [g E₁ − g′ E₂ + g″ iκ₊](0) − ∫₀ᵀ g‴ iκ₊`. -/
theorem splLine_ibp (hK : SplKernelFacts) {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, g u * fresnelE u =
      (g T * splPrimOne T - g₁ T * splPrimTwo T + g₂ T * (Complex.I * splKernelPos T)) +
        (-(g 0 * splPrimOne 0) + g₁ 0 * splPrimTwo 0 - g₂ 0 * (Complex.I * splKernelPos 0)) -
          ∫ u in (0 : ℝ)..T, g₃ u * (Complex.I * splKernelPos u) := by
  obtain ⟨hd0, hd1, hd2, _, i1, i2, i3⟩ := hg
  obtain ⟨k1, k2, k3, _⟩ := hK
  have hc1 : Continuous splPrimOne := continuous_iff_continuousAt.2 fun u => (k1 u).continuousAt
  have hc2 : Continuous splPrimTwo := continuous_iff_continuousAt.2 fun u => (k2 u).continuousAt
  have e1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T) (u := g) (v := splPrimOne)
    (u' := g₁) (v' := fresnelE) (fun x _ => hd0 x) (fun x _ => k1 x) i1.intervalIntegrable
    (splLine_continuous_fresnelE.intervalIntegrable _ _)
  have e2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T) (u := g₁) (v := splPrimTwo)
    (u' := g₂) (v' := splPrimOne) (fun x _ => hd1 x) (fun x _ => k2 x) i2.intervalIntegrable
    (hc1.intervalIntegrable _ _)
  have e3 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T) (u := g₂)
    (v := fun v => Complex.I * splKernelPos v) (u' := g₃) (v' := splPrimTwo) (fun x _ => hd2 x) (fun x _ => k3 x)
    i3.intervalIntegrable (hc2.intervalIntegrable _ _)
  rw [e1, e2, e3]
  ring

/-- The boundary term at `T` tends to `0`: `g(T) E₁(T) − g′(T) E₂(T) + g″(T) iκ₊(T) → 0` as `T → +∞`. -/
theorem splLine_tendsto_boundary (hK : SplKernelFacts) {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) :
    Tendsto (fun T : ℝ => g T * splPrimOne T - g₁ T * splPrimTwo T + g₂ T * (Complex.I * splKernelPos T)) atTop
      (𝓝 0) := by
  obtain ⟨hd0, hd1, hd2, i0, i1, i2, i3⟩ := hg
  have b1 := hK.2.2.2.1
  have b2 := hK.2.2.2.2.1
  have t0 : Tendsto g atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd0 x) i1.integrableOn i0.integrableOn
  have t1 : Tendsto g₁ atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd1 x) i2.integrableOn i1.integrableOn
  have t2 : Tendsto g₂ atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd2 x) i3.integrableOn i2.integrableOn
  have := ((splLine_tendsto_mul_bdd t0 b1).sub (splLine_tendsto_mul_bdd t1 b2)).add
    (splLine_tendsto_mul_bdd (h := fun v => Complex.I * splKernelPos v) t2 (splLine_norm_I_mul_kernelPos_le hK))
  simpa using this

/-- Proposition 3 before the values at `0` are inserted:
`∫₀^∞ g e = −g(0) E₁(0) + g′(0) E₂(0) − g″(0) iκ₊(0) − ∫₀^∞ g‴ iκ₊`. -/
theorem splLine_half_limit (hK : SplKernelFacts) {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) :
    ∫ u in Ioi 0, g u * fresnelE u =
      (-(g 0 * splPrimOne 0) + g₁ 0 * splPrimTwo 0 - g₂ 0 * (Complex.I * splKernelPos 0)) -
        ∫ u in Ioi 0, g₃ u * (Complex.I * splKernelPos u) := by
  have hcK : Continuous fun v => Complex.I * splKernelPos v :=
    continuous_iff_continuousAt.2 fun u => (hK.2.2.1 u).continuousAt
  have tB := splLine_tendsto_boundary hK hg
  have tL := intervalIntegral_tendsto_integral_Ioi 0
    (splLine_integrableOn_mul hg.2.2.2.1 splLine_continuous_fresnelE splLine_norm_fresnelE_le) tendsto_id
  have tR := intervalIntegral_tendsto_integral_Ioi 0
    (splLine_integrableOn_mul hg.2.2.2.2.2.2 hcK (splLine_norm_I_mul_kernelPos_le hK)) tendsto_id
  have tRHS := (tB.add_const (-(g 0 * splPrimOne 0) + g₁ 0 * splPrimTwo 0 -
    g₂ 0 * (Complex.I * splKernelPos 0))).sub tR
  have hfun : (fun T : ℝ => ∫ u in (0 : ℝ)..T, g u * fresnelE u) = fun T =>
      (g T * splPrimOne T - g₁ T * splPrimTwo T + g₂ T * (Complex.I * splKernelPos T)) +
        (-(g 0 * splPrimOne 0) + g₁ 0 * splPrimTwo 0 - g₂ 0 * (Complex.I * splKernelPos 0)) -
          ∫ u in (0 : ℝ)..id T, g₃ u * (Complex.I * splKernelPos u) :=
    funext (splLine_ibp hK hg)
  simp only [id] at tL
  rw [hfun] at tL
  have hlim := tendsto_nhds_unique tL tRHS
  rw [hlim]
  ring

/-- Proposition 3 (half-line): `∫₀^∞ g e = L g(0) + i g′(0) − i ∫₀^∞ g‴ κ₊`. -/
theorem splLine_half (hK : SplKernelFacts) {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) :
    ∫ u in Ioi 0, g u * fresnelE u =
      fresnelLimit * g 0 + Complex.I * g₁ 0 - Complex.I * ∫ t in Ioi 0, g₃ t * splKernelPos t := by
  have hint : ∫ t in Ioi 0, g₃ t * (Complex.I * splKernelPos t) =
      Complex.I * ∫ t in Ioi 0, g₃ t * splKernelPos t := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show g₃ t * (Complex.I * splKernelPos t) = Complex.I * (g₃ t * splKernelPos t)
    ring
  rw [splLine_half_limit hK hg, splLine_primOne_zero, splLine_primTwo_zero, splLine_kernelPos_zero, hint]
  ring

/-- The reflected amplitude: `g(−·)` with derivatives `−g′(−·)`, `g″(−·)`, `−g‴(−·)` is an amplitude. -/
theorem splLine_reflect_amplitude {g g₁ g₂ g₃ : ℝ → ℂ} (hg : SplAmplitude g g₁ g₂ g₃) :
    SplAmplitude (fun v => g (-v)) (fun v => -g₁ (-v)) (fun v => g₂ (-v)) (fun v => -g₃ (-v)) := by
  obtain ⟨hd0, hd1, hd2, i0, i1, i2, i3⟩ := hg
  have hneg : ∀ x : ℝ, HasDerivAt (fun v : ℝ => -v) (-1) x := fun x => (hasDerivAt_id x).neg
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, i0.comp_neg, i1.comp_neg.neg, i2.comp_neg, i3.comp_neg.neg⟩
  · have h : HasDerivAt (fun v => g (-v)) ((-1 : ℝ) • g₁ (-x)) x := (hd0 (-x)).scomp x (hneg x)
    refine h.congr_deriv ?_; simp
  · have h : HasDerivAt (fun v => -g₁ (-v)) (-((-1 : ℝ) • g₂ (-x))) x := ((hd1 (-x)).scomp x (hneg x)).neg
    refine h.congr_deriv ?_; simp
  · have h : HasDerivAt (fun v => g₂ (-v)) ((-1 : ℝ) • g₃ (-x)) x := (hd2 (-x)).scomp x (hneg x)
    refine h.congr_deriv ?_; simp

/-- `g e` is integrable on the line when `g` is (`|e| = 1`). -/
theorem splLine_integrable_mul_fresnelE {g : ℝ → ℂ} (i0 : Integrable g) : Integrable fun u => g u * fresnelE u := by
  refine Integrable.mono' (i0.norm.mul_const 1)
    (i0.aestronglyMeasurable.mul splLine_continuous_fresnelE.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (by unfold fresnelE; exact (Complex.norm_exp_ofReal_mul_I _).le) (norm_nonneg _)

/-- `g‴ κ` is integrable on the line when `g‴` is (`κ` is continuous and `|κ| ≤ 7/8`). -/
theorem splLine_integrable_mul_kernel (hK : SplKernelFacts) {g₃ : ℝ → ℂ} (i3 : Integrable g₃) :
    Integrable fun t => g₃ t * splKernel t := by
  have hcK := hK.2.2.2.2.2.2.1
  have hbK := hK.2.2.2.2.2.2.2
  refine Integrable.mono' (i3.norm.mul_const (7 / 8)) (i3.aestronglyMeasurable.mul hcK.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbK u) (norm_nonneg _)

/-- The left half-line by reflection, `e` being even: `∫_{−∞}^0 g e = ∫₀^∞ g(−u) e(u) du`. -/
theorem splLine_left_fresnelE (g : ℝ → ℂ) :
    ∫ u in Iic (0 : ℝ), g u * fresnelE u = ∫ u in Ioi (0 : ℝ), g (-u) * fresnelE u := by
  have h := integral_comp_neg_Ioi (0 : ℝ) (fun u => g u * fresnelE u)
  simp only [neg_zero, splLine_fresnelE_neg] at h
  exact h.symm

/-- The left half-line by reflection, `κ` being odd: `∫_{−∞}^0 g‴ κ = −∫₀^∞ g‴(−t) κ₊(t) dt`. -/
theorem splLine_left_kernel (hK : SplKernelFacts) (g₃ : ℝ → ℂ) :
    ∫ t in Iic (0 : ℝ), g₃ t * splKernel t = ∫ t in Ioi (0 : ℝ), g₃ (-t) * splKernelPos t * (-1) := by
  have hodd := hK.2.2.2.2.2.1
  have h := integral_comp_neg_Ioi (0 : ℝ) (fun t => g₃ t * splKernel t)
  simp only [neg_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [hodd, splKernel, ite_eq_left ht0]
  ring

/-- On the right half-line `κ = κ₊`: `∫₀^∞ g‴ κ = ∫₀^∞ g‴ κ₊`. -/
theorem splLine_right_kernel (g₃ : ℝ → ℂ) :
    ∫ t in Ioi (0 : ℝ), g₃ t * splKernel t = ∫ t in Ioi (0 : ℝ), g₃ t * splKernelPos t := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [splKernel, ite_eq_left ht0]

/-- **P-line** from P-kernel (Proposition 3′): `∫ g e = 2L g(0) − i ∫ g‴ κ` for every amplitude, by Proposition 3 for
`g` and for `g(−·)`. -/
theorem splLineFacts_of (hK : SplKernelFacts) : SplLineFacts := by
  intro g g₁ g₂ g₃ hg
  have h1 := splLine_half hK hg
  have h2 := splLine_half hK (splLine_reflect_amplitude hg)
  simp only [neg_zero] at h2
  have iL := splLine_integrable_mul_fresnelE hg.2.2.2.1
  have iR := splLine_integrable_mul_kernel hK hg.2.2.2.2.2.2
  have h2' : ∫ t in Ioi (0 : ℝ), -g₃ (-t) * splKernelPos t =
      ∫ t in Ioi (0 : ℝ), g₃ (-t) * splKernelPos t * (-1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [← intervalIntegral.integral_Iic_add_Ioi iL.integrableOn iL.integrableOn,
    ← intervalIntegral.integral_Iic_add_Ioi iR.integrableOn iR.integrableOn,
    splLine_left_fresnelE, splLine_left_kernel hK, splLine_right_kernel, h1, h2, h2']
  ring

end OscInt.StationaryLeadingAux
