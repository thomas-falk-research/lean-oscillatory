/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.StationaryLeading
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Sanity theorems through the draft batch-SPL statement constants (the quadratic-phase leading term)

As for the earlier batches (`docs/lessons.md`, rules 8 and 9): every theorem about a statement of batch SPL takes
that statement constant as its only statement hypothesis (the consistency theorem takes two), discharges its
hypotheses on closed data and concludes its conclusion there. Written by an agent of the lead before the statements
were frozen, against `OscInt/Statements/StationaryLeading.lean`, which it did not change. Planted copies and
witnesses: `docs/replay/plants/2026-11-19-SPL/`.

What is NOT here, on purpose: no proof of SPL-I, SPL-S, SPL-K or SPL-A; no limit of `fresnelPrim` at infinity
(`fresnelLimit` is used only as the closed form `√π (1 + i)/2`); no bound of `splKernel` except its value at `0`
and its oddness (`kernel_large` and `kernel_le_of_attained_of_sevenEighths` are conditional on statements); no
integration by parts for general amplitudes. The value of `∫ G_s(u) e^{iλu²/2} du` is Mathlib's complex Gaussian
integral, not a consequence of the batch.

Data:
* A. The definitions: `F(0) = 0`, `κ₊(0) = 0`, `κ(0) = 0`, `κ(−τ) = −κ(τ)`; `F(∞)² = πi/2` with `Re F(∞) > 0`;
  `√(2π) e^{iπ/4} = 2F(∞)` (the constant of the leading term in `splRemainder` is twice `fresnelLimit`).
* B. The class: for `s > 0` the Gaussian `G_s(u) = e^{−(su)²/2}` with its three derivatives is an amplitude. Bites:
  the constant `1` with zero derivatives is not (integrability); `G_1` with `G_1` in place of `G_1′` is not (the
  derivative).
* C. Exact data: `∫ G_s(u) e^{iλu²/2} du = (2π/(s² − λi))^{1/2}`, so `R(G_s, λ) = root − ℓ` with
  `ℓ = √(2π/λ) e^{iπ/4}`; `‖G_s‴‖₁ = s²(2 + 8e^{−3/2})` and `‖G_s″‖₁ = 4s e^{−1/2}`; the identity
  `root² − ℓ² = −2πs²/((s² − λi)(−λi))` and, both numbers being in the closed first quadrant with `|root| ≤ |ℓ|`,
  the certified bounds `√(2π)s²/(2√λ√(s⁴ + λ²)) ≤ |R(G_s, λ)| ≤ √(2π)s²/(√λ√(s⁴ + λ²))`. An amplitude with
  `‖g₃‖₁ = 0` is identically zero.
* D. SPL-I, SPL-S and SPL-K on the Gaussian family, and written out at `(s, λ) = (1, 4)` and `(2, 9)`; SPL-I forces
  `6/5 ≤ |∫ G_1‴(t) κ(2t) dt| ≤ 5/2`; SPL-S forces `|κ(τ)| ≥ 3/10` for some `τ ≥ 0`; the two numeric inequalities
  that SPL-K gives are within a factor `3` of the truth (`…_within`, unconditional); SPL-A at `τ = 0` and at
  `τ = 1`; SPL-A and SPL-K together give `|κ| ≤ 7/8` on the line.
* Data for the planted controls only (last section).

What this layer cannot see before a proof exists: any property of the kernel beyond `κ(0) = 0` and oddness, in
particular the argument `√λ t` of the kernel in SPL-I for `λ ≠ 1` otherwise than relative to SPL-I itself, and the
existence claim of SPL-A for `τ > 0`; see the plant record for what each planted mutation does.
-/

namespace OscInt.API.StationaryLeadingSanity

open OscInt.Statements MeasureTheory Set Filter
open scoped ContDiff Topology

/-! ## A. The definitions at explicit points -/

/-- `F(0) = 0`. -/
theorem fresnelPrim_zero : fresnelPrim 0 = 0 := by
  unfold fresnelPrim
  exact intervalIntegral.integral_same

/-- `κ₊(0) = 0`. -/
theorem splKernelPos_zero : splKernelPos 0 = 0 := by
  unfold splKernelPos
  rw [fresnelPrim_zero]
  simp

/-- `κ(0) = 0`. -/
theorem splKernel_zero : splKernel 0 = 0 := by
  unfold splKernel
  rw [ite_eq_left le_rfl, splKernelPos_zero]

/-- `κ` is odd: `κ(−τ) = −κ(τ)` for every real `τ` (from the definition by cases and `κ₊(0) = 0`). -/
theorem splKernel_neg (τ : ℝ) : splKernel (-τ) = -splKernel τ := by
  unfold splKernel
  rcases lt_trichotomy τ 0 with h | h | h
  · rw [ite_eq_left (by linarith), ite_eq_right (by linarith), neg_neg]
  · subst h
    simp [splKernelPos_zero]
  · rw [ite_eq_right (by linarith), ite_eq_left (by linarith), neg_neg]

/-- `|κ|` is even. -/
theorem norm_splKernel_neg (τ : ℝ) : ‖splKernel (-τ)‖ = ‖splKernel τ‖ := by
  rw [splKernel_neg, norm_neg]

/-- `‖κ(|τ|)‖ = ‖κ(τ)‖`. -/
theorem norm_splKernel_abs (τ : ℝ) : ‖splKernel |τ|‖ = ‖splKernel τ‖ := by
  rcases abs_cases τ with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, norm_splKernel_neg]

/-- `F(∞)² = πi/2`. -/
theorem fresnelLimit_sq : fresnelLimit ^ 2 = (Real.pi : ℂ) * Complex.I / 2 := by
  unfold fresnelLimit
  have h : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hI : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    rw [add_sq, Complex.I_sq]
    ring
  rw [div_pow, mul_pow, h, hI]
  ring

/-- `Re F(∞) = √π/2`. -/
theorem fresnelLimit_re : fresnelLimit.re = Real.sqrt Real.pi / 2 := by
  unfold fresnelLimit
  simp

/-- `Im F(∞) = √π/2`. -/
theorem fresnelLimit_im : fresnelLimit.im = Real.sqrt Real.pi / 2 := by
  unfold fresnelLimit
  simp

/-- `Re F(∞) > 0`: with `F(∞)² = πi/2` this fixes `F(∞)` among the two square roots of `πi/2`. -/
theorem fresnelLimit_re_pos : 0 < fresnelLimit.re := by
  rw [fresnelLimit_re]
  exact div_pos (Real.sqrt_pos.2 Real.pi_pos) two_pos

/-- `e^{iπ/4} = (√2/2)(1 + i)`. -/
theorem exp_pi_div_four : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

/-- `√(2π) e^{iπ/4} = 2 F(∞)`: the constant of the leading term of `splRemainder` is twice the closed form
`fresnelLimit`. -/
theorem sqrt_two_pi_mul_exp : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
    2 * fresnelLimit := by
  rw [exp_pi_div_four, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold fresnelLimit
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  push_cast
  linear_combination (((Real.sqrt Real.pi : ℝ) : ℂ) * (1 + Complex.I) / 2) * h2

/-! ## B. The class: the Gaussian family `G_s(u) = e^{−(su)²/2}` and two bites -/

/-- `e^{−(su)²/2}` as a real function. -/
noncomputable def gaussR (s u : ℝ) : ℝ := Real.exp (-(s * u) ^ 2 / 2)

/-- The Gaussian amplitude `G_s(u) = e^{−(su)²/2}`, complex-valued. -/
noncomputable def gauss (s u : ℝ) : ℂ := ((gaussR s u : ℝ) : ℂ)

/-- `G_s′(u) = −s²u e^{−(su)²/2}`. -/
noncomputable def gauss1 (s u : ℝ) : ℂ := ((-(s ^ 2 * u) * gaussR s u : ℝ) : ℂ)

/-- `G_s″(u) = (s⁴u² − s²) e^{−(su)²/2}`. -/
noncomputable def gauss2 (s u : ℝ) : ℂ := (((s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u : ℝ) : ℂ)

/-- `G_s‴(u) = (3s⁴u − s⁶u³) e^{−(su)²/2}`. -/
noncomputable def gauss3 (s u : ℝ) : ℂ := (((3 * s ^ 4 * u - s ^ 6 * u ^ 3) * gaussR s u : ℝ) : ℂ)

/-- The derivative of `e^{−(su)²/2}` is `−s²u e^{−(su)²/2}`. -/
theorem gaussR_hasDerivAt (s u : ℝ) : HasDerivAt (gaussR s) (-(s ^ 2 * u) * gaussR s u) u := by
  have h1 : HasDerivAt (fun u : ℝ => -(s * u) ^ 2 / 2) (-(s ^ 2 * u)) u := by
    have h := (hasDerivAt_pow 2 u).const_mul (-(s ^ 2) / 2)
    have e : (fun u : ℝ => -(s * u) ^ 2 / 2) = fun x => -(s ^ 2) / 2 * x ^ 2 := by
      funext x
      ring
    rw [e]
    convert h using 1
    push_cast
    ring
  have h2 := h1.exp
  unfold gaussR
  convert h2 using 1
  ring

/-- The derivative of `−s²u e^{−(su)²/2}` is `(s⁴u² − s²) e^{−(su)²/2}`. -/
theorem gaussR1_hasDerivAt (s u : ℝ) :
    HasDerivAt (fun u => -(s ^ 2 * u) * gaussR s u) ((s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u) u := by
  have h1 : HasDerivAt (fun u : ℝ => -(s ^ 2 * u)) (-(s ^ 2)) u := by
    have h := (hasDerivAt_id u).const_mul (-(s ^ 2))
    have e : (fun u : ℝ => -(s ^ 2 * u)) = fun x => -(s ^ 2) * id x := by
      funext x
      simp
    rw [e]
    convert h using 1
    ring
  have h := h1.mul (gaussR_hasDerivAt s u)
  convert h using 1
  ring

/-- The derivative of `(s⁴u² − s²) e^{−(su)²/2}` is `(3s⁴u − s⁶u³) e^{−(su)²/2}`. -/
theorem gaussR2_hasDerivAt (s u : ℝ) :
    HasDerivAt (fun u => (s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u) ((3 * s ^ 4 * u - s ^ 6 * u ^ 3) * gaussR s u) u := by
  have h1 : HasDerivAt (fun u : ℝ => s ^ 4 * u ^ 2 - s ^ 2) (s ^ 4 * (2 * u)) u := by
    have h := ((hasDerivAt_pow 2 u).const_mul (s ^ 4)).sub_const (s ^ 2)
    convert h using 1
    push_cast
    ring
  have h := h1.mul (gaussR_hasDerivAt s u)
  convert h using 1
  ring

/-- `e^{−(su)²/2} = e^{−(s²/2)u²}`, the form of Mathlib's Gaussian lemmas. -/
theorem gaussR_eq (s u : ℝ) : gaussR s u = Real.exp (-(s ^ 2 / 2) * u ^ 2) := by
  unfold gaussR
  congr 1
  ring

/-- `u^k e^{−(su)²/2}` is integrable on the line for `s > 0`. -/
theorem integrable_pow_mul_gaussR (s : ℝ) (hs : 0 < s) (k : ℕ) : Integrable (fun u : ℝ => u ^ k * gaussR s u) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := s ^ 2 / 2) (by positivity) (s := (k : ℝ))
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Real.rpow_natCast, gaussR_eq]

/-- A polynomial of degree at most three times `e^{−(su)²/2}` is integrable on the line for `s > 0`. -/
theorem integrable_cubic_mul_gaussR (s : ℝ) (hs : 0 < s) (a b c d : ℝ) :
    Integrable (fun u : ℝ => (a + b * u + c * u ^ 2 + d * u ^ 3) * gaussR s u) := by
  have h := (((integrable_pow_mul_gaussR s hs 0).const_mul a).add ((integrable_pow_mul_gaussR s hs 1).const_mul b)).add
    (((integrable_pow_mul_gaussR s hs 2).const_mul c).add ((integrable_pow_mul_gaussR s hs 3).const_mul d))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  ring

/-- A real integrable function is integrable as a complex-valued function. -/
theorem integrable_ofReal {f : ℝ → ℝ} (h : Integrable f) : Integrable (fun u => ((f u : ℝ) : ℂ)) :=
  h.ofReal

/-- **The class contains the Gaussians.** For `s > 0`, `G_s` with `G_s′, G_s″, G_s‴` is an amplitude. -/
theorem gauss_splAmplitude (s : ℝ) (hs : 0 < s) : SplAmplitude (gauss s) (gauss1 s) (gauss2 s) (gauss3 s) := by
  refine ⟨fun x => (gaussR_hasDerivAt s x).ofReal_comp, fun x => (gaussR1_hasDerivAt s x).ofReal_comp,
    fun x => (gaussR2_hasDerivAt s x).ofReal_comp, ?_, ?_, ?_, ?_⟩
  · refine (integrable_ofReal (integrable_cubic_mul_gaussR s hs 1 0 0 0)).congr (Eventually.of_forall fun u => ?_)
    simp [gauss]
  · refine (integrable_ofReal (integrable_cubic_mul_gaussR s hs 0 (-(s ^ 2)) 0 0)).congr
      (Eventually.of_forall fun u => ?_)
    unfold gauss1
    exact congrArg Complex.ofReal (by ring)
  · refine (integrable_ofReal (integrable_cubic_mul_gaussR s hs (-(s ^ 2)) 0 (s ^ 4) 0)).congr
      (Eventually.of_forall fun u => ?_)
    unfold gauss2
    exact congrArg Complex.ofReal (by ring)
  · refine (integrable_ofReal (integrable_cubic_mul_gaussR s hs 0 (3 * s ^ 4) 0 (-(s ^ 6)))).congr
      (Eventually.of_forall fun u => ?_)
    unfold gauss3
    exact congrArg Complex.ofReal (by ring)

/-- `G_s(0) = 1`. -/
theorem gauss_zero (s : ℝ) : gauss s 0 = 1 := by
  simp [gauss, gaussR]

/-- A constant function that is integrable on the line is zero. -/
theorem const_eq_zero_of_integrable {c : ℂ} (h : Integrable (fun _ : ℝ => c)) : c = 0 := by
  by_contra hc
  rw [integrable_const_iff] at h
  rcases h with h | h
  · exact hc h
  · have h1 := h.measure_univ_lt_top
    simp at h1

/-- **Bite (integrability).** The constant `1`, with zero derivatives, is not an amplitude: it is not integrable. -/
theorem one_not_splAmplitude : ¬ SplAmplitude (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  rintro ⟨-, -, -, h, -⟩
  exact one_ne_zero (const_eq_zero_of_integrable h)

/-- **Bite (the derivative).** `G_1` with the wrong first derivative `G_1` (in place of `G_1′`) is not an amplitude:
at `0` the derivative of `G_1` is `0`, not `G_1(0) = 1`. -/
theorem gauss_wrong_deriv_not_splAmplitude : ¬ SplAmplitude (gauss 1) (gauss 1) (gauss2 1) (gauss3 1) := by
  rintro ⟨h, -⟩
  have h1 : HasDerivAt (gauss 1) (gauss1 1 0) 0 := (gaussR_hasDerivAt 1 0).ofReal_comp
  have h2 := (h 0).unique h1
  rw [gauss_zero] at h2
  simp [gauss1] at h2

/-! ## C. Exact data for the Gaussian family -/

/-- `(2π/(s² − λi))^{1/2}` (principal branch): the value of `∫ G_s(u) e^{iλu²/2} du` (`integral_gauss_mul_exp`). -/
noncomputable def gaussRoot (s lam : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) / ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I)) ^ (1 / 2 : ℂ)

/-- `ℓ(λ) = √(2π/λ) e^{iπ/4}`: the leading term of `splRemainder g λ` for an amplitude with `g(0) = 1`. -/
noncomputable def splLead (lam : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi / lam) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- `∫ G_s(u) e^{iλu²/2} du = (2π/(s² − λi))^{1/2}` for `s > 0` and every real `λ` (Mathlib's
`integral_gaussian_complex` with `b = (s² − λi)/2`). -/
theorem integral_gauss_mul_exp (s : ℝ) (hs : 0 < s) (lam : ℝ) :
    ∫ u, gauss s u * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I) = gaussRoot s lam := by
  have hb : 0 < (((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) / 2).re := by
    have h : (((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) / 2).re = s ^ 2 / 2 := by
      simp [pow_two]
    rw [h]
    positivity
  have h := integral_gaussian_complex hb
  have e : ∀ u : ℝ, gauss s u * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) / 2) * (u : ℂ) ^ 2) := by
    intro u
    unfold gauss gaussR
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [h]
  unfold gaussRoot
  congr 1
  rw [div_div_eq_mul_div, mul_comm]

/-- **The remainder of the Gaussian in closed form**: `R(G_s, λ) = (2π/(s² − λi))^{1/2} − √(2π/λ) e^{iπ/4}` for
`s > 0` and every real `λ` (for `λ ≤ 0` this is the value of the Lean expression, in which `√(2π/λ) = 0`). -/
theorem splRemainder_gauss (s : ℝ) (hs : 0 < s) (lam : ℝ) :
    splRemainder (gauss s) lam = gaussRoot s lam - splLead lam := by
  unfold splRemainder splLead
  rw [integral_gauss_mul_exp s hs, gauss_zero, one_mul]

/-- `((2π/(s² − λi))^{1/2})² = 2π/(s² − λi)`. -/
theorem gaussRoot_sq (s lam : ℝ) :
    gaussRoot s lam ^ 2 = 2 * (Real.pi : ℂ) / ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) := by
  unfold gaussRoot
  have h : (1 / 2 : ℂ) = (((2 : ℕ) : ℂ))⁻¹ := by norm_num
  rw [h]
  exact Complex.cpow_nat_inv_pow _ two_ne_zero

/-- The principal square root has nonnegative real part. -/
theorem cpow_half_re_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have h : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
    rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re, h, Complex.im_mul_ofReal, Complex.log_im]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
    · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · linarith [Complex.arg_le_pi z, Real.pi_pos]

/-- The principal square root of a number of the closed upper half-plane has nonnegative imaginary part. -/
theorem cpow_half_im_nonneg {z : ℂ} (hz' : 0 ≤ z.im) : 0 ≤ (z ^ (1 / 2 : ℂ)).im := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have h : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
    rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_im, h, Complex.im_mul_ofReal, Complex.log_im]
    refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · linarith [Complex.arg_nonneg_iff.2 hz']
    · linarith [Complex.arg_le_pi z, Real.pi_pos]

/-- `2π/(s² − λi) = 2π (s² − λi)⁻¹` has imaginary part `2πλ/(s⁴ + λ²)`. -/
theorem gaussRoot_sq_im (s lam : ℝ) :
    (2 * (Real.pi : ℂ) / ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I)).im = 2 * Real.pi * lam / (s ^ 4 + lam ^ 2) := by
  have h : 2 * (Real.pi : ℂ) / ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) =
      ((2 * Real.pi : ℝ) : ℂ) * ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I)⁻¹ := by
    push_cast
    rw [div_eq_mul_inv]
  have hn : Complex.normSq ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) = s ^ 4 + lam ^ 2 := by
    rw [Complex.normSq_apply]
    simp [pow_two]
    ring
  rw [h, Complex.im_ofReal_mul, Complex.inv_im, hn]
  simp [pow_two]
  ring

/-- `Re (2π/(s² − λi))^{1/2} ≥ 0`. -/
theorem gaussRoot_re_nonneg (s lam : ℝ) : 0 ≤ (gaussRoot s lam).re :=
  cpow_half_re_nonneg _

/-- `Im (2π/(s² − λi))^{1/2} ≥ 0` for `λ ≥ 0`: with the previous lemma, the root is in the closed first quadrant. -/
theorem gaussRoot_im_nonneg (s lam : ℝ) (hlam : 0 ≤ lam) : 0 ≤ (gaussRoot s lam).im := by
  refine cpow_half_im_nonneg ?_
  rw [gaussRoot_sq_im]
  have := Real.pi_pos
  positivity

/-- `‖s² − λi‖ = √(s⁴ + λ²)`. -/
theorem norm_sq_sub_mul_I (s lam : ℝ) : ‖(s : ℂ) ^ 2 - (lam : ℂ) * Complex.I‖ = Real.sqrt (s ^ 4 + lam ^ 2) := by
  have hn : Complex.normSq ((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) = s ^ 4 + lam ^ 2 := by
    rw [Complex.normSq_apply]
    simp [pow_two]
    ring
  rw [← hn, ← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]

/-- `|(2π/(s² − λi))^{1/2}|² = 2π/√(s⁴ + λ²)`. -/
theorem norm_gaussRoot_sq (s lam : ℝ) : ‖gaussRoot s lam‖ ^ 2 = 2 * Real.pi / Real.sqrt (s ^ 4 + lam ^ 2) := by
  rw [← norm_pow, gaussRoot_sq, norm_div, norm_sq_sub_mul_I]
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

/-- `ℓ(λ)² = (2π/λ) i` for `λ > 0`. -/
theorem splLead_sq (lam : ℝ) (hlam : 0 < lam) : splLead lam ^ 2 = ((2 * Real.pi / lam : ℝ) : ℂ) * Complex.I := by
  unfold splLead
  have h1 : ((Real.sqrt (2 * Real.pi / lam) : ℝ) : ℂ) ^ 2 = ((2 * Real.pi / lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by have := Real.pi_pos; positivity)]
  have h2 : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) ^ 2 = Complex.I := by
    rw [exp_pi_div_four, mul_pow, ← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num), add_sq, Complex.I_sq]
    push_cast
    ring
  rw [mul_pow, h1, h2]

/-- `|ℓ(λ)| = √(2π/λ)`. -/
theorem norm_splLead (lam : ℝ) : ‖splLead lam‖ = Real.sqrt (2 * Real.pi / lam) := by
  unfold splLead
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- `Re ℓ(λ) ≥ 0`. -/
theorem splLead_re_nonneg (lam : ℝ) : 0 ≤ (splLead lam).re := by
  unfold splLead
  rw [exp_pi_div_four, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero, mul_one]
  positivity

/-- `Im ℓ(λ) ≥ 0`: `ℓ(λ)` is in the closed first quadrant. -/
theorem splLead_im_nonneg (lam : ℝ) : 0 ≤ (splLead lam).im := by
  unfold splLead
  rw [exp_pi_div_four, ← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul]
  simp only [Complex.add_im, Complex.one_im, Complex.I_im, zero_add, mul_one]
  positivity

/-- **The algebraic identity behind the certified bounds**: `root² − ℓ² = −2πs²/((s² − λi)(−λi))` for `s, λ > 0`. -/
theorem gaussRoot_sq_sub_splLead_sq (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    gaussRoot s lam ^ 2 - splLead lam ^ 2 =
      -(2 * (Real.pi : ℂ) * (s : ℂ) ^ 2) / (((s : ℂ) ^ 2 - (lam : ℂ) * Complex.I) * (-((lam : ℂ) * Complex.I))) := by
  have hw : (s : ℂ) ^ 2 - (lam : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h1 := norm_sq_sub_mul_I s lam
    rw [h, norm_zero] at h1
    have h2 : 0 < Real.sqrt (s ^ 4 + lam ^ 2) := Real.sqrt_pos.2 (by positivity)
    linarith
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  rw [gaussRoot_sq, splLead_sq lam hlam]
  push_cast
  field_simp
  linear_combination (Complex.I * (lam : ℂ) - (s : ℂ) ^ 2) * Complex.I_sq

/-- `|root² − ℓ²| = 2πs²/(λ √(s⁴ + λ²))` for `s, λ > 0`. -/
theorem norm_gaussRoot_sq_sub_splLead_sq (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    ‖gaussRoot s lam ^ 2 - splLead lam ^ 2‖ = 2 * Real.pi * s ^ 2 / (lam * Real.sqrt (s ^ 4 + lam ^ 2)) := by
  rw [gaussRoot_sq_sub_splLead_sq s lam hs hlam, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, norm_neg, norm_mul,
    norm_sq_sub_mul_I, Complex.norm_I, mul_one, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hs, abs_of_pos hlam,
    Complex.norm_ofNat]
  ring

/-- `|root| ≤ |ℓ|` for `λ > 0`. -/
theorem norm_gaussRoot_le_norm_splLead (s lam : ℝ) (hlam : 0 < lam) : ‖gaussRoot s lam‖ ≤ ‖splLead lam‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  have hpi := Real.pi_pos
  rw [norm_gaussRoot_sq, norm_splLead, Real.sq_sqrt (by positivity)]
  have h1 : lam ≤ Real.sqrt (s ^ 4 + lam ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (s ^ 2)])
  gcongr

/-- For `r, l` in the closed first quadrant with `|r| ≤ |l|`: `|r² − l²| ≤ 2|l| |r − l|` and
`|l| |r − l| ≤ |r² − l²|` (because `|l| ≤ |r + l| ≤ 2|l|`). -/
theorem norm_sub_two_sided {r l : ℂ} (hr : 0 ≤ r.re) (hr' : 0 ≤ r.im) (hl : 0 ≤ l.re) (hl' : 0 ≤ l.im)
    (hrl : ‖r‖ ≤ ‖l‖) : ‖r ^ 2 - l ^ 2‖ ≤ ‖r - l‖ * (2 * ‖l‖) ∧ ‖r - l‖ * ‖l‖ ≤ ‖r ^ 2 - l ^ 2‖ := by
  have hfac : ‖r ^ 2 - l ^ 2‖ = ‖r - l‖ * ‖r + l‖ := by
    rw [← norm_mul]
    congr 1
    ring
  have h1 : ‖r + l‖ ≤ 2 * ‖l‖ := by linarith [norm_add_le r l]
  have h2 : ‖l‖ ≤ ‖r + l‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [mul_nonneg hr hl, mul_nonneg hr' hl', mul_self_nonneg r.re, mul_self_nonneg r.im]
  rw [hfac]
  exact ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _), mul_le_mul_of_nonneg_left h2 (norm_nonneg _)⟩

/-- Real algebra for `splRemainder_gauss_bounds`: from `a²σ/(b²Q) ≤ 2N a/b` and `N a/b ≤ a²σ/(b²Q)` to
`aσ/(2bQ) ≤ N ≤ aσ/(bQ)`. -/
theorem two_sided_algebra {N a b Q σ : ℝ} (ha : 0 < a) (hb : 0 < b) (hQ : 0 < Q)
    (h1 : a ^ 2 * σ / (b ^ 2 * Q) ≤ N * (2 * (a / b))) (h2 : N * (a / b) ≤ a ^ 2 * σ / (b ^ 2 * Q)) :
    a * σ / (2 * b * Q) ≤ N ∧ N ≤ a * σ / (b * Q) := by
  have e1 : a ^ 2 * σ / (b ^ 2 * Q) = a * σ / (b * Q) * (a / b) := by
    field_simp
  have hab : 0 < a / b := div_pos ha hb
  rw [e1] at h1 h2
  constructor
  · have h3 : a * σ / (b * Q) ≤ N * 2 := by
      refine le_of_mul_le_mul_right ?_ hab
      linarith
    have e2 : a * σ / (2 * b * Q) = a * σ / (b * Q) / 2 := by
      field_simp
    rw [e2]
    linarith
  · exact le_of_mul_le_mul_right h2 hab

/-- **Certified two-sided bound of the remainder of the Gaussian.** For `s, λ > 0`:
`√(2π) s²/(2 √λ √(s⁴ + λ²)) ≤ |R(G_s, λ)| ≤ √(2π) s²/(√λ √(s⁴ + λ²))`. So `|R(G_s, λ)|` is known up to a factor `2`,
it is positive, and it is of the order `λ^{−3/2}` for large `λ`. -/
theorem splRemainder_gauss_bounds (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    Real.sqrt (2 * Real.pi) * s ^ 2 / (2 * Real.sqrt lam * Real.sqrt (s ^ 4 + lam ^ 2)) ≤
        ‖splRemainder (gauss s) lam‖ ∧
      ‖splRemainder (gauss s) lam‖ ≤
        Real.sqrt (2 * Real.pi) * s ^ 2 / (Real.sqrt lam * Real.sqrt (s ^ 4 + lam ^ 2)) := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := norm_sub_two_sided (gaussRoot_re_nonneg s lam) (gaussRoot_im_nonneg s lam hlam.le)
    (splLead_re_nonneg lam) (splLead_im_nonneg lam) (norm_gaussRoot_le_norm_splLead s lam hlam)
  have ha : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hq : 0 < Real.sqrt (s ^ 4 + lam ^ 2) := Real.sqrt_pos.2 (by positivity)
  have e : 2 * Real.pi * s ^ 2 / (lam * Real.sqrt (s ^ 4 + lam ^ 2)) =
      Real.sqrt (2 * Real.pi) ^ 2 * s ^ 2 / (Real.sqrt lam ^ 2 * Real.sqrt (s ^ 4 + lam ^ 2)) := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hlam.le]
  rw [norm_gaussRoot_sq_sub_splLead_sq s lam hs hlam, norm_splLead, Real.sqrt_div (by positivity), e] at h1 h2
  rw [splRemainder_gauss s hs]
  exact two_sided_algebra ha hb hq h1 h2

/-- `∫_ℝ |h'|` when `h′ = h'` everywhere, `h` and `h'` are integrable, `|h'|` is even, `h' ≥ 0` on `[0, c]` and
`h' ≤ 0` on `[c, ∞)`: the value is `2 (2h(c) − h(0))` (the fundamental theorem on `[0, c]` and on `[c, ∞)`, where
`h → 0`). A tool for the two integrals below; no object of the batch. -/
theorem integral_abs_of_sign_change {h h' : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ x, HasDerivAt h (h' x) x)
    (hi : Integrable h) (hi' : Integrable h') (heven : ∀ x, |h' (-x)| = |h' x|)
    (hpos : ∀ x, 0 ≤ x → x ≤ c → 0 ≤ h' x) (hneg : ∀ x, c ≤ x → h' x ≤ 0) :
    ∫ x, |h' x| = 2 * (2 * h c - h 0) := by
  have habs : Integrable (fun x => |h' x|) := hi'.abs
  have hlim : Tendsto h atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd x) hi'.integrableOn hi.integrableOn
  -- the right half-line
  have h1 : ∫ x in (0 : ℝ)..c, |h' x| = h c - h 0 := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi'.intervalIntegrable]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hc] at hx
    exact abs_of_nonneg (hpos x hx.1 hx.2)
  have h2 : ∫ x in Ioi c, |h' x| = h c := by
    have h3 : ∫ x in Ioi c, |h' x| = ∫ x in Ioi c, -h' x :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => abs_of_nonpos (hneg x (le_of_lt hx))
    rw [h3, integral_neg, integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi'.integrableOn hlim]
    ring
  have h4 : ∫ x in Ioi (0 : ℝ), |h' x| = 2 * h c - h 0 := by
    rw [← intervalIntegral.integral_interval_add_Ioi habs.integrableOn habs.integrableOn, h1, h2]
    ring
  -- the left half-line, by reflection
  have h5 : ∫ x in Iic (0 : ℝ), |h' x| = 2 * h c - h 0 := by
    have h6 := integral_comp_neg_Ioi (0 : ℝ) (fun x => |h' x|)
    rw [neg_zero] at h6
    rw [← h6, ← h4]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => heven x
  rw [← intervalIntegral.integral_Iic_add_Ioi habs.integrableOn habs.integrableOn, h4, h5]
  ring

/-- `e^{−(s·(√3/s))²/2} = e^{−3/2}` for `s > 0`. -/
theorem gaussR_sqrt_three_div (s : ℝ) (hs : 0 < s) : gaussR s (Real.sqrt 3 / s) = Real.exp (-(3 / 2)) := by
  unfold gaussR
  have h : s * (Real.sqrt 3 / s) = Real.sqrt 3 := by
    field_simp
  rw [h, Real.sq_sqrt (by norm_num)]
  congr 1
  ring

/-- `e^{−(s·(1/s))²/2} = e^{−1/2}` for `s > 0`. -/
theorem gaussR_one_div (s : ℝ) (hs : 0 < s) : gaussR s (1 / s) = Real.exp (-(1 / 2)) := by
  unfold gaussR
  have h : s * (1 / s) = 1 := by
    field_simp
  rw [h]
  congr 1
  ring

/-- **`‖G_s‴‖₁ = s² (2 + 8 e^{−3/2})`** for `s > 0` (`2 + 8e^{−3/2} = 3.78504…`): `G_s‴ = (G_s″)′` changes sign at
`0` and at `±√3/s`. -/
theorem integral_norm_gauss3 (s : ℝ) (hs : 0 < s) :
    ∫ t, ‖gauss3 s t‖ = s ^ 2 * (2 + 8 * Real.exp (-(3 / 2))) := by
  have hn : ∀ t, ‖gauss3 s t‖ = |(3 * s ^ 4 * t - s ^ 6 * t ^ 3) * gaussR s t| := fun t => by
    unfold gauss3
    rw [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hn]
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h3' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hg : ∀ x, 0 < gaussR s x := fun x => Real.exp_pos _
  have hfac : ∀ x : ℝ, 3 * s ^ 4 * x - s ^ 6 * x ^ 3 = s ^ 4 * x * (3 - (s * x) ^ 2) := fun x => by ring
  have hi : Integrable (fun u : ℝ => (s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u) := by
    refine (integrable_cubic_mul_gaussR s hs (-(s ^ 2)) 0 (s ^ 4) 0).congr (Eventually.of_forall fun u => ?_)
    show (-(s ^ 2) + 0 * u + s ^ 4 * u ^ 2 + 0 * u ^ 3) * gaussR s u = (s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u
    ring
  have hi' : Integrable (fun u : ℝ => (3 * s ^ 4 * u - s ^ 6 * u ^ 3) * gaussR s u) := by
    refine (integrable_cubic_mul_gaussR s hs 0 (3 * s ^ 4) 0 (-(s ^ 6))).congr (Eventually.of_forall fun u => ?_)
    show (0 + 3 * s ^ 4 * u + 0 * u ^ 2 + -(s ^ 6) * u ^ 3) * gaussR s u = (3 * s ^ 4 * u - s ^ 6 * u ^ 3) * gaussR s u
    ring
  rw [integral_abs_of_sign_change (c := Real.sqrt 3 / s) (by positivity) (gaussR2_hasDerivAt s) hi hi']
  · rw [gaussR_sqrt_three_div s hs]
    have e : gaussR s 0 = 1 := by simp [gaussR]
    rw [e]
    have e2 : s ^ 4 * (Real.sqrt 3 / s) ^ 2 = 3 * s ^ 2 := by
      rw [div_pow, h3']
      field_simp
    rw [e2]
    ring
  · intro x
    have e : gaussR s (-x) = gaussR s x := by
      unfold gaussR
      congr 1
      ring
    rw [e, abs_mul, abs_mul]
    congr 1
    rw [← abs_neg]
    congr 1
    ring
  · intro x hx0 hxc
    rw [le_div_iff₀ hs] at hxc
    rw [hfac]
    have h1 : (s * x) ^ 2 ≤ 3 := by nlinarith [mul_nonneg hs.le hx0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hx0) (by linarith)) (hg x).le
  · intro x hxc
    rw [div_le_iff₀ hs] at hxc
    rw [hfac]
    have hx0 : 0 ≤ x := by
      by_contra hneg
      nlinarith
    have h1 : 3 ≤ (s * x) ^ 2 := by nlinarith [mul_nonneg hs.le hx0]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hx0) (by linarith)) (hg x).le

/-- **`‖G_s″‖₁ = 4s e^{−1/2}`** for `s > 0` (used by one planted control): `G_s″ = (G_s′)′` changes sign at
`±1/s`. -/
theorem integral_norm_gauss2 (s : ℝ) (hs : 0 < s) : ∫ t, ‖gauss2 s t‖ = s * (4 * Real.exp (-(1 / 2))) := by
  have hn : ∀ t, ‖gauss2 s t‖ = |-((s ^ 4 * t ^ 2 - s ^ 2) * gaussR s t)| := fun t => by
    unfold gauss2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  simp_rw [hn]
  have hg : ∀ x, 0 < gaussR s x := fun x => Real.exp_pos _
  have hfac : ∀ x : ℝ, -((s ^ 4 * x ^ 2 - s ^ 2) * gaussR s x) = s ^ 2 * (1 - (s * x) ^ 2) * gaussR s x :=
    fun x => by ring
  have hi : Integrable (fun u : ℝ => -(-(s ^ 2 * u) * gaussR s u)) := by
    refine (integrable_cubic_mul_gaussR s hs 0 (s ^ 2) 0 0).congr (Eventually.of_forall fun u => ?_)
    show (0 + s ^ 2 * u + 0 * u ^ 2 + 0 * u ^ 3) * gaussR s u = -(-(s ^ 2 * u) * gaussR s u)
    ring
  have hi' : Integrable (fun u : ℝ => -((s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u)) := by
    refine (integrable_cubic_mul_gaussR s hs (s ^ 2) 0 (-(s ^ 4)) 0).congr (Eventually.of_forall fun u => ?_)
    show (s ^ 2 + 0 * u + -(s ^ 4) * u ^ 2 + 0 * u ^ 3) * gaussR s u = -((s ^ 4 * u ^ 2 - s ^ 2) * gaussR s u)
    ring
  rw [integral_abs_of_sign_change (c := 1 / s) (by positivity) (fun x => (gaussR1_hasDerivAt s x).fun_neg) hi hi']
  · rw [gaussR_one_div s hs]
    have e2 : s ^ 2 * (1 / s) = s := by
      field_simp
    rw [e2]
    ring
  · intro x
    have e : gaussR s (-x) = gaussR s x := by
      unfold gaussR
      congr 1
      ring
    rw [e]
    congr 2
    ring
  · intro x hx0 hxc
    rw [le_div_iff₀ hs] at hxc
    rw [hfac]
    have h1 : (s * x) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hs.le hx0]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hg x).le
  · intro x hxc
    rw [div_le_iff₀ hs] at hxc
    rw [hfac]
    have hx0 : 0 ≤ x := by
      by_contra hneg
      nlinarith
    have h1 : 1 ≤ (s * x) ^ 2 := by nlinarith [mul_nonneg hs.le hx0]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (hg x).le

/-! ### Certified numbers -/

/-- `e^{−3/2} ≤ 25/112` (`= 0.22321…`; true value `0.22313…`), from eight terms of the exponential series at `3/2`. -/
theorem exp_neg_three_halves_le : Real.exp (-(3 / 2)) ≤ 25 / 112 := by
  have h := Real.sum_le_exp_of_nonneg (x := 3 / 2) (by norm_num) 8
  have h1 : (112 / 25 : ℝ) ≤ Real.exp (3 / 2) := by
    refine le_trans ?_ h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  refine le_trans ?_ h1
  norm_num

/-- `e^{−1/2} ≤ 128/211` (`= 0.60663…`; true value `0.60653…`), from five terms of the exponential series at `1/2`. -/
theorem exp_neg_half_le : Real.exp (-(1 / 2)) ≤ 128 / 211 := by
  have h := Real.sum_le_exp_of_nonneg (x := 1 / 2) (by norm_num) 5
  have h1 : (211 / 128 : ℝ) ≤ Real.exp (1 / 2) := by
    refine le_trans ?_ h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  refine le_trans ?_ h1
  norm_num

/-- `2 + 8e^{−3/2} ≤ 379/100` (true value `3.78504…`). -/
theorem normThree_le : 2 + 8 * Real.exp (-(3 / 2)) ≤ 379 / 100 := by
  linarith [exp_neg_three_halves_le]

/-- `2 < 2 + 8e^{−3/2}`. -/
theorem normThree_pos : 0 < 2 + 8 * Real.exp (-(3 / 2)) := by
  linarith [Real.exp_pos (-(3 / 2))]

/-- `2.506 ≤ √(2π)` (true value `2.50662…`). -/
theorem sqrt_two_pi_lower : 2506 / 1000 ≤ Real.sqrt (2 * Real.pi) :=
  Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d4])

/-- `√(2π) ≤ 2.51`. -/
theorem sqrt_two_pi_upper : Real.sqrt (2 * Real.pi) ≤ 251 / 100 :=
  (Real.sqrt_le_left (by norm_num)).2 (by nlinarith [Real.pi_lt_d2])

/-- `(a²)^{−3/2} = 1/a³` for `a > 0` (`Real.rpow`). -/
theorem rpow_neg_three_halves_sq (a : ℝ) (ha : 0 < a) : (a ^ 2) ^ (-(3 : ℝ) / 2) = 1 / a ^ 3 := by
  have h : ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -((3 : ℕ) : ℝ) := by norm_num
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le, h, Real.rpow_neg ha.le, Real.rpow_natCast, one_div]

/-- `4^{−3/2} = 1/8`. -/
theorem rpow_four : (4 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 8 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, rpow_neg_three_halves_sq 2 two_pos]
  norm_num

/-- `9^{−3/2} = 1/27`. -/
theorem rpow_nine : (9 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 27 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, rpow_neg_three_halves_sq 3 (by norm_num)]
  norm_num

/-- `100^{−3/2} = 1/1000`. -/
theorem rpow_hundred : (100 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 1000 := by
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, rpow_neg_three_halves_sq 10 (by norm_num)]
  norm_num

/-- `1600^{−3/2} = 1/64000`. -/
theorem rpow_sixteen_hundred : (1600 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 64000 := by
  rw [show (1600 : ℝ) = 40 ^ 2 by norm_num, rpow_neg_three_halves_sq 40 (by norm_num)]
  norm_num

/-- `√4 = 2`. -/
theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√9 = 3`. -/
theorem sqrt_nine : Real.sqrt 9 = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√100 = 10`. -/
theorem sqrt_hundred : Real.sqrt 100 = 10 := by
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√1600 = 40`. -/
theorem sqrt_sixteen_hundred : Real.sqrt 1600 = 40 := by
  rw [show (1600 : ℝ) = 40 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The root at `s = 1`, `λ = 4`, written out. -/
theorem gaussRoot_one_four : gaussRoot 1 4 = (2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) := by
  unfold gaussRoot
  norm_num

/-- The root at `s = 2`, `λ = 9`, written out. -/
theorem gaussRoot_two_nine : gaussRoot 2 9 = (2 * (Real.pi : ℂ) / (4 - 9 * Complex.I)) ^ (1 / 2 : ℂ) := by
  unfold gaussRoot
  norm_num

/-- `0.151 ≤ |R(G_1, 4)| ≤ 0.305` (true value `0.2218…`; the bounds of `splRemainder_gauss_bounds` are
`0.15199…` and `0.30398…`). -/
theorem splRemainder_gauss_one_four_bounds :
    151 / 1000 ≤ ‖splRemainder (gauss 1) 4‖ ∧ ‖splRemainder (gauss 1) 4‖ ≤ 305 / 1000 := by
  obtain ⟨h1, h2⟩ := splRemainder_gauss_bounds 1 4 one_pos (by norm_num)
  rw [sqrt_four] at h1 h2
  have hq1 : Real.sqrt (1 ^ 4 + 4 ^ 2) ≤ 413 / 100 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq2 : 412 / 100 ≤ Real.sqrt (1 ^ 4 + 4 ^ 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hq0 : 0 < Real.sqrt (1 ^ 4 + 4 ^ 2) := lt_of_lt_of_le (by norm_num) hq2
  generalize Real.sqrt (1 ^ 4 + 4 ^ 2) = q at h1 h2 hq1 hq2 hq0
  constructor
  · refine le_trans ?_ h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sqrt_two_pi_lower]
  · refine le_trans h2 ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sqrt_two_pi_upper]

/-- `0.169 ≤ |R(G_2, 9)| ≤ 0.341` (the bounds of `splRemainder_gauss_bounds` are `0.16967…` and `0.33934…`). -/
theorem splRemainder_gauss_two_nine_bounds :
    169 / 1000 ≤ ‖splRemainder (gauss 2) 9‖ ∧ ‖splRemainder (gauss 2) 9‖ ≤ 341 / 1000 := by
  obtain ⟨h1, h2⟩ := splRemainder_gauss_bounds 2 9 two_pos (by norm_num)
  rw [sqrt_nine] at h1 h2
  have hq1 : Real.sqrt (2 ^ 4 + 9 ^ 2) ≤ 985 / 100 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq2 : 984 / 100 ≤ Real.sqrt (2 ^ 4 + 9 ^ 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hq0 : 0 < Real.sqrt (2 ^ 4 + 9 ^ 2) := lt_of_lt_of_le (by norm_num) hq2
  generalize Real.sqrt (2 ^ 4 + 9 ^ 2) = q at h1 h2 hq1 hq2 hq0
  constructor
  · refine le_trans ?_ h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sqrt_two_pi_lower]
  · refine le_trans h2 ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sqrt_two_pi_upper]

/-- An amplitude with `‖g₃‖₁ = 0` is identically zero: `g₂` is constant by the fundamental theorem of calculus
(for a derivative that exists everywhere and is integrable), an integrable constant is `0`, and so on down to `g`.
(A fact about the class `SplAmplitude`; it makes the conclusion of SPL-A non-degenerate.) -/
theorem eq_zero_of_integral_norm_eq_zero {g g₁ g₂ g₃ : ℝ → ℂ} (h : SplAmplitude g g₁ g₂ g₃)
    (h0 : ∫ t, ‖g₃ t‖ = 0) (x : ℝ) : g x = 0 := by
  obtain ⟨hd, hd₁, hd₂, hi, hi₁, hi₂, hi₃⟩ := h
  have hae : (fun t => ‖g₃ t‖) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => norm_nonneg (g₃ t)) hi₃.norm).1 h0
  have hae' : ∀ᵐ t ∂(volume : Measure ℝ), g₃ t = 0 := hae.mono fun t ht => norm_eq_zero.1 ht
  have hconst : ∀ y, g₂ y = g₂ 0 := by
    intro y
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := y) (fun t _ => hd₂ t)
      hi₃.intervalIntegrable
    have h2 : ∫ t in (0 : ℝ)..y, g₃ t = ∫ _t in (0 : ℝ)..y, (0 : ℂ) :=
      intervalIntegral.integral_congr_ae (hae'.mono fun t ht _ => ht)
    rw [h2, intervalIntegral.integral_zero] at h1
    exact (sub_eq_zero.1 h1.symm)
  have hz₂ : ∀ y, g₂ y = 0 := by
    have h1 : g₂ = fun _ => g₂ 0 := funext hconst
    rw [h1] at hi₂
    intro y
    rw [hconst y]
    exact const_eq_zero_of_integrable hi₂
  have hc₁ : ∀ y, g₁ y = g₁ 0 := fun y =>
    is_const_of_deriv_eq_zero (fun t => (hd₁ t).differentiableAt) (fun t => by rw [(hd₁ t).deriv, hz₂]) y 0
  have hz₁ : ∀ y, g₁ y = 0 := by
    have h1 : g₁ = fun _ => g₁ 0 := funext hc₁
    rw [h1] at hi₁
    intro y
    rw [hc₁ y]
    exact const_eq_zero_of_integrable hi₁
  have hc : ∀ y, g y = g 0 := fun y =>
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => by rw [(hd t).deriv, hz₁]) y 0
  have h1 : g = fun _ => g 0 := funext hc
  rw [h1] at hi
  rw [hc x]
  exact const_eq_zero_of_integrable hi

/-- An amplitude that is not identically zero has `‖g₃‖₁ > 0`. -/
theorem integral_norm_pos_of_splAmplitude {g g₁ g₂ g₃ : ℝ → ℂ} (h : SplAmplitude g g₁ g₂ g₃)
    (hne : ∃ x, g x ≠ 0) : 0 < ∫ t, ‖g₃ t‖ := by
  obtain ⟨x, hx⟩ := hne
  refine lt_of_le_of_ne (integral_nonneg fun t => norm_nonneg _) fun h0 => hx ?_
  exact eq_zero_of_integral_norm_eq_zero h h0.symm x

/-! ## D. The statements on data

Each theorem takes one statement constant as its only statement hypothesis (the consistency theorem takes two),
discharges its hypotheses on the Gaussian family and concludes its conclusion there in closed form. -/

/-- SPL-I on the Gaussian family: the closed form of the remainder equals the kernel integral of `G_s‴`. -/
theorem identity_gauss (h : StationaryLeadingIdentityStatement) (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    gaussRoot s lam - splLead lam =
      -Complex.I * ((lam ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * ∫ t, gauss3 s t * splKernel (Real.sqrt lam * t) := by
  have h1 := h (gauss s) (gauss1 s) (gauss2 s) (gauss3 s) lam (gauss_splAmplitude s hs) hlam
  rw [splRemainder_gauss s hs] at h1
  exact h1

/-- SPL-I at `G_1`, `λ = 4`, written out (`4^{−3/2} = 1/8`, `√4 = 2`). -/
theorem identity_gauss_one_four (h : StationaryLeadingIdentityStatement) :
    (2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 4) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      -Complex.I * ((1 / 8 : ℝ) : ℂ) * ∫ t, gauss3 1 t * splKernel (2 * t) := by
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [splRemainder_gauss 1 one_pos, gaussRoot_one_four, rpow_four, sqrt_four] at h1
  exact h1

/-- SPL-I at `G_2`, `λ = 9`, written out (`9^{−3/2} = 1/27`, `√9 = 3`). -/
theorem identity_gauss_two_nine (h : StationaryLeadingIdentityStatement) :
    (2 * (Real.pi : ℂ) / (4 - 9 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 9) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      -Complex.I * ((1 / 27 : ℝ) : ℂ) * ∫ t, gauss3 2 t * splKernel (3 * t) := by
  have h1 := h (gauss 2) (gauss1 2) (gauss2 2) (gauss3 2) 9 (gauss_splAmplitude 2 two_pos) (by norm_num)
  rw [splRemainder_gauss 2 two_pos, gaussRoot_two_nine, rpow_nine, sqrt_nine] at h1
  exact h1

/-- SPL-I forces the size of a kernel integral: `6/5 ≤ |∫ G_1‴(t) κ(2t) dt| ≤ 5/2` (it is `8 |R(G_1, 4)|`; against
`‖G_1‴‖₁ = 3.785…` this is a ratio between `0.31` and `0.67`). -/
theorem identity_integral_bounds (h : StationaryLeadingIdentityStatement) :
    6 / 5 ≤ ‖∫ t, gauss3 1 t * splKernel (2 * t)‖ ∧ ‖∫ t, gauss3 1 t * splKernel (2 * t)‖ ≤ 5 / 2 := by
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [rpow_four, sqrt_four] at h1
  obtain ⟨h2, h3⟩ := splRemainder_gauss_one_four_bounds
  rw [h1, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at h2 h3
  constructor <;> linarith

/-- SPL-S on the Gaussian family, with `‖G_s‴‖₁ = s²(2 + 8e^{−3/2})`. -/
theorem kernel_gauss (h : StationaryLeadingStatement) (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ‖gaussRoot s lam - splLead lam‖ ≤
      ‖splKernel τ‖ * (s ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * lam ^ (-(3 : ℝ) / 2) := by
  obtain ⟨τ, hτ, h1⟩ := h (gauss s) (gauss1 s) (gauss2 s) (gauss3 s) lam (gauss_splAmplitude s hs) hlam
  rw [splRemainder_gauss s hs, integral_norm_gauss3 s hs] at h1
  exact ⟨τ, hτ, h1⟩

/-- SPL-S at `G_1`, `λ = 4`, written out. -/
theorem kernel_gauss_one_four (h : StationaryLeadingStatement) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ‖(2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 4) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      ‖splKernel τ‖ * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) := by
  obtain ⟨τ, hτ, h1⟩ := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [splRemainder_gauss 1 one_pos, gaussRoot_one_four, integral_norm_gauss3 1 one_pos, rpow_four, one_pow,
    one_mul] at h1
  exact ⟨τ, hτ, h1⟩

/-- SPL-S at `G_2`, `λ = 9`, written out (`‖G_2‴‖₁ = 4(2 + 8e^{−3/2})`). -/
theorem kernel_gauss_two_nine (h : StationaryLeadingStatement) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ‖(2 * (Real.pi : ℂ) / (4 - 9 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 9) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      ‖splKernel τ‖ * (2 ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * (1 / 27) := by
  obtain ⟨τ, hτ, h1⟩ := h (gauss 2) (gauss1 2) (gauss2 2) (gauss3 2) 9 (gauss_splAmplitude 2 two_pos) (by norm_num)
  rw [splRemainder_gauss 2 two_pos, gaussRoot_two_nine, integral_norm_gauss3 2 two_pos, rpow_nine] at h1
  exact ⟨τ, hτ, h1⟩

/-- SPL-S forces a value of the kernel: some `τ ≥ 0` has `|κ(τ)| ≥ 3/10` (from `G_1`, `λ = 4`:
`0.151 ≤ |R| ≤ |κ(τ)| · 3.79/8`). The statement is not satisfied by a small kernel. -/
theorem kernel_large (h : StationaryLeadingStatement) : ∃ τ : ℝ, 0 ≤ τ ∧ 3 / 10 ≤ ‖splKernel τ‖ := by
  obtain ⟨τ, hτ, h1⟩ := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [integral_norm_gauss3 1 one_pos, rpow_four, one_pow, one_mul] at h1
  refine ⟨τ, hτ, ?_⟩
  have h2 := splRemainder_gauss_one_four_bounds.1
  nlinarith [normThree_le, normThree_pos, norm_nonneg (splKernel τ)]

/-- SPL-K on the Gaussian family. -/
theorem sevenEighths_gauss (h : StationaryLeadingSevenEighthsStatement) (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    ‖gaussRoot s lam - splLead lam‖ ≤ 7 / 8 * (s ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * lam ^ (-(3 : ℝ) / 2) := by
  have h1 := h (gauss s) (gauss1 s) (gauss2 s) (gauss3 s) lam (gauss_splAmplitude s hs) hlam
  rw [splRemainder_gauss s hs, integral_norm_gauss3 s hs] at h1
  exact h1

/-- SPL-K at `G_1`, `λ = 4`, written out: a numeric inequality, `|…| ≤ (7/8)(2 + 8e^{−3/2})/8 = 0.41399…`. -/
theorem sevenEighths_gauss_one_four (h : StationaryLeadingSevenEighthsStatement) :
    ‖(2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 4) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      7 / 8 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) := by
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [splRemainder_gauss 1 one_pos, gaussRoot_one_four, integral_norm_gauss3 1 one_pos, rpow_four, one_pow,
    one_mul] at h1
  exact h1

/-- The inequality of `sevenEighths_gauss_one_four` is not vacuous: its left side is at least one third of its
right side (unconditional; `0.151 ≥ 0.138`). -/
theorem sevenEighths_gauss_one_four_within :
    1 / 3 * (7 / 8 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8)) ≤
      ‖(2 * (Real.pi : ℂ) / (1 - 4 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 4) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ := by
  have h2 := splRemainder_gauss_one_four_bounds.1
  rw [splRemainder_gauss 1 one_pos, gaussRoot_one_four] at h2
  refine le_trans ?_ h2
  linarith [normThree_le]

/-- SPL-K at `G_2`, `λ = 9`, written out: `|…| ≤ (7/8) · 4(2 + 8e^{−3/2})/27 = 0.49065…`. -/
theorem sevenEighths_gauss_two_nine (h : StationaryLeadingSevenEighthsStatement) :
    ‖(2 * (Real.pi : ℂ) / (4 - 9 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 9) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤
      7 / 8 * (2 ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * (1 / 27) := by
  have h1 := h (gauss 2) (gauss1 2) (gauss2 2) (gauss3 2) 9 (gauss_splAmplitude 2 two_pos) (by norm_num)
  rw [splRemainder_gauss 2 two_pos, gaussRoot_two_nine, integral_norm_gauss3 2 two_pos, rpow_nine] at h1
  exact h1

/-- The inequality of `sevenEighths_gauss_two_nine` is not vacuous: its left side is at least one third of its
right side (unconditional; `0.169 ≥ 0.1636`). -/
theorem sevenEighths_gauss_two_nine_within :
    1 / 3 * (7 / 8 * (2 ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * (1 / 27)) ≤
      ‖(2 * (Real.pi : ℂ) / (4 - 9 * Complex.I)) ^ (1 / 2 : ℂ) -
        ((Real.sqrt (2 * Real.pi / 9) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ := by
  have h2 := splRemainder_gauss_two_nine_bounds.1
  rw [splRemainder_gauss 2 two_pos, gaussRoot_two_nine] at h2
  refine le_trans ?_ h2
  linarith [normThree_le]

/-- SPL-A at `τ = 0`: for every `ε > 0` a smooth compactly supported amplitude, not identically zero, with
`−ε ‖g₃‖₁ ≤ |R(g, 1)|` (`κ(0) = 0`; at `τ = 0` the statement asserts only that such amplitudes exist). -/
theorem attained_zero (h : StationaryLeadingAttainedStatement) (ε : ℝ) (hε : 0 < ε) :
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      -ε * (∫ t, ‖g₃ t‖) ≤ ‖splRemainder g 1‖ := by
  obtain ⟨g, g₁, g₂, g₃, h1, h2, h3, h4, h5⟩ := h 0 ε le_rfl hε
  rw [splKernel_zero, norm_zero, zero_sub] at h5
  exact ⟨g, g₁, g₂, g₃, h1, h2, h3, h4, h5⟩

/-- SPL-A at `τ = 1`, `ε = 1/100`, with the non-degeneracy that the class forces: `‖g₃‖₁ > 0`, so the inequality
bounds the ratio `|R(g, 1)| / ‖g₃‖₁` from below by `|κ(1)| − 1/100`. -/
theorem attained_one (h : StationaryLeadingAttainedStatement) :
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (0 < ∫ t, ‖g₃ t‖) ∧
      ‖splKernel 1‖ - 1 / 100 ≤ ‖splRemainder g 1‖ / ∫ t, ‖g₃ t‖ := by
  obtain ⟨g, g₁, g₂, g₃, h1, h2, h3, h4, h5⟩ := h 1 (1 / 100) zero_le_one (by norm_num)
  have hpos := integral_norm_pos_of_splAmplitude h1 h4
  exact ⟨g, g₁, g₂, g₃, h1, h2, h3, hpos, (le_div_iff₀ hpos).2 h5⟩

/-- **Consistency of SPL-A with SPL-K.** Together they bound the kernel: `|κ(τ)| ≤ 7/8` for every `τ ≥ 0`
(SPL-A gives `g ≠ 0` with `(|κ(τ)| − ε) ‖g₃‖₁ ≤ |R(g, 1)|`, SPL-K gives `|R(g, 1)| ≤ (7/8) ‖g₃‖₁`, and
`‖g₃‖₁ > 0` by `integral_norm_pos_of_splAmplitude`, proved here from the class alone). Nothing is proved about the
kernel unconditionally. -/
theorem kernel_le_of_attained_of_sevenEighths (hA : StationaryLeadingAttainedStatement)
    (hK : StationaryLeadingSevenEighthsStatement) (τ : ℝ) (hτ : 0 ≤ τ) : ‖splKernel τ‖ ≤ 7 / 8 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, g₁, g₂, g₃, hamp, -, -, hne, hle⟩ := hA τ ε hτ hε
  have hK' := hK g g₁ g₂ g₃ 1 hamp one_pos
  rw [Real.one_rpow, mul_one] at hK'
  have hpos := integral_norm_pos_of_splAmplitude hamp hne
  have h1 := le_of_mul_le_mul_right (hle.trans hK') hpos
  linarith

/-- The same for every real `τ`, because `|κ|` is even. -/
theorem kernel_le_of_attained_of_sevenEighths' (hA : StationaryLeadingAttainedStatement)
    (hK : StationaryLeadingSevenEighthsStatement) (τ : ℝ) : ‖splKernel τ‖ ≤ 7 / 8 := by
  rw [← norm_splKernel_abs]
  exact kernel_le_of_attained_of_sevenEighths hA hK |τ| (abs_nonneg τ)

/-! ## Data for the planted controls only

Certified values at the data of the plant record (`docs/replay/plants/2026-11-19-SPL/`): the Gaussian at
`(s, λ) = (1, 100)`, `(4, 1600)` and `(1, 0)`, the constant `1` (not an amplitude), oddness of `G_s‴`, and the
integral of an odd function. Nothing here is about the kernel. -/

/-- `1.24·10⁻³ ≤ |R(G_1, 100)|` (the lower bound of `splRemainder_gauss_bounds` is `1.25325…·10⁻³`). -/
theorem splRemainder_gauss_one_hundred_lower : 124 / 100000 ≤ ‖splRemainder (gauss 1) 100‖ := by
  have h1 := (splRemainder_gauss_bounds 1 100 one_pos (by norm_num)).1
  rw [sqrt_hundred] at h1
  have hq1 : Real.sqrt (1 ^ 4 + 100 ^ 2) ≤ 10001 / 100 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq0 : 0 < Real.sqrt (1 ^ 4 + 100 ^ 2) := Real.sqrt_pos.2 (by norm_num)
  generalize Real.sqrt (1 ^ 4 + 100 ^ 2) = q at h1 hq1 hq0
  refine le_trans ?_ h1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sqrt_two_pi_lower]

/-- `3.13·10⁻⁴ ≤ |R(G_4, 1600)|` (the lower bound of `splRemainder_gauss_bounds` is `3.1331…·10⁻⁴`). -/
theorem splRemainder_gauss_four_sixteen_hundred_lower : 313 / 1000000 ≤ ‖splRemainder (gauss 4) 1600‖ := by
  have h1 := (splRemainder_gauss_bounds 4 1600 (by norm_num) (by norm_num)).1
  rw [sqrt_sixteen_hundred] at h1
  have hq1 : Real.sqrt (4 ^ 4 + 1600 ^ 2) ≤ 16001 / 10 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq0 : 0 < Real.sqrt (4 ^ 4 + 1600 ^ 2) := Real.sqrt_pos.2 (by norm_num)
  generalize Real.sqrt (4 ^ 4 + 1600 ^ 2) = q at h1 hq1 hq0
  refine le_trans ?_ h1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sqrt_two_pi_lower]

/-- `|root(1, 100)|² = 2π/√10001`, between `0.0625 = (1/4)²` and `0.063001 = (251/1000)²`. -/
theorem norm_gaussRoot_one_hundred_bounds : 1 / 4 ≤ ‖gaussRoot 1 100‖ ∧ ‖gaussRoot 1 100‖ ≤ 251 / 1000 := by
  have h := norm_gaussRoot_sq 1 100
  have hq1 : Real.sqrt (1 ^ 4 + 100 ^ 2) ≤ 10001 / 100 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq2 : 100 ≤ Real.sqrt (1 ^ 4 + 100 ^ 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hq0 : 0 < Real.sqrt (1 ^ 4 + 100 ^ 2) := Real.sqrt_pos.2 (by norm_num)
  generalize Real.sqrt (1 ^ 4 + 100 ^ 2) = q at h hq1 hq2 hq0
  have hn := norm_nonneg (gaussRoot 1 100)
  rw [eq_div_iff hq0.ne'] at h
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    nlinarith [Real.pi_gt_d2]
  · by_contra hlt
    rw [not_le] at hlt
    nlinarith [Real.pi_lt_d2]

/-- `Im root(1, 100) ≥ 1/10` (true value `0.1247…`): `2 Re·Im = Im(root²) = 200π/10001` and `Re ≤ |root| ≤ 0.251`. -/
theorem gaussRoot_one_hundred_im_lower : 1 / 10 ≤ (gaussRoot 1 100).im := by
  have h1 : (gaussRoot 1 100 ^ 2).im = 2 * (gaussRoot 1 100).re * (gaussRoot 1 100).im := by
    rw [pow_two, Complex.mul_im]
    ring
  rw [gaussRoot_sq, gaussRoot_sq_im] at h1
  have h2 : (gaussRoot 1 100).re ≤ 251 / 1000 :=
    (Complex.re_le_norm _).trans norm_gaussRoot_one_hundred_bounds.2
  have h3 := gaussRoot_re_nonneg 1 100
  have h4 : 2 * Real.pi * 100 / (1 ^ 4 + 100 ^ 2) = 200 / 10001 * Real.pi := by
    norm_num
    ring
  rw [h4] at h1
  by_contra hlt
  rw [not_le] at hlt
  have h5 := gaussRoot_im_nonneg 1 100 (by norm_num)
  nlinarith [Real.pi_gt_d2]

/-- At `λ = 0` the Lean expression `splRemainder (gauss 1) 0` is `√(2π) − 0` in modulus (`√(2π/0) = 0`). -/
theorem norm_splRemainder_gauss_zero : ‖splRemainder (gauss 1) 0‖ = Real.sqrt (2 * Real.pi) := by
  have h0 : splLead 0 = 0 := by
    simp [splLead]
  rw [splRemainder_gauss 1 one_pos, h0, sub_zero]
  have h := norm_gaussRoot_sq 1 0
  have e : (1 : ℝ) ^ 4 + 0 ^ 2 = 1 := by norm_num
  rw [e, Real.sqrt_one, div_one] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `u ↦ 1 · e^{iλu²/2}` is not integrable on the line (its modulus is `1`). -/
theorem not_integrable_one_mul_exp (lam : ℝ) :
    ¬ Integrable (fun u : ℝ => (1 : ℂ) * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) := by
  intro h
  have h1 := h.norm
  have e : (fun u : ℝ => ‖(1 : ℂ) * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖) = fun _ => (1 : ℝ) := by
    funext u
    rw [one_mul, Complex.norm_exp_ofReal_mul_I]
  rw [e] at h1
  have h2 : Integrable (fun _ : ℝ => (1 : ℂ)) := by
    rw [integrable_const_iff] at h1 ⊢
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact Or.inr h1
  exact one_ne_zero (const_eq_zero_of_integrable h2)

/-- For the constant `1` (not an amplitude) the Bochner integral in `splRemainder` is `0`, so
`|splRemainder 1 1| = √(2π)`. -/
theorem norm_splRemainder_one : ‖splRemainder (fun _ => 1) 1‖ = Real.sqrt (2 * Real.pi) := by
  unfold splRemainder
  rw [integral_undef (not_integrable_one_mul_exp 1), zero_sub, norm_neg, one_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_one]

/-- `G_s‴` is odd. -/
theorem gauss3_neg (s t : ℝ) : gauss3 s (-t) = -gauss3 s t := by
  unfold gauss3 gaussR
  rw [← Complex.ofReal_neg]
  congr 1
  have e : -(s * -t) ^ 2 / 2 = -(s * t) ^ 2 / 2 := by ring
  rw [e]
  ring

/-- The Bochner integral of an odd function over the line is `0`. -/
theorem integral_eq_zero_of_odd {f : ℝ → ℂ} (h : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h1 := integral_neg_eq_self f volume
  simp_rw [h] at h1
  rw [integral_neg] at h1
  have h2 : (2 : ℂ) * ∫ x, f x = 0 := by linear_combination -h1
  simpa using h2

end OscInt.API.StationaryLeadingSanity
