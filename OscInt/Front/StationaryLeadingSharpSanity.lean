/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.StationaryLeadingSharp
import OscInt.Front.StationaryLeadingSanity
import OscInt.Front.StationaryLeadingFinal

/-! # Sanity theorems for batch SPL-N (SPL-NU, SPL-NL, SPL-NK, SPL-NC)

Draft, written before the statements are stamped, against `OscInt/Statements/StationaryLeadingSharp.lean`, which it
does not change. No proof of a batch-SPL-N statement exists in this file or is used by it, and no statement of the
batch is derived from another; the one theorem whose conclusion is a statement constant (`spln_cap_of_sharp`) takes
another statement constant of the batch as its hypothesis. Two forms (`docs/lessons.md`, rules 8 and 9).

Proved repository theorems used as data: SPL-S, SPL-K and SPL-A (`stationaryLeading`,
`stationaryLeadingSevenEighths`, `stationaryLeadingAttained`), and the batch-SPL sanity layer
(`OscInt.API.StationaryLeadingSanity`: the Gaussian family `G_s`, its remainder, `‖G_s‴‖₁`, `‖G_s″‖₁`, oddness of
`κ`, `κ(0) = 0`). The only facts about the kernel used are those these give: `|κ| ≤ 7/8` everywhere and
`|κ(τ)| ≥ 3/10` at some `τ ≥ 0`. No other bound on `κ` is proved here.

A. Unconditional, on closed data:
* The rationals: `72197399/10⁸ < 360987/500000 < 7/8`, with difference `10⁻⁸` between the first two.
* The kernel through proved theorems: `|κ| ≤ 7/8` (`spln_kernel_le_seven_eighths`), `|κ(τ)| ≥ 3/10` for some
  `τ ≥ 0` (`spln_kernel_large`); bites: SPL-NL's inequality fails at the point `0` (`spln_lower_fails_at_zero`), a cap
  `1/4` fails (`spln_cap_bite`).
* The two branches of `splKernel`: `F(−τ) = −F(τ)`, `κ₊(−τ) + κ₊(τ) = iτ² F(∞)`, `|F(∞)|² = π/2`; bite of the odd
  extension: `|κ₊(−2)| > 3` (`spln_kernelPos_neg_two`), so a cap on `κ₊` over the whole line is false.
* Data for SPL-NK: the Gaussian at `(s, λ) = (1, 4)` in the regime where SPL-NK's bound beats both the size
  `√(2π/λ)` of the leading term and SPL-K's bound (`spln_sharp_one_four_nontrivial`), and is within a factor
  `5/2` of the truth (`spln_sharp_one_four_within`); at `(1/2, 1/16)` (`λ < 1`); real powers at `1/16` and `100`.
* Bites of SPL-NK's hypotheses: at `λ = 0` the conclusion fails for `G_1`; for the constant `1` (not an amplitude)
  with zero derivatives it fails at `λ = 1`.
* Bites of SPL-NC: at `c = 7/8` the bound holds (proved SPL-K), so `c ≤ 72197399/10⁸` matters
  (`spln_sharpness_range_bite`); without `0 < λ` the bound fails for every `c` (`spln_sharpness_needs_pos_lam`); for
  `c ≤ 0` it fails on `G_1` at `λ = 4` (`spln_sharpness_nonpos`, the degenerate case of the binder `c`).

B. Conditional, each statement constant as the only statement hypothesis (consistency theorems take two): SPL-NU at
the point `8123/5000`, on the negative branch, at the point of `spln_kernel_large`, and against a lower value above
the cap; SPL-NK implies SPL-NU through the proved SPL-A (`spln_cap_of_sharp`); SPL-NL with oddness, against a cap
`72197399/10⁸`, with SPL-NU; SPL-NK on the Gaussian family and at `(1, 4)`, `(1/2, 1/16)`, `(1, 100)`, `(4, 1600)`;
SPL-NC in existential form, with a nonzero amplitude and `‖g₃‖₁ > 0`, through the proved SPL-S a kernel value above
`72197399/10⁸`, against the constant `7/10`, and with SPL-NK.

Planted copies: `plants/README.md` of the scratch work directory of the sanity agent (not in the repository).
-/

namespace OscInt.API.StationaryLeadingSharpSanity

open OscInt.Statements OscInt.API.StationaryLeadingSanity MeasureTheory

/-! ## A. The two rationals -/

/-- The cap of SPL-NU is below the constant `7/8` of SPL-K. -/
theorem spln_cap_lt_seven_eighths : (360987 / 500000 : ℝ) < 7 / 8 := by norm_num

/-- The lower value of SPL-NL is below the cap of SPL-NU. -/
theorem spln_lower_lt_cap : (72197399 / 100000000 : ℝ) < 360987 / 500000 := by norm_num

/-- The two rationals differ by `10⁻⁸`. -/
theorem spln_cap_sub_lower : (360987 / 500000 : ℝ) - 72197399 / 100000000 = 1 / 100000000 := by norm_num

/-! ## A. The kernel, through proved repository theorems only -/

/-- `|κ(τ)| ≤ 7/8` for every real `τ` (proved SPL-A and SPL-K, through `kernel_le_of_attained_of_sevenEighths'`). -/
theorem spln_kernel_le_seven_eighths (τ : ℝ) : ‖splKernel τ‖ ≤ 7 / 8 :=
  kernel_le_of_attained_of_sevenEighths' stationaryLeadingAttained stationaryLeadingSevenEighths τ

/-- Some `τ ≥ 0` has `|κ(τ)| ≥ 3/10` (proved SPL-S, through `kernel_large`). -/
theorem spln_kernel_large : ∃ τ : ℝ, 0 ≤ τ ∧ 3 / 10 ≤ ‖splKernel τ‖ := kernel_large stationaryLeading

/-- **Bite** of the point of SPL-NL: at `τ = 0` the inequality fails (`κ(0) = 0`). -/
theorem spln_lower_fails_at_zero : ¬ ((72197399 / 100000000 : ℝ) < ‖splKernel 0‖) := by
  rw [splKernel_zero, norm_zero]
  norm_num

/-- **Bite** of the cap: a cap `1/4` is false. -/
theorem spln_cap_bite : ¬ ∀ τ : ℝ, ‖splKernel τ‖ ≤ 1 / 4 := by
  intro h
  obtain ⟨τ, -, hτ⟩ := spln_kernel_large
  have := h τ
  linarith

/-! ## A. The two branches of the definition of `κ` -/

/-- `F(−τ) = −F(τ)`: the Fresnel primitive is odd. -/
theorem spln_fresnelPrim_neg (τ : ℝ) : fresnelPrim (-τ) = -fresnelPrim τ := by
  unfold fresnelPrim
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := τ)
    (f := fun v : ℝ => Complex.exp (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I))
  simp only [neg_sq, neg_zero] at h
  rw [intervalIntegral.integral_symm (-τ) 0, ← h]

/-- `κ₊(−τ) + κ₊(τ) = iτ² F(∞)`: `κ₊` itself is not odd. -/
theorem spln_kernelPos_neg_add (τ : ℝ) :
    splKernelPos (-τ) + splKernelPos τ = Complex.I * (τ : ℂ) ^ 2 * fresnelLimit := by
  unfold splKernelPos
  rw [spln_fresnelPrim_neg]
  simp only [neg_sq, Complex.ofReal_neg]
  ring

/-- `|F(∞)|² = π/2`. -/
theorem spln_norm_fresnelLimit_sq : ‖fresnelLimit‖ ^ 2 = Real.pi / 2 := by
  rw [← norm_pow, fresnelLimit_sq, norm_div, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  norm_num

/-- `|F(∞)| ≥ 5/4`. -/
theorem spln_norm_fresnelLimit_ge : 5 / 4 ≤ ‖fresnelLimit‖ := by
  have h := spln_norm_fresnelLimit_sq
  have h0 := norm_nonneg fresnelLimit
  nlinarith [Real.pi_gt_d2]

/-- On `[0, ∞)` the kernel is `κ₊`. -/
theorem spln_kernel_pos_branch {τ : ℝ} (hτ : 0 ≤ τ) : splKernel τ = splKernelPos τ := by
  unfold splKernel
  rw [ite_eq_left hτ]

/-- On `(−∞, 0)` the kernel is `τ ↦ −κ₊(−τ)`. -/
theorem spln_kernel_neg_branch {τ : ℝ} (hτ : τ < 0) : splKernel τ = -splKernelPos (-τ) := by
  unfold splKernel
  rw [ite_eq_right (not_le.2 hτ)]

/-- **Bite** of the definition by cases: `|κ₊(−2)| ≥ 4 |F(∞)| − |κ₊(2)| ≥ 5 − 7/8 > 3`, so a cap on `κ₊` over the
whole line (instead of the odd extension `κ`) is false. -/
theorem spln_kernelPos_neg_two : 3 < ‖splKernelPos (-2)‖ := by
  have h1 := spln_kernelPos_neg_add 2
  have h2 : ‖splKernelPos 2‖ ≤ 7 / 8 := by
    rw [← spln_kernel_pos_branch (by norm_num : (0 : ℝ) ≤ 2)]
    exact spln_kernel_le_seven_eighths 2
  have h3 : ‖Complex.I * ((2 : ℝ) : ℂ) ^ 2 * fresnelLimit‖ = 4 * ‖fresnelLimit‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos two_pos]
    ring
  have h4 : splKernelPos (-2) = Complex.I * ((2 : ℝ) : ℂ) ^ 2 * fresnelLimit - splKernelPos 2 := by
    rw [← h1]
    ring
  have h5 := norm_sub_norm_le (Complex.I * ((2 : ℝ) : ℂ) ^ 2 * fresnelLimit) (splKernelPos 2)
  rw [← h4, h3] at h5
  linarith [spln_norm_fresnelLimit_ge]

/-! ## A. Data for SPL-NK: real powers, and the Gaussian family -/

/-- `(1/16)^{−3/2} = 64`. -/
theorem spln_rpow_sixteenth : (1 / 16 : ℝ) ^ (-(3 : ℝ) / 2) = 64 := by
  rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, rpow_neg_three_halves_sq (1 / 4) (by norm_num)]
  norm_num

/-- `(1/16)^{−1/2} = 4` (used by one planted control). -/
theorem spln_rpow_sixteenth_half : (1 / 16 : ℝ) ^ (-(1 : ℝ) / 2) = 4 := by
  have h : ((2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -1 := by norm_num
  rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, ← Real.rpow_natCast (1 / 4 : ℝ) 2,
    ← Real.rpow_mul (by norm_num), h, Real.rpow_neg_one]
  norm_num

/-- `100^{−5/2} = 10⁻⁵` (used by one planted control). -/
theorem spln_rpow_hundred_five_halves : (100 : ℝ) ^ (-(5 : ℝ) / 2) = 1 / 100000 := by
  have h : ((2 : ℕ) : ℝ) * (-(5 : ℝ) / 2) = -((5 : ℕ) : ℝ) := by norm_num
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, ← Real.rpow_natCast (10 : ℝ) 2, ← Real.rpow_mul (by norm_num), h,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  norm_num

/-- `√(1/16) = 1/4`. -/
theorem spln_sqrt_sixteenth : Real.sqrt (1 / 16) = 1 / 4 := by
  rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `|R(G_{1/2}, 1/16)| ≥ 4.8` (the lower bound of `splRemainder_gauss_bounds` is `√(2π)/(2√(17/256)) = 4.86…`). -/
theorem spln_remainder_gauss_small_lower : 48 / 10 ≤ ‖splRemainder (gauss (1 / 2)) (1 / 16)‖ := by
  have h1 := (splRemainder_gauss_bounds (1 / 2) (1 / 16) (by norm_num) (by norm_num)).1
  rw [spln_sqrt_sixteenth] at h1
  have hq1 : Real.sqrt ((1 / 2) ^ 4 + (1 / 16) ^ 2) ≤ 26 / 100 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hq0 : 0 < Real.sqrt ((1 / 2 : ℝ) ^ 4 + (1 / 16) ^ 2) := Real.sqrt_pos.2 (by norm_num)
  generalize Real.sqrt ((1 / 2 : ℝ) ^ 4 + (1 / 16) ^ 2) = q at h1 hq1 hq0
  refine le_trans ?_ h1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sqrt_two_pi_lower]

/-- **Non-trivial regime** of SPL-NK at `G_1`, `λ = 4`: its bound `(360987/500000) ‖G_1‴‖₁/8 = 0.3415…` is below
the size `√(2π/4) = 1.2533…` of the leading term (so below the trivial bound of the remainder) and strictly below
the bound `0.4140…` of SPL-K. -/
theorem spln_sharp_one_four_nontrivial :
    (360987 / 500000 : ℝ) * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) < Real.sqrt (2 * Real.pi / 4) ∧
      (360987 / 500000 : ℝ) * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) <
        7 / 8 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) := by
  constructor
  · have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi / 4) :=
      Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
    have := normThree_le
    linarith
  · exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by norm_num) normThree_pos) (by norm_num)

/-- The bound of SPL-NK at `G_1`, `λ = 4` is within a factor `5/2` of the truth (unconditional: `0.151 ≥ 0.1367`). -/
theorem spln_sharp_one_four_within :
    2 / 5 * ((360987 / 500000 : ℝ) * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8)) ≤ ‖splRemainder (gauss 1) 4‖ := by
  have h := splRemainder_gauss_one_four_bounds.1
  have := normThree_le
  linarith

/-- **Bite** of `0 < λ` in SPL-NK: at `λ = 0` its conclusion fails for `G_1` (`0^{−3/2} = 0` for `Real.rpow`, and
the Lean value of `R(G_1, 0)` has modulus `√(2π)`). -/
theorem spln_sharp_conclusion_fails_lam_zero :
    ¬ (‖splRemainder (gauss 1) 0‖ ≤
      (360987 / 500000 : ℝ) * (∫ t, ‖gauss3 1 t‖) * (0 : ℝ) ^ (-(3 : ℝ) / 2)) := by
  rw [Real.zero_rpow (by norm_num), mul_zero, norm_splRemainder_gauss_zero, not_le]
  exact Real.sqrt_pos.2 (by positivity)

/-- **Bite** of `SplAmplitude` in SPL-NK: the constant `1` with zero derivatives is not an amplitude, and its
conclusion fails at `λ = 1`. -/
theorem spln_sharp_amplitude_bite :
    ¬ SplAmplitude (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
      ¬ (‖splRemainder (fun _ => 1) 1‖ ≤
        (360987 / 500000 : ℝ) * (∫ t, ‖(fun _ : ℝ => (0 : ℂ)) t‖) * (1 : ℝ) ^ (-(3 : ℝ) / 2)) := by
  refine ⟨one_not_splAmplitude, ?_⟩
  simp only [norm_zero, integral_zero, mul_zero, zero_mul, not_le]
  rw [norm_splRemainder_one]
  exact Real.sqrt_pos.2 (by positivity)

/-! ## A. Bites of SPL-NC -/

/-- **Bite** of `c ≤ 72197399/10⁸` in SPL-NC: at `c = 7/8` the bound holds (proved SPL-K), so SPL-NC cannot
extend to `c = 7/8`. -/
theorem spln_sharpness_range_bite :
    ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
      ‖splRemainder g lam‖ ≤ (7 / 8 : ℝ) * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) :=
  stationaryLeadingSevenEighths

/-- **Bite** of `0 < λ` in SPL-NC: without it the bound fails for every `c`, on `G_1` at `λ = 0`. -/
theorem spln_sharpness_needs_pos_lam (c : ℝ) :
    ¬ ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ →
      ‖splRemainder g lam‖ ≤ c * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := by
  intro h
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 0 (gauss_splAmplitude 1 one_pos)
  rw [Real.zero_rpow (by norm_num), mul_zero, norm_splRemainder_gauss_zero] at h1
  exact absurd h1 (not_le.2 (Real.sqrt_pos.2 (by positivity)))

/-- The degenerate case `c ≤ 0` of SPL-NC's binder: the bound fails on `G_1` at `λ = 4` (`|R(G_1, 4)| ≥ 0.151`). -/
theorem spln_sharpness_nonpos (c : ℝ) (hc : c ≤ 0) :
    ¬ ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
      ‖splRemainder g lam‖ ≤ c * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := by
  intro h
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [integral_norm_gauss3 1 one_pos, rpow_four] at h1
  have h2 := splRemainder_gauss_one_four_bounds.1
  have h3 : 0 ≤ (1 : ℝ) ^ 2 * (2 + 8 * Real.exp (-(3 / 2))) := by positivity
  have h4 : c * ((1 : ℝ) ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * (1 / 8) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc h3) (by norm_num)
  linarith

/-! ## B. SPL-NU through its statement constant -/

/-- SPL-NU at the point of SPL-NL. -/
theorem spln_cap_point (h : SplKernelCapStatement) : ‖splKernel (8123 / 5000)‖ ≤ 360987 / 500000 :=
  h (8123 / 5000)

/-- SPL-NU on the negative branch: at `−τ`, `τ > 0`, it bounds `κ₊(τ)`. -/
theorem spln_cap_neg_branch (h : SplKernelCapStatement) (τ : ℝ) (hτ : 0 < τ) :
    ‖splKernelPos τ‖ ≤ 360987 / 500000 := by
  have h1 := h (-τ)
  rw [spln_kernel_neg_branch (by linarith), norm_neg, neg_neg] at h1
  exact h1

/-- SPL-NU at the point of `spln_kernel_large`: `3/10 ≤ |κ(τ)| ≤ 360987/500000`. -/
theorem spln_cap_large (h : SplKernelCapStatement) :
    ∃ τ : ℝ, 0 ≤ τ ∧ 3 / 10 ≤ ‖splKernel τ‖ ∧ ‖splKernel τ‖ ≤ 360987 / 500000 := by
  obtain ⟨τ, hτ, h1⟩ := spln_kernel_large
  exact ⟨τ, hτ, h1, h τ⟩

/-- SPL-NU excludes a lower value `72197401/10⁸` (above the cap) at the point of SPL-NL. -/
theorem spln_cap_excludes_higher_lower (h : SplKernelCapStatement) :
    ¬ ((72197401 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖) := by
  have := h (8123 / 5000)
  intro h1
  linarith

/-- **Consistency of SPL-NK with SPL-NU, through the proved SPL-A**: SPL-NK implies SPL-NU (SPL-A gives `g ≠ 0`
with `(|κ(|τ|)| − ε) ‖g₃‖₁ ≤ |R(g, 1)|`, SPL-NK bounds `|R(g, 1)|` by `(360987/500000) ‖g₃‖₁`, and `‖g₃‖₁ > 0`). -/
theorem spln_cap_of_sharp (hK : StationaryLeadingSharpStatement) : SplKernelCapStatement := by
  intro τ
  rw [← norm_splKernel_abs]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, g₁, g₂, g₃, hamp, -, -, hne, hle⟩ := stationaryLeadingAttained |τ| ε (abs_nonneg τ) hε
  have hK' := hK g g₁ g₂ g₃ 1 hamp one_pos
  rw [Real.one_rpow, mul_one] at hK'
  have hpos := integral_norm_pos_of_splAmplitude hamp hne
  have h1 := le_of_mul_le_mul_right (hle.trans hK') hpos
  linarith

/-! ## B. SPL-NL through its statement constant -/

/-- SPL-NL makes the kernel nonzero at its point. -/
theorem spln_lower_ne_zero (h : SplKernelLowerStatement) : splKernel (8123 / 5000) ≠ 0 := by
  have h1 : (72197399 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖ := h
  intro h0
  rw [h0, norm_zero] at h1
  norm_num at h1

/-- SPL-NL at the reflected point `−8123/5000` (the negative branch, by oddness). -/
theorem spln_lower_neg_point (h : SplKernelLowerStatement) :
    (72197399 / 100000000 : ℝ) < ‖splKernel (-(8123 / 5000))‖ := by
  rw [norm_splKernel_neg]
  exact h

/-- SPL-NL excludes a cap `72197399/10⁸`. -/
theorem spln_lower_excludes_cap (h : SplKernelLowerStatement) :
    ¬ ∀ τ : ℝ, ‖splKernel τ‖ ≤ 72197399 / 100000000 := by
  have h1 : (72197399 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖ := h
  intro h2
  have := h2 (8123 / 5000)
  linarith

/-- SPL-NL is consistent with the proved `|κ| ≤ 7/8`. -/
theorem spln_lower_below_seven_eighths (h : SplKernelLowerStatement) :
    (72197399 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖ ∧ ‖splKernel (8123 / 5000)‖ ≤ 7 / 8 :=
  ⟨h, spln_kernel_le_seven_eighths _⟩

/-- **Consistency of SPL-NL with SPL-NU**: both at the point `8123/5000`. -/
theorem spln_lower_and_cap (hU : SplKernelCapStatement) (hL : SplKernelLowerStatement) :
    (72197399 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖ ∧ ‖splKernel (8123 / 5000)‖ ≤ 360987 / 500000 :=
  ⟨hL, hU _⟩

/-! ## B. SPL-NK through its statement constant -/

/-- SPL-NK on the Gaussian family, with `‖G_s‴‖₁ = s²(2 + 8e^{−3/2})`. -/
theorem spln_sharp_gauss (h : StationaryLeadingSharpStatement) (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    ‖gaussRoot s lam - splLead lam‖ ≤
      360987 / 500000 * (s ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * lam ^ (-(3 : ℝ) / 2) := by
  have h1 := h (gauss s) (gauss1 s) (gauss2 s) (gauss3 s) lam (gauss_splAmplitude s hs) hlam
  rw [splRemainder_gauss s hs, integral_norm_gauss3 s hs] at h1
  exact h1

/-- SPL-NK at `G_1`, `λ = 4`, written out (the non-trivial regime, `spln_sharp_one_four_nontrivial`). -/
theorem spln_sharp_one_four (h : StationaryLeadingSharpStatement) :
    ‖splRemainder (gauss 1) 4‖ ≤ 360987 / 500000 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 8) := by
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 4 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [integral_norm_gauss3 1 one_pos, rpow_four, one_pow, one_mul] at h1
  exact h1

/-- SPL-NK at `G_{1/2}`, `λ = 1/16` (`λ < 1`, `(1/16)^{−3/2} = 64`). -/
theorem spln_sharp_small (h : StationaryLeadingSharpStatement) :
    ‖splRemainder (gauss (1 / 2)) (1 / 16)‖ ≤
      360987 / 500000 * ((1 / 2) ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * 64 := by
  have h1 := h (gauss (1 / 2)) (gauss1 (1 / 2)) (gauss2 (1 / 2)) (gauss3 (1 / 2)) (1 / 16)
    (gauss_splAmplitude (1 / 2) (by norm_num)) (by norm_num)
  rw [integral_norm_gauss3 (1 / 2) (by norm_num), spln_rpow_sixteenth] at h1
  exact h1

/-- SPL-NK at `G_1`, `λ = 100`. -/
theorem spln_sharp_hundred (h : StationaryLeadingSharpStatement) :
    ‖splRemainder (gauss 1) 100‖ ≤ 360987 / 500000 * (2 + 8 * Real.exp (-(3 / 2))) * (1 / 1000) := by
  have h1 := h (gauss 1) (gauss1 1) (gauss2 1) (gauss3 1) 100 (gauss_splAmplitude 1 one_pos) (by norm_num)
  rw [integral_norm_gauss3 1 one_pos, rpow_hundred, one_pow, one_mul] at h1
  exact h1

/-- SPL-NK at `G_4`, `λ = 1600`. -/
theorem spln_sharp_sixteen_hundred (h : StationaryLeadingSharpStatement) :
    ‖splRemainder (gauss 4) 1600‖ ≤ 360987 / 500000 * (4 ^ 2 * (2 + 8 * Real.exp (-(3 / 2)))) * (1 / 64000) := by
  have h1 := h (gauss 4) (gauss1 4) (gauss2 4) (gauss3 4) 1600 (gauss_splAmplitude 4 (by norm_num)) (by norm_num)
  rw [integral_norm_gauss3 4 (by norm_num), rpow_sixteen_hundred] at h1
  exact h1

/-! ## B. SPL-NC through its statement constant -/

/-- SPL-NC in existential form. -/
theorem spln_sharpness_exists (h : StationaryLeadingSharpnessStatement) (c : ℝ)
    (hc : c ≤ 72197399 / 100000000) :
    ∃ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ ∧ 0 < lam ∧
      c * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) < ‖splRemainder g lam‖ := by
  have h1 := h c hc
  push Not at h1
  exact h1

/-- The amplitudes SPL-NC asserts at `c = 72197399/10⁸` are not identically zero and have `‖g₃‖₁ > 0`. -/
theorem spln_sharpness_nonzero (h : StationaryLeadingSharpnessStatement) :
    ∃ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ ∧ 0 < lam ∧ (∃ x, g x ≠ 0) ∧
      0 < ∫ t, ‖g₃ t‖ ∧ 72197399 / 100000000 * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) < ‖splRemainder g lam‖ := by
  obtain ⟨g, g₁, g₂, g₃, lam, hA, hl, hlt⟩ := spln_sharpness_exists h _ le_rfl
  have hne : ∃ x, g x ≠ 0 := by
    by_contra hz
    push Not at hz
    have hR : splRemainder g lam = 0 := by simp [splRemainder, hz]
    have h0 : 0 ≤ 72197399 / 100000000 * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun t => norm_nonneg _)) (Real.rpow_nonneg hl.le _)
    rw [hR, norm_zero] at hlt
    linarith
  exact ⟨g, g₁, g₂, g₃, lam, hA, hl, hne, integral_norm_pos_of_splAmplitude hA hne, hlt⟩

/-- SPL-NC with the proved SPL-S: some `τ ≥ 0` has `|κ(τ)| > 72197399/10⁸`. -/
theorem spln_sharpness_kernel (h : StationaryLeadingSharpnessStatement) :
    ∃ τ : ℝ, 0 ≤ τ ∧ 72197399 / 100000000 < ‖splKernel τ‖ := by
  obtain ⟨g, g₁, g₂, g₃, lam, hA, hl, -, hpos, hlt⟩ := spln_sharpness_nonzero h
  obtain ⟨τ, hτ, hS⟩ := stationaryLeading g g₁ g₂ g₃ lam hA hl
  refine ⟨τ, hτ, ?_⟩
  have hp : 0 < (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := mul_pos hpos (Real.rpow_pos_of_pos hl _)
  have h1 : 72197399 / 100000000 * ((∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)) <
      ‖splKernel τ‖ * ((∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)) := by
    rw [← mul_assoc, ← mul_assoc]
    linarith
  exact lt_of_mul_lt_mul_right h1 hp.le

/-- SPL-NC refutes the constant `7/10` in place of `360987/500000`. -/
theorem spln_sharpness_refutes (h : StationaryLeadingSharpnessStatement) :
    ¬ ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
      ‖splRemainder g lam‖ ≤ (7 / 10 : ℝ) * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) :=
  h (7 / 10) (by norm_num)

/-- **Consistency of SPL-NC with SPL-NK**: one amplitude and one `λ > 0` with
`(72197399/10⁸) ‖g₃‖₁ λ^{−3/2} < |R(g, λ)| ≤ (360987/500000) ‖g₃‖₁ λ^{−3/2}`. -/
theorem spln_sharp_and_sharpness (hK : StationaryLeadingSharpStatement) (hC : StationaryLeadingSharpnessStatement) :
    ∃ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ ∧ 0 < lam ∧
      72197399 / 100000000 * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) < ‖splRemainder g lam‖ ∧
      ‖splRemainder g lam‖ ≤ 360987 / 500000 * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := by
  obtain ⟨g, g₁, g₂, g₃, lam, hA, hl, hlt⟩ := spln_sharpness_exists hC _ le_rfl
  exact ⟨g, g₁, g₂, g₃, lam, hA, hl, hlt, hK g g₁ g₂ g₃ lam hA hl⟩

end OscInt.API.StationaryLeadingSharpSanity
