/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.PeriodicAnalyticSanity

/-! # Second sanity layer for the batch-PA statement constants

Answers the blind pre-proof reviews of batch PA: mutations that the first layer
(`OscInt/Front/PeriodicAnalyticSanity.lean`) does not detect. Same discipline (`docs/lessons.md`, rules 8 and 9): a
theorem about a frozen statement of `OscInt/Statements/PeriodicAnalytic.lean` takes that statement constant as its
only statement hypothesis and concludes on closed data; everything else is an unconditional lemma on data. No
statement of the batch is proved or used otherwise. Planted copies and witnesses of this layer:
`docs/replay/plants/2026-11-16-PA-second/`.

What the first layer could not see, and the datum added here:
* **Node positions of `trapezoidalSum`.** Both PA-T data of the first layer (`cos3` at `N = 3`, `expDatum` at `N = 1`)
  have every node value equal to `v(0)`. Here: `cos3` at `N = 6` (node values `7(−1)^j`, sum `0`) and at `N = 4`
  (node values `7, 0, −7, 0`, sum `0`); the integral is `0`, so PA-T concludes `0 ≤ bound` there. The content is the
  pinned value of `trapezoidalSum` at nodes that are not all equal.
* **PA-C at `k = 0`** (`expDatum`, coefficient `10π`): the mean, where the exponential factor is `1`.
* **Integrality of `k` and `n`.** At the half-integer `1/2` both conclusions are false: `I(0, 1/2) = 4 > 2π/e` (LC-1
  at `t = 0`, `η = 2`) and `|∫_0^{2π} 1 · e^{−iθ/2} dθ| = 4 > 2π/e` (PA-C at `v = 1`, `a = 2`, `M = 1`).
* **The bound must hold off the real axis.** `‖cos3 z‖ ≤ 7` on the real axis, yet `cos3` is not admissible with
  `M = 7` on the strip of half-width `1`.
* Data for the planted controls only (last section): the node sums of `cos3` at the planted nodes `πj/6` (`j < 6`)
  and `⌊j/4⌋` (`j < 4`), and `stripExp z = e^{iz}` for `|Im z| < 1`, `0` otherwise (holomorphic on the strip of
  half-width `1` only; `2π`-periodic and bounded by `e` everywhere; coefficient `2π` at `k = 1`).

What this layer still cannot see (verdicts NOT DETECTED in the plant record): the denominator `e^{aN} − 1` of PA-T
against `e^{aN}`, and the factor of `|t|` in LC-1 (`|t|` against `|t|/2`, false only for `|n| ≥ 2`). The sign of `n`
in LC-1 (`|n|` against `n`) is a true weakening.
-/

namespace OscInt.API.PeriodicAnalyticSanity2

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.LatticeExplicitSanity OscInt.API.LatticeCubeRootSanity
  OscInt.API.PeriodicAnalyticSanity

/-! ## Node positions (PA-T) -/

/-- On the real axis `cos3 x = 7 cos 3x`. -/
theorem cos3_ofReal (x : ℝ) : cos3 (x : ℂ) = ((7 * Real.cos (3 * x) : ℝ) : ℂ) := by
  simp [cos3]

/-- `cos3 x = 7 (−1)^m` when `3x = mπ`. -/
theorem cos3_of_mul_pi (x : ℝ) (m : ℕ) (hx : 3 * x = m * Real.pi) : cos3 (x : ℂ) = 7 * (-1) ^ m := by
  rw [cos3_ofReal, hx, Real.cos_nat_mul_pi]; push_cast; ring

/-- `cos3 x = 0` when `3x` is an odd multiple of `π/2`. -/
theorem cos3_of_odd_mul_half_pi (x : ℝ) (m : ℤ) (hx : 3 * x = (2 * m + 1) * Real.pi / 2) : cos3 (x : ℂ) = 0 := by
  rw [cos3_ofReal, Real.cos_eq_zero_iff.mpr ⟨m, hx⟩]; simp

/-- `cos3` is `7(−1)^j` at the node `2πj/6 = jπ/3`. -/
theorem cos3_node_six (j : ℕ) : cos3 ((2 * Real.pi * (j : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ j :=
  cos3_of_mul_pi _ j (by push_cast; ring)

/-- The 6-point trapezoidal sum of `cos3` is `0`: the node values are `7, −7, 7, −7, 7, −7`. -/
theorem trapezoidalSum_cos3_six : trapezoidalSum cos3 6 = 0 := by
  simp only [trapezoidalSum, cos3_node_six, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The 4-point trapezoidal sum of `cos3` is `0`: the node values are `7, 0, −7, 0`. -/
theorem trapezoidalSum_cos3_four : trapezoidalSum cos3 4 = 0 := by
  have h0 : cos3 ((2 * Real.pi * ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ 0 :=
    cos3_of_mul_pi _ 0 (by push_cast; ring)
  have h1 : cos3 ((2 * Real.pi * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) = 0 :=
    cos3_of_odd_mul_half_pi _ 1 (by push_cast; ring)
  have h2 : cos3 ((2 * Real.pi * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ 3 :=
    cos3_of_mul_pi _ 3 (by push_cast; ring)
  have h3 : cos3 ((2 * Real.pi * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) = 0 :=
    cos3_of_odd_mul_half_pi _ 4 (by push_cast; ring)
  simp only [trapezoidalSum, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]
  norm_num

/-- **PA-T through the statement constant** at `cos3`, `N = 6`, every `a > 0`: `I_6 = I = 0`, so the conclusion is
`0 ≤ bound`. The content is the value pin `trapezoidalSum_cos3_six` (node values not all equal) used on the way. -/
theorem trapezoid_cos3_six (h : TrapezoidalRuleStatement) (a : ℝ) (ha : 0 < a) :
    (0 : ℝ) ≤ 4 * Real.pi * (7 * Real.cosh (3 * a)) / (Real.exp (a * 6) - 1) := by
  have h1 := h cos3 a (7 * Real.cosh (3 * a)) 6 ha (by norm_num) (cos3_periodicAnalyticOn a ha)
  rw [trapezoidalSum_cos3_six, integral_cos3, sub_zero, norm_zero, Nat.cast_ofNat] at h1
  exact h1

/-- **PA-T through the statement constant** at `cos3`, `N = 4`, every `a > 0`: `I_4 = I = 0` (value pin
`trapezoidalSum_cos3_four`: node values `7, 0, −7, 0`). -/
theorem trapezoid_cos3_four (h : TrapezoidalRuleStatement) (a : ℝ) (ha : 0 < a) :
    (0 : ℝ) ≤ 4 * Real.pi * (7 * Real.cosh (3 * a)) / (Real.exp (a * 4) - 1) := by
  have h1 := h cos3 a (7 * Real.cosh (3 * a)) 4 ha (by norm_num) (cos3_periodicAnalyticOn a ha)
  rw [trapezoidalSum_cos3_four, integral_cos3, sub_zero, norm_zero, Nat.cast_ofNat] at h1
  exact h1

/-! ## PA-C at `k = 0` -/

/-- `∫_0^{2π} expDatum(θ) e^{−i·0·θ} dθ = 10π`, in the shape PA-C produces at `k = 0`. -/
theorem integral_expDatum_zero :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), expDatum (θ : ℂ) * Complex.exp (↑(-(((0 : ℤ) : ℝ) * θ)) * Complex.I) =
      10 * Real.pi := by
  rw [integral_expDatum_mul_mode]; norm_num; ring

/-- **PA-C through the statement constant** at `expDatum`, `k = 0`, every `a > 0`: the mean `10π` against the bound
`2π(√13 e^a + 5)` (the exponential factor is `e^{−a·0} = 1`). -/
theorem fourierCoeff_expDatum_zero (h : FourierCoeffStripStatement) (a : ℝ) (ha : 0 < a) :
    10 * Real.pi ≤ 2 * Real.pi * (Real.sqrt 13 * Real.exp a + 5) * Real.exp (-(a * 0)) := by
  have h1 := h expDatum a (Real.sqrt 13 * Real.exp a + 5) 0 ha (expDatum_periodicAnalyticOn a ha)
  rw [integral_expDatum_zero, norm_mul_pi, Complex.norm_ofNat, Int.cast_zero, abs_zero] at h1
  exact h1

/-! ## Integrality bites (LC-1 and PA-C at the half-integer `1/2`) -/

/-- `2π/e < 4`. -/
theorem two_pi_exp_neg_one_lt_four : 2 * Real.pi * Real.exp (-1) < 4 := by
  have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_one_gt_d9
  have h4 : Real.exp (-1) < 1 / 2 := by nlinarith [Real.exp_pos (-1)]
  have h5 := Real.pi_le_four
  have h6 := Real.pi_pos
  nlinarith

/-- `I(0, 1/2) = ∫_{−π}^{π} e^{ik/2} dk = 4`. -/
theorem latticeKernel1_zero_half : latticeKernel1 0 (1 / 2) = 4 := by
  have hc : (Complex.I / 2 : ℂ) ≠ 0 := by simp
  have hf : (fun k : ℝ => Complex.exp (↑((0 : ℝ) * Real.cos k + 1 / 2 * k) * Complex.I)) =
      fun k : ℝ => Complex.exp (Complex.I / 2 * (k : ℂ)) := by
    funext k; congr 1; push_cast; ring
  have e1 : Complex.exp (Complex.I / 2 * ((Real.pi : ℝ) : ℂ)) = Complex.I := by
    rw [show Complex.I / 2 * ((Real.pi : ℝ) : ℂ) = (Real.pi / 2 : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  have e2 : Complex.exp (Complex.I / 2 * ((-Real.pi : ℝ) : ℂ)) = -Complex.I := by
    rw [show Complex.I / 2 * ((-Real.pi : ℝ) : ℂ) = -(Complex.I / 2 * ((Real.pi : ℝ) : ℂ)) by push_cast; ring,
      Complex.exp_neg, e1, Complex.inv_I]
  rw [latticeKernel1, hf, integral_exp_mul_complex hc, e1, e2]
  field_simp
  ring

/-- **Bite: `n` must be an integer in LC-1.** At `t = 0`, `n = 1/2`, `η = 2` the bound would say `4 ≤ 2π/e`. -/
theorem lightCone_nonInteger_false :
    ¬ ‖latticeKernel1 0 (1 / 2)‖ ≤ 2 * Real.pi * Real.exp (|(0 : ℝ)| * Real.sinh 2 - |(1 / 2 : ℝ)| * 2) := by
  rw [latticeKernel1_zero_half, Complex.norm_ofNat, abs_zero, zero_mul, zero_sub,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), show (1 / 2 : ℝ) * 2 = 1 by norm_num]
  exact not_le.mpr two_pi_exp_neg_one_lt_four

/-- `∫_0^{2π} 1 · e^{−iθ/2} dθ = −4i`, in the shape PA-C would produce at `v = 1`, `k = 1/2`. -/
theorem halfMode_integral :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℂ) * Complex.exp (↑(-((1 / 2 : ℝ) * θ)) * Complex.I) =
      -4 * Complex.I := by
  have hc : (-(Complex.I / 2) : ℂ) ≠ 0 := by simp
  have hf : (fun θ : ℝ => (1 : ℂ) * Complex.exp (↑(-((1 / 2 : ℝ) * θ)) * Complex.I)) =
      fun θ : ℝ => Complex.exp (-(Complex.I / 2) * (θ : ℂ)) := by
    funext θ; rw [one_mul]; congr 1; push_cast; ring
  rw [hf, integral_exp_mul_complex hc,
    show -(Complex.I / 2) * ((2 * Real.pi : ℝ) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (4 : ℂ) * Complex.I_sq

/-- The half-integer coefficient of the constant `1` has modulus `4`. -/
theorem norm_halfMode_integral :
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℂ) * Complex.exp (↑(-((1 / 2 : ℝ) * θ)) * Complex.I)‖ = 4 := by
  rw [halfMode_integral]; simp

/-- **Bite: `k` must be an integer in PA-C.** At `v = 1` (`M = 1`), `a = 2`, `k = 1/2` the bound would say
`4 ≤ 2π/e`. -/
theorem fourierCoeff_nonInteger_false : ¬ (4 : ℝ) ≤ 2 * Real.pi * 1 * Real.exp (-(2 * |(1 / 2 : ℝ)|)) := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), show (2 : ℝ) * (1 / 2) = 1 by norm_num, mul_one]
  exact not_le.mpr two_pi_exp_neg_one_lt_four

/-! ## The bound must hold off the real axis -/

/-- On the real axis `cos3` is bounded by `7`. -/
theorem cos3_real_axis_bound : ∀ z : ℂ, z.im = 0 → ‖cos3 z‖ ≤ 7 := by
  intro z hz
  have h := norm_cos_le_cosh (3 * z)
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero, hz, mul_zero,
    Real.cosh_zero] at h
  simp only [cos3, norm_mul, Complex.norm_ofNat]
  linarith

/-- **Bite on the bound, off the real axis.** `cos3` is bounded by `7` on the real axis
(`cos3_real_axis_bound`) but is not admissible with `M = 7` on the strip of half-width `1`:
`cos3 (i/2) = 7 cosh (3/2) > 7`. -/
theorem cos3_not_bounded_by_seven : ¬ PeriodicAnalyticOn cos3 1 7 := by
  intro h
  have hz : (((1 / 2 : ℝ) : ℂ) * Complex.I) ∈ openStrip 1 := by
    change |(((1 / 2 : ℝ) : ℂ) * Complex.I).im| < 1
    rw [Complex.im_ofReal_mul, Complex.I_im, mul_one, abs_of_pos (by norm_num)]; norm_num
  have h0 := h.2.2 _ hz
  have hc : (1 : ℝ) < Real.cosh (3 / 2) := Real.one_lt_cosh.mpr (by norm_num)
  rw [cos3, show (3 : ℂ) * (((1 / 2 : ℝ) : ℂ) * Complex.I) = ((3 / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)] at h0
  linarith

/-! ## Data for the planted controls (`docs/replay/plants/2026-11-16-PA-second/`) -/

/-- The node sum of `cos3` at the planted nodes `πj/6`, `j < 6` (values `7, 0, −7, 0, 7, 0`). -/
theorem sum_cos3_half_nodes_six :
    ∑ j ∈ Finset.range 6, cos3 ((Real.pi * (j : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 7 := by
  have h0 : cos3 ((Real.pi * ((0 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ 0 :=
    cos3_of_mul_pi _ 0 (by push_cast; ring)
  have h1 : cos3 ((Real.pi * ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 0 :=
    cos3_of_odd_mul_half_pi _ 0 (by push_cast; ring)
  have h2 : cos3 ((Real.pi * ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ 1 :=
    cos3_of_mul_pi _ 1 (by push_cast; ring)
  have h3 : cos3 ((Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 0 :=
    cos3_of_odd_mul_half_pi _ 1 (by push_cast; ring)
  have h4 : cos3 ((Real.pi * ((4 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 7 * (-1) ^ 2 :=
    cos3_of_mul_pi _ 2 (by push_cast; ring)
  have h5 : cos3 ((Real.pi * ((5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) : ℝ) : ℂ) = 0 :=
    cos3_of_odd_mul_half_pi _ 2 (by push_cast; ring)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
  norm_num

/-- The node sum of `cos3` at the planted nodes `⌊j/4⌋ = 0`, `j < 4` (every value is `cos3 0 = 7`). -/
theorem sum_cos3_floor_nodes_four : ∑ j ∈ Finset.range 4, cos3 (((j / 4 : ℕ) : ℝ) : ℂ) = 28 := by
  have h : ∀ j ∈ Finset.range 4, cos3 (((j / 4 : ℕ) : ℝ) : ℂ) = 7 := by
    intro j hj
    rw [Nat.div_eq_of_lt (Finset.mem_range.mp hj)]
    simp [cos3]
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- `e^{iz}` on the open strip of half-width `1`, `0` elsewhere: holomorphic on that strip (and, trivially, where
it is `0`, for `|Im z| > 1`), discontinuous on the lines `|Im z| = 1`; `2π`-periodic and bounded by `e` on all of `ℂ`. -/
noncomputable def stripExp : ℂ → ℂ := fun z => if |z.im| < 1 then Complex.exp (Complex.I * z) else 0

/-- `stripExp` is holomorphic on the strip of half-width `1`. -/
theorem stripExp_differentiableOn : DifferentiableOn ℂ stripExp (openStrip 1) := by
  have h : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (Complex.I * z)) (openStrip 1) :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (Complex.I * z)).differentiableOn
  refine h.congr fun z hz => ?_
  have hz' : |z.im| < 1 := hz
  simp only [stripExp, hz', ite_true]

/-- `stripExp` is `2π`-periodic on all of `ℂ`. -/
theorem stripExp_periodic (z : ℂ) : stripExp (z + ((2 * Real.pi : ℝ) : ℂ)) = stripExp z := by
  simp only [stripExp, Complex.add_im, Complex.ofReal_im, add_zero]
  rw [show Complex.I * (z + ((2 * Real.pi : ℝ) : ℂ)) = Complex.I * z + 2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `stripExp` is bounded by `e` on all of `ℂ`. -/
theorem norm_stripExp_le (z : ℂ) : ‖stripExp z‖ ≤ Real.exp 1 := by
  simp only [stripExp]
  split_ifs with hz
  · rw [Complex.norm_exp, Real.exp_le_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith [neg_abs_le z.im]
  · rw [norm_zero]; exact (Real.exp_pos 1).le

/-- The coefficient of `stripExp` at `k = 1` is `2π` (on the real axis `stripExp θ = e^{iθ}`), in the shape PA-C
produces at `k = 1`. -/
theorem integral_stripExp_one :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), stripExp (θ : ℂ) * Complex.exp (↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I) =
      2 * Real.pi := by
  have hf : (fun θ : ℝ => stripExp (θ : ℂ) * Complex.exp (↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I)) =
      fun _ : ℝ => (1 : ℂ) := by
    funext θ
    simp only [stripExp, Complex.ofReal_im, abs_zero, zero_lt_one, ite_true]
    rw [← Complex.exp_add, show Complex.I * (θ : ℂ) + ↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I = 0 by push_cast; ring,
      Complex.exp_zero]
  rw [hf, intervalIntegral.integral_const]
  simp

end OscInt.API.PeriodicAnalyticSanity2
