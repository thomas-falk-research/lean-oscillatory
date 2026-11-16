/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.HadamardWalk
import OscInt.Front.GlobalSanity

/-! # Sanity theorems through the batch-HW statement constants (the Hadamard walk on the line)

As for the earlier batches (`docs/lessons.md`, rules 8 and 9): every theorem about a statement of batch HW takes that
statement constant as its only statement hypothesis, applies it to closed data and concludes on the data. No
statement of the batch is proved or used otherwise, and there is no lemma about the walk or about the kernel at a
general time `t`: everything else is an unconditional lemma about data at the times `0`, `1`, `2`. Planted copies and
witnesses: `docs/replay/plants/2026-11-16-HW/`.

Written by an agent of the lead in scratch, with the statement text copied verbatim at the top of its file because
the statement module did not exist yet; the lead removed that copy, added the import and changed two sentences of
this comment (the path of the plant record and this paragraph) when the batch entered the repository, and changed
nothing else.

Data:
* The walk from the point state `(a, b)`, all sites: after one step `((a + b)/√2, 0)` at `−1` and `(0, (a − b)/√2)`
  at `1`; after two steps `((a + b)/2, 0)` at `−2`, `((a − b)/2, (a + b)/2)` at `0`, `(0, −(a − b)/2)` at `2`.
* The dispersion relation: `sin ω(k) = sin k / √2`, `cos ω(k) = √(1 − sin² k / 2)`, `2 cos ω(k) = √(2 (1 + cos² k))`,
  `ω(0) = 0`, `ω(π/2) = π/4`.
* The kernel, all sites: `K(0, x) = 0`; `K(1, x) = δ_{x,0}`; `K(2, −1) = 1/√2`, `K(2, 1) = −1/√2`, `K(2, x) = 0`
  otherwise (the amplitudes at `t = 1, 2` are `1` and `−i√2 sin k`, `kernel_quotient_one`, `kernel_quotient_two`).
* HW-R at `t = 0` and `t = 1`, every site and every `(a, b)`, with the kernel values substituted (`hwR_zero`,
  `hwR_one`) and as tables over the sites (`hwR_zero_table`, `hwR_one_table`).
* HW-K at `t = 1`, `x = 0` (`1 ≤ 7 · 1^{−1/2} + 12 · 1^{−1/3}`, and `1 ≤ 19`), at `t = 2`, `x = −1`
  (`1/√2 ≤ 7 · 2^{−1/2} + 12 · 2^{−1/3}`) and at `t = 8`, every site (literal, and with `12 · 8^{−1/3} = 6`).
* HW-D at `t = 1` (`x = −1`, `x = 1`) and at `t = 2` (`x = 0`), every `(a, b)`.
* HW-L on a point state (the instances of HW-D at `t = 1`), on the two-site state `(1, 0)` at `0`, `(0, 1)` at `2`
  (`t = 1`, `x = 1`, both sites contribute, `ℓ¹` sum `2`), and on the state `(1, 0)` at the site `5` (`t = 1`, `x = 4`).
* Each instance obtained through a statement constant is also checked unconditionally on the data
  (`hwR_zero_check`, `hwR_one_check`, `hwK_check`, `hwD_one_check`, `hwD_two_check`, `hwL_two_site_check`): the
  draft statements are true on these instances.
* Bite: `0^{−1/3} = 0` in Lean; the bound of HW-D is false at `t = 0` (`hwD_zero_time_false`); the conclusion of HW-L
  is false for the constant state `(1, 1)`, whose support is infinite and whose `∑ᶠ` of norms is `0`
  (`hwL_const_false`). The bound of HW-K is true at `t = 0` (`hwK_zero_time_true`, `0 ≤ 0`): in HW-K the hypothesis
  `1 ≤ t` carries no content.
* Data for the planted controls only (last section): `ω` is odd, the integral of an odd function over `[−π, π]`,
  `√(2 (1 + cos² k)) = √2 √(1 + cos² k)`, `∫_{−π}^{π} e^{−i·0·k} dk = 2π`.

What this layer cannot see: every datum has `t ≤ 2` (and `t = 8` unevaluated), where the bounds of HW-K, HW-D and HW-L
are far from the trivial size (`19`, `39 (|a| + |b|)`). The constants `7`, `12`, `39` are tested only against `1`,
`1/√2`, `1/2`, and the exponents `−1/2`, `−1/3` only through the form of the conclusions and `8^{−1/3} = 1/2`; no
datum lies in the regime where a bound beats the trivial one (plant record: HW-K-c, HW-K-d, HW-D-d).
-/

namespace OscInt.API.HadamardWalkSanity

open OscInt.Statements OscInt.API.GlobalSanity

/-- `√2 ≠ 0` as a complex number. -/
theorem sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- `√2 · √2 = 2` as complex numbers. -/
theorem sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `z / √2 / √2 = z / 2`. -/
theorem div_sqrt_two_twice (z : ℂ) : z / ((Real.sqrt 2 : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) = z / 2 := by
  rw [div_div, sqrt_two_mul_self]

/-- `|1 / √2| = 1 / √2` for the complex number `1 / √2`. -/
theorem norm_one_div_sqrt_two : ‖(1 : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)‖ = 1 / Real.sqrt 2 := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-! ## Data: the walk after 0, 1 and 2 steps from a point state -/

/-- **Datum: no step.** The walk at time `0` is the initial state. -/
theorem hadamardWalk_point_zero (a b : ℂ) (x : ℤ) : hadamardWalk (pointState a b) 0 x = pointState a b x := rfl

/-- **Datum: one step from a point state, all sites.** `((a + b)/√2, 0)` at `−1`, `(0, (a − b)/√2)` at `1`, and
`(0, 0)` elsewhere: the first component has moved to the left. -/
theorem hadamardWalk_point_one (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 1 x =
      if x = -1 then ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = 1 then (0, (a - b) / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) := by
  have e : hadamardWalk (pointState a b) 1 x = hadamardStep (pointState a b) x := rfl
  rw [e, hadamardStep, pointState, pointState]
  by_cases h1 : x = -1
  · subst h1; simp
  · by_cases h2 : x = 1
    · subst h2; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]; simp

/-- **Datum: two steps from a point state, all sites.** `((a + b)/2, 0)` at `−2`, `((a − b)/2, (a + b)/2)` at `0`,
`(0, −(a − b)/2)` at `2`, and `(0, 0)` elsewhere. -/
theorem hadamardWalk_point_two (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 2 x =
      if x = -2 then ((a + b) / 2, 0)
      else if x = 0 then ((a - b) / 2, (a + b) / 2)
      else if x = 2 then (0, -((a - b) / 2)) else (0, 0) := by
  have e : hadamardWalk (pointState a b) 2 x = hadamardStep (hadamardWalk (pointState a b) 1) x := rfl
  rw [e, hadamardStep, hadamardWalk_point_one, hadamardWalk_point_one]
  by_cases h1 : x = -2
  · subst h1; norm_num [div_sqrt_two_twice]
  · by_cases h2 : x = 0
    · subst h2; norm_num [div_sqrt_two_twice]
    · by_cases h3 : x = 2
      · subst h3; norm_num [div_sqrt_two_twice, neg_div]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        simp

/-! ## Data: the dispersion relation -/

/-- `(sin k / √2)² = sin² k / 2`. -/
theorem sin_div_sqrt_two_sq (k : ℝ) : (Real.sin k / Real.sqrt 2) ^ 2 = Real.sin k ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]

/-- `sin k / √2` lies in `[−1, 1]`, where `arcsin` inverts `sin`. -/
theorem sin_div_sqrt_two_mem (k : ℝ) : -1 ≤ Real.sin k / Real.sqrt 2 ∧ Real.sin k / Real.sqrt 2 ≤ 1 := by
  have h : (Real.sin k / Real.sqrt 2) ^ 2 ≤ 1 := by
    rw [sin_div_sqrt_two_sq]; linarith [Real.sin_sq_le_one k]
  exact abs_le.mp ((sq_le_one_iff_abs_le_one _).mp h)

/-- **Datum: `sin ω(k) = sin k / √2`.** -/
theorem sin_hadamardDispersion (k : ℝ) : Real.sin (hadamardDispersion k) = Real.sin k / Real.sqrt 2 :=
  Real.sin_arcsin (sin_div_sqrt_two_mem k).1 (sin_div_sqrt_two_mem k).2

/-- **Datum: `cos ω(k) = √(1 − sin² k / 2)`.** -/
theorem cos_hadamardDispersion (k : ℝ) :
    Real.cos (hadamardDispersion k) = Real.sqrt (1 - Real.sin k ^ 2 / 2) := by
  rw [hadamardDispersion, Real.cos_arcsin, sin_div_sqrt_two_sq]

/-- **Datum: `2 cos ω(k) = √(2 (1 + cos² k))`**, the denominator of the kernel. -/
theorem two_cos_hadamardDispersion (k : ℝ) :
    2 * Real.cos (hadamardDispersion k) = Real.sqrt (2 * (1 + Real.cos k ^ 2)) := by
  have h : 2 * (1 + Real.cos k ^ 2) = 2 ^ 2 * (1 - Real.sin k ^ 2 / 2) := by
    linarith [Real.sin_sq_add_cos_sq k]
  rw [cos_hadamardDispersion, h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- **Datum: `ω(0) = 0`.** -/
theorem hadamardDispersion_zero : hadamardDispersion 0 = 0 := by
  simp [hadamardDispersion]

/-- **Datum: `ω(π/2) = π/4`** (the largest value of `ω`). -/
theorem hadamardDispersion_pi_div_two : hadamardDispersion (Real.pi / 2) = Real.pi / 4 := by
  have h : (1 : ℝ) / Real.sqrt 2 = Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, div_eq_div_iff (Real.sqrt_pos.mpr (by norm_num)).ne' (by norm_num),
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hadamardDispersion, Real.sin_pi_div_two, h, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-! ## Data: the kernel at the times 0, 1 and 2 -/

/-- The denominator `√(2 (1 + cos² k))` of the kernel is not zero. -/
theorem kernel_denominator_ne_zero (k : ℝ) : ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'

/-- `e^{−iθ} + e^{iθ} = 2 cos θ`. -/
theorem exp_neg_add_exp (θ : ℝ) :
    Complex.exp (↑(-θ) * Complex.I) + Complex.exp (↑θ * Complex.I) = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- `e^{−iθ} − e^{iθ} = −2i sin θ`. -/
theorem exp_neg_sub_exp (θ : ℝ) :
    Complex.exp (↑(-θ) * Complex.I) - Complex.exp (↑θ * Complex.I) = -((2 * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **Datum: the amplitude of the kernel at `t = 1` is `1`**: `e^{−iω} + e^{iω} = 2 cos ω = √(2 (1 + cos² k))`. -/
theorem kernel_quotient_one (k : ℝ) :
    (Complex.exp (↑(-(((1 : ℕ) : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ 1 * Complex.exp (↑(((1 : ℕ) : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) = 1 := by
  rw [pow_one, neg_one_mul, sub_neg_eq_add, exp_neg_add_exp, Nat.cast_one, one_mul, two_cos_hadamardDispersion]
  exact div_self (kernel_denominator_ne_zero k)

/-- **Datum: the amplitude of the kernel at `t = 2` is `−i√2 sin k = (−e^{ik} + e^{−ik}) / √2`**:
`e^{−2iω} − e^{2iω} = −4i sin ω cos ω` and `sin ω = sin k / √2`. -/
theorem kernel_quotient_two (k : ℝ) :
    (Complex.exp (↑(-(((2 : ℕ) : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ 2 * Complex.exp (↑(((2 : ℕ) : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) =
      -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) * Complex.exp (↑(((1 : ℤ) : ℝ) * k) * Complex.I) +
        1 / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (↑(((-1 : ℤ) : ℝ) * k) * Complex.I) := by
  have hr : 2 * (Real.sin k / Real.sqrt 2) = Real.sqrt 2 * Real.sin k := by
    rw [mul_div_assoc', div_eq_iff (Real.sqrt_pos.mpr (by norm_num)).ne']
    linear_combination (-Real.sin k) * Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h1 : 2 * Real.sin (((2 : ℕ) : ℝ) * hadamardDispersion k) =
      Real.sqrt 2 * Real.sin k * Real.sqrt (2 * (1 + Real.cos k ^ 2)) := by
    rw [Nat.cast_ofNat, Real.sin_two_mul, sin_hadamardDispersion, ← two_cos_hadamardDispersion]
    linear_combination (2 * Real.cos (hadamardDispersion k)) * hr
  rw [neg_one_sq, one_mul, exp_neg_sub_exp, h1, div_eq_iff (kernel_denominator_ne_zero k), Int.cast_neg,
    Int.cast_one, one_mul, neg_one_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  field_simp
  linear_combination (-Complex.sin (k : ℂ) * Complex.I *
    ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ)) * sqrt_two_mul_self

/-- **Datum: the unit Fourier coefficients.** `(2π)^{−1} ∫_{−π}^{π} e^{ink} dk` is `1` for `n = 0` and `0` for every
other integer `n`. -/
theorem fourier_unit (n : ℤ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, Complex.exp (↑((n : ℝ) * k) * Complex.I) =
      if n = 0 then 1 else 0 := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, intervalIntegral.integral_const]
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, Complex.real_smul, mul_one]
    exact inv_mul_cancel₀ hpi
  · rw [integral_exp_int_mul n hn, mul_zero]

/-- The Fourier coefficients of a sum of two exponentials. -/
theorem fourier_pair (c d : ℂ) (m n : ℤ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
        (c * Complex.exp (↑((m : ℝ) * k) * Complex.I) + d * Complex.exp (↑((n : ℝ) * k) * Complex.I)) =
      c * (if m = 0 then 1 else 0) + d * (if n = 0 then 1 else 0) := by
  have hc : ∀ j : ℤ, IntervalIntegrable (fun k : ℝ => Complex.exp (↑((j : ℝ) * k) * Complex.I))
      MeasureTheory.volume (-Real.pi) Real.pi := fun j =>
    (by fun_prop : Continuous fun k : ℝ => Complex.exp (↑((j : ℝ) * k) * Complex.I)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((hc m).const_mul c) ((hc n).const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← fourier_unit m, ← fourier_unit n]
  ring

/-- `e^{imk} e^{−ixk} = e^{i(m − x)k}` for integers `m`, `x`. -/
theorem exp_mul_exp_site (m x : ℤ) (k : ℝ) :
    Complex.exp (↑((m : ℝ) * k) * Complex.I) * Complex.exp (↑(-((x : ℝ) * k)) * Complex.I) =
      Complex.exp (↑(((m - x : ℤ) : ℝ) * k) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- **Datum: the kernel at `t = 0` is `0`** at every site (the two exponentials cancel). -/
theorem hadamardKernel_zero (x : ℤ) : hadamardKernel 0 x = 0 := by
  simp [hadamardKernel]

/-- **Datum: the kernel at `t = 1` is the unit datum `δ_{x,0}`** (the integrand is `e^{−ixk}`). -/
theorem hadamardKernel_one (x : ℤ) : hadamardKernel 1 x = if x = 0 then 1 else 0 := by
  have h := fourier_unit (-x)
  have e : ∀ k : ℝ, ((-x : ℤ) : ℝ) * k = -((x : ℝ) * k) := fun k => by push_cast; ring
  simp only [e, neg_eq_zero] at h
  rw [hadamardKernel]
  simp only [kernel_quotient_one, one_mul]
  exact h

/-- **Datum: the kernel at `t = 2`** is `1/√2` at `x = −1`, `−1/√2` at `x = 1` and `0` at every other site (the
integrand is `−i√2 sin k · e^{−ixk}`). -/
theorem hadamardKernel_two (x : ℤ) :
    hadamardKernel 2 x =
      if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0 := by
  have h := fourier_pair (-(1 / ((Real.sqrt 2 : ℝ) : ℂ))) (1 / ((Real.sqrt 2 : ℝ) : ℂ)) (1 - x) (-1 - x)
  rw [hadamardKernel]
  simp only [kernel_quotient_two, add_mul, mul_assoc, exp_mul_exp_site]
  rw [h]
  by_cases h1 : x = -1
  · subst h1; norm_num
  · by_cases h2 : x = 1
    · subst h2; norm_num
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]; simp

/-! ## HW-R through the statement constant, at `t = 0` and `t = 1` -/

/-- `z / √2 · (√2)⁻¹ = z / 2`. -/
theorem div_sqrt_two_mul_inv (z : ℂ) : z / ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = z / 2 := by
  rw [← div_eq_mul_inv, div_sqrt_two_twice]

/-- **Datum: the right side of HW-R at `t = 0`**, with the kernel values `K(1, ·) = δ` and `K(0, ·) = 0`
substituted, as a table over the sites. No walk and no kernel is mentioned. -/
theorem kernelSide_zero (a b : ℂ) (x : ℤ) :
    ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = 0 then 1 else 0)) =
      if x = -1 then ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = 1 then (0, (a - b) / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) := by
  by_cases h1 : x = -1
  · subst h1; norm_num
  · by_cases h2 : x = 1
    · subst h2; norm_num
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega)]; simp

/-- **Datum: the right side of HW-R at `t = 1`**, with the kernel values `K(2, ∓1) = ±1/√2` and `K(1, ·) = δ`
substituted, as a table over the sites. No walk and no kernel is mentioned. -/
theorem kernelSide_one (a b : ℂ) (x : ℤ) :
    ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x + 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x + 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + a * (if x = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x - 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x - 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + b * (if x = 0 then 1 else 0)) =
      if x = -2 then ((a + b) / 2, 0)
      else if x = 0 then ((a - b) / 2, (a + b) / 2)
      else if x = 2 then (0, -((a - b) / 2)) else (0, 0) := by
  have hm := div_sqrt_two_mul_inv
  by_cases h1 : x = -2
  · subst h1; norm_num [hm]
  · by_cases h2 : x = 0
    · subst h2
      norm_num [hm]
      constructor <;> ring
    · by_cases h3 : x = 2
      · subst h3; norm_num [hm]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2]
        simp

/-- **HW-R through the statement constant** at `t = 0`, every site: one step from the point state `(a, b)` is
`((a + b)/√2 · δ_{x+1,0}, (a − b)/√2 · δ_{x−1,0})`. Pins which component moves to the left, the coin signs and the
normalisation of `K(1, ·)`. -/
theorem hwR_zero (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 1 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = 0 then 1 else 0)) := by
  have h1 := h a b 0 x
  rw [zero_add, hadamardKernel_one, hadamardKernel_one, hadamardKernel_zero, mul_zero, mul_zero, add_zero,
    add_zero] at h1
  exact h1

/-- **HW-R through the statement constant** at `t = 0`, as a table: `((a + b)/√2, 0)` at `−1`, `(0, (a − b)/√2)` at
`1`, `(0, 0)` elsewhere. -/
theorem hwR_zero_table (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 1 x =
      if x = -1 then ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = 1 then (0, (a - b) / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) :=
  (hwR_zero h a b x).trans (kernelSide_zero a b x)

/-- **Check (unconditional)**: the instance of HW-R in `hwR_zero` is true on the data (`hadamardWalk_point_one`). -/
theorem hwR_zero_check (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 1 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = 0 then 1 else 0)) :=
  (hadamardWalk_point_one a b x).trans (kernelSide_zero a b x).symm

/-- **HW-R through the statement constant** at `t = 1`, every site: two steps from the point state `(a, b)`, with
the kernel values `K(2, ∓1) = ±1/√2`, `K(1, ·) = δ` substituted. Pins the sign of `x` in the kernel (through
`K(2, ±1)`) and the terms `a K(t, x)`, `b K(t, x)`. -/
theorem hwR_one (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 2 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x + 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x + 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + a * (if x = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x - 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x - 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + b * (if x = 0 then 1 else 0)) := by
  have h1 := h a b 1 x
  rw [one_add_one_eq_two, hadamardKernel_two, hadamardKernel_two, hadamardKernel_one] at h1
  exact h1

/-- **HW-R through the statement constant** at `t = 1`, as a table: `((a + b)/2, 0)` at `−2`,
`((a − b)/2, (a + b)/2)` at `0`, `(0, −(a − b)/2)` at `2`, `(0, 0)` elsewhere. -/
theorem hwR_one_table (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 2 x =
      if x = -2 then ((a + b) / 2, 0)
      else if x = 0 then ((a - b) / 2, (a + b) / 2)
      else if x = 2 then (0, -((a - b) / 2)) else (0, 0) :=
  (hwR_one h a b x).trans (kernelSide_one a b x)

/-- **Check (unconditional)**: the instance of HW-R in `hwR_one` is true on the data (`hadamardWalk_point_two`). -/
theorem hwR_one_check (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 2 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x + 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x + 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + a * (if x = 0 then 1 else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (if x - 1 = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x - 1 = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0) + b * (if x = 0 then 1 else 0)) :=
  (hadamardWalk_point_two a b x).trans (kernelSide_one a b x).symm

/-! ## HW-K through the statement constant -/

/-- **HW-K through the statement constant** at `t = 1`, `x = 0`, literal form: `|K(1, 0)| = 1`. -/
theorem hwK_one (h : HadamardKernelBoundStatement) :
    (1 : ℝ) ≤ 7 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h 1 0 le_rfl
  rw [hadamardKernel_one, ite_eq_left rfl, norm_one] at h1
  exact h1

/-- **HW-K through the statement constant** at `t = 1`, `x = 0`, simplified: `1 ≤ 19`. -/
theorem hwK_one_simplified (h : HadamardKernelBoundStatement) : (1 : ℝ) ≤ 19 := by
  have h1 := hwK_one h
  rw [Nat.cast_one, Real.one_rpow, Real.one_rpow] at h1
  linarith

/-- **HW-K through the statement constant** at `t = 2`, `x = −1`, literal form: `|K(2, −1)| = 1/√2`. -/
theorem hwK_two (h : HadamardKernelBoundStatement) :
    1 / Real.sqrt 2 ≤ 7 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h 2 (-1) (by norm_num)
  rw [hadamardKernel_two, ite_eq_left rfl, norm_one_div_sqrt_two] at h1
  exact h1

/-- **HW-K through the statement constant** at `t = 8` and an arbitrary site, literal form (the kernel is not
evaluated). -/
theorem hwK_eight (h : HadamardKernelBoundStatement) (x : ℤ) :
    ‖hadamardKernel 8 x‖ ≤ 7 * ((8 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((8 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) :=
  h 8 x (by norm_num)

/-- **Datum: `8^{−1/3} = 1/2`** with the exponent written as in the statements, `-(1 : ℝ) / 3`. -/
theorem eight_rpow_neg_third : ((8 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) = 1 / 2 := by
  have h8 : ((8 : ℕ) : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
  rw [h8, ← Real.rpow_mul (by norm_num), show ((3 : ℕ) : ℝ) * (-(1 : ℝ) / 3) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- **HW-K through the statement constant** at `t = 8`, with `12 · 8^{−1/3} = 6`: the second exponent is `−1/3`. -/
theorem hwK_eight_simplified (h : HadamardKernelBoundStatement) (x : ℤ) :
    ‖hadamardKernel 8 x‖ ≤ 7 * ((8 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 6 := by
  have h1 := hwK_eight h x
  rw [eight_rpow_neg_third] at h1
  linarith

/-- **Check (unconditional)**: the instances of HW-K in `hwK_one` and `hwK_two` are true: `1 ≤ 19` and
`1/√2 ≤ 7/√2 + 12 · 2^{−1/3}`. -/
theorem hwK_check :
    (1 : ℝ) ≤ 7 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      1 / Real.sqrt 2 ≤ 7 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  refine ⟨by norm_num, ?_⟩
  have h1 : ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
    rw [Nat.cast_ofNat, neg_div, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
  have h2 : (0 : ℝ) ≤ 12 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by positivity
  have h3 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  rw [h1]
  linarith

/-! ## HW-D through the statement constant -/

/-- **HW-D through the statement constant** at `t = 1`: the first component at `x = −1` and the second component at
`x = 1`. -/
theorem hwD_one (h : HadamardDecayStatement) (a b : ℂ) :
    ‖(a + b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a - b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := (h a b 1 (-1) le_rfl).1
  have h2 := (h a b 1 1 le_rfl).2
  rw [hadamardWalk_point_one, ite_eq_left rfl] at h1
  rw [hadamardWalk_point_one, ite_eq_right (by norm_num), ite_eq_left rfl] at h2
  exact ⟨h1, h2⟩

/-- **HW-D through the statement constant** at `t = 2`, `x = 0`: both components. -/
theorem hwD_two (h : HadamardDecayStatement) (a b : ℂ) :
    ‖(a - b) / 2‖ ≤ 39 * (‖a‖ + ‖b‖) * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a + b) / 2‖ ≤ 39 * (‖a‖ + ‖b‖) * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h a b 2 0 (by norm_num)
  rw [hadamardWalk_point_two, ite_eq_right (by norm_num), ite_eq_left rfl] at h1
  exact h1

/-- `1 ≤ √2`. -/
theorem one_le_sqrt_two : 1 ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt' one_pos]; norm_num

/-- `|z / √2| ≤ |z|`. -/
theorem norm_div_sqrt_two_le (z : ℂ) : ‖z / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  exact div_le_self (norm_nonneg z) one_le_sqrt_two

/-- **Check (unconditional)**: the instances of HW-D in `hwD_one` are true (`|a ± b| ≤ |a| + |b|`, `1 ≤ √2`). -/
theorem hwD_one_check (a b : ℂ) :
    ‖(a + b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a - b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := (norm_div_sqrt_two_le (a + b)).trans (norm_add_le a b)
  have h2 := (norm_div_sqrt_two_le (a - b)).trans (norm_sub_le a b)
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  rw [Nat.cast_one, Real.one_rpow]
  constructor <;> linarith

/-- **Check (unconditional)**: the instances of HW-D in `hwD_two` are true (`2^{−1/3} ≥ 1/2`). -/
theorem hwD_two_check (a b : ℂ) :
    ‖(a - b) / 2‖ ≤ 39 * (‖a‖ + ‖b‖) * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a + b) / 2‖ ≤ 39 * (‖a‖ + ‖b‖) * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hp : (1 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (-1 : ℝ) ≤ -(1 : ℝ) / 3 by norm_num)
    rw [Real.rpow_neg_one] at h
    rw [Nat.cast_ofNat]
    linarith
  have h1 := norm_sub_le a b
  have h2 := norm_add_le a b
  have hab : 0 ≤ ‖a‖ + ‖b‖ := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hm := mul_le_mul_of_nonneg_left hp hab
  rw [norm_div, norm_div, Complex.norm_ofNat]
  constructor <;> linarith

/-! ## HW-L through the statement constant -/

/-- The support of a point state is finite. -/
theorem pointState_finite (a b : ℂ) : {y : ℤ | pointState a b y ≠ (0, 0)}.Finite := by
  refine (Set.finite_singleton (0 : ℤ)).subset fun y hy => ?_
  by_contra hne
  exact hy (by rw [pointState, ite_eq_right (show ¬ y = 0 from hne)])

/-- **Datum: the `ℓ¹` sum of a point state** is `|a| + |b|`. -/
theorem pointState_finsum (a b : ℂ) :
    ∑ᶠ y : ℤ, (‖(pointState a b y).1‖ + ‖(pointState a b y).2‖) = ‖a‖ + ‖b‖ := by
  rw [finsum_eq_single _ (0 : ℤ) fun y hy => by simp [pointState, hy]]
  simp [pointState]

/-- **HW-L through the statement constant** on a point state at `t = 1`: the instances of HW-D in `hwD_one` (the
`ℓ¹` sum is `|a| + |b|`). -/
theorem hwL_point (h : HadamardDispersiveStatement) (a b : ℂ) :
    ‖(a + b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a - b) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := (h (pointState a b) 1 (-1) (pointState_finite a b) le_rfl).1
  have h2 := (h (pointState a b) 1 1 (pointState_finite a b) le_rfl).2
  rw [hadamardWalk_point_one, ite_eq_left rfl, pointState_finsum] at h1
  rw [hadamardWalk_point_one, ite_eq_right (by norm_num), ite_eq_left rfl, pointState_finsum] at h2
  exact ⟨h1, h2⟩

/-- Datum for HW-L: the two-site state `(1, 0)` at the site `0`, `(0, 1)` at the site `2`, `(0, 0)` elsewhere. Both
sites contribute to the walk at `t = 1`, `x = 1`. -/
def twoSiteState (y : ℤ) : ℂ × ℂ :=
  if y = 0 then (1, 0) else if y = 2 then (0, 1) else (0, 0)

/-- The support of the two-site state is finite. -/
theorem twoSiteState_finite : {y : ℤ | twoSiteState y ≠ (0, 0)}.Finite := by
  refine (Set.toFinite ({0, 2} : Set ℤ)).subset fun y hy => ?_
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  exact hy (by rw [twoSiteState, ite_eq_right hne.1, ite_eq_right hne.2])

/-- **Datum: the `ℓ¹` sum of the two-site state is `2`.** -/
theorem twoSiteState_finsum : ∑ᶠ y : ℤ, (‖(twoSiteState y).1‖ + ‖(twoSiteState y).2‖) = 2 := by
  have hs : Function.support (fun y : ℤ => ‖(twoSiteState y).1‖ + ‖(twoSiteState y).2‖) ⊆
      (({0, 2} : Finset ℤ) : Set ℤ) := by
    intro y hy
    by_contra hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hy (by simp [twoSiteState, hne.1, hne.2])
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (by norm_num)]
  norm_num [twoSiteState]

/-- **Datum: one step from the two-site state at `x = 1`** is `(1/√2, 1/√2)`: the first component comes from the
site `2`, the second from the site `0`. -/
theorem twoSiteState_walk_one :
    hadamardWalk twoSiteState 1 1 = (1 / ((Real.sqrt 2 : ℝ) : ℂ), 1 / ((Real.sqrt 2 : ℝ) : ℂ)) := by
  have e : hadamardWalk twoSiteState 1 1 = hadamardStep twoSiteState 1 := rfl
  rw [e, hadamardStep]
  norm_num [twoSiteState]

/-- **HW-L through the statement constant** on the two-site state at `t = 1`, `x = 1`: both components are `1/√2`
and the `ℓ¹` sum is `2`. -/
theorem hwL_two_site (h : HadamardDispersiveStatement) :
    1 / Real.sqrt 2 ≤ 39 * 2 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      1 / Real.sqrt 2 ≤ 39 * 2 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h twoSiteState 1 1 twoSiteState_finite le_rfl
  rw [twoSiteState_walk_one, twoSiteState_finsum, norm_one_div_sqrt_two] at h1
  exact h1

/-- **Check (unconditional)**: the instance of HW-L in `hwL_two_site` is true (`1/√2 ≤ 1 ≤ 78`). -/
theorem hwL_two_site_check : 1 / Real.sqrt 2 ≤ 39 * 2 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]; exact one_le_sqrt_two
  rw [Nat.cast_one, Real.one_rpow]
  linarith

/-- Datum for HW-L away from the origin: the state `(1, 0)` at the site `5`, `(0, 0)` elsewhere. -/
def fiveState (y : ℤ) : ℂ × ℂ :=
  if y = 5 then (1, 0) else (0, 0)

/-- The support of `fiveState` is finite. -/
theorem fiveState_finite : {y : ℤ | fiveState y ≠ (0, 0)}.Finite := by
  refine (Set.finite_singleton (5 : ℤ)).subset fun y hy => ?_
  by_contra hne
  exact hy (by rw [fiveState, ite_eq_right (show ¬ y = 5 from hne)])

/-- **Datum: the `ℓ¹` sum of `fiveState` is `1`.** -/
theorem fiveState_finsum : ∑ᶠ y : ℤ, (‖(fiveState y).1‖ + ‖(fiveState y).2‖) = 1 := by
  rw [finsum_eq_single _ (5 : ℤ) fun y hy => by simp [fiveState, hy]]
  simp [fiveState]

/-- **Datum: one step from `fiveState` at `x = 4`** is `(1/√2, 0)`. -/
theorem fiveState_walk_one : hadamardWalk fiveState 1 4 = (1 / ((Real.sqrt 2 : ℝ) : ℂ), 0) := by
  have e : hadamardWalk fiveState 1 4 = hadamardStep fiveState 4 := rfl
  rw [e, hadamardStep]
  norm_num [fiveState]

/-- **HW-L through the statement constant** on `fiveState` at `t = 1`, `x = 4`, first component: the sum runs over
all sites, not over the origin only. -/
theorem hwL_five (h : HadamardDispersiveStatement) :
    1 / Real.sqrt 2 ≤ 39 * 1 * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := (h fiveState 1 4 fiveState_finite le_rfl).1
  rw [fiveState_walk_one, fiveState_finsum, norm_one_div_sqrt_two] at h1
  exact h1

/-! ## Bite data: the time `0` and a state of infinite support -/

/-- **Datum: `0^{−1/3} = 0` in Lean** (`Real.rpow`), with the exponent written as in the statements. -/
theorem real_zero_rpow_neg_third : (0 : ℝ) ^ (-(1 : ℝ) / 3) = 0 :=
  Real.zero_rpow (by norm_num)

/-- **Datum: `0^{−1/3} = 0` in Lean**, with the base and the exponent written as in the statements at `t = 0`. -/
theorem zero_rpow_neg_third : ((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) = 0 := by
  rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]

/-- **Datum: `0^{−1/2} = 0` in Lean.** -/
theorem zero_rpow_neg_half : ((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) = 0 := by
  rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]

/-- **Bite: the bound of HW-D is false at `t = 0`** (point state `(1, 0)`, site `0`: `1 ≤ 39 · 1 · 0`). The
hypothesis `1 ≤ t` carries content. -/
theorem hwD_zero_time_false :
    ¬ ‖(hadamardWalk (pointState 1 0) 0 0).1‖ ≤ 39 * (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) * ((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [hadamardWalk_point_zero, zero_rpow_neg_third]
  norm_num [pointState]

/-- **Datum: the bound of HW-K holds at `t = 0`** (`0 ≤ 0`): there the hypothesis `1 ≤ t` carries no content, since
`K(0, ·) = 0`. -/
theorem hwK_zero_time_true (x : ℤ) :
    ‖hadamardKernel 0 x‖ ≤ 7 * ((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [hadamardKernel_zero, zero_rpow_neg_third, zero_rpow_neg_half]
  norm_num

/-- Datum for the bite of HW-L: the constant state `(1, 1)` at every site. -/
def constState (_ : ℤ) : ℂ × ℂ := (1, 1)

/-- The support of the constant state is infinite. -/
theorem constState_infinite : ¬ {y : ℤ | constState y ≠ (0, 0)}.Finite := by
  have h : {y : ℤ | constState y ≠ (0, 0)} = Set.univ := by
    ext y; simp [constState]
  rw [h]
  exact Set.infinite_univ

/-- **Datum: the `∑ᶠ` of the norms of the constant state is `0`** (infinite support). -/
theorem constState_finsum : ∑ᶠ y : ℤ, (‖(constState y).1‖ + ‖(constState y).2‖) = 0 := by
  refine finsum_of_infinite_support ?_
  have h : Function.support (fun y : ℤ => ‖(constState y).1‖ + ‖(constState y).2‖) = Set.univ := by
    ext y; simp [constState]
  rw [h]
  exact Set.infinite_univ

/-- **Datum: one step from the constant state** is `(√2, 0)` at every site. -/
theorem constState_walk_one (x : ℤ) : hadamardWalk constState 1 x = (((Real.sqrt 2 : ℝ) : ℂ), 0) := by
  have e : hadamardWalk constState 1 x = hadamardStep constState x := rfl
  have h2 : ((1 : ℂ) + 1) / ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [div_eq_iff sqrt_two_ne_zero, sqrt_two_mul_self]; norm_num
  rw [e, hadamardStep]
  simp only [constState]
  rw [h2, sub_self, zero_div]

/-- **Bite: the conclusion of HW-L is false for the constant state** at `t = 1` (`√2 ≤ 39 · 0 · 1`). The hypothesis
of finite support carries content. -/
theorem hwL_const_false (x : ℤ) :
    ¬ ‖(hadamardWalk constState 1 x).1‖ ≤
      39 * (∑ᶠ y : ℤ, (‖(constState y).1‖ + ‖(constState y).2‖)) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [constState_walk_one, constState_finsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  norm_num

/-! ## Data for the planted controls only -/

/-- **Datum: `ω` is odd**, `ω(−k) = −ω(k)`. -/
theorem hadamardDispersion_neg (k : ℝ) : hadamardDispersion (-k) = -hadamardDispersion k := by
  rw [hadamardDispersion, hadamardDispersion, Real.sin_neg, neg_div, Real.arcsin_neg]

/-- The integral over `[−π, π]` of an odd function is `0`. -/
theorem integral_odd (f : ℝ → ℂ) (hf : ∀ k : ℝ, f (-k) = -f k) : ∫ k in (-Real.pi)..Real.pi, f k = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi) f
  simp only [hf, neg_neg, intervalIntegral.integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- `√(2 (1 + cos² k)) = √2 · √(1 + cos² k)`. -/
theorem sqrt_two_mul_amplitude (k : ℝ) :
    Real.sqrt (2 * (1 + Real.cos k ^ 2)) = Real.sqrt 2 * Real.sqrt (1 + Real.cos k ^ 2) :=
  Real.sqrt_mul (by norm_num) _

/-- `(√2)⁻¹ · (√2)⁻¹ = 1/2` as complex numbers. -/
theorem inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, sqrt_two_mul_self]; norm_num

/-- **Datum: the integral of the integrand of `K(1, 0)`**, `∫_{−π}^{π} e^{−i·0·k} dk = 2π`. -/
theorem integral_site_zero :
    ∫ k in (-Real.pi)..Real.pi, Complex.exp (↑(-(((0 : ℤ) : ℝ) * k)) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) := by
  simp only [Int.cast_zero, zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero,
    intervalIntegral.integral_const]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, Complex.real_smul, mul_one]

end OscInt.API.HadamardWalkSanity
