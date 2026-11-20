/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.HadamardWalkSanity

/-! # Second sanity layer for the batch-HW statement constants

Answers the blind pre-proof review of batch HW: mutations of the frozen statements of
`OscInt/Statements/HadamardWalk.lean` that the first layer (`OscInt/Front/HadamardWalkSanity.lean`) does not detect,
because all its exact data are at the times `t ≤ 2`. Same discipline (`docs/lessons.md`, rules 8 and 9): a theorem
about a frozen statement takes that statement constant as its only statement hypothesis and concludes on closed
data; everything else is an unconditional lemma on data at the fixed times `1`, `2`, `3` and `5`. No statement of
the batch is proved or used otherwise, and there is no lemma about the walk or about the kernel at a general time
`t` (no recursion in `t`, no Fourier representation of the walk, no linearity): each kernel value is one integral of
an explicit trigonometric polynomial, each walk value a finite computation with the step.
Planted copies and witnesses of this layer: `docs/replay/plants/2026-11-16-HW-second/`.

Written in scratch by an agent of the lead; lead, agent and reviewers are AI agents of one model family.

What the first layer could not see, and the datum added here:
* **The walk after three steps from a point state, all sites** (`hadamardWalk_point_three`):
  `((a + b)/2/√2, 0)` at `−3`, `(a/√2, (a + b)/2/√2)` at `−1`, `(−((a − b)/2)/√2, −b/√2)` at `1`,
  `(0, (a − b)/2/√2)` at `3`, `(0, 0)` elsewhere.
* **The kernel at `t = 3`, all sites** (`hadamardKernel_three`): `K(3, ±2) = 1/2`, `0` elsewhere; the amplitude is
  `cos 2k` (`kernel_quotient_three`: `cos 3ω / cos ω = 4 cos² ω − 3` and `cos² ω = 1 − sin² k / 2`).
* **HW-R at `t = 2`**, every site and every `(a, b)`, with the kernel values substituted (`hwR_two`,
  `hwR_two_table`), checked unconditionally against the walk (`hwR_two_check`). At `x = ±1` the summands
  `a K(2, x)`, `b K(2, x)` are `∓a/√2`, `∓b/√2`, odd in `x`: the first layer had them only at `t ≤ 1`, where
  `K(0, ·) = 0` and `K(1, ·) = δ` are even, so `K(t, x) ↦ K(t, −x)` in these summands was invisible.
* **HW-D at `t = 3`, `x = −1`** (`hwD_three`, `hwD_three_unit`: `1/√2 ≤ 39 · (1 + 0) · 3^{−1/3}`), checked
  unconditionally (`hwD_three_check`), with the bite `¬ (1/√2 ≤ 1 · 3^{−1/3})` (`hwD_constant_one_bite`,
  `hwD_constant_one_false`): the constant `1` in the place of `39` is false. The first layer tested `39` at
  `t = 1` and `t = 2` only (against `1/√2` and `1/2`), where the constant `1` holds as well.
* **HW-L at `t ≠ 1`**: on a point state at `t = 3`, `x = −1` (`hwL_point_three`), and on the two-site state of the
  first layer at `t = 2`, `x = 0`, where the walk is `(1, 1/2)` (`twoSiteState_walk_two`, `hwL_two_site_two`,
  checked by `hwL_two_site_two_check`); the bite of the constant on the walk (`hwL_constant_one_false`).
* **The support hypothesis of HW-L, with a state whose first component vanishes**: the constant state `(0, 1)`
  (`constSecondState`) has infinite support, `∑ᶠ` of norms `0`, an empty set of sites with a nonzero first
  component, and one step gives `(1/√2, −1/√2)` at every site; the conclusion of HW-L is false for it
  (`hwL_constSecond_false`).
* **The kernel at `t = 5`, all sites** (`hadamardKernel_five`): `1/4, 1/2, −1/2, 1/2, 1/4` at `−4, −2, 0, 2, 4`
  (the amplitude is `−1/2 + cos 2k + cos 4k / 2`, `kernel_quotient_five`), **HW-K at `t = 5`, `x = 0`**
  (`hwK_five`, checked by `hwK_five_check`) and the bite `¬ (1/2 ≤ 1 · 5^{−1/2} + 0 · 5^{−1/3})`
  (`hwK_constants_one_zero_bite`): the constants `(1, 0)` in the place of `(7, 12)` are false. At `t = 1, 2, 3` the
  bound `t^{−1/2}` holds (`1 ≤ 1`, `1/√2 ≤ 1/√2`, `1/2 ≤ 1/√3`).

What this layer still cannot see (verdicts in the plant record): every datum has `t ≤ 5`, where the bounds with
the constants `7`, `12`, `39` are far above the size of the data, so no mutation of an exponent is refuted
(`39 · t^{e}` is below the largest datum `1/√2` at `t = 3` only for `e < −3.65`); `7 t^{−1/2} · 12 t^{−1/3}` in
the place of the sum in HW-K (first false at `t = 7749` in floating point) and `t^{−1/3}` alone in HW-K (no
violation known for `t ≤ 9000`) have no witness.
-/

namespace OscInt.API.HadamardWalkSanity2

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.HadamardWalkSanity

/-! ## Data: the walk after 3 steps from a point state -/

/-- **Datum: three steps from a point state, all sites.** `((a + b)/2/√2, 0)` at `−3`, `(a/√2, (a + b)/2/√2)` at
`−1`, `(−((a − b)/2)/√2, −b/√2)` at `1`, `(0, (a − b)/2/√2)` at `3`, and `(0, 0)` elsewhere. -/
theorem hadamardWalk_point_three (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 3 x =
      if x = -3 then ((a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = -1 then (a / ((Real.sqrt 2 : ℝ) : ℂ), (a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 1 then (-((a - b) / 2) / ((Real.sqrt 2 : ℝ) : ℂ), -b / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 3 then (0, (a - b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) := by
  have e : hadamardWalk (pointState a b) 3 x = hadamardStep (hadamardWalk (pointState a b) 2) x := rfl
  rw [e, hadamardStep, hadamardWalk_point_two, hadamardWalk_point_two]
  by_cases h1 : x = -3
  · subst h1; norm_num
  · by_cases h2 : x = -1
    · subst h2; norm_num; ring
    · by_cases h3 : x = 1
      · subst h3; norm_num; ring
      · by_cases h4 : x = 3
        · subst h4; norm_num
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
            ite_eq_right h4]
          simp

/-! ## Data: the kernel at the time 3 -/

/-- **Datum: the amplitude of the kernel at `t = 3` is `cos 2k = (e^{2ik} + e^{−2ik}) / 2`**:
`e^{−3iω} + e^{3iω} = 2 cos 3ω = (4 cos² ω − 3) · 2 cos ω` and `cos² ω = 1 − sin² k / 2`. -/
theorem kernel_quotient_three (k : ℝ) :
    (Complex.exp (↑(-(((3 : ℕ) : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ 3 * Complex.exp (↑(((3 : ℕ) : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) =
      1 / 2 * Complex.exp (↑(((2 : ℤ) : ℝ) * k) * Complex.I) +
        1 / 2 * Complex.exp (↑(((-2 : ℤ) : ℝ) * k) * Complex.I) := by
  have hs : Real.cos (hadamardDispersion k) ^ 2 = 1 - Real.sin k ^ 2 / 2 := by
    rw [Real.cos_sq', sin_hadamardDispersion, sin_div_sqrt_two_sq]
  have h1 : 2 * Real.cos (((3 : ℕ) : ℝ) * hadamardDispersion k) =
      Real.cos (2 * k) * Real.sqrt (2 * (1 + Real.cos k ^ 2)) := by
    rw [Nat.cast_ofNat, Real.cos_three_mul, ← two_cos_hadamardDispersion, Real.cos_two_mul]
    linear_combination (8 * Real.cos (hadamardDispersion k)) * hs +
      (-4 * Real.cos (hadamardDispersion k)) * Real.sin_sq_add_cos_sq k
  have h2 := exp_neg_add_exp (2 * k)
  rw [show (-1 : ℂ) ^ 3 = -1 by norm_num, neg_one_mul, sub_neg_eq_add, exp_neg_add_exp, h1, Complex.ofReal_mul,
    mul_div_assoc, div_self (kernel_denominator_ne_zero k), mul_one, Int.cast_neg, Int.cast_ofNat, neg_mul]
  push_cast at h2 ⊢
  linear_combination (-1 / 2 : ℂ) * h2

/-- **Datum: the kernel at `t = 3`** is `1/2` at `x = −2` and at `x = 2`, and `0` at every other site (the integrand
is `cos 2k · e^{−ixk}`). -/
theorem hadamardKernel_three (x : ℤ) :
    hadamardKernel 3 x = if x = -2 then 1 / 2 else if x = 2 then 1 / 2 else 0 := by
  have h := fourier_pair (1 / 2) (1 / 2) (2 - x) (-2 - x)
  rw [hadamardKernel]
  simp only [kernel_quotient_three, add_mul, mul_assoc, exp_mul_exp_site]
  rw [h]
  by_cases h1 : x = -2
  · subst h1; norm_num
  · by_cases h2 : x = 2
    · subst h2; norm_num
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]; simp

/-! ## HW-R through the statement constant, at `t = 2` -/

/-- **Datum: the right side of HW-R at `t = 2`**, with the kernel values `K(3, ±2) = 1/2` and `K(2, ∓1) = ±1/√2`
substituted, as a table over the sites. No walk and no kernel is mentioned. -/
theorem kernelSide_two (a b : ℂ) (x : ℤ) :
    ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = -2 then 1 / 2 else if x + 1 = 2 then 1 / 2 else 0) +
          a * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = -2 then 1 / 2 else if x - 1 = 2 then 1 / 2 else 0) +
          b * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0)) =
      if x = -3 then ((a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = -1 then (a / ((Real.sqrt 2 : ℝ) : ℂ), (a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 1 then (-((a - b) / 2) / ((Real.sqrt 2 : ℝ) : ℂ), -b / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 3 then (0, (a - b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) := by
  by_cases h1 : x = -3
  · subst h1; norm_num; ring
  · by_cases h2 : x = -1
    · subst h2; norm_num; constructor <;> ring
    · by_cases h3 : x = 1
      · subst h3; norm_num; constructor <;> ring
      · by_cases h4 : x = 3
        · subst h4; norm_num; ring
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2,
            ite_eq_right h3]
          simp

/-- **HW-R through the statement constant** at `t = 2`, every site: three steps from the point state `(a, b)`, with
the kernel values `K(3, ±2) = 1/2`, `K(2, ∓1) = ±1/√2` substituted. The summands `a K(2, x)` and `b K(2, x)` are
odd in `x`: this pins the sign of the site in them. -/
theorem hwR_two (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 3 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = -2 then 1 / 2 else if x + 1 = 2 then 1 / 2 else 0) +
          a * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = -2 then 1 / 2 else if x - 1 = 2 then 1 / 2 else 0) +
          b * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ)
            else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0)) := by
  have h1 := h a b 2 x
  rw [show (2 : ℕ) + 1 = 3 from rfl, hadamardKernel_three, hadamardKernel_three, hadamardKernel_two] at h1
  exact h1

/-- **HW-R through the statement constant** at `t = 2`, as a table: `((a + b)/2/√2, 0)` at `−3`,
`(a/√2, (a + b)/2/√2)` at `−1`, `(−((a − b)/2)/√2, −b/√2)` at `1`, `(0, (a − b)/2/√2)` at `3`, `(0, 0)` elsewhere. -/
theorem hwR_two_table (h : HadamardKernelStatement) (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 3 x =
      if x = -3 then ((a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ), 0)
      else if x = -1 then (a / ((Real.sqrt 2 : ℝ) : ℂ), (a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 1 then (-((a - b) / 2) / ((Real.sqrt 2 : ℝ) : ℂ), -b / ((Real.sqrt 2 : ℝ) : ℂ))
      else if x = 3 then (0, (a - b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)) else (0, 0) :=
  (hwR_two h a b x).trans (kernelSide_two a b x)

/-- **Check (unconditional)**: the instance of HW-R in `hwR_two` is true on the data (`hadamardWalk_point_three`). -/
theorem hwR_two_check (a b : ℂ) (x : ℤ) :
    hadamardWalk (pointState a b) 3 x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x + 1 = -2 then 1 / 2 else if x + 1 = 2 then 1 / 2 else 0) +
          a * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0),
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * (if x - 1 = -2 then 1 / 2 else if x - 1 = 2 then 1 / 2 else 0) +
          b * (if x = -1 then 1 / ((Real.sqrt 2 : ℝ) : ℂ) else if x = 1 then -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) else 0)) :=
  (hadamardWalk_point_three a b x).trans (kernelSide_two a b x).symm

/-! ## HW-D through the statement constant, at `t = 3` -/

/-- **HW-D through the statement constant** at `t = 3`, `x = −1`: both components, every `(a, b)`. -/
theorem hwD_three (h : HadamardDecayStatement) (a b : ℂ) :
    ‖a / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h a b 3 (-1) (by norm_num)
  rw [hadamardWalk_point_three, ite_eq_right (by norm_num), ite_eq_left rfl] at h1
  exact h1

/-- **HW-D through the statement constant** at `t = 3`, `x = −1`, state `(1, 0)`, first component, literal form:
`1/√2 ≤ 39 · (1 + 0) · 3^{−1/3}`. -/
theorem hwD_three_unit (h : HadamardDecayStatement) :
    1 / Real.sqrt 2 ≤ 39 * ((1 : ℝ) + 0) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := (hwD_three h 1 0).1
  rw [norm_one_div_sqrt_two, norm_one, norm_zero] at h1
  exact h1

/-- **Datum: `(3^{−1/3})³ = 1/3`**, with the base and the exponent written as in the statements. -/
theorem three_rpow_neg_third_cube : (((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = 1 / 3 := by
  have h : (((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) ^ ((3 : ℕ) : ℝ) = 1 / 3 := by
    rw [← Real.rpow_mul (by positivity), show -(1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  exact (Real.rpow_natCast _ 3).symm.trans h

/-- **Datum: `3^{−1/3} < 1/√2`** (cube both sides: `1/3 < 1/(2√2)`). -/
theorem three_rpow_neg_third_lt : ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) < 1 / Real.sqrt 2 := by
  by_contra hc
  have hs0 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hs2 : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h3 := pow_le_pow_left₀ hs0.le (not_lt.mp hc) 3
  rw [three_rpow_neg_third_cube, show (1 / Real.sqrt 2) ^ 3 = 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2)
    by ring, hs2] at h3
  have h4 : 1 / Real.sqrt 2 ≤ 2 / 3 := by linarith
  have h5 := mul_le_mul h4 h4 hs0.le (by norm_num)
  rw [hs2] at h5
  norm_num at h5

/-- **Datum: `1/3 ≤ 3^{−1/3}`.** -/
theorem third_le_three_rpow : (1 : ℝ) / 3 ≤ ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
    (show (-1 : ℝ) ≤ -(1 : ℝ) / 3 by norm_num)
  rw [Real.rpow_neg_one] at h
  rw [Nat.cast_ofNat]
  linarith

/-- **Check (unconditional)**: the instances of HW-D in `hwD_three` are true (`3^{−1/3} ≥ 1/3`, `1 ≤ √2`). -/
theorem hwD_three_check (a b : ℂ) :
    ‖a / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := norm_div_sqrt_two_le a
  have h2 := (norm_div_sqrt_two_le ((a + b) / 2)).trans_eq (norm_div (a + b) 2)
  rw [Complex.norm_ofNat] at h2
  have h3 := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hm := mul_le_mul_of_nonneg_left third_le_three_rpow (add_nonneg ha hb)
  constructor <;> linarith

/-- **Bite: `¬ (1/√2 ≤ 1 · 3^{−1/3})`.** The bound of HW-D with the constant `1` in the place of `39` is false at
`t = 3`, `x = −1` for the state `(1, 0)` (numbers only; on the walk: `hwD_constant_one_false`). -/
theorem hwD_constant_one_bite : ¬ (1 / Real.sqrt 2 ≤ 1 * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) := by
  rw [one_mul]
  exact not_le.mpr three_rpow_neg_third_lt

/-- **Bite on the walk: the bound of HW-D with the constant `1` is false** at `t = 3`, `x = −1`, first component,
for the point state `(1, 0)`. -/
theorem hwD_constant_one_false :
    ¬ ‖(hadamardWalk (pointState 1 0) 3 (-1)).1‖ ≤ 1 * (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [hadamardWalk_point_three, ite_eq_right (by norm_num), ite_eq_left rfl, norm_one_div_sqrt_two, norm_one,
    norm_zero, add_zero, mul_one]
  exact hwD_constant_one_bite

/-! ## HW-L through the statement constant, at `t = 2` and `t = 3` -/

/-- **HW-L through the statement constant** on a point state at `t = 3`, `x = −1`: the instances of HW-D in
`hwD_three` (the `ℓ¹` sum is `|a| + |b|`). The exponent of `t` in HW-L is exercised at `t ≠ 1`. -/
theorem hwL_point_three (h : HadamardDispersiveStatement) (a b : ℂ) :
    ‖a / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(a + b) / 2 / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ 39 * (‖a‖ + ‖b‖) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h (pointState a b) 3 (-1) (pointState_finite a b) (by norm_num)
  rw [hadamardWalk_point_three, ite_eq_right (by norm_num), ite_eq_left rfl, pointState_finsum] at h1
  exact h1

/-- **Bite on the walk: the bound of HW-L with the constant `1` is false** at `t = 3`, `x = −1`, first component,
for the point state `(1, 0)` (`ℓ¹` sum `1`). -/
theorem hwL_constant_one_false :
    ¬ ‖(hadamardWalk (pointState 1 0) 3 (-1)).1‖ ≤
      1 * (∑ᶠ y : ℤ, (‖(pointState 1 0 y).1‖ + ‖(pointState 1 0 y).2‖)) * ((3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  rw [pointState_finsum]
  exact hwD_constant_one_false

/-- **Datum: two steps from the two-site state at `x = 0`** give `(1, 1/2)`: the first component is the sum of the
contributions `1/2` of the two sites, the second comes from the site `0` only. -/
theorem twoSiteState_walk_two : hadamardWalk twoSiteState 2 0 = (1, 1 / 2) := by
  have e : hadamardWalk twoSiteState 2 0 = hadamardStep (hadamardStep twoSiteState) 0 := rfl
  have hi := inv_sqrt_two_mul_self
  rw [e]
  simp only [hadamardStep]
  norm_num [twoSiteState]
  constructor
  · rw [div_eq_mul_inv, add_mul, hi]; norm_num
  · rw [div_eq_mul_inv, hi]

/-- **HW-L through the statement constant** on the two-site state at `t = 2`, `x = 0`: the components are `1` and
`1/2` and the `ℓ¹` sum is `2`. -/
theorem hwL_two_site_two (h : HadamardDispersiveStatement) :
    (1 : ℝ) ≤ 39 * 2 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      (1 : ℝ) / 2 ≤ 39 * 2 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hn : ‖(1 : ℂ) / 2‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  have h1 := h twoSiteState 2 0 twoSiteState_finite (by norm_num)
  rw [twoSiteState_walk_two, twoSiteState_finsum, norm_one, hn] at h1
  exact h1

/-- **Datum: `1/2 ≤ 2^{−1/3}`.** -/
theorem half_le_two_rpow : (1 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
    (show (-1 : ℝ) ≤ -(1 : ℝ) / 3 by norm_num)
  rw [Real.rpow_neg_one] at h
  rw [Nat.cast_ofNat]
  linarith

/-- **Check (unconditional)**: the instances of HW-L in `hwL_two_site_two` are true (`2^{−1/3} ≥ 1/2`). -/
theorem hwL_two_site_two_check :
    (1 : ℝ) ≤ 39 * 2 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) ∧
      (1 : ℝ) / 2 ≤ 39 * 2 * ((2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h := half_le_two_rpow
  constructor <;> linarith

/-! ## Bite data: a state of infinite support whose first component vanishes -/

/-- Datum for the support hypothesis of HW-L: the constant state `(0, 1)` at every site. Its first component
vanishes everywhere. -/
def constSecondState (_ : ℤ) : ℂ × ℂ := (0, 1)

/-- The support of the constant state `(0, 1)` is infinite. -/
theorem constSecondState_infinite : ¬ {y : ℤ | constSecondState y ≠ (0, 0)}.Finite := by
  have h : {y : ℤ | constSecondState y ≠ (0, 0)} = Set.univ := by
    ext y; simp [constSecondState]
  rw [h]
  exact Set.infinite_univ

/-- **Datum: the set of sites where the first component of the constant state `(0, 1)` is not zero is finite** (it
is empty). -/
theorem constSecondState_first_finite : {y : ℤ | (constSecondState y).1 ≠ 0}.Finite := by
  have h : {y : ℤ | (constSecondState y).1 ≠ 0} = ∅ := by
    ext y; simp [constSecondState]
  rw [h]
  exact Set.finite_empty

/-- **Datum: the `∑ᶠ` of the norms of the constant state `(0, 1)` is `0`** (infinite support). -/
theorem constSecondState_finsum : ∑ᶠ y : ℤ, (‖(constSecondState y).1‖ + ‖(constSecondState y).2‖) = 0 := by
  refine finsum_of_infinite_support ?_
  have h : Function.support (fun y : ℤ => ‖(constSecondState y).1‖ + ‖(constSecondState y).2‖) = Set.univ := by
    ext y; simp [constSecondState]
  rw [h]
  exact Set.infinite_univ

/-- **Datum: one step from the constant state `(0, 1)`** is `(1/√2, −(1/√2))` at every site. -/
theorem constSecondState_walk_one (x : ℤ) :
    hadamardWalk constSecondState 1 x = (1 / ((Real.sqrt 2 : ℝ) : ℂ), -(1 / ((Real.sqrt 2 : ℝ) : ℂ))) := by
  have e : hadamardWalk constSecondState 1 x = hadamardStep constSecondState x := rfl
  rw [e, hadamardStep]
  simp only [constSecondState]
  rw [zero_add, zero_sub, neg_div]

/-- **Bite: the conclusion of HW-L is false for the constant state `(0, 1)`** at `t = 1` (`1/√2 ≤ 39 · 0 · 1`). The
hypothesis of finite support must count the sites where either component is not zero. -/
theorem hwL_constSecond_false (x : ℤ) :
    ¬ ‖(hadamardWalk constSecondState 1 x).1‖ ≤
      39 * (∑ᶠ y : ℤ, (‖(constSecondState y).1‖ + ‖(constSecondState y).2‖)) * ((1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h2 : 0 < 1 / Real.sqrt 2 := by positivity
  rw [constSecondState_walk_one, constSecondState_finsum, norm_one_div_sqrt_two, mul_zero, zero_mul]
  exact not_le.mpr h2

/-! ## Data: the kernel at the time 5, and HW-K there -/

/-- **Datum: the amplitude of the kernel at `t = 5` is `−1/2 + cos 2k + cos 4k / 2`**:
`cos 5ω = cos 3ω cos 2ω − sin 3ω sin 2ω = (1 − 6 sin² k + 4 sin⁴ k) cos ω` with `sin² ω = sin² k / 2`. -/
theorem kernel_quotient_five (k : ℝ) :
    (Complex.exp (↑(-(((5 : ℕ) : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ 5 * Complex.exp (↑(((5 : ℕ) : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) =
      -(1 / 2) * Complex.exp (↑(((0 : ℤ) : ℝ) * k) * Complex.I) +
        (1 / 2 * Complex.exp (↑(((2 : ℤ) : ℝ) * k) * Complex.I) +
          1 / 2 * Complex.exp (↑(((-2 : ℤ) : ℝ) * k) * Complex.I)) +
        (1 / 4 * Complex.exp (↑(((4 : ℤ) : ℝ) * k) * Complex.I) +
          1 / 4 * Complex.exp (↑(((-4 : ℤ) : ℝ) * k) * Complex.I)) := by
  have hs : Real.sin (hadamardDispersion k) ^ 2 = Real.sin k ^ 2 / 2 := by
    rw [sin_hadamardDispersion, sin_div_sqrt_two_sq]
  have hcs := Real.sin_sq_add_cos_sq (hadamardDispersion k)
  have hk := Real.sin_sq_add_cos_sq k
  have h1 : 2 * Real.cos (((5 : ℕ) : ℝ) * hadamardDispersion k) =
      (-(1 / 2) + Real.cos (2 * k) + 1 / 2 * Real.cos (4 * k)) * Real.sqrt (2 * (1 + Real.cos k ^ 2)) := by
    rw [show ((5 : ℕ) : ℝ) * hadamardDispersion k = 3 * hadamardDispersion k + 2 * hadamardDispersion k by
      push_cast; ring, show 4 * k = 2 * (2 * k) by ring, Real.cos_add, Real.cos_three_mul, Real.sin_three_mul,
      Real.cos_two_mul, Real.sin_two_mul, ← two_cos_hadamardDispersion, Real.cos_two_mul (2 * k),
      Real.cos_two_mul k]
    linear_combination
      (16 * Real.sin k ^ 2 * Real.cos (hadamardDispersion k) - 16 * Real.cos (hadamardDispersion k) ^ 3 +
        16 * Real.cos (hadamardDispersion k) * Real.sin (hadamardDispersion k) ^ 2 -
        8 * Real.cos (hadamardDispersion k)) * hs +
      (-8 * Real.sin k ^ 2 * Real.cos (hadamardDispersion k) + 16 * Real.cos (hadamardDispersion k) ^ 3 -
        4 * Real.cos (hadamardDispersion k)) * hcs +
      (-8 * Real.cos k ^ 2 * Real.cos (hadamardDispersion k) + 8 * Real.sin k ^ 2 * Real.cos (hadamardDispersion k) -
        4 * Real.cos (hadamardDispersion k)) * hk
  have h2 := exp_neg_add_exp (2 * k)
  have h4 := exp_neg_add_exp (4 * k)
  rw [show (-1 : ℂ) ^ 5 = -1 by norm_num, neg_one_mul, sub_neg_eq_add, exp_neg_add_exp, h1, Complex.ofReal_mul,
    mul_div_assoc, div_self (kernel_denominator_ne_zero k), mul_one]
  simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, neg_mul, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  push_cast at h2 h4 ⊢
  linear_combination (-1 / 2 : ℂ) * h2 + (-1 / 4 : ℂ) * h4

/-- The normalised integral of a sum of two continuous functions over `[−π, π]`. -/
theorem fourier_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, (f k + g k) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ k in (-Real.pi)..Real.pi, f k) +
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, g k := by
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_add]

/-- The Fourier coefficients of one exponential with a constant factor. -/
theorem fourier_single (c : ℂ) (n : ℤ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, c * Complex.exp (↑((n : ℝ) * k) * Complex.I) =
      c * (if n = 0 then 1 else 0) := by
  rw [intervalIntegral.integral_const_mul, ← fourier_unit n]
  ring

/-- **Datum: the kernel at `t = 5`, all sites**, as a sum of unit data: `−1/2` at `0`, `1/2` at `±2`, `1/4` at
`±4`, `0` elsewhere (the integrand is `(−1/2 + cos 2k + cos 4k / 2) e^{−ixk}`). -/
theorem hadamardKernel_five (x : ℤ) :
    hadamardKernel 5 x =
      -(1 / 2) * (if 0 - x = 0 then 1 else 0) +
        (1 / 2 * (if 2 - x = 0 then 1 else 0) + 1 / 2 * (if -2 - x = 0 then 1 else 0)) +
        (1 / 4 * (if 4 - x = 0 then 1 else 0) + 1 / 4 * (if -4 - x = 0 then 1 else 0)) := by
  rw [hadamardKernel]
  simp only [kernel_quotient_five, add_mul, mul_assoc, exp_mul_exp_site]
  rw [fourier_add _ _ (by fun_prop) (by fun_prop), fourier_add _ _ (by fun_prop) (by fun_prop), fourier_single,
    fourier_pair, fourier_pair]

/-- **Datum: `K(5, 0) = −1/2`.** -/
theorem hadamardKernel_five_zero : hadamardKernel 5 0 = -(1 / 2) := by
  rw [hadamardKernel_five]; norm_num

/-- **Datum: `K(5, ±2) = 1/2` and `K(5, ±4) = 1/4`.** -/
theorem hadamardKernel_five_table :
    hadamardKernel 5 (-4) = 1 / 4 ∧ hadamardKernel 5 (-2) = 1 / 2 ∧ hadamardKernel 5 2 = 1 / 2 ∧
      hadamardKernel 5 4 = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hadamardKernel_five] <;> norm_num

/-- **HW-K through the statement constant** at `t = 5`, `x = 0`, literal form: `|K(5, 0)| = 1/2`. -/
theorem hwK_five (h : HadamardKernelBoundStatement) :
    (1 : ℝ) / 2 ≤ 7 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 := h 5 0 (by norm_num)
  rw [hadamardKernel_five_zero, norm_neg, norm_div, norm_one, Complex.norm_ofNat] at h1
  exact h1

/-- **Datum: `5^{−1/2} = 1/√5`**, with the base and the exponent written as in the statements. -/
theorem five_rpow_neg_half : ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt 5 := by
  rw [Nat.cast_ofNat, neg_div, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]

/-- **Check (unconditional)**: the instance of HW-K in `hwK_five` is true (`7/√5 ≥ 7/3`). -/
theorem hwK_five_check :
    (1 : ℝ) / 2 ≤ 7 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
  have h1 : Real.sqrt 5 ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (0 : ℝ) ≤ 12 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by positivity
  have h3 : (1 : ℝ) / 3 ≤ 1 / Real.sqrt 5 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) h1
  rw [five_rpow_neg_half]
  linarith

/-- **Bite: `¬ (1/2 ≤ 1 · 5^{−1/2} + 0 · 5^{−1/3})`.** The bound of HW-K with the constants `(1, 0)` in the place of
`(7, 12)` is false at `t = 5`, `x = 0` (`√5 > 2`). -/
theorem hwK_constants_one_zero_bite :
    ¬ ((1 : ℝ) / 2 ≤ 1 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 0 * ((5 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) := by
  have h1 : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : 1 / Real.sqrt 5 < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) h1
  rw [five_rpow_neg_half, one_mul, zero_mul, add_zero]
  exact not_le.mpr h2

end OscInt.API.HadamardWalkSanity2
