/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.KusminLandau

/-! # Sanity theorems through the batch-KL statement constants

As for batches LE, LE2 and HC (lessons 33, 38, 44, 47): every theorem about a frozen statement of
`OscInt/Statements/KusminLandau.lean` takes that statement constant as its only hypothesis, discharges its hypotheses
on closed data and concludes its conclusion there. Nothing here proves, or argues towards, the statements themselves:
the file contains finite sums with explicit terms, instances of the shared hypothesis `DiffsMonotoneIn` on data, and
its negation on data. Planted copies: `docs/replay/plants/2026-11-16-KL/`.

Data (`e(x) = e^{2πix}`, written `eTerm x` here; `expSum c N = Σ_{n ≤ N} eTerm (c n)` by `rfl`):
* `cThird = 0, 1/3, 1` (`N = 2`, `k = 0`, `λ = 1/3`, differences nondecreasing): `|S| = √3 = cot(π/6)`, the bound of
  KL-D is attained (Landau).
* `cAnti = 0, 2/3, 1` (differences nonincreasing) and `cShift = 0, 4/3, 3` (`k = 1`): the same norm `√3`.
* `cSix = 0, 1/6, 1/3, 1/2, 4/3, 13/6, 3` (`N = 6`, `λ = 1/6`): `S = 1 + 2√3 i`, `|S| = √13`.
* `cAlt = 0, 1/4, 1, 5/4, 2`: differences `1/4, 3/4, 1/4, 3/4` in the cell of `λ = 1/4` but not monotone;
  `S = 3 + 2i`, `|S| = √13`.
* `cOne` (one term, `N = 0`): `S = 1`; `cQuarter = 0, 1/4` (`N = 1`): `S = 1 + i`; `cInt n = n`: `S = 3` at `N = 2`.
* KL-F: `f(x) = x/4` on `[0, 1]` (`k = 0`), `f(x) = 5x/4` on `[0, 1]` (`k = 1`), and `f(x) = 3x/4 − x²/8` on `[0, 2]`
  (`f′` decreasing from `3/4` to `1/4`), all with `λ = 1/4`.
* Bites on `DiffsMonotoneIn`: `cAlt` (monotonicity), `cQuarter` at `λ = 1/3` (lower end of the cell), `cInt` at
  `λ = 1/2` (upper end of the cell).
-/

namespace OscInt.API.KusminLandauSanity

open OscInt.Statements Set

/-! ## The terms `e(x)` at the points used -/

/-- `e(x) = e^{2πix}`, literally the summand of `expSum` and of KL-F. -/
noncomputable def eTerm (x : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * x) * Complex.I)

/-- `expSum` in terms of `eTerm` (definitional). -/
theorem expSum_eq (c : ℕ → ℝ) (N : ℕ) : expSum c N = ∑ n ∈ Finset.range (N + 1), eTerm (c n) := rfl

/-- `e(x) = cos 2πx + i sin 2πx`. -/
theorem eTerm_eq (x : ℝ) :
    eTerm x = ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ) + ((Real.sin (2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
  rw [eTerm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `e(y + m) = e(y)` for an integer `m`. -/
theorem eTerm_add_int (y : ℝ) (m : ℤ) : eTerm (y + m) = eTerm y := by
  rw [eTerm_eq, eTerm_eq, mul_add, show 2 * Real.pi * (m : ℝ) = m * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- `e(x) = e(y)` when `x = y + m`, `m` an integer (the form used on numerals). -/
theorem eTerm_of (x y : ℝ) (m : ℤ) (h : x = y + m) : eTerm x = eTerm y := by
  rw [h, eTerm_add_int]

theorem eTerm_zero : eTerm 0 = 1 := by simp [eTerm]

theorem eTerm_int (m : ℤ) : eTerm m = 1 := by
  simpa [eTerm_zero] using eTerm_add_int 0 m

theorem eTerm_quarter : eTerm (1 / 4) = Complex.I := by
  rw [eTerm_eq, show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem eTerm_half : eTerm (1 / 2) = -1 := by
  rw [eTerm_eq, show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  simp

theorem eTerm_sixth : eTerm (1 / 6) = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_eq, show 2 * Real.pi * (1 / 6) = Real.pi / 3 by ring, Real.cos_pi_div_three, Real.sin_pi_div_three]

theorem eTerm_third : eTerm (1 / 3) = ((-(1 / 2) : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_eq, show 2 * Real.pi * (1 / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]

theorem eTerm_two_thirds :
    eTerm (2 / 3) = ((-(1 / 2) : ℝ) : ℂ) + ((-(Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_eq, show 2 * Real.pi * (2 / 3) = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_pi_div_three, Real.sin_pi_div_three]

theorem eTerm_one : eTerm 1 = 1 := by simpa using eTerm_int 1

theorem eTerm_two : eTerm 2 = 1 := by simpa using eTerm_int 2

theorem eTerm_three : eTerm 3 = 1 := by simpa using eTerm_int 3

theorem eTerm_four_thirds :
    eTerm (4 / 3) = ((-(1 / 2) : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_of (4 / 3) (1 / 3) 1 (by norm_num), eTerm_third]

theorem eTerm_thirteen_sixths :
    eTerm (13 / 6) = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_of (13 / 6) (1 / 6) 2 (by norm_num), eTerm_sixth]

theorem eTerm_five_quarters : eTerm (5 / 4) = Complex.I := by
  rw [eTerm_of (5 / 4) (1 / 4) 1 (by norm_num), eTerm_quarter]

/-- `cot(π/6) = √3`, in the literal form of the bound of KL-D at `λ = 1/3`. -/
theorem cot_third : Real.cos (Real.pi * (1 / 3) / 2) / Real.sin (Real.pi * (1 / 3) / 2) = Real.sqrt 3 := by
  rw [show Real.pi * (1 / 3) / 2 = Real.pi / 6 by ring, Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

/-- `cot(π/4) = 1`, in the literal form of the bound of KL-D at `λ = 1/2`. -/
theorem cot_half : Real.cos (Real.pi * (1 / 2) / 2) / Real.sin (Real.pi * (1 / 2) / 2) = 1 := by
  rw [show Real.pi * (1 / 2) / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four, Real.sin_pi_div_four]
  exact div_self (by positivity)

/-! ## The sequences -/

/-- `0, 1/3, 1`: differences `1/3, 2/3` (nondecreasing), the extremal sequence at `λ = 1/3`. -/
noncomputable def cThird : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 3
  | _ => 1

/-- `0, 2/3, 1`: differences `2/3, 1/3` (nonincreasing). -/
noncomputable def cAnti : ℕ → ℝ
  | 0 => 0
  | 1 => 2 / 3
  | _ => 1

/-- `0, 4/3, 3`: differences `4/3, 5/3`, the cell `[k + 1/3, k + 2/3]` with `k = 1`. -/
noncomputable def cShift : ℕ → ℝ
  | 0 => 0
  | 1 => 4 / 3
  | _ => 3

/-- `0, 1/6, 1/3, 1/2, 4/3, 13/6, 3`: differences `1/6, 1/6, 1/6, 5/6, 5/6, 5/6`. -/
noncomputable def cSix : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 6
  | 2 => 1 / 3
  | 3 => 1 / 2
  | 4 => 4 / 3
  | 5 => 13 / 6
  | _ => 3

/-- `0, 1/4, 1, 5/4, 2`: differences `1/4, 3/4, 1/4, 3/4`, in the cell of `λ = 1/4` but not monotone. -/
noncomputable def cAlt : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 1
  | 3 => 5 / 4
  | _ => 2

/-- The one-term datum (`N = 0`). -/
def cOne : ℕ → ℝ := fun _ => 0

/-- `0, 1/4` (`N = 1`). -/
noncomputable def cQuarter : ℕ → ℝ
  | 0 => 0
  | _ => 1 / 4

/-- `n ↦ n`: every difference is `1`. -/
def cInt : ℕ → ℝ := fun n => n

/-! ## Unconditional values of the sums -/

theorem expSum_cThird :
    expSum cThird 2 = ((3 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cThird, eTerm_zero, eTerm_third, eTerm_one]
  push_cast
  ring

theorem expSum_cAnti :
    expSum cAnti 2 = ((3 / 2 : ℝ) : ℂ) + ((-(Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cAnti, eTerm_zero, eTerm_two_thirds,
    eTerm_one]
  push_cast
  ring

theorem expSum_cShift :
    expSum cShift 2 = ((3 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cShift, eTerm_zero, eTerm_four_thirds,
    eTerm_three]
  push_cast
  ring

theorem expSum_cSix : expSum cSix 6 = ((1 : ℝ) : ℂ) + ((2 * Real.sqrt 3 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cSix, eTerm_zero, eTerm_sixth, eTerm_third,
    eTerm_half, eTerm_four_thirds, eTerm_thirteen_sixths, eTerm_three]
  push_cast
  ring

theorem expSum_cAlt : expSum cAlt 4 = ((3 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cAlt, eTerm_zero, eTerm_quarter, eTerm_one,
    eTerm_five_quarters, eTerm_two]
  push_cast
  ring

theorem expSum_cOne : expSum cOne 0 = 1 := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cOne, eTerm_zero, zero_add]

theorem expSum_cQuarter : expSum cQuarter 1 = ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cQuarter, eTerm_zero, eTerm_quarter]
  push_cast
  ring

theorem expSum_cInt : expSum cInt 2 = 3 := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cInt, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, eTerm_zero, eTerm_one, eTerm_two]
  norm_num

/-- **Equality datum**: `|e(0) + e(1/3) + e(1)| = √3 = cot(π/6)`. -/
theorem norm_expSum_cThird : ‖expSum cThird 2‖ = Real.sqrt 3 := by
  rw [expSum_cThird, Complex.norm_add_mul_I]
  congr 1
  linear_combination (1 / 4 : ℝ) * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

theorem norm_expSum_cAnti : ‖expSum cAnti 2‖ = Real.sqrt 3 := by
  rw [expSum_cAnti, Complex.norm_add_mul_I]
  congr 1
  linear_combination (1 / 4 : ℝ) * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

theorem norm_expSum_cShift : ‖expSum cShift 2‖ = Real.sqrt 3 := by
  rw [expSum_cShift, Complex.norm_add_mul_I]
  congr 1
  linear_combination (1 / 4 : ℝ) * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

theorem norm_expSum_cSix : ‖expSum cSix 6‖ = Real.sqrt 13 := by
  rw [expSum_cSix, Complex.norm_add_mul_I]
  congr 1
  linear_combination (4 : ℝ) * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

theorem norm_expSum_cAlt : ‖expSum cAlt 4‖ = Real.sqrt 13 := by
  rw [expSum_cAlt, Complex.norm_add_mul_I]
  congr 1
  norm_num

theorem norm_expSum_cQuarter : ‖expSum cQuarter 1‖ = Real.sqrt 2 := by
  rw [expSum_cQuarter, Complex.norm_add_mul_I]
  congr 1
  norm_num

/-! ## The shared hypothesis on data -/

theorem diffs_cThird : DiffsMonotoneIn cThird 2 0 (1 / 3) := by
  refine ⟨Or.inl fun n hn => ?_, fun n hn => ?_⟩
  · obtain rfl : n = 0 := by omega
    norm_num [cThird]
  · interval_cases n <;> norm_num [cThird]

/-- The nonincreasing branch of `DiffsMonotoneIn`. -/
theorem diffs_cAnti : DiffsMonotoneIn cAnti 2 0 (1 / 3) := by
  refine ⟨Or.inr fun n hn => ?_, fun n hn => ?_⟩
  · obtain rfl : n = 0 := by omega
    norm_num [cAnti]
  · interval_cases n <;> norm_num [cAnti]

/-- The cell with `k = 1`. -/
theorem diffs_cShift : DiffsMonotoneIn cShift 2 1 (1 / 3) := by
  refine ⟨Or.inl fun n hn => ?_, fun n hn => ?_⟩
  · obtain rfl : n = 0 := by omega
    norm_num [cShift]
  · interval_cases n <;> norm_num [cShift]

theorem diffs_cSix : DiffsMonotoneIn cSix 6 0 (1 / 6) := by
  refine ⟨Or.inl fun n hn => ?_, fun n hn => ?_⟩
  · have hn' : n < 5 := by omega
    interval_cases n <;> norm_num [cSix]
  · interval_cases n <;> norm_num [cSix]

theorem diffs_cQuarter : DiffsMonotoneIn cQuarter 1 0 (1 / 4) := by
  refine ⟨Or.inl fun n hn => ?_, fun n hn => ?_⟩
  · omega
  · interval_cases n
    norm_num [cQuarter]

/-- With `N = 0` there is no difference: the hypothesis holds for every `k` and `lam`. -/
theorem diffs_cOne (k : ℤ) (lam : ℝ) : DiffsMonotoneIn cOne 0 k lam :=
  ⟨Or.inl fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _)⟩

/-- The differences of `cAlt` lie in the cell `[1/4, 3/4]`: its bite is on monotonicity alone. -/
theorem cAlt_cell :
    ∀ n < 4, ((0 : ℤ) : ℝ) + 1 / 4 ≤ cAlt (n + 1) - cAlt n ∧
      cAlt (n + 1) - cAlt n ≤ ((0 : ℤ) : ℝ) + 1 - 1 / 4 := by
  intro n hn
  interval_cases n <;> norm_num [cAlt]

/-- Every difference of `cInt` is `1`: its bite at `λ = 1/2` is on the upper end of the cell alone. -/
theorem cInt_diff (n : ℕ) : cInt (n + 1) - cInt n = 1 := by
  simp [cInt]

/-- **Bite (monotonicity).** The differences `1/4, 3/4, 1/4, 3/4` are neither nondecreasing nor nonincreasing. -/
theorem not_diffs_cAlt : ¬ DiffsMonotoneIn cAlt 4 0 (1 / 4) := by
  rintro ⟨h | h, -⟩
  · have := h 1 (by norm_num)
    norm_num [cAlt] at this
  · have := h 0 (by norm_num)
    norm_num [cAlt] at this

/-- **Bite (lower end of the cell).** The difference `1/4` is outside `[1/3, 2/3]`. -/
theorem not_diffs_cQuarter_third : ¬ DiffsMonotoneIn cQuarter 1 0 (1 / 3) := by
  rintro ⟨-, h⟩
  have := (h 0 (by norm_num)).1
  norm_num [cQuarter] at this

/-- **Bite (upper end of the cell).** The difference `1` is above `1 − 1/2`. -/
theorem not_diffs_cInt : ¬ DiffsMonotoneIn cInt 2 0 (1 / 2) := by
  rintro ⟨-, h⟩
  have := (h 0 (by norm_num)).2
  rw [cInt_diff] at this
  norm_num at this

/-! ## KL-D and KL-C through the statement constants -/

/-- **KL-D through the statement constant** at the extremal datum: the conclusion is `|S| ≤ √3`, and
`norm_expSum_cThird` says `|S| = √3`. Any smaller bound at `λ = 1/3` is refuted by this datum. -/
theorem kl_third (h : KusminLandauStatement) : ‖expSum cThird 2‖ ≤ Real.sqrt 3 := by
  have := h cThird 2 0 (1 / 3) (by norm_num) (by norm_num) diffs_cThird
  rwa [cot_third] at this

/-- **KL-D through the statement constant**, nonincreasing differences. -/
theorem kl_anti (h : KusminLandauStatement) : ‖expSum cAnti 2‖ ≤ Real.sqrt 3 := by
  have := h cAnti 2 0 (1 / 3) (by norm_num) (by norm_num) diffs_cAnti
  rwa [cot_third] at this

/-- **KL-D through the statement constant**, integer shift `k = 1`. -/
theorem kl_shift (h : KusminLandauStatement) : ‖expSum cShift 2‖ ≤ Real.sqrt 3 := by
  have := h cShift 2 1 (1 / 3) (by norm_num) (by norm_num) diffs_cShift
  rwa [cot_third] at this

/-- **KL-D through the statement constant** at `λ = 1/6`, seven terms: `√13 ≤ cot(π/12)`. -/
theorem kl_six (h : KusminLandauStatement) :
    Real.sqrt 13 ≤ Real.cos (Real.pi * (1 / 6) / 2) / Real.sin (Real.pi * (1 / 6) / 2) := by
  have := h cSix 6 0 (1 / 6) (by norm_num) (by norm_num) diffs_cSix
  rwa [norm_expSum_cSix] at this

/-- **KL-D through the statement constant** at `N = 0`, `λ = 1/2` (the end of the range of `λ`): `1 ≤ cot(π/4)`,
where `cot(π/4) = 1` (`cot_half`): a second datum where the bound is attained. -/
theorem kl_one_half (h : KusminLandauStatement) :
    (1 : ℝ) ≤ Real.cos (Real.pi * (1 / 2) / 2) / Real.sin (Real.pi * (1 / 2) / 2) := by
  have := h cOne 0 0 (1 / 2) (by norm_num) le_rfl (diffs_cOne 0 (1 / 2))
  rwa [expSum_cOne, norm_one] at this

/-- **KL-C through the statement constant** at `λ = 1/6`: `√13 ≤ 12/π`. -/
theorem klc_six (h : KusminLandauTwoOverPiStatement) : Real.sqrt 13 ≤ 2 / (Real.pi * (1 / 6)) := by
  have := h cSix 6 0 (1 / 6) (by norm_num) (by norm_num) diffs_cSix
  rwa [norm_expSum_cSix] at this

/-- **KL-C through the statement constant** at `λ = 1/3`: `√3 ≤ 6/π`. -/
theorem klc_third (h : KusminLandauTwoOverPiStatement) : Real.sqrt 3 ≤ 2 / (Real.pi * (1 / 3)) := by
  have := h cThird 2 0 (1 / 3) (by norm_num) (by norm_num) diffs_cThird
  rwa [norm_expSum_cThird] at this

/-! ## KL-F through the statement constant -/

/-- The integers of `[0, 1]`. -/
theorem Icc_ceil_floor_zero_one : Finset.Icc ⌈(0 : ℝ)⌉ ⌊(1 : ℝ)⌋ = {0, 1} := by
  rw [Int.ceil_zero, Int.floor_one]
  decide

/-- The integers of `[0, 2]`. -/
theorem Icc_ceil_floor_zero_two : Finset.Icc ⌈(0 : ℝ)⌉ ⌊(2 : ℝ)⌋ = {0, 1, 2} := by
  rw [Int.ceil_zero, show ⌊(2 : ℝ)⌋ = 2 from Int.floor_ofNat 2]
  decide

/-- **KL-F through the statement constant**, `f(x) = x/4` on `[0, 1]` (`f′ = 1/4`, `k = 0`, `λ = 1/4`): the sum is
`e(0) + e(1/4) = 1 + i`, so `√2 ≤ cot(π/8)`. -/
theorem klf_quarter (h : KusminLandauDerivStatement) :
    Real.sqrt 2 ≤ Real.cos (Real.pi * (1 / 4) / 2) / Real.sin (Real.pi * (1 / 4) / 2) := by
  have h1 := h (fun x => x / 4) (fun _ => 1 / 4) 0 1 0 (1 / 4) (by norm_num) (by norm_num)
    ⟨by fun_prop, fun x _ => (hasDerivAt_id x).div_const 4⟩ (Or.inl monotoneOn_const)
    (fun x _ => by norm_num)
  have hs : ∑ n ∈ Finset.Icc ⌈(0 : ℝ)⌉ ⌊(1 : ℝ)⌋, eTerm ((n : ℝ) / 4) =
      ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I := by
    rw [Icc_ceil_floor_zero_one, Finset.sum_pair (by norm_num)]
    rw [Int.cast_zero, Int.cast_one, zero_div, eTerm_zero, eTerm_quarter]
    simp
  have h2 : ‖((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I‖ ≤ _ := hs ▸ h1
  rw [Complex.norm_add_mul_I] at h2
  norm_num at h2
  exact h2

/-- **KL-F through the statement constant**, `f(x) = 5x/4` on `[0, 1]` (`f′ = 5/4`, `k = 1`, `λ = 1/4`): the sum is
`e(0) + e(5/4) = 1 + i`. -/
theorem klf_quarter_shift (h : KusminLandauDerivStatement) :
    Real.sqrt 2 ≤ Real.cos (Real.pi * (1 / 4) / 2) / Real.sin (Real.pi * (1 / 4) / 2) := by
  have h1 := h (fun x => 5 * x / 4) (fun _ => 5 / 4) 0 1 1 (1 / 4) (by norm_num) (by norm_num)
    ⟨by fun_prop, fun x _ => by simpa using ((hasDerivAt_id x).const_mul 5).div_const 4⟩ (Or.inl monotoneOn_const)
    (fun x _ => by norm_num)
  have hs : ∑ n ∈ Finset.Icc ⌈(0 : ℝ)⌉ ⌊(1 : ℝ)⌋, eTerm (5 * (n : ℝ) / 4) =
      ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I := by
    rw [Icc_ceil_floor_zero_one, Finset.sum_pair (by norm_num)]
    rw [Int.cast_zero, Int.cast_one, mul_zero, zero_div, mul_one, eTerm_zero, eTerm_five_quarters]
    simp
  have h2 : ‖((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I‖ ≤ _ := hs ▸ h1
  rw [Complex.norm_add_mul_I] at h2
  norm_num at h2
  exact h2

/-- **KL-F through the statement constant**, antitone branch: `f(x) = 3x/4 − x²/8` on `[0, 2]`, `f′(x) = 3/4 − x/4`
decreasing with values in `[1/4, 3/4]`; `f(0) = 0`, `f(1) = 5/8`, `f(2) = 1`, so the sum is `2 + e(5/8)`. -/
theorem klf_antitone (h : KusminLandauDerivStatement) :
    ‖2 + Complex.exp (↑(2 * Real.pi * (5 / 8)) * Complex.I)‖ ≤
      Real.cos (Real.pi * (1 / 4) / 2) / Real.sin (Real.pi * (1 / 4) / 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 3 / 4 * x - x ^ 2 / 8) (3 / 4 - x / 4) x := by
    intro x
    have h0 : HasDerivAt (fun x : ℝ => 3 / 4 * x - x ^ 2 / 8)
        (3 / 4 * 1 - ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 8) x :=
      ((hasDerivAt_id x).const_mul (3 / 4 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 8)
    exact h0.congr_deriv (by norm_num; ring)
  have h1 := h (fun x => 3 / 4 * x - x ^ 2 / 8) (fun x => 3 / 4 - x / 4) 0 2 0 (1 / 4) (by norm_num)
    (by norm_num) ⟨by fun_prop, fun x _ => hd x⟩
    (Or.inr fun x _ y _ hxy => by simp only; linarith)
    (fun x hx => by
      obtain ⟨h0, h2⟩ := hx
      simp only [Int.cast_zero]
      constructor <;> linarith)
  have hs : ∑ n ∈ Finset.Icc ⌈(0 : ℝ)⌉ ⌊(2 : ℝ)⌋, eTerm (3 / 4 * (n : ℝ) - (n : ℝ) ^ 2 / 8) =
      2 + eTerm (5 / 8) := by
    rw [Icc_ceil_floor_zero_two, Finset.sum_insert (by decide), Finset.sum_pair (by norm_num)]
    norm_num [eTerm_zero, eTerm_one]
    ring
  exact hs ▸ h1

end OscInt.API.KusminLandauSanity
