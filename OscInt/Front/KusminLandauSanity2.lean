/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.KusminLandauSanity

/-! # Second sanity layer through the batch-KL statement constants

Answers the blind pre-proof reviews of batch KL, which found the statements faithful but found mutations that the
first layer (`OscInt/Front/KusminLandauSanity.lean`) does not detect. As there, every theorem about a frozen statement
of `OscInt/Statements/KusminLandau.lean` takes that statement constant as its only hypothesis, discharges its
hypotheses on closed data and concludes its conclusion there. Nothing here proves, or argues towards, the statements
themselves: the file contains finite sums with explicit terms, instances of the shared hypothesis `DiffsMonotoneIn` on
data, and its negation on data. Planted copies: `docs/replay/plants/2026-11-16-KL-second/`.

Data added (`eTerm x = e^{2πix}` as in the first layer):
* `cLast = 0, 1/3, 1, 4/3` (`N = 3`): differences `1/3, 2/3, 1/3` in the cell of `λ = 1/3`; only the LAST comparison of
  consecutive differences fails. `S = 2 + 2e(1/3) = 1 + √3 i`, `|S| = 2 > √3`.
* `cCells = 0, 1/4, 1, 9/4, 4` (`N = 4`): differences `1/4, 3/4, 5/4, 7/4`, increasing, each at distance `1/4` from
  the integers, but in two cells (`k = 0` and `k = 1`). `S = 3 + 2i`, `|S| = √13`.
* `cNeg = 0, −2/3, −1` (`N = 2`): differences `−2/3, −1/3`, the cell `[k + 1/3, k + 2/3]` with `k = −1`. `|S| = √3`.
* KL-C at `λ = 1/2` (the end of the range of `λ`) on the one-term datum `cOne`.
* KL-F: `f(x) = x/2` on `[0, 2]` (`λ = 1/2`: the terms `1, −1, 1` sum to `1 = cot(π/4)`, the bound is attained in the
  derivative form); `f(x) = x/4` on `[−1/2, 3/2]` (end points that are not integers: `⌈a⌉ = 0`, `⌊b⌋ = 1`); and
  `a = b = 1/2` (no integer in `[a, b]`: the sum is empty).
* Bites on `DiffsMonotoneIn`: `cLast` (the last comparison), `cCells` (no single cell, for every integer `k`).
-/

namespace OscInt.API.KusminLandauSanity2

open OscInt.Statements OscInt.API.KusminLandauSanity Set

/-! ## The terms `e(x)` at the further points used -/

theorem eTerm_four : eTerm 4 = 1 := by simpa using eTerm_int 4

theorem eTerm_neg_one : eTerm (-1) = 1 := by simpa using eTerm_int (-1)

theorem eTerm_nine_quarters : eTerm (9 / 4) = Complex.I := by
  rw [eTerm_of (9 / 4) (1 / 4) 2 (by norm_num), eTerm_quarter]

theorem eTerm_neg_two_thirds :
    eTerm (-2 / 3) = ((-(1 / 2) : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [eTerm_of (-2 / 3) (1 / 3) (-1) (by norm_num), eTerm_third]

/-! ## The sequences -/

/-- `0, 1/3, 1, 4/3`: differences `1/3, 2/3, 1/3`; the first comparison is nondecreasing, the last one is not. -/
noncomputable def cLast : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 3
  | 2 => 1
  | _ => 4 / 3

/-- `0, 1/4, 1, 9/4, 4`: differences `1/4, 3/4, 5/4, 7/4`, increasing, in the cells of `λ = 1/4` with `k = 0` (the
first two) and `k = 1` (the last two). -/
noncomputable def cCells : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 1
  | 3 => 9 / 4
  | _ => 4

/-- `0, −2/3, −1`: differences `−2/3, −1/3`, the cell `[k + 1/3, k + 2/3]` with `k = −1`. -/
noncomputable def cNeg : ℕ → ℝ
  | 0 => 0
  | 1 => -2 / 3
  | _ => -1

/-! ## Unconditional values of the sums -/

/-- `e(0) + e(1/3) + e(1) + e(4/3) = 2 + 2e(1/3)`. -/
theorem expSum_cLast_eq : expSum cLast 3 = 2 + 2 * eTerm (1 / 3) := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cLast, eTerm_zero, eTerm_one,
    eTerm_of (4 / 3) (1 / 3) 1 (by norm_num)]
  ring

theorem expSum_cLast : expSum cLast 3 = ((1 : ℝ) : ℂ) + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I := by
  rw [expSum_cLast_eq, eTerm_third]
  push_cast
  ring

theorem expSum_cCells : expSum cCells 4 = ((3 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cCells, eTerm_zero, eTerm_quarter, eTerm_one,
    eTerm_nine_quarters, eTerm_four]
  push_cast
  ring

theorem expSum_cNeg :
    expSum cNeg 2 = ((3 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [expSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, cNeg, eTerm_zero, eTerm_neg_two_thirds,
    eTerm_neg_one]
  push_cast
  ring

/-- `|2 + 2e(1/3)| = 2`, which is above `√3 = cot(π/6)`. -/
theorem norm_expSum_cLast : ‖expSum cLast 3‖ = 2 := by
  rw [expSum_cLast, Complex.norm_add_mul_I, Real.sq_sqrt (by norm_num), show (1 : ℝ) ^ 2 + 3 = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem norm_expSum_cCells : ‖expSum cCells 4‖ = Real.sqrt 13 := by
  rw [expSum_cCells, Complex.norm_add_mul_I]
  congr 1
  norm_num

theorem norm_expSum_cNeg : ‖expSum cNeg 2‖ = Real.sqrt 3 := by
  rw [expSum_cNeg, Complex.norm_add_mul_I]
  congr 1
  linear_combination (1 / 4 : ℝ) * Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

/-! ## The shared hypothesis on data -/

/-- A negative integer shift: the cell with `k = −1`. -/
theorem diffs_cNeg : DiffsMonotoneIn cNeg 2 (-1) (1 / 3) := by
  refine ⟨Or.inl fun n hn => ?_, fun n hn => ?_⟩
  · obtain rfl : n = 0 := by omega
    norm_num [cNeg]
  · interval_cases n <;> norm_num [cNeg]

/-- The differences of `cLast` lie in the cell `[1/3, 2/3]`: its bite is on monotonicity alone. -/
theorem cLast_cell :
    ∀ n < 3, ((0 : ℤ) : ℝ) + 1 / 3 ≤ cLast (n + 1) - cLast n ∧
      cLast (n + 1) - cLast n ≤ ((0 : ℤ) : ℝ) + 1 - 1 / 3 := by
  intro n hn
  interval_cases n <;> norm_num [cLast]

/-- The first comparison of the differences of `cLast` is nondecreasing (`1/3 ≤ 2/3`): its bite is on the last
comparison alone. -/
theorem cLast_first : cLast (0 + 1) - cLast 0 ≤ cLast (0 + 2) - cLast (0 + 1) := by
  norm_num [cLast]

/-- The differences of `cCells` are nondecreasing: its bite is on the cell alone. -/
theorem cCells_mono : ∀ n, n + 1 < 4 → cCells (n + 1) - cCells n ≤ cCells (n + 2) - cCells (n + 1) := by
  intro n hn
  have hn' : n < 3 := by omega
  interval_cases n <;> norm_num [cCells]

/-- Each difference of `cCells` lies in SOME cell `[k + 1/4, k + 3/4]`, with `k` depending on the difference. -/
theorem cCells_cells :
    ∀ n < 4, ∃ k : ℤ, (k : ℝ) + 1 / 4 ≤ cCells (n + 1) - cCells n ∧
      cCells (n + 1) - cCells n ≤ (k : ℝ) + 1 - 1 / 4 := by
  intro n hn
  interval_cases n
  · exact ⟨0, by norm_num [cCells]⟩
  · exact ⟨0, by norm_num [cCells]⟩
  · exact ⟨1, by norm_num [cCells]⟩
  · exact ⟨1, by norm_num [cCells]⟩

/-- **Bite (the last comparison).** The differences `1/3, 2/3, 1/3` are neither nondecreasing (the comparison at
`n = 1`, the last one, fails) nor nonincreasing (the comparison at `n = 0` fails). -/
theorem not_diffs_cLast : ¬ DiffsMonotoneIn cLast 3 0 (1 / 3) := by
  rintro ⟨h | h, -⟩
  · have := h 1 (by norm_num)
    norm_num [cLast] at this
  · have := h 0 (by norm_num)
    norm_num [cLast] at this

/-- **Bite (one cell for all differences).** The differences `1/4` and `7/4` are in no common cell
`[k + 1/4, k + 3/4]`: the first forces `k ≤ 0`, the last forces `k ≥ 1`. -/
theorem not_diffs_cCells : ∀ k : ℤ, ¬ DiffsMonotoneIn cCells 4 k (1 / 4) := by
  rintro k ⟨-, h⟩
  have h0 := (h 0 (by norm_num)).1
  have h3 := (h 3 (by norm_num)).2
  norm_num [cCells] at h0 h3
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have h1' : (1 : ℤ) ≤ k := by exact_mod_cast h1
  have h0' : k ≤ (0 : ℤ) := by exact_mod_cast h0
  omega

/-! ## KL-D and KL-C through the statement constants -/

/-- **KL-D through the statement constant**, negative integer shift `k = −1`: `|S| ≤ √3`, and `norm_expSum_cNeg`
says `|S| = √3`. -/
theorem kl_neg (h : KusminLandauStatement) : ‖expSum cNeg 2‖ ≤ Real.sqrt 3 := by
  have := h cNeg 2 (-1) (1 / 3) (by norm_num) (by norm_num) diffs_cNeg
  rwa [cot_third] at this

/-- **KL-C through the statement constant** at `N = 0`, `λ = 1/2` (the end of the range of `λ`): `1 ≤ 4/π`. -/
theorem klc_one_half (h : KusminLandauTwoOverPiStatement) : (1 : ℝ) ≤ 2 / (Real.pi * (1 / 2)) := by
  have := h cOne 0 0 (1 / 2) (by norm_num) le_rfl (diffs_cOne 0 (1 / 2))
  rwa [expSum_cOne, norm_one] at this

/-! ## KL-F through the statement constant -/

/-- The integers of `[−1/2, 3/2]`: `⌈−1/2⌉ = 0` and `⌊3/2⌋ = 1`. -/
theorem Icc_ceil_floor_neg_half_three_halves : Finset.Icc ⌈(-1 / 2 : ℝ)⌉ ⌊(3 / 2 : ℝ)⌋ = {0, 1} := by
  rw [show ⌈(-1 / 2 : ℝ)⌉ = 0 from Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩,
    show ⌊(3 / 2 : ℝ)⌋ = 1 from Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩]
  decide

/-- There is no integer in `[1/2, 1/2]`: `⌈1/2⌉ = 1 > 0 = ⌊1/2⌋`. -/
theorem Icc_ceil_floor_half_half : Finset.Icc ⌈(1 / 2 : ℝ)⌉ ⌊(1 / 2 : ℝ)⌋ = ∅ := by
  rw [show ⌈(1 / 2 : ℝ)⌉ = 1 from Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩,
    show ⌊(1 / 2 : ℝ)⌋ = 0 from Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩]
  decide

/-- `e(0) + e(1/2) + e(1) = 1 − 1 + 1 = 1`: the sum of KL-F for `f(x) = x/2` on `[0, 2]`. -/
theorem klf_half_sum : ∑ n ∈ Finset.Icc ⌈(0 : ℝ)⌉ ⌊(2 : ℝ)⌋, eTerm ((n : ℝ) / 2) = 1 := by
  rw [Icc_ceil_floor_zero_two, Finset.sum_insert (by decide), Finset.sum_pair (by norm_num)]
  norm_num [eTerm_zero, eTerm_half, eTerm_one]

/-- **Equality datum for KL-F**: for `f(x) = x/2` on `[0, 2]` and `λ = 1/2` the two sides of the conclusion of KL-F,
in its literal form, are equal (both are `1`). -/
theorem klf_half_attained :
    ‖∑ n ∈ Finset.Icc ⌈(0 : ℝ)⌉ ⌊(2 : ℝ)⌋, Complex.exp (↑(2 * Real.pi * ((n : ℝ) / 2)) * Complex.I)‖ =
      Real.cos (Real.pi * (1 / 2) / 2) / Real.sin (Real.pi * (1 / 2) / 2) := by
  rw [cot_half]
  exact (congrArg norm klf_half_sum).trans norm_one

/-- **KL-F through the statement constant**, `f(x) = x/2` on `[0, 2]` (`f′ = 1/2`, `k = 0`, `λ = 1/2`): the sum is
`e(0) + e(1/2) + e(1) = 1`, so `1 ≤ cot(π/4)`, where `cot(π/4) = 1` (`cot_half`, `klf_half_attained`). -/
theorem klf_half (h : KusminLandauDerivStatement) :
    (1 : ℝ) ≤ Real.cos (Real.pi * (1 / 2) / 2) / Real.sin (Real.pi * (1 / 2) / 2) := by
  have h1 := h (fun x => x / 2) (fun _ => 1 / 2) 0 2 0 (1 / 2) (by norm_num) le_rfl
    ⟨by fun_prop, fun x _ => (hasDerivAt_id x).div_const 2⟩ (Or.inl monotoneOn_const)
    (fun x _ => by norm_num)
  have h2 : ‖(1 : ℂ)‖ ≤ _ := klf_half_sum ▸ h1
  rwa [norm_one] at h2

/-- **KL-F through the statement constant**, end points that are not integers: `f(x) = x/4` on `[−1/2, 3/2]`
(`f′ = 1/4`, `k = 0`, `λ = 1/4`). The integers of the interval are `0` and `1`, the sum is `e(0) + e(1/4) = 1 + i`,
so `√2 ≤ cot(π/8)`. -/
theorem klf_fractional (h : KusminLandauDerivStatement) :
    Real.sqrt 2 ≤ Real.cos (Real.pi * (1 / 4) / 2) / Real.sin (Real.pi * (1 / 4) / 2) := by
  have h1 := h (fun x => x / 4) (fun _ => 1 / 4) (-1 / 2) (3 / 2) 0 (1 / 4) (by norm_num) (by norm_num)
    ⟨by fun_prop, fun x _ => (hasDerivAt_id x).div_const 4⟩ (Or.inl monotoneOn_const)
    (fun x _ => by norm_num)
  have hs : ∑ n ∈ Finset.Icc ⌈(-1 / 2 : ℝ)⌉ ⌊(3 / 2 : ℝ)⌋, eTerm ((n : ℝ) / 4) =
      ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I := by
    rw [Icc_ceil_floor_neg_half_three_halves, Finset.sum_pair (by norm_num)]
    rw [Int.cast_zero, Int.cast_one, zero_div, eTerm_zero, eTerm_quarter]
    simp
  have h2 : ‖((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I‖ ≤ _ := hs ▸ h1
  rw [Complex.norm_add_mul_I] at h2
  norm_num at h2
  exact h2

/-- **KL-F through the statement constant**, empty sum: `a = b = 1/2`, `f(x) = x/2`, `k = 0`, `λ = 1/2`. No integer
lies in `[1/2, 1/2]`, the sum over `Finset.Icc ⌈a⌉ ⌊b⌋` is empty and the conclusion is `0 ≤ cot(π/4)`. The literal is
true without the statement (`cot_half`); the datum only records that the statement applies with `⌈a⌉ > ⌊b⌋` and that
its sum is then `0` (compare plant KL-F-f, where the index set is enlarged to `Finset.Icc ⌊a⌋ ⌈b⌉`). -/
theorem klf_empty (h : KusminLandauDerivStatement) :
    (0 : ℝ) ≤ Real.cos (Real.pi * (1 / 2) / 2) / Real.sin (Real.pi * (1 / 2) / 2) := by
  have h1 := h (fun x => x / 2) (fun _ => 1 / 2) (1 / 2) (1 / 2) 0 (1 / 2) (by norm_num) le_rfl
    ⟨by fun_prop, fun x _ => (hasDerivAt_id x).div_const 2⟩ (Or.inl monotoneOn_const)
    (fun x _ => by norm_num)
  rwa [Icc_ceil_floor_half_half, Finset.sum_empty, norm_zero] at h1

end OscInt.API.KusminLandauSanity2
