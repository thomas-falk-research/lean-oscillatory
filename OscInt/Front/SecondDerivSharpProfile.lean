/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Batch VC2, part VC5: `A(w) ≤ 7/2` on `[0, π]` (the frozen statement VC2-N; route `docs/proof-VC2.md`, V8)

With `β = √(2w)`: `sin y ≤ y − y³/6 + y⁵/120 − y⁷/5040 + y⁹/362880` for `y ≥ 0` (seven rounds of "nonnegative
derivative and value `0` at `0`", starting from `1 − y²/2 ≤ cos y`), so
`A(w) ≤ B(β) = (2/3) β³ − (2/105) β⁷ + (2/10395) β¹¹ − (2/2027025) β¹⁵ + (2/654729075) β¹⁹`
(the moments `∫_0^β (β²/2 − u²/2)^n du` come from the recursion `(2n + 3) I_{n+1} = (n + 1) β² I_n`), and
`B ≤ 7/2` on `[0, 51/20]` by six cells; on a cell the positive monomials are bounded by their chords and the negative
ones by their tangents at the midpoint, so that only the two ends of the cell have to be evaluated.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-! ### The Taylor bound for the sine -/

/-- A function that vanishes at `0` and has a nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem vdc2N_nonneg_of_deriv (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x) (h0 : f 0 = 0)
    (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y hy => ?_
    rw [(hd y).deriv]
    rw [interior_Ici] at hy
    exact hg y (le_of_lt hy)
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  rwa [h0] at h

/-- The derivative of `x ^ k / c`, with the exponent and its real value as separate arguments. -/
theorem vdc2N_hasDerivAt_pow (m k : ℕ) (a c y : ℝ) (hk : k = m + 1) (ha : a = m + 1) :
    HasDerivAt (fun x : ℝ => x ^ k / c) (a * y ^ m / c) y := by
  subst hk ha
  have h := (hasDerivAt_pow (m + 1) y).div_const c
  simpa using h

/-- `y − y³/6 ≤ sin y` for `y ≥ 0`. -/
theorem vdc2N_sin3 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.sin x - x + x ^ 3 / 6 := by
  refine vdc2N_nonneg_of_deriv (fun y => Real.sin y - y + y ^ 3 / 6) (fun y => Real.cos y - 1 + y ^ 2 / 2)
    (fun y => ?_) (by simp) (fun y _ => by linarith [Real.one_sub_sq_div_two_le_cos (x := y)]) x hx
  exact (((Real.hasDerivAt_sin y).fun_sub (hasDerivAt_id' y)).fun_add
    (vdc2N_hasDerivAt_pow 2 3 3 6 y rfl (by norm_num))).congr_deriv (by ring)

/-- `cos y ≤ 1 − y²/2 + y⁴/24` for `y ≥ 0`. -/
theorem vdc2N_cos4 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x := by
  refine vdc2N_nonneg_of_deriv (fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    (fun y => Real.sin y - y + y ^ 3 / 6) (fun y => ?_) (by simp) vdc2N_sin3 x hx
  exact ((((hasDerivAt_const y (1 : ℝ)).fun_sub (vdc2N_hasDerivAt_pow 1 2 2 2 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 3 4 4 24 y rfl (by norm_num))).fun_sub (Real.hasDerivAt_cos y)).congr_deriv (by ring)

/-- `sin y ≤ y − y³/6 + y⁵/120` for `y ≥ 0`. -/
theorem vdc2N_sin5 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := by
  refine vdc2N_nonneg_of_deriv (fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y)
    (fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y) (fun y => ?_) (by simp) vdc2N_cos4 x hx
  exact ((((hasDerivAt_id' y).fun_sub (vdc2N_hasDerivAt_pow 2 3 3 6 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 4 5 5 120 y rfl (by norm_num))).fun_sub (Real.hasDerivAt_sin y)).congr_deriv (by ring)

/-- `1 − y²/2 + y⁴/24 − y⁶/720 ≤ cos y` for `y ≥ 0`. -/
theorem vdc2N_cos6 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.cos x - 1 + x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 := by
  refine vdc2N_nonneg_of_deriv (fun y => Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720)
    (fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y) (fun y => ?_) (by simp) vdc2N_sin5 x hx
  exact (((((Real.hasDerivAt_cos y).fun_sub (hasDerivAt_const y (1 : ℝ))).fun_add
    (vdc2N_hasDerivAt_pow 1 2 2 2 y rfl (by norm_num))).fun_sub
    (vdc2N_hasDerivAt_pow 3 4 4 24 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 5 6 6 720 y rfl (by norm_num))).congr_deriv (by ring)

/-- `y − y³/6 + y⁵/120 − y⁷/5040 ≤ sin y` for `y ≥ 0`. -/
theorem vdc2N_sin7 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.sin x - x + x ^ 3 / 6 - x ^ 5 / 120 + x ^ 7 / 5040 := by
  refine vdc2N_nonneg_of_deriv (fun y => Real.sin y - y + y ^ 3 / 6 - y ^ 5 / 120 + y ^ 7 / 5040)
    (fun y => Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720) (fun y => ?_) (by simp) vdc2N_cos6 x hx
  exact (((((Real.hasDerivAt_sin y).fun_sub (hasDerivAt_id' y)).fun_add
    (vdc2N_hasDerivAt_pow 2 3 3 6 y rfl (by norm_num))).fun_sub
    (vdc2N_hasDerivAt_pow 4 5 5 120 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 6 7 7 5040 y rfl (by norm_num))).congr_deriv (by ring)

/-- `cos y ≤ 1 − y²/2 + y⁴/24 − y⁶/720 + y⁸/40320` for `y ≥ 0`. -/
theorem vdc2N_cos8 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x := by
  refine vdc2N_nonneg_of_deriv (fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 - Real.cos y)
    (fun y => Real.sin y - y + y ^ 3 / 6 - y ^ 5 / 120 + y ^ 7 / 5040) (fun y => ?_) (by simp) vdc2N_sin7 x hx
  exact ((((((hasDerivAt_const y (1 : ℝ)).fun_sub (vdc2N_hasDerivAt_pow 1 2 2 2 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 3 4 4 24 y rfl (by norm_num))).fun_sub
    (vdc2N_hasDerivAt_pow 5 6 6 720 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 7 8 8 40320 y rfl (by norm_num))).fun_sub (Real.hasDerivAt_cos y)).congr_deriv (by ring)

/-- `sin y ≤ y − y³/6 + y⁵/120 − y⁷/5040 + y⁹/362880` for `y ≥ 0`. -/
theorem vdc2N_sin9 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x := by
  refine vdc2N_nonneg_of_deriv (fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 + y ^ 9 / 362880 - Real.sin y)
    (fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 - Real.cos y) (fun y => ?_) (by simp)
    vdc2N_cos8 x hx
  exact ((((((hasDerivAt_id' y).fun_sub (vdc2N_hasDerivAt_pow 2 3 3 6 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 4 5 5 120 y rfl (by norm_num))).fun_sub
    (vdc2N_hasDerivAt_pow 6 7 7 5040 y rfl (by norm_num))).fun_add
    (vdc2N_hasDerivAt_pow 8 9 9 362880 y rfl (by norm_num))).fun_sub (Real.hasDerivAt_sin y)).congr_deriv (by ring)

/-! ### The moments `∫_0^β (β²/2 − u²/2)^n du` -/

/-- The moment `∫_0^β (β²/2 − u²/2)^n du`. -/
noncomputable def vdc2N_mom (β : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..β, (β ^ 2 / 2 - u ^ 2 / 2) ^ n

/-- The recursion `(2n + 3) I_{n+1} = (n + 1) β² I_n`, from the derivative of `u (β²/2 − u²/2)^{n+1}`. -/
theorem vdc2N_mom_rec (β a : ℝ) (n k : ℕ) (hk : k = n + 1) (ha : a = n) :
    (2 * a + 3) * vdc2N_mom β k = (a + 1) * β ^ 2 * vdc2N_mom β n := by
  subst hk ha
  have hd : ∀ u ∈ uIcc (0 : ℝ) β, HasDerivAt (fun u : ℝ => u * (β ^ 2 / 2 - u ^ 2 / 2) ^ (n + 1))
      ((2 * (n : ℝ) + 3) * (β ^ 2 / 2 - u ^ 2 / 2) ^ (n + 1) -
        ((n : ℝ) + 1) * β ^ 2 * (β ^ 2 / 2 - u ^ 2 / 2) ^ n) u := by
    intro u _
    have hy : HasDerivAt (fun u : ℝ => β ^ 2 / 2 - u ^ 2 / 2) (-u) u :=
      ((hasDerivAt_const u (β ^ 2 / 2)).fun_sub (vdc2N_hasDerivAt_pow 1 2 2 2 u rfl (by norm_num))).congr_deriv
        (by ring)
    refine ((hasDerivAt_id' u).fun_mul (hy.fun_pow (n + 1))).congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hc : ∀ m : ℕ, Continuous fun u : ℝ => (β ^ 2 / 2 - u ^ 2 / 2) ^ m := fun m => by fun_prop
  have hi1 : IntervalIntegrable (fun u : ℝ => (2 * (n : ℝ) + 3) * (β ^ 2 / 2 - u ^ 2 / 2) ^ (n + 1))
      MeasureTheory.volume 0 β := (continuous_const.mul (hc (n + 1))).intervalIntegrable 0 β
  have hi2 : IntervalIntegrable (fun u : ℝ => ((n : ℝ) + 1) * β ^ 2 * (β ^ 2 / 2 - u ^ 2 / 2) ^ n)
      MeasureTheory.volume 0 β := (continuous_const.mul (hc n)).intervalIntegrable 0 β
  have h : (∫ u in (0 : ℝ)..β, ((2 * (n : ℝ) + 3) * (β ^ 2 / 2 - u ^ 2 / 2) ^ (n + 1) -
      ((n : ℝ) + 1) * β ^ 2 * (β ^ 2 / 2 - u ^ 2 / 2) ^ n)) =
      β * (β ^ 2 / 2 - β ^ 2 / 2) ^ (n + 1) - 0 * (β ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) ^ (n + 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul,
    sub_zero] at h
  unfold vdc2N_mom
  linarith

/-- The odd moments up to the ninth: `I₁ = β³/3`, `I₃ = 2β⁷/35`, `I₅ = 8β¹¹/693`, `I₇ = 16β¹⁵/6435`,
`I₉ = 128β¹⁹/230945`. -/
theorem vdc2N_mom_values (β : ℝ) :
    vdc2N_mom β 1 = 1 / 3 * β ^ 3 ∧ vdc2N_mom β 3 = 2 / 35 * β ^ 7 ∧ vdc2N_mom β 5 = 8 / 693 * β ^ 11 ∧
      vdc2N_mom β 7 = 16 / 6435 * β ^ 15 ∧ vdc2N_mom β 9 = 128 / 230945 * β ^ 19 := by
  have h0 : vdc2N_mom β 0 = β := by simp [vdc2N_mom]
  have h1 : vdc2N_mom β 1 = 1 / 3 * β ^ 3 := by
    linear_combination (1 / 3) * vdc2N_mom_rec β 0 0 1 rfl (by norm_num) + (1 / 3 * β ^ 2) * h0
  have h2 : vdc2N_mom β 2 = 2 / 15 * β ^ 5 := by
    linear_combination (1 / 5) * vdc2N_mom_rec β 1 1 2 rfl (by norm_num) + (2 / 5 * β ^ 2) * h1
  have h3 : vdc2N_mom β 3 = 2 / 35 * β ^ 7 := by
    linear_combination (1 / 7) * vdc2N_mom_rec β 2 2 3 rfl (by norm_num) + (3 / 7 * β ^ 2) * h2
  have h4 : vdc2N_mom β 4 = 8 / 315 * β ^ 9 := by
    linear_combination (1 / 9) * vdc2N_mom_rec β 3 3 4 rfl (by norm_num) + (4 / 9 * β ^ 2) * h3
  have h5 : vdc2N_mom β 5 = 8 / 693 * β ^ 11 := by
    linear_combination (1 / 11) * vdc2N_mom_rec β 4 4 5 rfl (by norm_num) + (5 / 11 * β ^ 2) * h4
  have h6 : vdc2N_mom β 6 = 16 / 3003 * β ^ 13 := by
    linear_combination (1 / 13) * vdc2N_mom_rec β 5 5 6 rfl (by norm_num) + (6 / 13 * β ^ 2) * h5
  have h7 : vdc2N_mom β 7 = 16 / 6435 * β ^ 15 := by
    linear_combination (1 / 15) * vdc2N_mom_rec β 6 6 7 rfl (by norm_num) + (7 / 15 * β ^ 2) * h6
  have h8 : vdc2N_mom β 8 = 128 / 109395 * β ^ 17 := by
    linear_combination (1 / 17) * vdc2N_mom_rec β 7 7 8 rfl (by norm_num) + (8 / 17 * β ^ 2) * h7
  have h9 : vdc2N_mom β 9 = 128 / 230945 * β ^ 19 := by
    linear_combination (1 / 19) * vdc2N_mom_rec β 8 8 9 rfl (by norm_num) + (9 / 19 * β ^ 2) * h8
  exact ⟨h1, h3, h5, h7, h9⟩

/-- The profile at `w = β²/2` is at most the polynomial `B(β)`. -/
theorem vdc2N_profile_le_poly (β : ℝ) (hβ : 0 ≤ β) :
    2 * ∫ u in (0 : ℝ)..β, Real.sin (β ^ 2 / 2 - u ^ 2 / 2) ≤
      2 / 3 * β ^ 3 - 2 / 105 * β ^ 7 + 2 / 10395 * β ^ 11 - 2 / 2027025 * β ^ 15 + 2 / 654729075 * β ^ 19 := by
  have hc : ∀ (m : ℕ) (c : ℝ), IntervalIntegrable (fun u : ℝ => (β ^ 2 / 2 - u ^ 2 / 2) ^ m / c)
      MeasureTheory.volume 0 β := fun m c => (by fun_prop : Continuous _).intervalIntegrable 0 β
  have hs : IntervalIntegrable (fun u : ℝ => Real.sin (β ^ 2 / 2 - u ^ 2 / 2)) MeasureTheory.volume 0 β :=
    (by fun_prop : Continuous _).intervalIntegrable 0 β
  have i1 := (hc 1 1).sub (hc 3 6)
  have i2 := i1.add (hc 5 120)
  have i3 := i2.sub (hc 7 5040)
  have i4 := i3.add (hc 9 362880)
  have hle : (∫ u in (0 : ℝ)..β, Real.sin (β ^ 2 / 2 - u ^ 2 / 2)) ≤
      ∫ u in (0 : ℝ)..β, ((β ^ 2 / 2 - u ^ 2 / 2) ^ 1 / 1 - (β ^ 2 / 2 - u ^ 2 / 2) ^ 3 / 6 +
        (β ^ 2 / 2 - u ^ 2 / 2) ^ 5 / 120 - (β ^ 2 / 2 - u ^ 2 / 2) ^ 7 / 5040 +
        (β ^ 2 / 2 - u ^ 2 / 2) ^ 9 / 362880) := by
    refine intervalIntegral.integral_mono_on hβ hs i4 fun u hu => ?_
    have hy : 0 ≤ β ^ 2 / 2 - u ^ 2 / 2 := by
      have := pow_le_pow_left₀ hu.1 hu.2 2
      linarith
    have := vdc2N_sin9 _ hy
    rw [pow_one, div_one]
    linarith
  rw [intervalIntegral.integral_add i3 (hc 9 362880), intervalIntegral.integral_sub i2 (hc 7 5040),
    intervalIntegral.integral_add i1 (hc 5 120), intervalIntegral.integral_sub (hc 1 1) (hc 3 6),
    intervalIntegral.integral_div, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div] at hle
  obtain ⟨h1, h3, h5, h7, h9⟩ := vdc2N_mom_values β
  unfold vdc2N_mom at h1 h3 h5 h7 h9
  rw [h1, h3, h5, h7, h9] at hle
  linarith

/-! ### The polynomial bound by cells -/

/-- The chord bound for a power on `[l, r]`: `(r − l) β^k ≤ (r − β) l^k + (β − l) r^k`. -/
theorem vdc2N_chord (l r β : ℝ) (hl : 0 ≤ l) (h1 : l ≤ β) (h2 : β ≤ r) (k : ℕ) :
    (r - l) * β ^ k ≤ (r - β) * l ^ k + (β - l) * r ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one]
    linarith
  | succ k ih =>
    have hβ : 0 ≤ β := hl.trans h1
    have hpow : l ^ k ≤ r ^ k := pow_le_pow_left₀ hl (h1.trans h2) k
    have h3 : 0 ≤ (r - β) * (β - l) * (r ^ k - l ^ k) :=
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1)) (sub_nonneg.2 hpow)
    have h4 := mul_le_mul_of_nonneg_left ih hβ
    rw [pow_succ, pow_succ, pow_succ]
    linarith

/-- The tangent bound for a power: `(m + 1) c^m β ≤ β^{m+1} + m c^{m+1}` for `c, β ≥ 0`. -/
theorem vdc2N_tangent (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (m k : ℕ) (a : ℝ) (hk : k = m + 1) (ha : a = m) :
    (a + 1) * c ^ m * β ≤ β ^ k + a * c ^ k := by
  subst hk ha
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := mul_le_mul_of_nonneg_left ih hβ
    have h2 : 0 ≤ ((m : ℝ) + 1) * c ^ m * (β - c) ^ 2 := by positivity
    have e1 : c ^ (m + 1) = c ^ m * c := pow_succ c m
    have e2 : c ^ (m + 1 + 1) = c ^ m * c * c := by rw [pow_succ, pow_succ]
    have e3 : β ^ (m + 1 + 1) = β ^ (m + 1) * β := pow_succ _ _
    rw [e1] at h1
    rw [e2, e3, e1]
    push_cast
    nlinarith [h1, h2]

/-- One cell: on `[l, r]` the chords of the positive monomials and the tangents at `c` of the negative ones
give an affine bound for `B`, so `B ≤ 7/2` on the cell if that bound is at most `7/2` at `l` and at `r`. -/
theorem vdc2N_cell (l r c β : ℝ) (hl : 0 ≤ l) (hlr : l < r) (hc : 0 ≤ c) (h1 : l ≤ β) (h2 : β ≤ r)
    (hL : 2 / 3 * l ^ 3 - 2 / 105 * (7 * c ^ 6 * l - 6 * c ^ 7) + 2 / 10395 * l ^ 11 -
      2 / 2027025 * (15 * c ^ 14 * l - 14 * c ^ 15) + 2 / 654729075 * l ^ 19 ≤ 7 / 2)
    (hR : 2 / 3 * r ^ 3 - 2 / 105 * (7 * c ^ 6 * r - 6 * c ^ 7) + 2 / 10395 * r ^ 11 -
      2 / 2027025 * (15 * c ^ 14 * r - 14 * c ^ 15) + 2 / 654729075 * r ^ 19 ≤ 7 / 2) :
    2 / 3 * β ^ 3 - 2 / 105 * β ^ 7 + 2 / 10395 * β ^ 11 - 2 / 2027025 * β ^ 15 + 2 / 654729075 * β ^ 19 ≤
      7 / 2 := by
  have hβ : 0 ≤ β := hl.trans h1
  have hrl : 0 ≤ r - l := sub_nonneg.2 hlr.le
  have c3 := vdc2N_chord l r β hl h1 h2 3
  have c11 := vdc2N_chord l r β hl h1 h2 11
  have c19 := vdc2N_chord l r β hl h1 h2 19
  have t7 := mul_le_mul_of_nonneg_left (vdc2N_tangent c β hc hβ 6 7 6 rfl (by norm_num)) hrl
  have t15 := mul_le_mul_of_nonneg_left (vdc2N_tangent c β hc hβ 14 15 14 rfl (by norm_num)) hrl
  have eL := mul_le_mul_of_nonneg_left hL (sub_nonneg.2 h2)
  have eR := mul_le_mul_of_nonneg_left hR (sub_nonneg.2 h1)
  refine le_of_mul_le_mul_left ?_ (sub_pos.2 hlr)
  linarith

/-- `B(β) ≤ 7/2` for `0 ≤ β ≤ 51/20`, by six cells. -/
theorem vdc2N_poly_le (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 51 / 20) :
    2 / 3 * β ^ 3 - 2 / 105 * β ^ 7 + 2 / 10395 * β ^ 11 - 2 / 2027025 * β ^ 15 + 2 / 654729075 * β ^ 19 ≤
      7 / 2 := by
  rcases le_total β (17 / 10) with h | h
  · exact vdc2N_cell 0 (17 / 10) (17 / 20) β (by norm_num) (by norm_num) (by norm_num) h0 h
      (by norm_num) (by norm_num)
  rcases le_total β (39 / 20) with h' | h'
  · exact vdc2N_cell (17 / 10) (39 / 20) (73 / 40) β (by norm_num) (by norm_num) (by norm_num) h h'
      (by norm_num) (by norm_num)
  rcases le_total β (21 / 10) with h'' | h''
  · exact vdc2N_cell (39 / 20) (21 / 10) (81 / 40) β (by norm_num) (by norm_num) (by norm_num) h' h''
      (by norm_num) (by norm_num)
  rcases le_total β (9 / 4) with h3 | h3
  · exact vdc2N_cell (21 / 10) (9 / 4) (87 / 40) β (by norm_num) (by norm_num) (by norm_num) h'' h3
      (by norm_num) (by norm_num)
  rcases le_total β (12 / 5) with h4 | h4
  · exact vdc2N_cell (9 / 4) (12 / 5) (93 / 40) β (by norm_num) (by norm_num) (by norm_num) h3 h4
      (by norm_num) (by norm_num)
  · exact vdc2N_cell (12 / 5) (51 / 20) (99 / 40) β (by norm_num) (by norm_num) (by norm_num) h4 h1
      (by norm_num) (by norm_num)

/-- **VC2-N** `A(w) ≤ 7/2` for `0 ≤ w ≤ π`. -/
theorem vdc2ProfileBound_part : Vdc2ProfileBoundStatement := by
  intro w hw
  have hsq : Real.sqrt (2 * w) ^ 2 = 2 * w := Real.sq_sqrt (by linarith [hw.1])
  have hβ : 0 ≤ Real.sqrt (2 * w) := Real.sqrt_nonneg _
  have hw2 : Real.sqrt (2 * w) ^ 2 / 2 = w := by rw [hsq]; ring
  have hle : Real.sqrt (2 * w) ≤ 51 / 20 := by
    by_contra hcon
    have hlt : 51 / 20 < Real.sqrt (2 * w) := lt_of_not_ge hcon
    have hπ := Real.pi_lt_d2
    nlinarith [hw.2]
  have h := vdc2N_profile_le_poly (Real.sqrt (2 * w)) hβ
  rw [hw2] at h
  exact h.trans (vdc2N_poly_le _ hβ hle)

end OscInt.SecondDerivSharpAux
