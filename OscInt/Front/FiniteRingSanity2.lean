/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.FiniteRingSanity

/-! # Second sanity layer for the batch-FR statement constants

Answers the blind pre-proof review of batch FR: mutations of the frozen statements of
`OscInt/Statements/FiniteRing.lean` that the first layer (`OscInt/Front/FiniteRingSanity.lean`) does not detect. Same
discipline (`docs/lessons.md`, rules 8 and 9): a theorem about a frozen statement takes that statement constant as
its only statement hypothesis and concludes on closed data; everything else is an unconditional lemma on data (the
rings of 2, 4 and 6 sites, the chains of 1 and 2 sites, the line kernel at the times `0`, `1/4` and `−1/4`). No
statement of the batch is proved or used otherwise, and every fact about a kernel is for a fixed number of sites.
Planted copies and witnesses of this layer: `docs/replay/plants/2026-11-16-FR-second/`.

Written in scratch by an agent of the lead; lead, agent and reviewers are AI agents of one model family.

What the first layer could not see, and the datum added here:
* **FR-K, the two neighbours of a site.** On the ring of 2 sites `r + 1 ≡ r − 1`, so `R(r + 1) + R(r − 1)` and
  `3 R(r + 1) − R(r − 1)` agree. Here: the equation at `N = 4`, `r = 1` (`R₄(t, 2) ≠ R₄(t, 0)`), with the
  unconditional derivative of `R₄(·, 1)` as a check.
* **FR-K, unit datum where `2 ∣ r` but `N ∤ r`**: `R₄(0, 2) = 0`.
* **FR-U with a datum that is not even**: the mode `iˣ e^{−2is}` on the ring of 4 sites (`iMode`), checked at `x = 1`.
* **FR-P away from `N = 1`, `r = ±1`**: `N = 2`, `r = 2`, `t = 0` (left side `1`), where `e^{ηN} ≠ e^{ηN²}` and
  `cosh(rη) ≠ cosh η`; and **at a negative time**: `N = 1`, `r = 1`, `t = −1/4`, where `‖R₁ − G‖ ≥ 1/2`
  (`ringP_signed_time_false`: the time enters as `|t|`).
* **FC-K at a wall site** (`M = 1`, `x = 2`, `y = 1`: the neighbours `C₁(t; 3, 1) = −e^{−2it}` and
  `C₁(t; 1, 1) = e^{−2it}` cancel), **the unit datum with `y < x`** (`C₂(0; 2, 1) = 0`), **outside the hypotheses**
  (`C₁(0; 1, 3) = C₁(0; 1, −1) = −1`), and **on a bond at every time**: the ring of 6 sites
  (`ringKernel_six`, modes with `cos k = ±1/2`) gives `C₂(t; 1, 1) = C₂(t; 2, 2) = e^{−2it} cos t` and
  `C₂(t; 2, 1) = C₂(t; 1, 2) = i e^{−2it} sin t`, and the equation at `M = 2`, `x = y = 1` has a neighbour term that
  does not vanish.
* **FC-U with a two-term sum**: the solution `twoSiteMode` with the datum `(1, 0)` on the chain of 2 sites, at
  `x = 2`.
* **The line kernel at `t ≠ 0`, with its phase**: `‖G(1/4, 0) − (15/16) e^{−i/2}‖ ≤ 33/25600` and
  `‖G(1/4, 1) − (i/4) e^{−i/2}‖ ≤ 1/36` (Taylor expansion of `e^{i cos(k)/2}` with the remainder of
  `Complex.exp_bound`). The first layer had `G(0, n) = δ_{n,0}` and a lower bound for `‖G(1/4, 0)‖` only: data that
  a kernel without the phase factor `e^{−2it}`, with the time scale `t`, or with the sign of `t` reversed also has.
* **FC-P with a nonzero left side**: `‖C₂(1/4; x, x) − G(1/4, 0)‖ ≥ 1/40` for `x = 1, 2` (sharp form `767/25600`,
  true value `0.03044`), and the instances of FC-P at `M = 2`, `t = 1/4`, `(x, y) = (1, 1)` and `(2, 2)` for every
  `η > 0`, in the literal form of the statement. At `η = 2` the wall term, the ring term, `cosh((x + y)η)` and the
  exponent `2(M + 1)η` each carry the bound (`chainP_eta_two_numbers`), and at `η = log 16` so does the factor `2`
  of `2|t|` (`chainP_half_time_false`).
* Each instance obtained through a statement constant is also checked unconditionally where the data decide it
  (`ringKernel_four_one_hasDerivAt`, `ringK_unit_four_check`, `ringU_iMode_check`, `ringP_two_two_check`,
  `chainKernel_one_wall_two_hasDerivAt`, `chainKernel_two_zero_lower_offdiag`, `chainKernel_two_diag_hasDerivAt`,
  `chainU_two_check`, `chainP_two_check` at `η = 1`): the frozen statements are true on these instances.
* Data for the planted controls only: `R₄(0, 0)`, `R₄(0, −1)`, `R₄(0, −2)`, `iMode 0 (−1) = −i`,
  `2 cosh 2 < e⁴ − 1`, rational bounds for `e²` to `e^{16}`, `‖1 − e^{−i/2}‖ ≥ 15/32`, `‖I(1/4, 1)‖ ≤ 3π/8`,
  `‖I(−1/2, 1) + iπ/2‖ ≤ π/2`, `R₆(4π, 0) = 1`.

What this layer still cannot see (verdicts NOT DETECTED in the plant record): FR-S at `t ≠ 0` (no datum: it needs a
sum of infinitely many line-kernel values), so `G(t, ·) ↦ G(2t, ·)` and `R_N(t, r) ↦ R_N(−t, r)` in FR-S; the wall
term of FC-P at `x ≠ y` (`e^{−(x+y)η} ↦ e^{−2xη}` is not violated on the chain of 2 sites in floating point; a
violation needs `x + y ≤ M`, `x > y`, so the chain of 3 sites at `t ≠ 0`); the denominator `e^{ηN} − 1` against
`e^{ηN}` in FR-P (first run). FC-P outside its four site hypotheses has no datum and no known violation.
-/

namespace OscInt.API.FiniteRingSanity2

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.LatticeExplicitSanity OscInt.API.LatticeCubeRootSanity
  OscInt.API.PeriodicAnalyticSanity OscInt.API.FiniteRingSanity

/-! ## FR-K: distinct neighbours, and a unit datum at `2 ∣ r`, `N ∤ r` (ring of 4 sites) -/

/-- **Datum (unconditional): the time derivative of `R₄(·, 1) = (1 − e^{−4is}) / 4`** is `i e^{−4it}`. The check of
`ringK_four_deriv` and the second derivative at one point in the planted control K1. -/
theorem ringKernel_four_one_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => ringKernel 4 s 1) (Complex.I * Complex.exp (↑(-(4 * t)) * Complex.I)) t := by
  have hf : (fun s : ℝ => ringKernel 4 s 1) = fun s : ℝ => (1 - Complex.exp (↑(-(4 * s)) * Complex.I)) / 4 := by
    funext s; rw [ringKernel_four_one]
  rw [hf]
  convert ((hasDerivAt_exp_neg 4 t).const_sub 1).div_const 4 using 1
  push_cast; ring

/-- **FR-K through the statement constant**, equation at a site with two different neighbours: at `N = 4`, `r = 1`
the derivative of `s ↦ R₄(s, 1)` is `i (R₄(t, 2) + R₄(t, 0) − 2 R₄(t, 1)) = i e^{−4it}`. On the ring of 2 sites the two
neighbours of a site are the same site, so the first layer cannot tell `R(r + 1) + R(r − 1)` from
`3 R(r + 1) − R(r − 1)`. Plant detected: K1. -/
theorem ringK_four_deriv (h : RingKernelStatement) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ringKernel 4 s 1) (Complex.I * Complex.exp (↑(-(4 * t)) * Complex.I)) t := by
  have h1 := (h 4 t 1 (by norm_num)).1
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, ringKernel_four_two,
    ringKernel_four_zero, ringKernel_four_one] at h1
  convert h1 using 1
  ring

/-- **FR-K through the statement constant**, unit datum on the ring of 4 sites: `R₄(0, 2) = 0` (`2 ∣ 2` but `4 ∤ 2`)
and `R₄(0, 4) = 1`. Plant detected: K2 (`N ∣ r ↦ 2 ∣ r`, which the first layer's unit data, on the ring of 2 sites,
cannot see). -/
theorem ringK_unit_four (h : RingKernelStatement) : ringKernel 4 0 2 = 0 ∧ ringKernel 4 0 4 = 1 := by
  have h1 := (h 4 0 2 (by norm_num)).2.1
  have h2 := (h 4 0 4 (by norm_num)).2.1
  rw [ite_eq_right (by norm_num)] at h1
  rw [ite_eq_left (by norm_num)] at h2
  exact ⟨h1, h2⟩

/-- **Check (unconditional)**: the instance of FR-K in `ringK_unit_four` is true on the data. -/
theorem ringK_unit_four_check : ringKernel 4 0 2 = 0 ∧ ringKernel 4 0 4 = 1 :=
  ⟨ringKernel_four_time_zero.2.1, ringKernel_four_time_zero.2.2.2⟩

/-! ## FR-U with a datum that is not even (ring of 4 sites, the mode `iˣ e^{−2is}`) -/

/-- `R₄(t, −2) = (1 − 2 e^{−2it} + e^{−4it}) / 4`. -/
theorem ringKernel_four_neg_two (t : ℝ) :
    ringKernel 4 t (-2) =
      (1 - 2 * Complex.exp (↑(-(2 * t)) * Complex.I) + Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; norm_num [zpow_neg, zpow_ofNat]; ring

/-- `R₄(t, 4) = (1 + 2 e^{−2it} + e^{−4it}) / 4`. -/
theorem ringKernel_four_four (t : ℝ) :
    ringKernel 4 t 4 =
      (1 + 2 * Complex.exp (↑(-(2 * t)) * Complex.I) + Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; norm_num [zpow_ofNat, Complex.I_pow_four]

/-- **FR-U through the statement constant** at `N = 4` and the mode `k = π/2`, `u(s, x) = iˣ e^{−2is}`, whose datum
`(1, i, −1, −i)` is not even in the site: the kernel sum over the period `{0, 1, 2, 3}`. Both data of the first layer
(`piMode`, the constant) are even, so it cannot tell `u(0, y)` from `u(0, −y)`. Plant detected: U1. -/
theorem ringU_iMode (h : RingUniqueStatement) (t : ℝ) (x : ℤ) :
    iMode t x = ∑ y ∈ Finset.range 4, ringKernel 4 t (x - (y : ℤ)) * iMode 0 (y : ℤ) :=
  h 4 iMode (by norm_num) iMode_periodic iMode_hasDerivAt t x

/-- **Check (unconditional)**: the instance of FR-U in `ringU_iMode` is true at the site `x = 1`: the left side is
`i e^{−2it}` and the right side is `R₄(t, 1) + i R₄(t, 0) − R₄(t, −1) − i R₄(t, −2) = i e^{−2it}`. -/
theorem ringU_iMode_check (t : ℝ) :
    iMode t 1 = ∑ y ∈ Finset.range 4, ringKernel 4 t (1 - (y : ℤ)) * iMode 0 (y : ℤ) := by
  obtain ⟨m0, m1, m2, m3⟩ := iMode_zero
  have e0 : (1 : ℤ) - ((0 : ℕ) : ℤ) = 1 := by norm_num
  have e1 : (1 : ℤ) - ((1 : ℕ) : ℤ) = 0 := by norm_num
  have e2 : (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 := by norm_num
  have e3 : (1 : ℤ) - ((3 : ℕ) : ℤ) = -2 := by norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, e0, e1, e2, e3,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.cast_ofNat, m0, m1, m2, m3, ringKernel_four_one,
    ringKernel_four_zero, ringKernel_four_neg_one, ringKernel_four_neg_two, iMode, zpow_one]
  ring

/-- **Data for the planted control U1**: `R₄(0, 0) = 1` and `R₄(0, −1) = R₄(0, −2) = 0`. -/
theorem ringKernel_four_time_zero_neg :
    ringKernel 4 0 0 = 1 ∧ ringKernel 4 0 (-1) = 0 ∧ ringKernel 4 0 (-2) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ringKernel_four_zero]; norm_num
  · rw [ringKernel_four_neg_one]; simp
  · rw [ringKernel_four_neg_two]; norm_num

/-- **Datum for the planted control U1**: `iMode 0 (−1) = i^{−1} = −i`, not `iMode 0 1 = i`. -/
theorem iMode_zero_neg_one : iMode 0 (-1) = -Complex.I := by
  norm_num [iMode, zpow_neg]

/-! ## FR-P away from `N = 1`, with `r ≠ ±1`, and at a negative time -/

/-- **Datum: ring of 2 sites against the line at time 0**, `r = 2`: `R₂(0, 2) − G(0, 2) = 1 − 0`. -/
theorem ring_two_sub_line_zero : ringKernel 2 0 2 - lineKernel 0 2 = 1 := by
  rw [ringKernel_two, lineKernel_zero, ite_eq_left (by decide), ite_eq_right (by norm_num)]
  norm_num

/-- **FR-P through the statement constant** at `N = 2`, `t = 0`, `r = 2`, in the literal form of the statement:
`|R₂(0, 2) − G(0, 2)| = 1`. Every FR-P datum of the first layer has `N = 1` and `r = ±1`, where `e^{ηN}` and
`e^{ηN²}` agree and `cosh(rη) = cosh η`. Plants detected: P1, P2. -/
theorem ringP_two_two (h : RingFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    (1 : ℝ) ≤ 2 * Real.exp (2 * |(0 : ℝ)| * Real.sinh η) * Real.cosh (((2 : ℤ) : ℝ) * η) /
      (Real.exp (η * ((2 : ℕ) : ℝ)) - 1) := by
  have h1 := h 2 0 η 2 (by norm_num) hη
  rw [ring_two_sub_line_zero, norm_one] at h1
  exact h1

/-- **Check (unconditional)**: the instance of FR-P in `ringP_two_two` is true:
`e^{2η} − 1 ≤ e^{2η} + e^{−2η} = 2 cosh 2η`. -/
theorem ringP_two_two_check (η : ℝ) (hη : 0 < η) :
    (1 : ℝ) ≤ 2 * Real.exp (2 * |(0 : ℝ)| * Real.sinh η) * Real.cosh (((2 : ℤ) : ℝ) * η) /
      (Real.exp (η * ((2 : ℕ) : ℝ)) - 1) := by
  have h0 : 0 < η * ((2 : ℕ) : ℝ) := by positivity
  have h1 : 0 < Real.exp (η * ((2 : ℕ) : ℝ)) - 1 := by linarith [Real.add_one_lt_exp h0.ne']
  rw [le_div_iff₀ h1, abs_zero, mul_zero, zero_mul, Real.exp_zero, mul_one, Real.cosh_eq, Int.cast_ofNat,
    Nat.cast_ofNat, mul_comm η 2]
  linarith [Real.exp_pos (-(2 * η))]

/-- **Bite: `2 cosh 2 < e⁴ − 1`**, so `1 ≤ 2 cosh 2 / (e⁴ − 1)` is false: the bound of FR-P at `N = 2`, `t = 0`,
`r = 2` with `e^{ηN²}` in place of `e^{ηN}` at `η = 1` (plant P1), and with `cosh η` in place of `cosh(rη)` at `η = 2`
(plant P2). -/
theorem two_cosh_two_lt : 2 * Real.cosh 2 < Real.exp 4 - 1 := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hy : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  have hy0 := Real.exp_pos (-2)
  have hy1 : Real.exp (-2) ≤ 1 := by nlinarith
  rw [h4, Real.cosh_eq]
  nlinarith

/-- **Datum at a negative time**: `‖G(−1/4, 1)‖ ≤ 1/2`, from `‖I(−1/2, 1) + iπ/2‖ ≤ π/2` (batch PA sanity). -/
theorem lineKernel_neg_quarter_one_le : ‖lineKernel (-1 / 4) 1‖ ≤ 1 / 2 := by
  have h := latticeKernel1_one_approx (-1 / 2) (by rw [abs_le]; constructor <;> norm_num)
  have h2 := norm_le_norm_add_norm_sub' (latticeKernel1 (-1 / 2) 1)
    ((Real.pi : ℂ) * ((-1 / 2 : ℝ) : ℂ) * Complex.I)
  have h3 : ‖(Real.pi : ℂ) * ((-1 / 2 : ℝ) : ℂ) * Complex.I‖ = Real.pi / 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_neg (by norm_num)]
    ring
  have h4 : 2 * Real.pi * (-1 / 2 : ℝ) ^ 2 = Real.pi / 2 := by ring
  rw [h3] at h2
  rw [h4] at h
  rw [lineKernel, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), Int.cast_one, show (2 : ℝ) * (-1 / 4) = -1 / 2 by norm_num,
    inv_mul_le_iff₀ (by positivity)]
  linarith

/-- **Datum at a negative time: ring of 1 site against the line**, `t = −1/4`, `r = 1`:
`|R₁ − G| ≥ 1 − |G| ≥ 1/2`. The witness datum of the planted control P3. -/
theorem ring_one_sub_line_lower : 1 / 2 ≤ ‖ringKernel 1 (-1 / 4) 1 - lineKernel (-1 / 4) 1‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (lineKernel (-1 / 4) 1)
  rw [norm_one] at h
  rw [ringKernel_one]
  linarith [lineKernel_neg_quarter_one_le]

/-- **FR-P through the statement constant** at `N = 1`, `r = 1` and the negative time `t = −1/4`, in the literal form
of the statement (`ringP_time` of the first layer at a concrete negative time): the time enters as `|t|`. -/
theorem ringP_neg_time (h : RingFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    ‖1 - lineKernel (-1 / 4) 1‖ ≤
      2 * Real.exp (2 * |(-1 / 4 : ℝ)| * Real.sinh η) * Real.cosh (((1 : ℤ) : ℝ) * η) /
        (Real.exp (η * ((1 : ℕ) : ℝ)) - 1) := by
  have h1 := h 1 (-1 / 4) η 1 (by norm_num) hη
  rw [ringKernel_one] at h1
  exact h1

/-- **FR-P through the statement constant** at `N = 1`, `r = 1`, `t = −1/4` with the left side bounded below on
data: `1/2 ≤` the bound, for every `η > 0`. Plant detected: P3 (`|t| ↦ t`: at `η = 3` the planted bound is
`2 e^{−sinh(3)/2} cosh 3 / (e³ − 1) < 0.01`). -/
theorem ringP_neg_time_half (h : RingFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    1 / 2 ≤ 2 * Real.exp (2 * |(-1 / 4 : ℝ)| * Real.sinh η) * Real.cosh (((1 : ℤ) : ℝ) * η) /
        (Real.exp (η * ((1 : ℕ) : ℝ)) - 1) :=
  ring_one_sub_line_lower.trans (h 1 (-1 / 4) η 1 (by norm_num) hη)

/-- **Bite: the time enters the bound of FR-P as `|t|`.** At `N = 1`, `r = 1`, `t = −1/4`, `η = 3` the bound with
`t` in place of `|t|` is `2 e^{−sinh(3)/2} cosh 3 / (e³ − 1) < 0.01`, below the left side `≥ 1/2`. -/
theorem ringP_signed_time_false :
    ¬ ‖ringKernel 1 (-1 / 4) 1 - lineKernel (-1 / 4) 1‖ ≤
      2 * Real.exp (2 * (-1 / 4 : ℝ) * Real.sinh 3) * Real.cosh (((1 : ℤ) : ℝ) * 3) /
        (Real.exp (3 * ((1 : ℕ) : ℝ)) - 1) := by
  intro h
  have hx : (17 / 2 : ℝ) ≤ Real.exp 3 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 3) (by norm_num)
    linarith
  have hy : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; norm_num
  have hy0 := Real.exp_pos (-3)
  have hy1 : Real.exp (-3) ≤ 1 := by nlinarith
  have hs : 2 * (-1 / 4 : ℝ) * Real.sinh 3 ≤ -(15 / 8) := by rw [Real.sinh_eq]; linarith
  have hq : (4 : ℝ) ≤ Real.exp (15 / 8) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 15 / 8) (by norm_num)
    norm_num at this
    linarith
  have hz : Real.exp (-(15 / 8)) * Real.exp (15 / 8) = 1 := by rw [← Real.exp_add]; norm_num
  have hz0 := Real.exp_pos (-(15 / 8))
  have hE : Real.exp (2 * (-1 / 4 : ℝ) * Real.sinh 3) ≤ 1 / 4 := by
    refine (Real.exp_le_exp.mpr hs).trans ?_
    nlinarith
  have hE0 := Real.exp_pos (2 * (-1 / 4 : ℝ) * Real.sinh 3)
  have h1 := ring_one_sub_line_lower.trans h
  rw [Int.cast_one, one_mul, Nat.cast_one, mul_one, le_div_iff₀ (by linarith), Real.cosh_eq] at h1
  have h2 := mul_le_mul_of_nonneg_right hE (by linarith : (0 : ℝ) ≤ Real.exp 3 + Real.exp (-3))
  linarith

/-! ## FC-K at a wall site, off the diagonal, and outside its hypotheses -/

/-- **Datum, chain of 1 site, the site beyond the right wall.** `C₁(t; 3, 1) = R₄(t, 2) − R₄(t, 4) = −e^{−2it}`: the
odd reflection of `C₁(t; 1, 1)` in the wall `x = 2`. -/
theorem chainKernel_one_three (t : ℝ) : chainKernel 1 t 3 1 = -Complex.exp (↑(-(2 * t)) * Complex.I) := by
  have h : chainKernel 1 t 3 1 = ringKernel 4 t 2 - ringKernel 4 t 4 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_two, ringKernel_four_four]; ring

/-- **FC-K through the statement constant**, equation at the wall site `x = 2` of the chain of 1 site (`y = 1`):
the equation reads `∂_t C₁(t; 2, 1) = i (C₁(t; 3, 1) + C₁(t; 1, 1) − 2 C₁(t; 2, 1)) = i (−e^{−2it} + e^{−2it} − 0) = 0`.
At `x = y = 1` (first layer) both neighbours are walls and vanish, so the sign of a neighbour is not seen there.
Plant detected: CK1. -/
theorem chainK_one_wall_site (h : ChainKernelStatement) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chainKernel 1 s 2 1) 0 t := by
  have h1 := (h 1 t 2 1 le_rfl (by norm_num)).1
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, chainKernel_one_three,
    chainKernel_one, chainKernel_one_wall_two] at h1
  convert h1 using 1
  ring

/-- **Check (unconditional)**: the instance of FC-K in `chainK_one_wall_site` is true: `C₁(·; 2, 1) = 0`. -/
theorem chainKernel_one_wall_two_hasDerivAt (t : ℝ) : HasDerivAt (fun s : ℝ => chainKernel 1 s 2 1) 0 t := by
  have hf : (fun s : ℝ => chainKernel 1 s 2 1) = fun _ : ℝ => (0 : ℂ) := by
    funext s; rw [chainKernel_one_wall_two]
  rw [hf]
  exact hasDerivAt_const t 0

/-- **Datum: the hypothesis `y ≤ M` of FC-K carries content.** `C₁(0; 1, 3) = R₄(0, −2) − R₄(0, 4) = −1`, not the
unit datum `δ_{1,3} = 0`. The witness datum of the planted control CK4. -/
theorem chainKernel_one_source_three : chainKernel 1 0 1 3 = -1 := by
  have h : chainKernel 1 0 1 3 = ringKernel 4 0 (-2) - ringKernel 4 0 4 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_neg_two, ringKernel_four_four]; norm_num

/-- **Datum: the hypothesis `1 ≤ y` of FC-K carries content.** `C₁(0; 1, −1) = R₄(0, 2) − R₄(0, 0) = −1`, not the
unit datum `δ_{1,−1} = 0`. The witness datum of the planted control CK5. -/
theorem chainKernel_one_source_neg_one : chainKernel 1 0 1 (-1) = -1 := by
  have h : chainKernel 1 0 1 (-1) = ringKernel 4 0 2 - ringKernel 4 0 0 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_two, ringKernel_four_zero]; norm_num

/-- `R₆(0, 1) = 0`. -/
theorem ringKernel_six_zero_one : ringKernel 6 0 1 = 0 := by
  have hθ : ((1 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 3 := by push_cast; ring
  rw [ringKernel_six_time_zero, hθ, sum_pow_root, mul_zero]
  · intro hw
    have h1 := congrArg Complex.re hw
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three] at h1
    norm_num at h1
  · rw [← Complex.exp_nat_mul,
      show ((6 : ℕ) : ℂ) * (↑(Real.pi / 3) * Complex.I) = 2 * ↑Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]

/-- **Datum: chain of 2 sites at time 0, off the diagonal with `y < x`.** `C₂(0; 2, 1) = R₆(0, 1) − R₆(0, 3) = 0`:
the check of `chainK_two_lower_offdiag` and the witness datum of the planted control CK2. -/
theorem chainKernel_two_zero_lower_offdiag : chainKernel 2 0 2 1 = 0 := by
  have h : chainKernel 2 0 2 1 = ringKernel 6 0 1 - ringKernel 6 0 3 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_zero_one, ringKernel_six_zero_three, sub_zero]

/-- **FC-K through the statement constant**, unit datum off the diagonal with `y < x` on the chain of 2 sites:
`C₂(0; 2, 1) = 0`. The first layer has the unit datum at `x = y` and at `x < y` only. Plant detected: CK2
(`x = y ↦ y ≤ x`). -/
theorem chainK_two_lower_offdiag (h : ChainKernelStatement) : chainKernel 2 0 2 1 = 0 := by
  obtain ⟨-, -, -, hu⟩ := h 2 0 2 1 le_rfl (by norm_num)
  have h1 := hu (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at h1
  exact h1

/-! ## The ring of 6 sites and the chain of 2 sites at every time -/

/-- `w = e^{iπ/3}`, the primitive sixth root of unity: the modes of the ring of 6 sites are `1, w, w², −1, −w, −w²`. -/
noncomputable def sixRoot : ℂ := Complex.exp (↑(Real.pi / 3) * Complex.I)

/-- `w² = w − 1`, from `w + w⁻¹ = 2 cos(π/3) = 1`. -/
theorem sixRoot_sq : sixRoot ^ 2 = sixRoot - 1 := by
  have h1 : Complex.exp (-↑(Real.pi / 3) * Complex.I) * sixRoot = 1 := by
    rw [sixRoot, ← Complex.exp_add]; simp
  have hc : Complex.cos (↑(Real.pi / 3)) = 1 / 2 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_three]; norm_num
  rw [Complex.cos] at hc
  rw [sixRoot] at h1 ⊢
  linear_combination (2 * Complex.exp (↑(Real.pi / 3) * Complex.I)) * hc - h1

/-- The modes `k = 2π/3, 4π/3, 5π/3` of the ring of 6 sites: `e^{ik} = w², −w, −w²`. -/
theorem sixRoot_modes :
    Complex.exp (↑(2 * (Real.pi / 3)) * Complex.I) = sixRoot ^ 2 ∧
      Complex.exp (↑(4 * (Real.pi / 3)) * Complex.I) = -sixRoot ∧
      Complex.exp (↑(5 * (Real.pi / 3)) * Complex.I) = -sixRoot ^ 2 := by
  have h2 : Complex.exp (↑(2 * (Real.pi / 3)) * Complex.I) = sixRoot ^ 2 := by
    rw [sixRoot, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨h2, ?_, ?_⟩
  · rw [show (↑(4 * (Real.pi / 3)) : ℂ) * Complex.I = ↑Real.pi * Complex.I + ↑(Real.pi / 3) * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I, sixRoot]
    ring
  · rw [show (↑(5 * (Real.pi / 3)) : ℂ) * Complex.I = ↑Real.pi * Complex.I + ↑(2 * (Real.pi / 3)) * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I, h2]
    ring

/-- `cos(2π/3) = cos(4π/3) = −1/2` and `cos(5π/3) = 1/2`. -/
theorem cos_third_pi_multiples :
    Real.cos (2 * (Real.pi / 3)) = -1 / 2 ∧ Real.cos (4 * (Real.pi / 3)) = -1 / 2 ∧
      Real.cos (5 * (Real.pi / 3)) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.cos_two_mul, Real.cos_pi_div_three]; norm_num
  · rw [show 4 * (Real.pi / 3) = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num
  · rw [show 5 * (Real.pi / 3) = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub, Real.cos_pi_div_three]

/-- **Datum, ring of 6 sites.** With `w = e^{iπ/3}`:
`R₆(t, r) = (1 + (wʳ + (−w²)ʳ) e^{−it} + (w²ʳ + (−w)ʳ) e^{−3it} + (−1)ʳ e^{−4it}) / 6`: the modes `k = jπ/3` with
`cos k = 1, 1/2, −1/2, −1, −1/2, 1/2`. -/
theorem ringKernel_six (t : ℝ) (r : ℤ) :
    ringKernel 6 t r = (1 + (sixRoot ^ r + (-sixRoot ^ 2) ^ r) * Complex.exp (↑(-t) * Complex.I) +
      ((sixRoot ^ 2) ^ r + (-sixRoot) ^ r) * Complex.exp (↑(-(3 * t)) * Complex.I) +
      (-1) ^ r * Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  have hθ1 : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi / 3 := by push_cast; ring
  have hθ2 : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 2 * (Real.pi / 3) := by push_cast; ring
  have hθ3 : 2 * Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi := by push_cast; ring
  have hθ4 : 2 * Real.pi * ((4 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 4 * (Real.pi / 3) := by push_cast; ring
  have hθ5 : 2 * Real.pi * ((5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 5 * (Real.pi / 3) := by push_cast; ring
  obtain ⟨z2, z4, z5⟩ := sixRoot_modes
  obtain ⟨c2, c4, c5⟩ := cos_third_pi_multiples
  have h1 := exp_mode t (Real.pi / 3) (1 / 2) r sixRoot Real.cos_pi_div_three rfl
  have h2 := exp_mode t (2 * (Real.pi / 3)) (-1 / 2) r (sixRoot ^ 2) c2 z2
  have h3 := exp_mode t Real.pi (-1) r (-1) Real.cos_pi Complex.exp_pi_mul_I
  have h4 := exp_mode t (4 * (Real.pi / 3)) (-1 / 2) r (-sixRoot) c4 z4
  have h5 := exp_mode t (5 * (Real.pi / 3)) (1 / 2) r (-sixRoot ^ 2) c5 z5
  rw [show 2 * t * ((1 / 2 : ℝ) - 1) = -t by ring] at h1 h5
  rw [show 2 * t * ((-1 / 2 : ℝ) - 1) = -(3 * t) by ring] at h2 h4
  rw [show 2 * t * ((-1 : ℝ) - 1) = -(4 * t) by ring] at h3
  rw [ringKernel, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, hθ1, hθ2, hθ3, hθ4, hθ5, h1, h2, h3, h4, h5]
  simp
  ring

/-- `R₆(t, 0) = (1 + 2 e^{−it} + 2 e^{−3it} + e^{−4it}) / 6`. -/
theorem ringKernel_six_site_zero (t : ℝ) :
    ringKernel 6 t 0 = (1 + 2 * Complex.exp (↑(-t) * Complex.I) + 2 * Complex.exp (↑(-(3 * t)) * Complex.I) +
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  rw [ringKernel_six]; simp only [zpow_zero]; ring

/-- `R₆(t, 1) = (1 + e^{−it} − e^{−3it} − e^{−4it}) / 6`. -/
theorem ringKernel_six_site_one (t : ℝ) :
    ringKernel 6 t 1 = (1 + Complex.exp (↑(-t) * Complex.I) - Complex.exp (↑(-(3 * t)) * Complex.I) -
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  rw [ringKernel_six]; simp only [zpow_one]
  linear_combination
    ((Complex.exp (↑(-(3 * t)) * Complex.I) - Complex.exp (↑(-t) * Complex.I)) / 6) * sixRoot_sq

/-- `R₆(t, −1) = (1 + e^{−it} − e^{−3it} − e^{−4it}) / 6`. -/
theorem ringKernel_six_site_neg_one (t : ℝ) :
    ringKernel 6 t (-1) = (1 + Complex.exp (↑(-t) * Complex.I) - Complex.exp (↑(-(3 * t)) * Complex.I) -
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  have i1 : sixRoot⁻¹ = 1 - sixRoot := inv_eq_of_mul_eq_one_right (by linear_combination -sixRoot_sq)
  have i2 : (-sixRoot ^ 2)⁻¹ = sixRoot :=
    inv_eq_of_mul_eq_one_right (by linear_combination (-sixRoot - 1) * sixRoot_sq)
  have i3 : (sixRoot ^ 2)⁻¹ = -sixRoot :=
    inv_eq_of_mul_eq_one_right (by linear_combination (-sixRoot - 1) * sixRoot_sq)
  have i4 : (-sixRoot)⁻¹ = sixRoot - 1 := inv_eq_of_mul_eq_one_right (by linear_combination -sixRoot_sq)
  have i5 : (-1 : ℂ)⁻¹ = -1 := by norm_num
  rw [ringKernel_six]; simp only [zpow_neg_one]
  rw [i1, i2, i3, i4, i5]
  ring

/-- `R₆(t, 2) = (1 − e^{−it} − e^{−3it} + e^{−4it}) / 6`. -/
theorem ringKernel_six_site_two (t : ℝ) :
    ringKernel 6 t 2 = (1 - Complex.exp (↑(-t) * Complex.I) - Complex.exp (↑(-(3 * t)) * Complex.I) +
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  rw [ringKernel_six]; simp only [zpow_ofNat]
  linear_combination ((sixRoot ^ 2 + sixRoot + 1) *
    (Complex.exp (↑(-t) * Complex.I) + Complex.exp (↑(-(3 * t)) * Complex.I)) / 6) * sixRoot_sq

/-- `R₆(t, 3) = (1 − 2 e^{−it} + 2 e^{−3it} − e^{−4it}) / 6`. -/
theorem ringKernel_six_site_three (t : ℝ) :
    ringKernel 6 t 3 = (1 - 2 * Complex.exp (↑(-t) * Complex.I) + 2 * Complex.exp (↑(-(3 * t)) * Complex.I) -
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  rw [ringKernel_six]; simp only [zpow_ofNat]
  linear_combination ((sixRoot ^ 3 - 2) * (sixRoot + 1) *
    (Complex.exp (↑(-(3 * t)) * Complex.I) - Complex.exp (↑(-t) * Complex.I)) / 6) * sixRoot_sq

/-- `R₆(t, 4) = (1 − e^{−it} − e^{−3it} + e^{−4it}) / 6`. -/
theorem ringKernel_six_site_four (t : ℝ) :
    ringKernel 6 t 4 = (1 - Complex.exp (↑(-t) * Complex.I) - Complex.exp (↑(-(3 * t)) * Complex.I) +
      Complex.exp (↑(-(4 * t)) * Complex.I)) / 6 := by
  rw [ringKernel_six]; simp only [zpow_ofNat]
  linear_combination ((sixRoot ^ 4 - sixRoot ^ 2 + 1) * (sixRoot ^ 2 + sixRoot + 1) *
    (Complex.exp (↑(-t) * Complex.I) + Complex.exp (↑(-(3 * t)) * Complex.I)) / 6) * sixRoot_sq

/-- `e^{−2it} cos t = (e^{−it} + e^{−3it}) / 2`. A fact about the exponential; no kernel is mentioned. -/
theorem exp_two_mul_cos (t : ℝ) :
    Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.cos t : ℝ) : ℂ) =
      (Complex.exp (↑(-t) * Complex.I) + Complex.exp (↑(-(3 * t)) * Complex.I)) / 2 := by
  have h1 : Complex.exp (↑(-t) * Complex.I) =
      Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (↑t * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h3 : Complex.exp (↑(-(3 * t)) * Complex.I) =
      Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (-↑t * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, h3, Complex.ofReal_cos, Complex.cos]
  ring

/-- `i e^{−2it} sin t = (e^{−it} − e^{−3it}) / 2`. A fact about the exponential; no kernel is mentioned. -/
theorem exp_two_mul_sin (t : ℝ) :
    Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) =
      (Complex.exp (↑(-t) * Complex.I) - Complex.exp (↑(-(3 * t)) * Complex.I)) / 2 := by
  have h1 : Complex.exp (↑(-t) * Complex.I) =
      Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (↑t * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h3 : Complex.exp (↑(-(3 * t)) * Complex.I) =
      Complex.exp (↑(-(2 * t)) * Complex.I) * Complex.exp (-↑t * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, h3, Complex.ofReal_sin, Complex.sin]
  linear_combination (Complex.exp (↑(-(2 * t)) * Complex.I) *
    (Complex.exp (-↑t * Complex.I) - Complex.exp (↑t * Complex.I)) / 2) * Complex.I_mul_I

/-- **Datum, chain of 2 sites, diagonal.** `C₂(t; 1, 1) = R₆(t, 0) − R₆(t, 2) = e^{−2it} cos t`: the two Dirichlet
modes have the eigenvalues `−1` and `−3`. -/
theorem chainKernel_two_diag (t : ℝ) :
    chainKernel 2 t 1 1 = Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.cos t : ℝ) : ℂ) := by
  have h : chainKernel 2 t 1 1 = ringKernel 6 t 0 - ringKernel 6 t 2 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_zero, ringKernel_six_site_two, exp_two_mul_cos]; ring

/-- **Datum, chain of 2 sites, diagonal at the second site.** `C₂(t; 2, 2) = R₆(t, 0) − R₆(t, 4) = e^{−2it} cos t`. -/
theorem chainKernel_two_diag_two (t : ℝ) :
    chainKernel 2 t 2 2 = Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.cos t : ℝ) : ℂ) := by
  have h : chainKernel 2 t 2 2 = ringKernel 6 t 0 - ringKernel 6 t 4 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_zero, ringKernel_six_site_four, exp_two_mul_cos]; ring

/-- **Datum, chain of 2 sites, off the diagonal.** `C₂(t; 2, 1) = R₆(t, 1) − R₆(t, 3) = i e^{−2it} sin t`. -/
theorem chainKernel_two_off (t : ℝ) :
    chainKernel 2 t 2 1 = Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) := by
  have h : chainKernel 2 t 2 1 = ringKernel 6 t 1 - ringKernel 6 t 3 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_one, ringKernel_six_site_three, exp_two_mul_sin]; ring

/-- **Datum, chain of 2 sites, off the diagonal, transposed.**
`C₂(t; 1, 2) = R₆(t, −1) − R₆(t, 3) = i e^{−2it} sin t`. -/
theorem chainKernel_two_off_transpose (t : ℝ) :
    chainKernel 2 t 1 2 = Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) := by
  have h : chainKernel 2 t 1 2 = ringKernel 6 t (-1) - ringKernel 6 t 3 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_neg_one, ringKernel_six_site_three, exp_two_mul_sin]; ring

/-- **Datum, chain of 2 sites, left wall.** `C₂(t; 0, 1) = R₆(t, −1) − R₆(t, 1) = 0`. -/
theorem chainKernel_two_wall_zero (t : ℝ) : chainKernel 2 t 0 1 = 0 := by
  have h : chainKernel 2 t 0 1 = ringKernel 6 t (-1) - ringKernel 6 t 1 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_neg_one, ringKernel_six_site_one, sub_self]

/-- **Datum, chain of 2 sites, right wall.** `C₂(t; 3, 1) = R₆(t, 2) − R₆(t, 4) = 0`. -/
theorem chainKernel_two_wall_three (t : ℝ) : chainKernel 2 t 3 1 = 0 := by
  have h : chainKernel 2 t 3 1 = ringKernel 6 t 2 - ringKernel 6 t 4 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_site_two, ringKernel_six_site_four, sub_self]

/-- **Datum (unconditional): the time derivative of `C₂(·; 1, 1) = e^{−2is} cos s`** is
`−e^{−2it} (sin t + 2i cos t)`. The check of `chainK_two_bond` and the second derivative at one point in the planted
control CK3. -/
theorem chainKernel_two_diag_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => chainKernel 2 s 1 1)
      (-(Complex.exp (↑(-(2 * t)) * Complex.I) *
        (((Real.sin t : ℝ) : ℂ) + 2 * Complex.I * ((Real.cos t : ℝ) : ℂ)))) t := by
  have hf : (fun s : ℝ => chainKernel 2 s 1 1) =
      fun s : ℝ => Complex.exp (↑(-(2 * s)) * Complex.I) * ((Real.cos s : ℝ) : ℂ) := by
    funext s; rw [chainKernel_two_diag]
  have hc : HasDerivAt (fun s : ℝ => ((Real.cos s : ℝ) : ℂ)) ((-Real.sin t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_cos t).ofReal_comp
  rw [hf]
  convert (hasDerivAt_exp_neg 2 t).mul hc using 1
  push_cast; ring

/-- **FC-K through the statement constant**, equation on a bond: at `M = 2`, `x = y = 1` the right neighbour is a
site of the chain and the left neighbour is a wall, and the equation reads
`∂_t C₂(t; 1, 1) = i (C₂(t; 2, 1) + C₂(t; 0, 1) − 2 C₂(t; 1, 1)) = i (i e^{−2it} sin t + 0 − 2 e^{−2it} cos t)`. On the
chain of 1 site every solution is a multiple of `e^{−2is}`, so a neighbour term is never seen there. Plant detected:
CK3 (both neighbour terms dropped). -/
theorem chainK_two_bond (h : ChainKernelStatement) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chainKernel 2 s 1 1)
      (-(Complex.exp (↑(-(2 * t)) * Complex.I) *
        (((Real.sin t : ℝ) : ℂ) + 2 * Complex.I * ((Real.cos t : ℝ) : ℂ)))) t := by
  have h1 := (h 2 t 1 1 le_rfl (by norm_num)).1
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, chainKernel_two_off,
    chainKernel_two_wall_zero, chainKernel_two_diag] at h1
  convert h1 using 1
  linear_combination (-(Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ))) * Complex.I_mul_I

/-- Datum for FC-U: on the chain of 2 sites, the solution with the datum `(1, 0)`,
`u(s, 1) = e^{−2is} cos s`, `u(s, 2) = i e^{−2is} sin s`, `u = 0` elsewhere. It is not an eigenvector of the site
swap, and its datum distinguishes the two sites. -/
noncomputable def twoSiteMode (s : ℝ) (x : ℤ) : ℂ :=
  if x = 1 then Complex.exp (↑(-(2 * s)) * Complex.I) * ((Real.cos s : ℝ) : ℂ)
  else if x = 2 then Complex.I * Complex.exp (↑(-(2 * s)) * Complex.I) * ((Real.sin s : ℝ) : ℂ) else 0

/-- `twoSiteMode` at the first site. -/
theorem twoSiteMode_one (s : ℝ) :
    twoSiteMode s 1 = Complex.exp (↑(-(2 * s)) * Complex.I) * ((Real.cos s : ℝ) : ℂ) := by
  simp [twoSiteMode]

/-- `twoSiteMode` at the second site. -/
theorem twoSiteMode_two (s : ℝ) :
    twoSiteMode s 2 = Complex.I * Complex.exp (↑(-(2 * s)) * Complex.I) * ((Real.sin s : ℝ) : ℂ) := by
  simp [twoSiteMode]

/-- `twoSiteMode` vanishes at the walls `0` and `3`. -/
theorem twoSiteMode_walls (t : ℝ) : twoSiteMode t 0 = 0 ∧ twoSiteMode t (((2 : ℕ) : ℤ) + 1) = 0 := by
  norm_num [twoSiteMode]

/-- The datum of `twoSiteMode` is `(1, 0)`. -/
theorem twoSiteMode_zero : twoSiteMode 0 1 = 1 ∧ twoSiteMode 0 2 = 0 := by
  rw [twoSiteMode_one, twoSiteMode_two]; simp

/-- `twoSiteMode` solves the equation at the two sites of the chain. -/
theorem twoSiteMode_hasDerivAt (t : ℝ) (x : ℤ) (h1 : 1 ≤ x) (h2 : x ≤ ((2 : ℕ) : ℤ)) :
    HasDerivAt (fun s : ℝ => twoSiteMode s x)
      (Complex.I * (twoSiteMode t (x + 1) + twoSiteMode t (x - 1) - 2 * twoSiteMode t x)) t := by
  have hc : HasDerivAt (fun s : ℝ => ((Real.cos s : ℝ) : ℂ)) ((-Real.sin t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_cos t).ofReal_comp
  have hs : HasDerivAt (fun s : ℝ => ((Real.sin s : ℝ) : ℂ)) ((Real.cos t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_sin t).ofReal_comp
  obtain ⟨w0, w3⟩ := twoSiteMode_walls t
  have hx : x = 1 ∨ x = 2 := by push_cast at h2; omega
  rcases hx with rfl | rfl
  · rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, twoSiteMode_two, w0,
      twoSiteMode_one, funext twoSiteMode_one]
    convert (hasDerivAt_exp_neg 2 t).mul hc using 1
    push_cast
    linear_combination (Complex.exp (-(2 * (t : ℂ)) * Complex.I) * Complex.sin (t : ℂ)) * Complex.I_mul_I
  · rw [show (2 : ℤ) + 1 = ((2 : ℕ) : ℤ) + 1 by norm_num, w3, show (2 : ℤ) - 1 = 1 by norm_num,
      twoSiteMode_one, twoSiteMode_two, funext twoSiteMode_two]
    convert ((hasDerivAt_exp_neg 2 t).const_mul Complex.I).mul hs using 1
    push_cast; ring

/-- **FC-U through the statement constant** at `M = 2`, the solution `twoSiteMode` and the site `x = 2`: the kernel
sum has two terms, `i e^{−2it} sin t = C₂(t; 2, 1) u(0, 1) + C₂(t; 2, 2) u(0, 2)` with the datum `u(0, ·) = (1, 0)`.
The first layer has the chain of 1 site only, where the sum has one term. Plant detected: CU1 (`u(0, y) ↦ u(0, x)`). -/
theorem chainU_two (h : ChainUniqueStatement) (t : ℝ) :
    Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) =
      chainKernel 2 t 2 1 * twoSiteMode 0 1 + chainKernel 2 t 2 2 * twoSiteMode 0 2 := by
  have h1 := h 2 twoSiteMode twoSiteMode_walls twoSiteMode_hasDerivAt t 2 (by norm_num) (by norm_num)
  have hI : Finset.Icc (1 : ℤ) ((2 : ℕ) : ℤ) = {1, 2} := by decide
  rw [hI, Finset.sum_pair (by norm_num), twoSiteMode_two] at h1
  exact h1

/-- **Check (unconditional)**: the instance of FC-U in `chainU_two` is true on the data `chainKernel_two_off`,
`chainKernel_two_diag_two` and the datum `(1, 0)`. -/
theorem chainU_two_check (t : ℝ) :
    Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) =
      chainKernel 2 t 2 1 * twoSiteMode 0 1 + chainKernel 2 t 2 2 * twoSiteMode 0 2 := by
  rw [twoSiteMode_zero.1, twoSiteMode_zero.2, chainKernel_two_off]; ring

/-! ## The line kernel at `t = 1/4`, with its phase -/

/-- `∫_{−π}^{π} cosⁿ k dk` for `n = 1, 2, 3, 4`: `0`, `π`, `0`, `3π/4`. -/
theorem integral_cos_pows :
    (∫ k in (-Real.pi)..Real.pi, Real.cos k) = 0 ∧ (∫ k in (-Real.pi)..Real.pi, Real.cos k ^ 2) = Real.pi ∧
      (∫ k in (-Real.pi)..Real.pi, Real.cos k ^ 3) = 0 ∧
      (∫ k in (-Real.pi)..Real.pi, Real.cos k ^ 4) = 3 * Real.pi / 4 := by
  have h2 : (∫ k in (-Real.pi)..Real.pi, Real.cos k ^ 2) = Real.pi := by
    rw [integral_cos_sq]; simp
  refine ⟨by simp, h2, by simp, ?_⟩
  rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow, h2]
  simp
  ring

/-- Taylor polynomial of degree 4 of `e^{ic}` for real `|c| ≤ 1/2`, with the remainder of `Complex.exp_bound`:
`|e^{ic} − (1 − c²/2 + c⁴/24) − i (c − c³/6)| ≤ |c|⁵ / 100 ≤ 1/3200`. No kernel is mentioned. -/
theorem norm_exp_sub_taylor_four (c : ℝ) (hc : |c| ≤ 1 / 2) :
    ‖Complex.exp (↑c * Complex.I) -
      (((1 - c ^ 2 / 2 + c ^ 4 / 24 : ℝ) : ℂ) + ((c - c ^ 3 / 6 : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / 3200 := by
  have hx : ‖(↑c : ℂ) * Complex.I‖ = |c| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := ↑c * Complex.I) (by rw [hx]; linarith) (n := 5) (by norm_num)
  have hs : ∑ m ∈ Finset.range 5, (↑c * Complex.I) ^ m / (m.factorial : ℂ) =
      ((1 - c ^ 2 / 2 + c ^ 4 / 24 : ℝ) : ℂ) + ((c - c ^ 3 / 6 : ℝ) : ℂ) * Complex.I := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, show Nat.factorial 0 = 1 from rfl, show Nat.factorial 1 = 1 from rfl,
      show Nat.factorial 2 = 2 from rfl, show Nat.factorial 3 = 6 from rfl, show Nat.factorial 4 = 24 from rfl]
    push_cast
    linear_combination ((c : ℂ) ^ 2 / 2 + (c : ℂ) ^ 3 * Complex.I / 6 +
      (c : ℂ) ^ 4 * (Complex.I ^ 2 - 1) / 24) * Complex.I_sq
  have h6 : ((Nat.succ 5 : ℕ) : ℝ) * (((Nat.factorial 5 : ℕ) : ℝ) * ((5 : ℕ) : ℝ))⁻¹ = 1 / 100 := by
    norm_num [Nat.factorial]
  have h5 : |c| ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ (abs_nonneg c) hc 5
  rw [hs, hx, h6] at hb
  norm_num at h5
  linarith

/-- Taylor polynomial of degree 2 of `e^{ic}` for real `|c| ≤ 1/2`, with the remainder of `Complex.exp_bound`:
`|e^{ic} − (1 + ic − c²/2)| ≤ 2|c|³/9 ≤ 1/36`. No kernel is mentioned. -/
theorem norm_exp_sub_taylor_two (c : ℝ) (hc : |c| ≤ 1 / 2) :
    ‖Complex.exp (↑c * Complex.I) - (1 + ↑c * Complex.I - ((c ^ 2 / 2 : ℝ) : ℂ))‖ ≤ 1 / 36 := by
  have hx : ‖(↑c : ℂ) * Complex.I‖ = |c| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := ↑c * Complex.I) (by rw [hx]; linarith) (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (↑c * Complex.I) ^ m / (m.factorial : ℂ) =
      1 + ↑c * Complex.I - ((c ^ 2 / 2 : ℝ) : ℂ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, show Nat.factorial 0 = 1 from rfl,
      show Nat.factorial 1 = 1 from rfl, show Nat.factorial 2 = 2 from rfl]
    push_cast
    linear_combination ((c : ℂ) ^ 2 / 2) * Complex.I_sq
  have h6 : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))⁻¹ = 2 / 9 := by
    norm_num [Nat.factorial]
  have h5 : |c| ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg c) hc 3
  rw [hs, hx, h6] at hb
  norm_num at h5
  linarith

/-- `|cos k / 2| ≤ 1/2`. -/
theorem abs_half_cos_le (k : ℝ) : |1 / 2 * Real.cos k| ≤ 1 / 2 := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith [Real.abs_cos_le_one k]

/-- **Datum: `I(1/2, 0)` to fourth order.** `‖I(1/2, 0) − 2π · 15/16‖ ≤ 2π · 33/25600`: expansion of `e^{i cos(k)/2}`
to degree 4, `∫ cos² = π`, `∫ cos⁴ = 3π/4`, the odd powers integrate to `0`; the error is `π/512` (the term of
degree 4) plus `2π/3200` (the remainder). The first layers had the lower bound `latticeKernel1_zero_freq_lower`
only. -/
theorem latticeKernel1_half_zero_approx :
    ‖latticeKernel1 (1 / 2) 0 - ((2 * Real.pi : ℝ) : ℂ) * ((15 / 16 : ℝ) : ℂ)‖ ≤ 2 * Real.pi * (33 / 25600) := by
  obtain ⟨i1, i2, i3, i4⟩ := integral_cos_pows
  have hp : (∫ k in (-Real.pi)..Real.pi, (1 - 1 / 8 * Real.cos k ^ 2 + 1 / 384 * Real.cos k ^ 4)) =
      2 * Real.pi - Real.pi / 8 + Real.pi / 512 := by
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, i2, i4,
      intervalIntegral.integral_const]
    simp
    ring
  have hq : (∫ k in (-Real.pi)..Real.pi, (1 / 2 * Real.cos k - 1 / 48 * Real.cos k ^ 3)) = 0 := by
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, i1, i3]
    ring
  have hR : ∀ k : ℝ, ‖Complex.exp (↑(1 / 2 * Real.cos k) * Complex.I) -
      (((1 - 1 / 8 * Real.cos k ^ 2 + 1 / 384 * Real.cos k ^ 4 : ℝ) : ℂ) +
        ((1 / 2 * Real.cos k - 1 / 48 * Real.cos k ^ 3 : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / 3200 := by
    intro k
    have h := norm_exp_sub_taylor_four (1 / 2 * Real.cos k) (abs_half_cos_le k)
    rw [show 1 - (1 / 2 * Real.cos k) ^ 2 / 2 + (1 / 2 * Real.cos k) ^ 4 / 24 =
        1 - 1 / 8 * Real.cos k ^ 2 + 1 / 384 * Real.cos k ^ 4 by ring,
      show 1 / 2 * Real.cos k - (1 / 2 * Real.cos k) ^ 3 / 6 =
        1 / 2 * Real.cos k - 1 / 48 * Real.cos k ^ 3 by ring] at h
    exact h
  have hint : latticeKernel1 (1 / 2) 0 - ((2 * Real.pi - Real.pi / 8 + Real.pi / 512 : ℝ) : ℂ) =
      ∫ k in (-Real.pi)..Real.pi, (Complex.exp (↑(1 / 2 * Real.cos k) * Complex.I) -
        (((1 - 1 / 8 * Real.cos k ^ 2 + 1 / 384 * Real.cos k ^ 4 : ℝ) : ℂ) +
          ((1 / 2 * Real.cos k - 1 / 48 * Real.cos k ^ 3 : ℝ) : ℂ) * Complex.I)) := by
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      hp, hq, latticeKernel1]
    simp only [zero_mul, add_zero, Complex.ofReal_zero]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi) (fun k _ => hR k)
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity), ← hint] at hb
  have e : latticeKernel1 (1 / 2) 0 - ((2 * Real.pi : ℝ) : ℂ) * ((15 / 16 : ℝ) : ℂ) =
      (latticeKernel1 (1 / 2) 0 - ((2 * Real.pi - Real.pi / 8 + Real.pi / 512 : ℝ) : ℂ)) +
        ((Real.pi / 512 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith [Real.pi_pos]

/-- `∫_{−π}^{π} cos² k · e^{ik} dk = 0`. -/
theorem integral_cos_sq_mul_exp :
    ∫ k in (-Real.pi)..Real.pi, ((Real.cos k ^ 2 : ℝ) : ℂ) * Complex.exp (↑k * Complex.I) = 0 := by
  have h1 := integral_exp_int_mul 1 one_ne_zero
  have h3 := integral_exp_int_mul 3 (by norm_num)
  have hm := integral_exp_int_mul (-1) (by norm_num)
  have hpt : ∀ k : ℝ, ((Real.cos k ^ 2 : ℝ) : ℂ) * Complex.exp (↑k * Complex.I) =
      1 / 2 * Complex.exp (↑(((1 : ℤ) : ℝ) * k) * Complex.I) +
        1 / 4 * Complex.exp (↑(((3 : ℤ) : ℝ) * k) * Complex.I) +
        1 / 4 * Complex.exp (↑(((-1 : ℤ) : ℝ) * k) * Complex.I) := by
    intro k
    have e1 : Complex.exp (↑(((1 : ℤ) : ℝ) * k) * Complex.I) = Complex.exp (↑k * Complex.I) := by
      congr 1; push_cast; ring
    have e3 : Complex.exp (↑(((3 : ℤ) : ℝ) * k) * Complex.I) =
        Complex.exp (↑k * Complex.I) * Complex.exp (↑k * Complex.I) * Complex.exp (↑k * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have em : Complex.exp (↑(((-1 : ℤ) : ℝ) * k) * Complex.I) = Complex.exp (-↑k * Complex.I) := by
      congr 1; push_cast; ring
    have e' : Complex.exp (-↑k * Complex.I) * Complex.exp (↑k * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [e1, e3, em, Complex.ofReal_pow, Complex.ofReal_cos, Complex.cos]
    linear_combination ((2 * Complex.exp (↑k * Complex.I) + Complex.exp (-↑k * Complex.I)) / 4) * e'
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    h1, h3, hm]
  simp

/-- **Datum: `I(1/2, 1)` to second order.** `‖I(1/2, 1) − iπ/2‖ ≤ 2π/36`: expansion of `e^{i cos(k)/2}` to degree 2
(`∫ e^{ik} = 0`, `∫ cos k e^{ik} = π`, `∫ cos² k e^{ik} = 0`) with the remainder `2|c|³/9`. The first-order bound
`latticeKernel1_one_approx` gives `π/2` here, which is the size of the value itself. -/
theorem latticeKernel1_half_one_approx :
    ‖latticeKernel1 (1 / 2) 1 - ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I‖ ≤
      2 * Real.pi * (1 / 36) := by
  have h1 := integral_exp_int_mul 1 one_ne_zero
  have hR : ∀ k : ℝ, ‖(Complex.exp (↑(1 / 2 * Real.cos k) * Complex.I) -
      (1 + ↑(1 / 2 * Real.cos k) * Complex.I - (((1 / 2 * Real.cos k) ^ 2 / 2 : ℝ) : ℂ))) *
      Complex.exp (↑k * Complex.I)‖ ≤ 1 / 36 := by
    intro k
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_exp_sub_taylor_two _ (abs_half_cos_le k)
  have hdec : ∀ k : ℝ, Complex.exp (↑(1 / 2 * Real.cos k + 1 * k) * Complex.I) =
      Complex.exp (↑(((1 : ℤ) : ℝ) * k) * Complex.I) +
        (1 / 2 * Complex.I) * ((Real.cos k : ℂ) * Complex.exp (↑k * Complex.I)) +
        (-1 / 8) * (((Real.cos k ^ 2 : ℝ) : ℂ) * Complex.exp (↑k * Complex.I)) +
        (Complex.exp (↑(1 / 2 * Real.cos k) * Complex.I) -
          (1 + ↑(1 / 2 * Real.cos k) * Complex.I - (((1 / 2 * Real.cos k) ^ 2 / 2 : ℝ) : ℂ))) *
          Complex.exp (↑k * Complex.I) := by
    intro k
    rw [show (↑(1 / 2 * Real.cos k + 1 * k) : ℂ) * Complex.I =
        ↑(1 / 2 * Real.cos k) * Complex.I + ↑k * Complex.I by push_cast; ring, Complex.exp_add, Int.cast_one,
      one_mul]
    push_cast; ring
  have hint : latticeKernel1 (1 / 2) 1 - ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I =
      ∫ k in (-Real.pi)..Real.pi, (Complex.exp (↑(1 / 2 * Real.cos k) * Complex.I) -
        (1 + ↑(1 / 2 * Real.cos k) * Complex.I - (((1 / 2 * Real.cos k) ^ 2 / 2 : ℝ) : ℂ))) *
        Complex.exp (↑k * Complex.I) := by
    rw [latticeKernel1]
    simp_rw [hdec]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos_mul_exp,
      integral_cos_sq_mul_exp]
    push_cast; ring
  rw [hint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi) (fun k _ => hR k)
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity)] at hb
  linarith

/-- **Datum: the line kernel at `t = 1/4`, `n = 0`, sharp form.** `‖G(1/4, 0) − (15/16) e^{−i/2}‖ ≤ 33/25600`:
`G(t, 0) = e^{−2it} J₀(2t)` and `J₀(1/2) = 1 − 1/16 + 1/1024 − …` (true value of the left side `0.00097`). Pins the
phase factor `e^{−2it}` and the time scale `2t` of `lineKernel`. -/
theorem lineKernel_quarter_zero_approx_sharp :
    ‖lineKernel (1 / 4) 0 - (15 / 16 : ℝ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)‖ ≤ 33 / 25600 := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hc : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hpi
  have h := latticeKernel1_half_zero_approx
  have e : lineKernel (1 / 4) 0 - ((15 / 16 : ℝ) : ℂ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) *
        (latticeKernel1 (1 / 2) 0 - ((2 * Real.pi : ℝ) : ℂ) * ((15 / 16 : ℝ) : ℂ)) := by
    rw [lineKernel, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, Int.cast_zero]
    linear_combination (((15 / 16 : ℝ) : ℂ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)) * hc
  rw [e, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
  exact h

/-- **Datum: the line kernel at `t = 1/4`, `n = 0`**, in the form requested by the lead:
`‖G(1/4, 0) − (15/16) e^{−i/2}‖ ≤ 1/384`. Weaker than `lineKernel_quarter_zero_approx_sharp`. -/
theorem lineKernel_quarter_zero_approx :
    ‖lineKernel (1 / 4) 0 - (15 / 16 : ℝ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)‖ ≤ 1 / 384 :=
  lineKernel_quarter_zero_approx_sharp.trans (by norm_num)

/-- **Datum: the line kernel at `t = 1/4`, `n = 1`, sharp form.** `‖G(1/4, 1) − (i/4) e^{−i/2}‖ ≤ 1/36`:
`G(t, 1) = i e^{−2it} J₁(2t)` and `J₁(1/2) = 1/4 − 1/128 + …`. Pins the sign convention `iⁿ`, and the time scale `2t`
at `n = 1` (the planted control L2 has `‖G′(1/4, 1)‖ ≤ 3/16`, at distance `≥ 1/16` from `i/4`). -/
theorem lineKernel_quarter_one_approx_sharp :
    ‖lineKernel (1 / 4) 1 - (1 / 4 : ℝ) * Complex.I * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)‖ ≤ 1 / 36 := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hc : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hpi
  have h := latticeKernel1_half_one_approx
  have e : lineKernel (1 / 4) 1 - ((1 / 4 : ℝ) : ℂ) * Complex.I * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) *
        (latticeKernel1 (1 / 2) 1 - ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [lineKernel, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, Int.cast_one]
    linear_combination (((1 / 4 : ℝ) : ℂ) * Complex.I * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)) * hc
  rw [e, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **Datum: the line kernel at `t = 1/4`, `n = 1`**, in the form requested by the lead:
`‖G(1/4, 1) − (i/4) e^{−i/2}‖ ≤ 1/8`. Weaker than `lineKernel_quarter_one_approx_sharp`. -/
theorem lineKernel_quarter_one_approx :
    ‖lineKernel (1 / 4) 1 - (1 / 4 : ℝ) * Complex.I * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)‖ ≤ 1 / 8 :=
  lineKernel_quarter_one_approx_sharp.trans (by norm_num)

/-! ## FC-P with a nonzero left side: the chain of 2 sites against the line at `t = 1/4` -/

/-- A number at distance `≥ 767/25600` from `G(1/4, 0)`: `e^{−i/2} cos(1/4)`, since `cos(1/4) ≥ 31/32` and
`‖G(1/4, 0) − (15/16) e^{−i/2}‖ ≤ 33/25600`. -/
theorem sub_lineKernel_quarter_lower (z : ℂ)
    (hz : z = Complex.exp (↑(-(2 * (1 / 4 : ℝ))) * Complex.I) * ((Real.cos (1 / 4) : ℝ) : ℂ)) :
    767 / 25600 ≤ ‖z - lineKernel (1 / 4) 0‖ := by
  have h1 := lineKernel_quarter_zero_approx_sharp
  have hc : 31 / 32 ≤ Real.cos (1 / 4) := by
    have := Real.one_sub_sq_div_two_le_cos (x := 1 / 4)
    norm_num at this
    linarith
  have e : z - lineKernel (1 / 4) 0 =
      ((Real.cos (1 / 4) - 15 / 16 : ℝ) : ℂ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) -
        (lineKernel (1 / 4) 0 - (15 / 16 : ℝ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)) := by
    rw [hz, show (-(2 * (1 / 4)) : ℝ) = -(1 / 2) by norm_num]
    push_cast; ring
  have h2 := norm_sub_norm_le
    (((Real.cos (1 / 4) - 15 / 16 : ℝ) : ℂ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I))
    (lineKernel (1 / 4) 0 - (15 / 16 : ℝ) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)] at h2
  rw [e]
  linarith

/-- **Datum at a nonzero time: chain of 2 sites against the line, sharp form**, `t = 1/4`, `x = y = 1`:
`|C₂ − G| ≥ cos(1/4) − 15/16 − 33/25600 ≥ 767/25600 > 0.0299` (true value `0.03044`: the image `G(t, 2)` in the
wall). The datum that the first layer's plant record names as missing for FC-P. -/
theorem chain_two_sub_line_lower_sharp :
    767 / 25600 ≤ ‖chainKernel 2 (1 / 4) 1 1 - lineKernel (1 / 4) 0‖ :=
  sub_lineKernel_quarter_lower _ (chainKernel_two_diag (1 / 4))

/-- **Datum at a nonzero time: chain of 2 sites against the line**, `t = 1/4`, `x = y = 1`, in the form requested
by the lead: `|C₂ − G| ≥ 1/40`. -/
theorem chain_two_sub_line_lower : 1 / 40 ≤ ‖chainKernel 2 (1 / 4) 1 1 - lineKernel (1 / 4) 0‖ :=
  le_trans (by norm_num) chain_two_sub_line_lower_sharp

/-- **Datum at a nonzero time: chain of 2 sites against the line**, `t = 1/4`, `x = y = 2`: the same bound (the
image in the right wall). -/
theorem chain_two_sub_line_lower_two : 1 / 40 ≤ ‖chainKernel 2 (1 / 4) 2 2 - lineKernel (1 / 4) 0‖ :=
  le_trans (by norm_num) (sub_lineKernel_quarter_lower _ (chainKernel_two_diag_two (1 / 4)))

/-- **FC-P through the statement constant** at `M = 2`, `t = 1/4`, `x = y = 1`, in the literal form of the statement,
with the left side bounded below on data: `1/40 ≤` the bound, for every `η > 0`. Here the wall term `e^{−2η}` is the
main term for large `η`. Plants detected: CP3 (wall term dropped), CP7 (wall exponent doubled). -/
theorem chainP_two_one_one (h : ChainFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    1 / 40 ≤ Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh η) *
      (Real.exp (-(((1 + 1 : ℤ) : ℝ) * η)) +
        2 * (Real.cosh (((1 - 1 : ℤ) : ℝ) * η) + Real.cosh (((1 + 1 : ℤ) : ℝ) * η)) /
          (Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * η) - 1)) := by
  have h1 := h 2 (1 / 4) η 1 1 hη le_rfl (by norm_num) le_rfl (by norm_num)
  rw [show lineKernel (1 / 4) ((1 : ℤ) - 1) = lineKernel (1 / 4) 0 by rw [sub_self]] at h1
  exact chain_two_sub_line_lower.trans h1

/-- **FC-P through the statement constant** at `M = 2`, `t = 1/4`, `x = y = 2`, in the literal form of the statement:
`1/40 ≤` the bound, for every `η > 0`. Here the ring term `2 cosh(4η) / (e^{6η} − 1) ≈ e^{−2η}` is the main term for
large `η`. Plants detected: CP4 (ring term dropped), CP5 (`cosh((x + y)η)` dropped), CP6 (`M + 1 ↦ M + 2`). -/
theorem chainP_two_two_two (h : ChainFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    1 / 40 ≤ Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh η) *
      (Real.exp (-(((2 + 2 : ℤ) : ℝ) * η)) +
        2 * (Real.cosh (((2 - 2 : ℤ) : ℝ) * η) + Real.cosh (((2 + 2 : ℤ) : ℝ) * η)) /
          (Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * η) - 1)) := by
  have h1 := h 2 (1 / 4) η 2 2 hη (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show lineKernel (1 / 4) ((2 : ℤ) - 2) = lineKernel (1 / 4) 0 by rw [sub_self]] at h1
  exact chain_two_sub_line_lower_two.trans h1

/-- **Check (unconditional)**: the two instances of FC-P above are true at `η = 1` on rough numbers: both right
sides are at least `e^{−2} ≥ 1/9 > 1/40` (at `x = y = 1` by the wall term; at `x = y = 2` by the ring term,
`2 (1 + cosh 4) / (e⁶ − 1) ≥ e^{−2}`). -/
theorem chainP_two_check :
    1 / 40 ≤ Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh 1) *
        (Real.exp (-(((1 + 1 : ℤ) : ℝ) * 1)) +
          2 * (Real.cosh (((1 - 1 : ℤ) : ℝ) * 1) + Real.cosh (((1 + 1 : ℤ) : ℝ) * 1)) /
            (Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * 1) - 1)) ∧
      1 / 40 ≤ Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh 1) *
        (Real.exp (-(((2 + 2 : ℤ) : ℝ) * 1)) +
          2 * (Real.cosh (((2 - 2 : ℤ) : ℝ) * 1) + Real.cosh (((2 + 2 : ℤ) : ℝ) * 1)) /
            (Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * 1) - 1)) := by
  have hA : 1 ≤ Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh 1) :=
    Real.one_le_exp (by have := Real.sinh_nonneg_iff.mpr (zero_le_one' ℝ); positivity)
  have h2 : Real.exp 2 ≤ 9 := by
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e2]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hm : 1 / 9 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 2) h2
  have h6 : (1 : ℝ) < Real.exp 6 := by linarith [Real.add_one_lt_exp (by norm_num : (6 : ℝ) ≠ 0)]
  have e6 : Real.exp 6 = Real.exp 4 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have e0 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  have hr : Real.exp (-2) ≤ 2 * (1 + Real.cosh 4) / (Real.exp 6 - 1) := by
    rw [le_div_iff₀ (by linarith), Real.cosh_eq, e6]
    nlinarith [Real.exp_pos 4, Real.exp_pos (-4), Real.exp_pos (-2), Real.exp_pos 2]
  have hw : 0 ≤ Real.exp (-8) := (Real.exp_pos _).le
  have hq : 0 ≤ 2 * (1 + Real.cosh 2) / (Real.exp 6 - 1) :=
    div_nonneg (by have := Real.cosh_pos 2; linarith) (by linarith)
  have n1 : ((1 + 1 : ℤ) : ℝ) * 1 = 2 := by norm_num
  have n2 : ((1 - 1 : ℤ) : ℝ) * 1 = 0 := by norm_num
  have n3 : ((2 + 2 : ℤ) : ℝ) * 1 = 4 := by norm_num
  have n4 : ((2 - 2 : ℤ) : ℝ) * 1 = 0 := by norm_num
  have n5 : 2 * (((2 : ℕ) : ℝ) + 1) * 1 = 6 := by norm_num
  rw [n1, n2, n3, n4, n5, Real.cosh_zero]
  constructor
  · nlinarith
  · have h8 : Real.exp (-4) = Real.exp (-2) * Real.exp (-2) := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-4)]

/-- Rational bounds for `e²`, `e⁴`, `e⁸`, `e^{12}`, `e^{16}`, from `2.718 ≤ e ≤ 2.7183` by squaring. No kernel is
mentioned. -/
theorem exp_bounds :
    (7387 / 1000 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ 739 / 100 ∧ (545 / 10 : ℝ) ≤ Real.exp 4 ∧
      Real.exp 4 ≤ 5462 / 100 ∧ (2970 : ℝ) ≤ Real.exp 8 ∧ Real.exp 8 ≤ 2984 ∧ (161865 : ℝ) ≤ Real.exp 12 ∧
      (8820900 : ℝ) ≤ Real.exp 16 := by
  have hl : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hu : Real.exp 1 ≤ 27183 / 10000 := by linarith [Real.exp_one_lt_d9]
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have e8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have e12 : Real.exp 12 = Real.exp 8 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have e16 : Real.exp 16 = Real.exp 8 * Real.exp 8 := by rw [← Real.exp_add]; norm_num
  have l2 : (7387 / 1000 : ℝ) ≤ Real.exp 2 := by
    rw [e2]; exact le_trans (by norm_num) (mul_le_mul hl hl (by norm_num) (by linarith))
  have u2 : Real.exp 2 ≤ 739 / 100 := by
    rw [e2]; exact le_trans (mul_le_mul hu hu (by linarith) (by norm_num)) (by norm_num)
  have l4 : (545 / 10 : ℝ) ≤ Real.exp 4 := by
    rw [e4]; exact le_trans (by norm_num) (mul_le_mul l2 l2 (by norm_num) (by linarith))
  have u4 : Real.exp 4 ≤ 5462 / 100 := by
    rw [e4]; exact le_trans (mul_le_mul u2 u2 (by linarith) (by norm_num)) (by norm_num)
  have l8 : (2970 : ℝ) ≤ Real.exp 8 := by
    rw [e8]; exact le_trans (by norm_num) (mul_le_mul l4 l4 (by norm_num) (by linarith))
  have u8 : Real.exp 8 ≤ 2984 := by
    rw [e8]; exact le_trans (mul_le_mul u4 u4 (by linarith) (by norm_num)) (by norm_num)
  have l12 : (161865 : ℝ) ≤ Real.exp 12 := by
    rw [e12]; exact le_trans (by norm_num) (mul_le_mul l8 l4 (by norm_num) (by linarith))
  have l16 : (8820900 : ℝ) ≤ Real.exp 16 := by
    rw [e16]; exact le_trans (by norm_num) (mul_le_mul l8 l8 (by norm_num) (by linarith))
  exact ⟨l2, u2, l4, u4, l8, u8, l12, l16⟩

/-- **Numbers for the witnesses of the planted controls CP3 to CP7** (`t = 1/4`, `η = 2`): the time factor
`e^{sinh(2)/2} ≤ 7.39`, `e^{−8} ≤ 1/2970`, and the ring terms `2 (1 + cosh 4) / (e^{12} − 1)`,
`2 (1 + cosh 8) / (e^{16} − 1)` and `2 / (e^{12} − 1)` are at most `1/1000`. With these every planted bound is below
`7.39 · 0.0014 < 1/40`. -/
theorem chainP_eta_two_numbers :
    Real.exp (2 * |(1 / 4 : ℝ)| * Real.sinh 2) ≤ 739 / 100 ∧ Real.exp (-8) ≤ 1 / 2970 ∧
      2 * (1 + Real.cosh 4) / (Real.exp 12 - 1) ≤ 1 / 1000 ∧
      2 * (1 + Real.cosh 8) / (Real.exp 16 - 1) ≤ 1 / 1000 ∧ 2 * 1 / (Real.exp 12 - 1) ≤ 1 / 1000 := by
  obtain ⟨l2, u2, l4, u4, l8, u8, l12, l16⟩ := exp_bounds
  have m2 : 0 < Real.exp (-2) := Real.exp_pos _
  have m4 : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have m8 : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hs : 2 * |(1 / 4 : ℝ)| * Real.sinh 2 ≤ 2 := by
      rw [abs_of_pos (by norm_num), Real.sinh_eq]; linarith
    exact (Real.exp_le_exp.mpr hs).trans u2
  · rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) l8
  · rw [div_le_iff₀ (by linarith), Real.cosh_eq]; linarith
  · rw [div_le_iff₀ (by linarith), Real.cosh_eq]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

/-- **Bite: `e^{−6} + 2 (cosh 2 + cosh 6) / (e^{12} − 1) < 1`**: the bound of FC-P at `M = 2`, `t = 0`, `x = 1`,
`y = 2`, `η = 2`. With `G(t, 0)` in place of `G(t, x − y)` the left side there is `|C₂(0; 1, 2) − G(0, 0)| = 1`
(plant CP2). -/
theorem chainP_offdiag_bound_lt :
    Real.exp (-6) + 2 * (Real.cosh 2 + Real.cosh 6) / (Real.exp 12 - 1) < 1 := by
  obtain ⟨l2, u2, l4, u4, l8, u8, l12, l16⟩ := exp_bounds
  have e6 : Real.exp 6 = Real.exp 4 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have u6 : Real.exp 6 ≤ 404 := by
    rw [e6]; exact le_trans (mul_le_mul u4 u2 (by linarith) (by norm_num)) (by norm_num)
  have l6 : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have m6 : Real.exp (-6) ≤ 1 / 7 := by rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) l6
  have m2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hr : 2 * (Real.cosh 2 + Real.cosh 6) / (Real.exp 12 - 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith), Real.cosh_eq, Real.cosh_eq]; linarith
  linarith

/-- **Bite: the time enters the bound of FC-P as `2|t|`.** At `M = 2`, `x = y = 1`, `t = 1/4`, `η = log 16` the bound
with `|t|` in place of `2|t|` is `e^{255/128} (1/256 + 2 (1 + cosh(2 log 16)) / (16⁶ − 1)) ≤ 7.39 · 0.003922 < 0.0290`,
below the left side `≥ 767/25600 > 0.0299` (floating point: `0.02875` against `0.03044`; `η = log 16` is within
`10⁻³` of the minimiser of the planted bound, and at `η = 3` the planted bound is `0.03041`, not a violation). -/
theorem chainP_half_time_false :
    ¬ ‖chainKernel 2 (1 / 4) 1 1 - lineKernel (1 / 4) ((1 : ℤ) - 1)‖ ≤
      Real.exp (|(1 / 4 : ℝ)| * Real.sinh (Real.log 16)) *
        (Real.exp (-(((1 + 1 : ℤ) : ℝ) * Real.log 16)) +
          2 * (Real.cosh (((1 - 1 : ℤ) : ℝ) * Real.log 16) + Real.cosh (((1 + 1 : ℤ) : ℝ) * Real.log 16)) /
            (Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * Real.log 16) - 1)) := by
  intro h
  have h16 : Real.exp (Real.log 16) = 16 := Real.exp_log (by norm_num)
  have hs : |(1 / 4 : ℝ)| * Real.sinh (Real.log 16) ≤ 2 := by
    rw [abs_of_pos (by norm_num), Real.sinh_eq, Real.exp_neg, h16]; norm_num
  have hA : Real.exp (|(1 / 4 : ℝ)| * Real.sinh (Real.log 16)) ≤ 739 / 100 :=
    (Real.exp_le_exp.mpr hs).trans exp_bounds.2.1
  have e2 : Real.exp (((1 + 1 : ℤ) : ℝ) * Real.log 16) = 256 := by
    rw [show ((1 + 1 : ℤ) : ℝ) * Real.log 16 = Real.log 16 + Real.log 16 by push_cast; ring, Real.exp_add, h16]
    norm_num
  have e6 : Real.exp (2 * (((2 : ℕ) : ℝ) + 1) * Real.log 16) = 16777216 := by
    rw [show 2 * (((2 : ℕ) : ℝ) + 1) * Real.log 16 = ((6 : ℕ) : ℝ) * Real.log 16 by push_cast; ring,
      Real.exp_nat_mul, h16]
    norm_num
  rw [show lineKernel (1 / 4) ((1 : ℤ) - 1) = lineKernel (1 / 4) 0 by rw [sub_self],
    show ((1 - 1 : ℤ) : ℝ) * Real.log 16 = 0 by norm_num, Real.cosh_zero, Real.cosh_eq, Real.exp_neg, e2,
    e6] at h
  have h2 := chain_two_sub_line_lower_sharp.trans h
  have h3 := mul_le_mul_of_nonneg_right hA
    (by norm_num : (0 : ℝ) ≤ (256 : ℝ)⁻¹ + 2 * (1 + (256 + (256 : ℝ)⁻¹) / 2) / (16777216 - 1))
  norm_num at h2 h3
  linarith

/-! ## Data for the planted controls on the definition of `lineKernel` -/

/-- **Datum for the planted control L1**: `‖1 − e^{−i/2}‖ ≥ sin(1/2) ≥ 15/32`. A line kernel without the phase factor
`e^{−2it}` is at distance `≥ (15/16)(15/32) − 33/25600 > 1/384` from `(15/16) e^{−i/2}` at `t = 1/4`, `n = 0`. -/
theorem norm_one_sub_exp_half_lower : 15 / 32 ≤ ‖1 - Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)‖ := by
  have hs : 15 / 32 ≤ Real.sin (1 / 2) := by
    have := Real.sin_gt_sub_cube (x := 1 / 2) (by norm_num)
    norm_num at this
    linarith
  have him : (1 - Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I)).im = Real.sin (1 / 2) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]; simp
  have h := Complex.abs_im_le_norm (1 - Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I))
  rw [him, abs_of_nonneg (by linarith)] at h
  linarith

/-- **Data for the planted controls L2 and L3**: `‖I(1/4, 1)‖ ≤ 3π/8` and `‖I(−1/2, 1) + iπ/2‖ ≤ π/2`, both from
`latticeKernel1_one_approx` (batch PA sanity). -/
theorem latticeKernel1_one_bounds :
    ‖latticeKernel1 (1 / 4) 1‖ ≤ 3 * Real.pi / 8 ∧
      ‖latticeKernel1 (-(1 / 2)) 1 + ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I‖ ≤ Real.pi / 2 := by
  constructor
  · have h := latticeKernel1_one_approx (1 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)
    have h2 := norm_le_norm_add_norm_sub' (latticeKernel1 (1 / 4) 1)
      ((Real.pi : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I)
    have h3 : ‖(Real.pi : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I‖ = Real.pi / 4 := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num)]
      ring
    have h4 : 2 * Real.pi * (1 / 4 : ℝ) ^ 2 = Real.pi / 8 := by ring
    rw [h3] at h2
    rw [h4] at h
    linarith
  · have h := latticeKernel1_one_approx (-(1 / 2)) (by rw [abs_le]; constructor <;> norm_num)
    have h4 : 2 * Real.pi * (-(1 / 2) : ℝ) ^ 2 = Real.pi / 2 := by ring
    have e : latticeKernel1 (-(1 / 2)) 1 + ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I =
        latticeKernel1 (-(1 / 2)) 1 - (Real.pi : ℂ) * ((-(1 / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e]
    rw [h4] at h
    exact h

/-! ## Data for the planted control on the definition of `ringKernel` -/

/-- `e^{inπ} = (−1)ⁿ` for an integer `n`. No kernel is mentioned. -/
theorem exp_int_mul_pi (n : ℤ) : Complex.exp (↑((n : ℝ) * Real.pi) * Complex.I) = (-1) ^ n := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]; congr 1; push_cast; ring

/-- **Datum for the planted control R1: `R₆(4π, 0) = 1`.** At `t = 4π` the phases `e^{−it}`, `e^{−3it}`, `e^{−4it}` of
the ring of 6 sites are all `1`. With `cos³ k` in place of `cos k` in `ringKernel` the modes `k = ±π/3, ±2π/3` have
the phases `e^{−7it/4} = e^{−9it/4} = −1` there, and the value is `−1/3`. (The rings of 1, 2 and 4 sites cannot see
this plant: their modes have `cos k ∈ {0, ±1}`.) -/
theorem ringKernel_six_four_pi : ringKernel 6 (4 * Real.pi) 0 = 1 := by
  have h1 := exp_int_mul_pi (-4)
  have h3 := exp_int_mul_pi (-12)
  have h4 := exp_int_mul_pi (-16)
  rw [ringKernel_six_site_zero, show -(4 * Real.pi) = ((-4 : ℤ) : ℝ) * Real.pi by push_cast; ring,
    show -(3 * (4 * Real.pi)) = ((-12 : ℤ) : ℝ) * Real.pi by push_cast; ring,
    show -(4 * (4 * Real.pi)) = ((-16 : ℤ) : ℝ) * Real.pi by push_cast; ring, h1, h3, h4]
  norm_num

end OscInt.API.FiniteRingSanity2
