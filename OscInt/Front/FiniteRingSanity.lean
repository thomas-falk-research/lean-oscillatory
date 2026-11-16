/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.FiniteRing
import OscInt.Front.PeriodicAnalyticSanity

/-! # Sanity theorems through the batch-FR statement constants (ring of `N` sites, open chain)

As for batches LE, LE2, HC and PA (`docs/lessons.md`, rules 8 and 9): every theorem about a statement of batch FR
takes that statement constant as its only statement hypothesis, discharges its hypotheses on closed data and
concludes its conclusion there. No statement of the batch is proved or used otherwise. Everything else is an
unconditional lemma about data: the rings of `1`, `2`, `4` sites (and of `0`, `3`, `6` sites at time `0` for the
planted controls), the chain of `1` site, explicit solutions. Planted copies and witnesses:
`docs/replay/plants/2026-11-16-FR/`.

Written by an agent of the lead in scratch, with the statement text copied verbatim at the top of its file because
the statement module did not exist yet; the lead removed that copy and added the import when the batch entered
the repository, and changed nothing else.

Data:
* `R₁(t, r) = 1`; `R₂(t, r) = (1 + (−1)ʳ e^{−4it}) / 2`; `R₄(t, r) = (1 + (iʳ + (−i)ʳ) e^{−2it} + (−1)ʳ e^{−4it}) / 4`;
  `R₀ = 0` in Lean (`0 < N` carries content); `G(0, n) = δ_{n,0}`.
* `C₁(t; 1, 1) = e^{−2it}` and the wall values `C₁(t; 0, 1) = C₁(t; 2, 1) = 0`.
* FR-K at `N = 2`: the equation at `r = 0` (with the unconditional derivative of `R₂(·, 0)` as a check), the unit
  datum at `r = 1` and `r = 2`, the period at `r = 1`.
* FR-U at `N = 2` and the mode `(−1)ˣ e^{−4is}` (`piMode`), and at `N = 1` and the constant `1`.
* FR-S at `N = 1`, `t = 0`, `r = 0` and at `N = 2`, `t = 0`, `r = 1`.
* FR-P at `N = 1`, `t = 0`, `r = ±1` for every `η > 0` (left side `1`; the bound `2 cosh η / (e^η − 1)` tends to `1`
  as `η → ∞`, so the constant `2` and the factor `cosh(rη)` are tested sharply), and at `N = 1`, `r = 1` and every
  `t` with the line kernel not evaluated (form of the time dependence only).
* FC-K, FC-U, FC-P at `M = 1`, `x = y = 1` (`chainMode c` is the solution `c e^{−2is}` at the one site), and the
  unit datum of FC-K off the diagonal at `M = 2` (`C₂(0; 1, 2) = 0`).
* Each instance obtained through a statement constant is also checked unconditionally on the data where the data
  decide it (`ringK_check`, `ringKernel_two_zero_hasDerivAt`, `ringU_mode_check`, `ringS_two_check`,
  `ringP_one_check`, `chainK_check`, `chainKernel_two_zero_offdiag`, `chainU_one_check`): the draft statements are
  true on these instances.
* Bite: `ringP_half_time_false`, at `N = 2`, `r = 0`, `t = 1/4`, `η = log 16` the bound of FR-P with `|t|` in place of
  `2|t|` is false (from `‖I(1/2, 0)‖ ≥ 2π(1 − 1/16)`, batch LE2 sanity).
* Data for the planted controls only (last sections): the unit datum of the ring of 4 sites, the mode
  `iˣ e^{−2is}` (`iMode`, not even in `x`), `R₆(0, −1) = R₆(0, 3) = 0`, `C₂(0; 1, 2) = 0`, `R₃(0, 1) = 0`,
  `R₃(0, 3) = 1`.

What this layer cannot see: FC-P has no exact datum with a nonzero left side here (at `M = 1`, `t = 0` the left side
is `0`), and FR-P has none at `t ≠ 0` apart from the lower bound behind `ringP_half_time_false`; the `− 1` in the
denominator of FR-P and the wall term `e^{−(x+y)η}` of FC-P are therefore not tested by a datum (plant record).
-/

namespace OscInt.API.FiniteRingSanity

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.LatticeExplicitSanity OscInt.API.LatticeCubeRootSanity

/-- One mode of a ring kernel: with `cos θ = c` and `e^{iθ} = z`, the summand `e^{i(2t(cos θ − 1) + rθ)}` is
`zʳ e^{2it(c − 1)}`. A fact about the exponential; no kernel is mentioned. -/
theorem exp_mode (t θ c : ℝ) (r : ℤ) (z : ℂ) (hc : Real.cos θ = c) (hz : Complex.exp (↑θ * Complex.I) = z) :
    Complex.exp (↑(2 * t * (Real.cos θ - 1) + (r : ℝ) * θ) * Complex.I) =
      z ^ r * Complex.exp (↑(2 * t * (c - 1)) * Complex.I) := by
  rw [← hz, ← Complex.exp_int_mul, ← Complex.exp_add, hc]
  congr 1; push_cast; ring

/-- `(−1)ʳ` as a case distinction on the parity of the integer `r`. -/
theorem neg_one_zpow_ite (r : ℤ) : (-1 : ℂ) ^ r = if Even r then 1 else -1 := by
  split_ifs with he
  · exact he.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp he).neg_one_zpow

/-- `e^{iπ/2} = i`. -/
theorem exp_half_pi : Complex.exp (↑(Real.pi / 2) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]; simp

/-- `e^{3iπ/2} = −i`. -/
theorem exp_three_half_pi : Complex.exp (↑(3 * Real.pi / 2) * Complex.I) = -Complex.I := by
  rw [show (↑(3 * Real.pi / 2) : ℂ) * Complex.I = ↑Real.pi * Complex.I + ↑(Real.pi / 2) * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I, exp_half_pi]
  ring

/-- `cos(3π/2) = 0`. -/
theorem cos_three_half_pi : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]

/-- `d/ds e^{−ias} = −ia e^{−ias}` for real `a`. -/
theorem hasDerivAt_exp_neg (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (↑(-(a * s)) * Complex.I))
      (-(a : ℂ) * Complex.I * Complex.exp (↑(-(a * t)) * Complex.I)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => (↑(-(a * s)) : ℂ) * Complex.I) (-(a : ℂ) * Complex.I) t := by
    convert h0.const_mul (-(a : ℂ) * Complex.I) using 1
    · funext s; push_cast; ring
    · ring
  convert h1.cexp using 1
  ring

/-- **Datum, ring of 1 site.** `R₁(t, r) = 1`: the only mode is `k = 0`. -/
theorem ringKernel_one (t : ℝ) (r : ℤ) : ringKernel 1 t r = 1 := by
  simp [ringKernel]

/-- **Datum, ring of 0 sites.** `R₀ = 0` in Lean (empty sum, and `0⁻¹ = 0`): the hypothesis `0 < N` carries content. -/
theorem ringKernel_zero_size (t : ℝ) (r : ℤ) : ringKernel 0 t r = 0 := by
  simp [ringKernel]

/-- **Datum, ring of 2 sites.** `R₂(t, r) = (1 + (−1)ʳ e^{−4it}) / 2`: the modes `k = 0` and `k = π`. -/
theorem ringKernel_two (t : ℝ) (r : ℤ) :
    ringKernel 2 t r = (1 + (if Even r then 1 else -1) * Complex.exp (↑(-(4 * t)) * Complex.I)) / 2 := by
  have hθ : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi := by push_cast; ring
  have h1 := exp_mode t Real.pi (-1) r (-1) Real.cos_pi Complex.exp_pi_mul_I
  rw [show 2 * t * ((-1 : ℝ) - 1) = -(4 * t) by ring, neg_one_zpow_ite] at h1
  rw [ringKernel, Finset.sum_range_succ, Finset.sum_range_one, hθ, h1]
  simp
  ring

/-- **Datum, the line at time 0.** `G(0, n) = δ_{n,0}`: the integral of `e^{ink}` over `[−π, π]` divided by `2π`. -/
theorem lineKernel_zero (n : ℤ) : lineKernel 0 n = if n = 0 then 1 else 0 := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [lineKernel]
  split_ifs with hn
  · subst hn
    simp only [mul_zero, Int.cast_zero, latticeKernel1_zero_zero, neg_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one]
    exact inv_mul_cancel₀ hpi
  · have h0 := integral_exp_int_mul n hn
    have h1 : latticeKernel1 (2 * 0) (n : ℝ) = 0 := by simpa [latticeKernel1] using h0
    rw [h1, mul_zero]

/-- **Datum, ring of 4 sites.** `R₄(t, r) = (1 + (iʳ + (−i)ʳ) e^{−2it} + (−1)ʳ e^{−4it}) / 4`: the modes
`k = 0, π/2, π, 3π/2` with `cos k = 1, 0, −1, 0`. -/
theorem ringKernel_four (t : ℝ) (r : ℤ) :
    ringKernel 4 t r = (1 + (Complex.I ^ r + (-Complex.I) ^ r) * Complex.exp (↑(-(2 * t)) * Complex.I) +
      (-1) ^ r * Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  have hθ1 : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = Real.pi / 2 := by push_cast; ring
  have hθ2 : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = Real.pi := by push_cast; ring
  have hθ3 : 2 * Real.pi * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 * Real.pi / 2 := by push_cast; ring
  have h1 := exp_mode t (Real.pi / 2) 0 r Complex.I Real.cos_pi_div_two exp_half_pi
  have h2 := exp_mode t Real.pi (-1) r (-1) Real.cos_pi Complex.exp_pi_mul_I
  have h3 := exp_mode t (3 * Real.pi / 2) 0 r (-Complex.I) cos_three_half_pi exp_three_half_pi
  rw [show 2 * t * ((0 : ℝ) - 1) = -(2 * t) by ring] at h1 h3
  rw [show 2 * t * ((-1 : ℝ) - 1) = -(4 * t) by ring] at h2
  rw [ringKernel, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hθ1, hθ2, hθ3, h1, h2, h3]
  simp
  ring

/-- `R₄(t, 0) = (1 + 2 e^{−2it} + e^{−4it}) / 4`. -/
theorem ringKernel_four_zero (t : ℝ) :
    ringKernel 4 t 0 = (1 + 2 * Complex.exp (↑(-(2 * t)) * Complex.I) + Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; simp; ring

/-- `R₄(t, 2) = (1 − 2 e^{−2it} + e^{−4it}) / 4`. -/
theorem ringKernel_four_two (t : ℝ) :
    ringKernel 4 t 2 = (1 - 2 * Complex.exp (↑(-(2 * t)) * Complex.I) + Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; norm_num [zpow_ofNat]; ring

/-- `R₄(t, 1) = (1 − e^{−4it}) / 4`. -/
theorem ringKernel_four_one (t : ℝ) :
    ringKernel 4 t 1 = (1 - Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; simp; ring

/-- `R₄(t, −1) = (1 − e^{−4it}) / 4`. -/
theorem ringKernel_four_neg_one (t : ℝ) :
    ringKernel 4 t (-1) = (1 - Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; simp; ring

/-- `R₄(t, 3) = (1 − e^{−4it}) / 4`. -/
theorem ringKernel_four_three (t : ℝ) :
    ringKernel 4 t 3 = (1 - Complex.exp (↑(-(4 * t)) * Complex.I)) / 4 := by
  rw [ringKernel_four]; norm_num [zpow_ofNat, pow_succ]; ring

/-- **Datum, chain of 1 site.** `C₁(t; 1, 1) = R₄(t, 0) − R₄(t, 2) = e^{−2it}`: the one site of the chain has the
eigenvalue `−2` of the Dirichlet Laplacian. -/
theorem chainKernel_one (t : ℝ) : chainKernel 1 t 1 1 = Complex.exp (↑(-(2 * t)) * Complex.I) := by
  have h : chainKernel 1 t 1 1 = ringKernel 4 t 0 - ringKernel 4 t 2 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_zero, ringKernel_four_two]; ring

/-- **Datum, chain of 1 site, left wall.** `C₁(t; 0, 1) = R₄(t, −1) − R₄(t, 1) = 0`. -/
theorem chainKernel_one_wall_zero (t : ℝ) : chainKernel 1 t 0 1 = 0 := by
  have h : chainKernel 1 t 0 1 = ringKernel 4 t (-1) - ringKernel 4 t 1 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_neg_one, ringKernel_four_one]; ring

/-- **Datum, chain of 1 site, right wall.** `C₁(t; 2, 1) = R₄(t, 1) − R₄(t, 3) = 0`. -/
theorem chainKernel_one_wall_two (t : ℝ) : chainKernel 1 t 2 1 = 0 := by
  have h : chainKernel 1 t 2 1 = ringKernel 4 t 1 - ringKernel 4 t 3 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_four_one, ringKernel_four_three]; ring

/-- **Datum (unconditional): the time derivative of `R₂(·, 0) = (1 + e^{−4is}) / 2`** is `−2i e^{−4it}`. Used as the
second derivative at one point in the planted controls FR-K-a and FR-K-e, and as a check that the instance of FR-K
in `ringK_two_deriv` is true. -/
theorem ringKernel_two_zero_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => ringKernel 2 s 0) (-2 * Complex.I * Complex.exp (↑(-(4 * t)) * Complex.I)) t := by
  have hf : (fun s : ℝ => ringKernel 2 s 0) = fun s : ℝ => (1 + Complex.exp (↑(-(4 * s)) * Complex.I)) / 2 := by
    funext s; rw [ringKernel_two]; simp
  rw [hf]
  convert ((hasDerivAt_exp_neg 4 t).const_add 1).div_const 2 using 1
  push_cast; ring

/-- **FR-K through the statement constant**, equation: at `N = 2`, `r = 0` the derivative of `s ↦ R₂(s, 0)` is
`i (R₂(t, 1) + R₂(t, −1) − 2 R₂(t, 0)) = −2i e^{−4it}`. Plants detected: the Laplacian coefficient `2 ↦ 1`, the sign of
`i`. -/
theorem ringK_two_deriv (h : RingKernelStatement) (t : ℝ) :
    deriv (fun s => ringKernel 2 s 0) t = -2 * Complex.I * Complex.exp (↑(-(4 * t)) * Complex.I) := by
  have h1 := (h 2 t 0 (by norm_num)).1
  rw [h1.deriv, ringKernel_two, ringKernel_two, ringKernel_two]
  simp
  ring

/-- **FR-K through the statement constant**, unit datum on the ring of 2 sites: `R₂(0, 1) = 0` (off the lattice `2ℤ`)
and `R₂(0, 2) = 1` (on `2ℤ`, away from `0`). Plant detected: `N ∣ r ↦ r = 0`. -/
theorem ringK_unit (h : RingKernelStatement) : ringKernel 2 0 1 = 0 ∧ ringKernel 2 0 2 = 1 := by
  have h1 := (h 2 0 1 (by norm_num)).2.1
  have h2 := (h 2 0 2 (by norm_num)).2.1
  rw [ite_eq_right (by norm_num)] at h1
  rw [ite_eq_left (by norm_num)] at h2
  exact ⟨h1, h2⟩

/-- **FR-K through the statement constant**, period: `R₂(t, 3) = R₂(t, 1)`. Plant detected: period `N ↦ 1`. -/
theorem ringK_period (h : RingKernelStatement) (t : ℝ) : ringKernel 2 t 3 = ringKernel 2 t 1 := by
  have h1 := (h 2 t 1 (by norm_num)).2.2
  rw [show (1 : ℤ) + ((2 : ℕ) : ℤ) = 3 by norm_num] at h1
  exact h1

/-- **Check (unconditional)**: the three instances of FR-K above are true on the data of `ringKernel_two`. -/
theorem ringK_check (t : ℝ) :
    (ringKernel 2 0 1 = 0 ∧ ringKernel 2 0 2 = 1) ∧ ringKernel 2 t 3 = ringKernel 2 t 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [ringKernel_two]; norm_num
  · rw [ringKernel_two]; norm_num
  · rw [ringKernel_two, ringKernel_two, ite_eq_right (by decide), ite_eq_right (by decide)]

/-- Datum for FR-U: the mode `k = π` on the ring of 2 sites, `u(s, x) = (−1)ˣ e^{−4is}`. -/
noncomputable def piMode (s : ℝ) (x : ℤ) : ℂ :=
  (if Even x then 1 else -1) * Complex.exp (↑(-(4 * s)) * Complex.I)

/-- `piMode` has period 2 in the site. -/
theorem piMode_periodic (t : ℝ) (x : ℤ) : piMode t (x + ((2 : ℕ) : ℤ)) = piMode t x := by
  simp [piMode]

/-- The sign `(−1)ˣ` changes from a site to the next one. -/
theorem parity_sign_succ (x : ℤ) : (if Even (x + 1) then (1 : ℂ) else -1) = -(if Even x then 1 else -1) := by
  by_cases hx : Even x
  · rw [ite_eq_right (Int.even_add_one.not.mpr (not_not.mpr hx)), ite_eq_left hx]
  · rw [ite_eq_left (Int.even_add_one.mpr hx), ite_eq_right hx, neg_neg]

/-- The sign `(−1)ˣ` changes from a site to the previous one. -/
theorem parity_sign_pred (x : ℤ) : (if Even (x - 1) then (1 : ℂ) else -1) = -(if Even x then 1 else -1) := by
  by_cases hx : Even x
  · rw [ite_eq_right (Int.even_sub_one.not.mpr (not_not.mpr hx)), ite_eq_left hx]
  · rw [ite_eq_left (Int.even_sub_one.mpr hx), ite_eq_right hx, neg_neg]

/-- `piMode` solves `i u′ + Δu = 0` (eigenvalue `2 cos π − 2 = −4`). -/
theorem piMode_hasDerivAt (t : ℝ) (x : ℤ) :
    HasDerivAt (fun s : ℝ => piMode s x)
      (Complex.I * (piMode t (x + 1) + piMode t (x - 1) - 2 * piMode t x)) t := by
  have h := (hasDerivAt_exp_neg 4 t).const_mul (if Even x then (1 : ℂ) else -1)
  have e1 : piMode t (x + 1) = -piMode t x := by rw [piMode, piMode, parity_sign_succ, neg_mul]
  have e2 : piMode t (x - 1) = -piMode t x := by rw [piMode, piMode, parity_sign_pred, neg_mul]
  rw [e1, e2]
  convert h using 1
  · funext s; rw [piMode]
  · rw [piMode]; push_cast; ring

/-- **FR-U through the statement constant** at `N = 2` and the mode `k = π`: the kernel sum of the datum
`(1, −1)` over the period `{0, 1}` is `R₂(t, x) − R₂(t, x − 1)`, and it equals `(−1)ˣ e^{−4it}`. Plants detected:
a dropped hypothesis changes the application; the range `N ↦ N + 1` adds a third term. -/
theorem ringU_mode (h : RingUniqueStatement) (t : ℝ) (x : ℤ) :
    (if Even x then 1 else -1) * Complex.exp (↑(-(4 * t)) * Complex.I) =
      ringKernel 2 t x - ringKernel 2 t (x - 1) := by
  have h1 := h 2 piMode (by norm_num) piMode_periodic piMode_hasDerivAt t x
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h1
  simpa [piMode, sub_eq_add_neg] using h1

/-- **Check (unconditional)**: the instance of FR-U in `ringU_mode` is true on the data of `ringKernel_two`. -/
theorem ringU_mode_check (t : ℝ) (x : ℤ) :
    (if Even x then 1 else -1) * Complex.exp (↑(-(4 * t)) * Complex.I) =
      ringKernel 2 t x - ringKernel 2 t (x - 1) := by
  rw [ringKernel_two, ringKernel_two, parity_sign_pred]
  ring

/-- **FR-U through the statement constant** at `N = 1` and the constant solution `u = 1`: `R₁(t, x) = 1`
(true by `ringKernel_one`). -/
theorem ringU_const (h : RingUniqueStatement) (t : ℝ) (x : ℤ) : ringKernel 1 t x = 1 := by
  have h1 := h 1 (fun _ _ => 1) (by norm_num) (fun _ _ => rfl)
    (fun t _ => by convert hasDerivAt_const t (1 : ℂ) using 1; ring) t x
  simpa using h1.symm

/-- **FR-S through the statement constant** at `N = 1`, `t = 0`, `r = 0`: the coset is `ℤ` and the sum of the unit
datum of the line is `1`. -/
theorem ringS_origin (h : RingCosetSumStatement) : HasSum (fun m : ℤ => if m = 0 then (1 : ℂ) else 0) 1 := by
  have h1 := h 1 0 0 (by norm_num)
  simpa [lineKernel_zero, ringKernel_one] using h1

/-- **FR-S through the statement constant** at `N = 2`, `t = 0`, `r = 1`: the coset `1 + 2ℤ` misses the origin and
the sum is `R₂(0, 1) = 0`. Plants detected: the step `N ↦ N + 1` of the coset, a shifted right side. -/
theorem ringS_two (h : RingCosetSumStatement) : ∑' m : ℤ, lineKernel 0 (1 + m * 2) = 0 := by
  have h1 := (h 2 0 1 (by norm_num)).tsum_eq
  rw [ringKernel_two] at h1
  simpa using h1

/-- **Check (unconditional)**: every term of the sum in `ringS_two` is `0`, so the instance is true. -/
theorem ringS_two_check (m : ℤ) : lineKernel 0 (1 + m * 2) = 0 := by
  rw [lineKernel_zero, ite_eq_right (by omega)]

/-- **FR-P through the statement constant** at `N = 1`, `t = 0`, `r = 1`: `|R₁(0, 1) − G(0, 1)| = 1` and the bound is
`2 cosh η / (e^η − 1)`. Plants detected: the constant `2 ↦ 1`, `cosh(rη) ↦ 1`. -/
theorem ringP_one (h : RingFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    1 ≤ 2 * Real.cosh η / (Real.exp η - 1) := by
  have h1 := h 1 0 η 1 (by norm_num) hη
  rw [ringKernel_one, lineKernel_zero, ite_eq_right (by norm_num)] at h1
  simpa using h1

/-- **FR-P through the statement constant** at `N = 1`, `r = 1` and every time `t`: the left side is
`|1 − G(t, 1)|` (`G(t, 1)` is not evaluated for `t ≠ 0`) and the time enters the bound as `2|t|`. Plant rejected by
the form of this conclusion: `2|t| ↦ |t|` (refuted on data by `ringP_half_time_false`). -/
theorem ringP_time (h : RingFiniteSizeStatement) (t η : ℝ) (hη : 0 < η) :
    ‖1 - lineKernel t 1‖ ≤ 2 * Real.exp (2 * |t| * Real.sinh η) * Real.cosh η / (Real.exp η - 1) := by
  have h1 := h 1 t η 1 (by norm_num) hη
  rw [ringKernel_one] at h1
  simpa using h1

/-- **FR-P through the statement constant** at `r = −1`: the same bound (the bound is even in `r`; a bound that is
not even in `r`, such as `e^{rη}` in place of `cosh(rη)`, would change this conclusion). -/
theorem ringP_neg_one (h : RingFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    1 ≤ 2 * Real.cosh η / (Real.exp η - 1) := by
  have h1 := h 1 0 η (-1) (by norm_num) hη
  rw [ringKernel_one, lineKernel_zero, ite_eq_right (by norm_num)] at h1
  simpa using h1

/-- **Check (unconditional)**: the instance of FR-P in `ringP_one` is true: `e^η − 1 ≤ e^η + e^{−η} = 2 cosh η`. -/
theorem ringP_one_check (η : ℝ) (hη : 0 < η) : 1 ≤ 2 * Real.cosh η / (Real.exp η - 1) := by
  have h1 : 0 < Real.exp η - 1 := by linarith [Real.add_one_lt_exp hη.ne']
  rw [le_div_iff₀ h1, Real.cosh_eq]
  linarith [Real.exp_pos (-η)]

/-- **FC-K through the statement constant**, equation: at `M = 1`, `x = y = 1`, with the two wall values taken from
the statement itself, the derivative of `s ↦ C₁(s; 1, 1)` is `−2i e^{−2it}`. Plants detected: walls moved to `M`, the
reflection sign in the kernel. -/
theorem chainK_one (h : ChainKernelStatement) (t : ℝ) :
    deriv (fun s => chainKernel 1 s 1 1) t = -2 * Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) := by
  obtain ⟨hd, hw0, hw2, -⟩ := h 1 t 1 1 le_rfl (by norm_num)
  rw [show ((1 : ℕ) : ℤ) + 1 = 2 by norm_num] at hw2
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, hw0, hw2, chainKernel_one] at hd
  rw [hd.deriv]
  ring

/-- **FC-K through the statement constant**, unit datum: `C₁(0; 1, 1) = 1`. -/
theorem chainK_unit (h : ChainKernelStatement) : chainKernel 1 0 1 1 = 1 := by
  obtain ⟨-, -, -, hu⟩ := h 1 0 1 1 le_rfl (by norm_num)
  simpa using hu le_rfl (by norm_num)

/-- **FC-K through the statement constant**, unit datum off the diagonal on the chain of 2 sites:
`C₂(0; 1, 2) = 0` (true by `chainKernel_two_zero_offdiag`, from the ring of 6 sites). Plant detected: the unit datum
`δ_{xy} ↦ 1`, which the chain of 1 site cannot see. -/
theorem chainK_two_offdiag (h : ChainKernelStatement) : chainKernel 2 0 1 2 = 0 := by
  obtain ⟨-, -, -, hu⟩ := h 2 0 1 2 (by norm_num) (by norm_num)
  have h1 := hu le_rfl (by norm_num)
  rw [ite_eq_right (by norm_num)] at h1
  exact h1

/-- **Check (unconditional)**: the instances of FC-K at `M = 1` above are true on the data: the derivative of
`e^{−2is}` and the value at `t = 0`. -/
theorem chainK_check (t : ℝ) :
    HasDerivAt (fun s : ℝ => chainKernel 1 s 1 1) (-2 * Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I)) t ∧
      chainKernel 1 0 1 1 = 1 := by
  refine ⟨?_, by rw [chainKernel_one]; simp⟩
  have hf : (fun s : ℝ => chainKernel 1 s 1 1) = fun s : ℝ => Complex.exp (↑(-(2 * s)) * Complex.I) := by
    funext s; rw [chainKernel_one]
  rw [hf]
  convert hasDerivAt_exp_neg 2 t using 1

/-- Datum for FC-U: on the chain of 1 site, `u(s, 1) = c e^{−2is}` and `u = 0` elsewhere. -/
noncomputable def chainMode (c : ℂ) (s : ℝ) (x : ℤ) : ℂ :=
  if x = 1 then c * Complex.exp (↑(-(2 * s)) * Complex.I) else 0

/-- `chainMode c` vanishes at the walls `0` and `2`. -/
theorem chainMode_walls (c : ℂ) (t : ℝ) : chainMode c t 0 = 0 ∧ chainMode c t (((1 : ℕ) : ℤ) + 1) = 0 := by
  simp [chainMode]

/-- `chainMode c` solves the equation at the one site of the chain. -/
theorem chainMode_hasDerivAt (c : ℂ) (t : ℝ) (x : ℤ) (h1 : 1 ≤ x) (h2 : x ≤ ((1 : ℕ) : ℤ)) :
    HasDerivAt (fun s : ℝ => chainMode c s x)
      (Complex.I * (chainMode c t (x + 1) + chainMode c t (x - 1) - 2 * chainMode c t x)) t := by
  obtain rfl : x = 1 := by omega
  have h := (hasDerivAt_exp_neg 2 t).const_mul c
  convert h using 1
  · funext s; simp [chainMode]
  · simp [chainMode]; ring

/-- **FC-U through the statement constant** at `M = 1`: `c e^{−2it} = C₁(t; 1, 1) c` for every complex `c`. Plant
detected: a dropped wall hypothesis changes the application. -/
theorem chainU_one (h : ChainUniqueStatement) (t : ℝ) (c : ℂ) :
    c * Complex.exp (↑(-(2 * t)) * Complex.I) = chainKernel 1 t 1 1 * c := by
  have h1 := h 1 (chainMode c) (chainMode_walls c) (chainMode_hasDerivAt c) t 1 le_rfl (by norm_num)
  rw [Nat.cast_one, Finset.Icc_self, Finset.sum_singleton] at h1
  simpa [chainMode] using h1

/-- **Check (unconditional)**: the instance of FC-U in `chainU_one` is true on the datum `chainKernel_one`. -/
theorem chainU_one_check (t : ℝ) (c : ℂ) :
    c * Complex.exp (↑(-(2 * t)) * Complex.I) = chainKernel 1 t 1 1 * c := by
  rw [chainKernel_one]; ring

/-- **FC-P through the statement constant** at `M = 1`, `x = y = 1`: the left side is `|e^{−2it} − G(t, 0)|`
(`G(t, 0)` is not evaluated for `t ≠ 0`). -/
theorem chainP_one (h : ChainFiniteSizeStatement) (t η : ℝ) (hη : 0 < η) :
    ‖Complex.exp (↑(-(2 * t)) * Complex.I) - lineKernel t 0‖ ≤
      Real.exp (2 * |t| * Real.sinh η) *
        (Real.exp (-(2 * η)) + 2 * (1 + Real.cosh (2 * η)) / (Real.exp (4 * η) - 1)) := by
  have h1 := h 1 t η 1 1 hη le_rfl (by norm_num) le_rfl (by norm_num)
  rw [chainKernel_one, show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at h1
  rw [show 2 * (((1 : ℕ) : ℝ) + 1) * η = 4 * η by push_cast; ring] at h1
  simpa using h1

/-- **FC-P through the statement constant** at `t = 0`: the left side is `0` and the instance is trivial. This layer
has no exact datum for FC-P with a nonzero left side. -/
theorem chainP_one_zero (h : ChainFiniteSizeStatement) (η : ℝ) (hη : 0 < η) :
    0 ≤ Real.exp (-(2 * η)) + 2 * (1 + Real.cosh (2 * η)) / (Real.exp (4 * η) - 1) := by
  have h1 := chainP_one h 0 η hη
  rw [lineKernel_zero, ite_eq_left rfl] at h1
  simpa using h1

/-- **Datum for the planted controls: the unit datum of the ring of 4 sites** over one period, `R₄(0, r) = 0` for
`r = 1, 2, 3` and `R₄(0, 4) = 1`. -/
theorem ringKernel_four_time_zero :
    ringKernel 4 0 1 = 0 ∧ ringKernel 4 0 2 = 0 ∧ ringKernel 4 0 3 = 0 ∧ ringKernel 4 0 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ringKernel_four_one]; simp
  · rw [ringKernel_four_two]; norm_num
  · rw [ringKernel_four_three]; simp
  · rw [ringKernel_four]; norm_num [zpow_ofNat, Complex.I_pow_four]

/-- Datum for the planted control FR-U-d: the mode `k = π/2` on the ring of 4 sites, `u(s, x) = iˣ e^{−2is}` (not
even in the site `x`). -/
noncomputable def iMode (s : ℝ) (x : ℤ) : ℂ := Complex.I ^ x * Complex.exp (↑(-(2 * s)) * Complex.I)

/-- `iMode` has period 4 in the site. -/
theorem iMode_periodic (t : ℝ) (x : ℤ) : iMode t (x + ((4 : ℕ) : ℤ)) = iMode t x := by
  have h4 : Complex.I ^ (((4 : ℕ) : ℤ)) = 1 := by rw [zpow_natCast, Complex.I_pow_four]
  rw [iMode, iMode, zpow_add₀ Complex.I_ne_zero, h4, mul_one]

/-- `iMode` solves `i u′ + Δu = 0` (eigenvalue `2 cos(π/2) − 2 = −2`). -/
theorem iMode_hasDerivAt (t : ℝ) (x : ℤ) :
    HasDerivAt (fun s : ℝ => iMode s x) (Complex.I * (iMode t (x + 1) + iMode t (x - 1) - 2 * iMode t x)) t := by
  have h := (hasDerivAt_exp_neg 2 t).const_mul (Complex.I ^ x)
  have e1 : iMode t (x + 1) = Complex.I * iMode t x := by
    rw [iMode, iMode, zpow_add₀ Complex.I_ne_zero, zpow_one]; ring
  have e2 : iMode t (x - 1) = -Complex.I * iMode t x := by
    rw [iMode, iMode, zpow_sub₀ Complex.I_ne_zero, zpow_one, div_eq_mul_inv, Complex.inv_I]; ring
  rw [e1, e2]
  convert h using 1
  · funext s; rw [iMode]
  · rw [iMode]; push_cast; ring

/-- The values of `iMode` at time 0 over one period: `1, i, −1, −i`. -/
theorem iMode_zero : iMode 0 0 = 1 ∧ iMode 0 1 = Complex.I ∧ iMode 0 2 = -1 ∧ iMode 0 3 = -Complex.I := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [iMode, zpow_ofNat, pow_succ]

/-- The powers of an `n`-th root of unity other than `1` sum to `0` (geometric sum; no kernel is mentioned). -/
theorem sum_pow_root (w : ℂ) (n : ℕ) (hw : w ≠ 1) (hn : w ^ n = 1) : ∑ j ∈ Finset.range n, w ^ j = 0 := by
  rw [geom_sum_eq hw, hn, sub_self, zero_div]

/-- **Datum for the planted controls: the ring of 6 sites at time 0**, `R₆(0, r) = 6⁻¹ Σ_{j<6} (e^{irπ/3})ʲ`. -/
theorem ringKernel_six_time_zero (r : ℤ) :
    ringKernel 6 0 r =
      6⁻¹ * ∑ j ∈ Finset.range 6, Complex.exp (↑((r : ℝ) * (Real.pi / 3)) * Complex.I) ^ j := by
  rw [ringKernel]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `R₆(0, 3) = 0`. -/
theorem ringKernel_six_zero_three : ringKernel 6 0 3 = 0 := by
  have hw : Complex.exp (↑(((3 : ℤ) : ℝ) * (Real.pi / 3)) * Complex.I) = -1 := by
    rw [show ((3 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi by push_cast; ring, Complex.exp_pi_mul_I]
  rw [ringKernel_six_time_zero, hw, sum_pow_root _ _ (by norm_num) (by norm_num), mul_zero]

/-- `R₆(0, −1) = 0`. -/
theorem ringKernel_six_zero_neg_one : ringKernel 6 0 (-1) = 0 := by
  have hθ : ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 3) := by push_cast; ring
  rw [ringKernel_six_time_zero, hθ, sum_pow_root, mul_zero]
  · intro hw
    have h1 := congrArg Complex.re hw
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_three] at h1
    norm_num at h1
  · rw [← Complex.exp_nat_mul,
      show ((6 : ℕ) : ℂ) * (↑(-(Real.pi / 3)) * Complex.I) = -(2 * ↑Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- **Datum: chain of 2 sites at time 0, off the diagonal.** `C₂(0; 1, 2) = R₆(0, −1) − R₆(0, 3) = 0`: the check of
`chainK_two_offdiag` and the witness datum of the planted control FC-K-b. -/
theorem chainKernel_two_zero_offdiag : chainKernel 2 0 1 2 = 0 := by
  have h : chainKernel 2 0 1 2 = ringKernel 6 0 (-1) - ringKernel 6 0 3 := by
    rw [chainKernel]; norm_num
  rw [h, ringKernel_six_zero_neg_one, ringKernel_six_zero_three, sub_zero]

/-- **Datum for the planted control FC-K-d: the ring of 3 sites at time 0**,
`R₃(0, r) = 3⁻¹ Σ_{j<3} (e^{2irπ/3})ʲ`. -/
theorem ringKernel_three_time_zero (r : ℤ) :
    ringKernel 3 0 r =
      3⁻¹ * ∑ j ∈ Finset.range 3, Complex.exp (↑((r : ℝ) * (2 * (Real.pi / 3))) * Complex.I) ^ j := by
  rw [ringKernel]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `R₃(0, 1) = 0`. -/
theorem ringKernel_three_zero_one : ringKernel 3 0 1 = 0 := by
  have hθ : ((1 : ℤ) : ℝ) * (2 * (Real.pi / 3)) = 2 * (Real.pi / 3) := by push_cast; ring
  rw [ringKernel_three_time_zero, hθ, sum_pow_root, mul_zero]
  · intro hw
    have h1 := congrArg Complex.re hw
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_two_mul, Real.cos_pi_div_three] at h1
    norm_num at h1
  · rw [← Complex.exp_nat_mul,
      show ((3 : ℕ) : ℂ) * (↑(2 * (Real.pi / 3)) * Complex.I) = 2 * ↑Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]

/-- `R₃(0, 3) = 1`. -/
theorem ringKernel_three_zero_three : ringKernel 3 0 3 = 1 := by
  have hw : Complex.exp (↑(((3 : ℤ) : ℝ) * (2 * (Real.pi / 3))) * Complex.I) = 1 := by
    rw [show (↑(((3 : ℤ) : ℝ) * (2 * (Real.pi / 3))) : ℂ) * Complex.I = 2 * ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_two_pi_mul_I]
  rw [ringKernel_three_time_zero, hw]
  norm_num

/-- **Datum at a nonzero time: ring of 2 sites against the line**, `t = 1/4`, `r = 0`:
`|R₂ − G| ≥ |G| − |R₂| ≥ (1 − t²) − cos 2t ≥ 0.059`, from `‖I(1/2, 0)‖ ≥ 2π(1 − 1/16)` and
`R₂(t, 0) = e^{−2it} cos 2t`. -/
theorem ring_two_sub_line_lower : 59 / 1000 ≤ ‖ringKernel 2 (1 / 4) 0 - lineKernel (1 / 4) 0‖ := by
  have hG : 15 / 16 ≤ ‖lineKernel (1 / 4) 0‖ := by
    have hl := latticeKernel1_zero_freq_lower (1 / 2)
    rw [lineKernel, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), Int.cast_zero, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
      le_inv_mul_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hR : ‖ringKernel 2 (1 / 4) 0‖ ≤ 8783 / 10000 := by
    have h1 : Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) * Complex.exp (↑(1 / 2 : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    have h2 : Complex.exp (↑(-(4 * (1 / 4 : ℝ))) * Complex.I) =
        Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) * Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e : ringKernel 2 (1 / 4) 0 =
        Complex.exp (↑(-(1 / 2 : ℝ)) * Complex.I) * ((Real.cos (1 / 2) : ℝ) : ℂ) := by
      rw [ringKernel_two, ite_eq_left Even.zero, one_mul, h2, Complex.ofReal_cos, Complex.cos,
        show -(((1 / 2 : ℝ) : ℂ)) * Complex.I = ↑(-(1 / 2 : ℝ)) * Complex.I by push_cast; ring]
      linear_combination (-1 / 2 : ℂ) * h1
    have hc := abs_le.mp (Real.cos_bound (x := 1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hc
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hc.1])]
    linarith [hc.2]
  have h3 := norm_sub_norm_le (lineKernel (1 / 4) 0) (ringKernel 2 (1 / 4) 0)
  rw [norm_sub_rev] at h3
  linarith

/-- **Bite: the time enters the bound of FR-P as `2|t|`.** At `N = 2`, `r = 0`, `t = 1/4`, `η = log 16` the bound
with `|t|` in place of `2|t|` is `2 e^{sinh(log 16)/4} / 255 < 2e²/255 < 0.058`, below the left side `≥ 0.059`. -/
theorem ringP_half_time_false :
    ¬ ‖ringKernel 2 (1 / 4) 0 - lineKernel (1 / 4) 0‖ ≤
      2 * Real.exp (|(1 / 4 : ℝ)| * Real.sinh (Real.log 16)) * Real.cosh (((0 : ℤ) : ℝ) * Real.log 16) /
        (Real.exp (Real.log 16 * ((2 : ℕ) : ℝ)) - 1) := by
  intro h
  have h16 : Real.exp (Real.log 16) = 16 := Real.exp_log (by norm_num)
  have hs : |(1 / 4 : ℝ)| * Real.sinh (Real.log 16) ≤ 1 + 1 := by
    rw [abs_of_pos (by norm_num), Real.sinh_eq, Real.exp_neg, h16]; norm_num
  have he : Real.exp (|(1 / 4 : ℝ)| * Real.sinh (Real.log 16)) ≤ 739 / 100 := by
    refine (Real.exp_le_exp.mpr hs).trans ?_
    rw [Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  rw [Int.cast_zero, zero_mul, Real.cosh_zero, mul_one, Nat.cast_ofNat,
    show Real.log 16 * 2 = Real.log 16 + Real.log 16 by ring, Real.exp_add, h16,
    le_div_iff₀ (by norm_num)] at h
  linarith [ring_two_sub_line_lower]

end OscInt.API.FiniteRingSanity
