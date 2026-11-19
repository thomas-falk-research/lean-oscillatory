/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.PeriodicAnalytic
import OscInt.Front.LatticeCubeRootSanity

/-! # Sanity theorems through the batch-PA statement constants

As for batches LE, LE2 and HC (`docs/lessons.md`, rules 8 and 9): every theorem about a frozen statement of
`OscInt/Statements/PeriodicAnalytic.lean` takes that statement constant as its only statement hypothesis, discharges
its hypotheses on closed data and concludes its conclusion there. No statement of the batch is proved or used
otherwise. Planted copies and witnesses: `docs/replay/plants/2026-11-16-PA/`.

Data:
* `cos3 z = 7 cos 3z`: entire, `2π`-periodic, bounded by `7 cosh 3a` on the strip `|Im z| < a`; Fourier coefficients
  `7π` at `k = ±3` and `0` otherwise; its 3-point trapezoidal sum is `14π` although its integral is `0` (aliasing).
* `expDatum z = (2 + 3i) e^{iz} + 5`: bounded by `√13 e^a + 5` on the strip; coefficients `10π` at `k = 0` and
  `2π(2 + 3i)` at `k = 1`; its 1-point trapezoidal sum is `2π(7 + 3i)`.
* PA-T at `cos3`, `N = 3` and at `expDatum`, `N = 1`, for every `a > 0`. At `cos3` the conclusion is sharp as `a → ∞`
  (the ratio of the two sides tends to `1`: both aliased modes `±3` contribute), so a smaller constant or a faster
  rate is refuted by data; at `expDatum` (one aliased mode) the ratio tends to `2`.
* PA-C at `cos3`, `k = 3` and `k = −3` (tests `|k|`), and at `expDatum`, `k = 1`, for every `a > 0`; sharp as `a → ∞`.
* LC-1 at `t = 1`, `n = 5`, `η = 2` and at `t = −1`, `n = −5` (tests both absolute values): the bound is
  `2π e^{sinh 2 − 10} < 2π/100`, far below the trivial `2π`; at `t = n = η = 0` the bound `2π` is attained.
* Bites on the shared hypothesis `PeriodicAnalyticOn`: `cos3` is not bounded by `1` (bound conjunct); `e^{iz/2}` is not
  admissible on any strip (period conjunct); for `a ≤ 0` every function is admissible (`0 < a` carries content).
  Bite on LC-1: at `η = −1` the bound is false (`0 ≤ η` is needed).
* Data for the planted controls only (last section): `cosRe3 z = 7 cos(3 Re z)` (not analytic; same real-axis values
  as `cos3`; bounded by `7`), `halfExp z = e^{iz/2}` with its two integrals, and `‖I(1/4, 1)‖ ≥ π/8`.

What this layer cannot see: the differentiability conjunct has no unconditional bite here (that `cosRe3` is not
holomorphic is not proved); its removal is refuted in the plant record through `cosRe3`.
-/

namespace OscInt.API.PeriodicAnalyticSanity

open OscInt.Statements OscInt.API.GlobalSanity OscInt.API.LatticeExplicitSanity OscInt.API.LatticeCubeRootSanity

/-- First datum: `7 cos 3z`. -/
noncomputable def cos3 : ℂ → ℂ := fun z => 7 * Complex.cos (3 * z)

/-- Second datum: `(2 + 3i) e^{iz} + 5` (a nonzero mean and one mode, with a non-real coefficient). -/
noncomputable def expDatum : ℂ → ℂ := fun z => (2 + 3 * Complex.I) * Complex.exp (Complex.I * z) + 5

/-- `|cos w| ≤ cosh (Im w)`. -/
theorem norm_cos_le_cosh (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  have h1 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp
  have h3 := norm_add_le (Complex.exp (w * Complex.I)) (Complex.exp (-w * Complex.I))
  rw [Complex.cos, Real.cosh_eq, norm_div, Complex.norm_ofNat]
  rw [h1, h2] at h3
  linarith

/-- `|2 + 3i| = √13`. -/
theorem norm_two_add_three_I : ‖(2 + 3 * Complex.I : ℂ)‖ = Real.sqrt 13 := by
  have := Complex.norm_add_mul_I 2 3
  rw [show ((2 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * Complex.I = 2 + 3 * Complex.I by push_cast; ring] at this
  rw [this]; norm_num

/-- `0` lies in every strip of positive half-width. -/
theorem zero_mem_openStrip (a : ℝ) (ha : 0 < a) : (0 : ℂ) ∈ openStrip a := by
  simpa [openStrip] using ha

/-- `cos3` is admissible on the strip of half-width `a`, with the bound `7 cosh 3a`. -/
theorem cos3_periodicAnalyticOn (a : ℝ) (ha : 0 < a) : PeriodicAnalyticOn cos3 a (7 * Real.cosh (3 * a)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (by unfold cos3; fun_prop : Differentiable ℂ cos3).differentiableOn
  · intro z _
    have := Complex.cos_add_nat_mul_two_pi (3 * z) 3
    simp only [cos3]
    rw [← this]
    congr 2; push_cast; ring
  · intro z hz
    have hz' : |z.im| < a := hz
    have h1 := norm_cos_le_cosh (3 * z)
    have h2 : Real.cosh (3 * z).im ≤ Real.cosh (3 * a) := by
      rw [Real.cosh_le_cosh]
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
      rw [abs_mul, abs_mul, abs_of_pos ha]; norm_num; linarith
    simp only [cos3, norm_mul, Complex.norm_ofNat]
    linarith

/-- `expDatum` is admissible on the strip of half-width `a`, with the bound `√13 e^a + 5`. -/
theorem expDatum_periodicAnalyticOn (a : ℝ) (_ha : 0 < a) :
    PeriodicAnalyticOn expDatum a (Real.sqrt 13 * Real.exp a + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (by unfold expDatum; fun_prop : Differentiable ℂ expDatum).differentiableOn
  · intro z _
    simp only [expDatum]
    rw [show Complex.I * (z + ((2 * Real.pi : ℝ) : ℂ)) = Complex.I * z + 2 * Real.pi * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · intro z hz
    have hz' : |z.im| < a := hz
    have h1 : ‖Complex.exp (Complex.I * z)‖ ≤ Real.exp a := by
      rw [Complex.norm_exp, Real.exp_le_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      linarith [neg_abs_le z.im]
    calc ‖expDatum z‖ ≤ ‖(2 + 3 * Complex.I) * Complex.exp (Complex.I * z)‖ + ‖(5 : ℂ)‖ := norm_add_le _ _
      _ = Real.sqrt 13 * ‖Complex.exp (Complex.I * z)‖ + 5 := by
        rw [norm_mul, norm_two_add_three_I, Complex.norm_ofNat]
      _ ≤ Real.sqrt 13 * Real.exp a + 5 := by
        have := Real.sqrt_nonneg 13
        nlinarith

/-- `∫_0^{2π} e^{imθ} dθ = 0` for an integer `m ≠ 0`. -/
theorem integral_mode_ne_zero (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) = 0 := by
  have hc : ((m : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((m : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) =
      Complex.exp ((m : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by push_cast; ring⟩
  rw [h1, sub_self, zero_div]

/-- `∫_0^{2π} e^{imθ} dθ` is `2π` for `m = 0` and `0` otherwise. -/
theorem integral_mode (m : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) =
      if m = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm; simp
  · exact integral_mode_ne_zero m hm

/-- `∫_0^{2π} (c₁ e^{im₁θ} + c₂ e^{im₂θ}) dθ`. -/
theorem integral_two_modes (c₁ c₂ : ℂ) (m₁ m₂ : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (c₁ * Complex.exp ((m₁ : ℂ) * Complex.I * (θ : ℂ)) +
        c₂ * Complex.exp ((m₂ : ℂ) * Complex.I * (θ : ℂ))) =
      c₁ * (if m₁ = 0 then 2 * (Real.pi : ℂ) else 0) + c₂ * (if m₂ = 0 then 2 * (Real.pi : ℂ) else 0) := by
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous fun θ : ℝ => c₁ * Complex.exp ((m₁ : ℂ) * Complex.I * (θ : ℂ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => c₂ * Complex.exp ((m₂ : ℂ) * Complex.I * (θ : ℂ))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_mode, integral_mode]

/-- `cos3(θ) e^{−ikθ} = (7/2) e^{i(3−k)θ} + (7/2) e^{i(−3−k)θ}`. -/
theorem cos3_mul_mode (θ : ℝ) (k : ℤ) :
    cos3 (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      7 / 2 * Complex.exp (((3 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) +
        7 / 2 * Complex.exp (((-3 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
  have e1 : Complex.exp (3 * (θ : ℂ) * Complex.I) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      Complex.exp (((3 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(3 * (θ : ℂ)) * Complex.I) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      Complex.exp (((-3 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [cos3, Complex.cos]
  linear_combination (7 / 2 : ℂ) * e1 + (7 / 2 : ℂ) * e2

/-- `expDatum(θ) e^{−ikθ} = (2 + 3i) e^{i(1−k)θ} + 5 e^{−ikθ}`. -/
theorem expDatum_mul_mode (θ : ℝ) (k : ℤ) :
    expDatum (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      (2 + 3 * Complex.I) * Complex.exp (((1 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) +
        5 * Complex.exp (((-k : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
  simp only [expDatum]
  rw [add_mul, mul_assoc, ← Complex.exp_add]
  rw [show Complex.I * (θ : ℂ) + ↑(-((k : ℝ) * θ)) * Complex.I = ((1 - k : ℤ) : ℂ) * Complex.I * (θ : ℂ) by
      push_cast; ring,
    show (↑(-((k : ℝ) * θ)) : ℂ) * Complex.I = ((-k : ℤ) : ℂ) * Complex.I * (θ : ℂ) by push_cast; ring]

/-- The Fourier coefficients of `cos3`: `∫_0^{2π} cos3(θ) e^{−ikθ} dθ` is `7π` for `k = ±3` and `0` otherwise. -/
theorem integral_cos3_mul_mode (k : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cos3 (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      7 / 2 * (if 3 - k = 0 then 2 * (Real.pi : ℂ) else 0) + 7 / 2 * (if -3 - k = 0 then 2 * (Real.pi : ℂ) else 0) := by
  simp_rw [cos3_mul_mode]
  exact integral_two_modes _ _ _ _

/-- The Fourier coefficients of `expDatum`: `2π(2 + 3i)` for `k = 1`, `10π` for `k = 0` and `0` otherwise. -/
theorem integral_expDatum_mul_mode (k : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), expDatum (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      (2 + 3 * Complex.I) * (if 1 - k = 0 then 2 * (Real.pi : ℂ) else 0) +
        5 * (if -k = 0 then 2 * (Real.pi : ℂ) else 0) := by
  simp_rw [expDatum_mul_mode]
  exact integral_two_modes _ _ _ _

/-- `∫_0^{2π} cos3 = 0`. -/
theorem integral_cos3 : ∫ θ in (0 : ℝ)..(2 * Real.pi), cos3 (θ : ℂ) = 0 := by
  have h := integral_cos3_mul_mode 0
  simpa using h

/-- `∫_0^{2π} expDatum = 10π`. -/
theorem integral_expDatum : ∫ θ in (0 : ℝ)..(2 * Real.pi), expDatum (θ : ℂ) = 10 * Real.pi := by
  have h := integral_expDatum_mul_mode 0
  simp only [Int.cast_zero, zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one] at h
  rw [h]; norm_num; ring

/-- `∫_0^{2π} cos3(θ) e^{−3iθ} dθ = 7π`, in the shape PA-C produces at `k = 3`. -/
theorem integral_cos3_three :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cos3 (θ : ℂ) * Complex.exp (↑(-(((3 : ℤ) : ℝ) * θ)) * Complex.I) =
      7 * Real.pi := by
  rw [integral_cos3_mul_mode]; norm_num; ring

/-- `∫_0^{2π} cos3(θ) e^{3iθ} dθ = 7π`, in the shape PA-C produces at `k = −3`. -/
theorem integral_cos3_neg_three :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cos3 (θ : ℂ) * Complex.exp (↑(-(((-3 : ℤ) : ℝ) * θ)) * Complex.I) =
      7 * Real.pi := by
  rw [integral_cos3_mul_mode]; norm_num; ring

/-- `∫_0^{2π} expDatum(θ) e^{−iθ} dθ = 2π(2 + 3i)`, in the shape PA-C produces at `k = 1`. -/
theorem integral_expDatum_one :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), expDatum (θ : ℂ) * Complex.exp (↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I) =
      2 * Real.pi * (2 + 3 * Complex.I) := by
  rw [integral_expDatum_mul_mode]; norm_num; ring

/-- `cos3` is `7` at every node `2πj/3`. -/
theorem cos3_node (j : ℕ) : cos3 ((2 * Real.pi * (j : ℝ) / ((3 : ℕ) : ℝ) : ℝ) : ℂ) = 7 := by
  have h := Complex.cos_nat_mul_two_pi j
  simp only [cos3]
  rw [show (3 : ℂ) * ((2 * Real.pi * (j : ℝ) / ((3 : ℕ) : ℝ) : ℝ) : ℂ) = (j : ℂ) * (2 * Real.pi) by
    push_cast; ring, h, mul_one]

/-- The 3-point trapezoidal sum of `cos3` is `14π` (the rule aliases `e^{±3iθ}` to the constant mode). -/
theorem trapezoidalSum_cos3 : trapezoidalSum cos3 3 = 14 * Real.pi := by
  simp only [trapezoidalSum, cos3_node, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- The 1-point trapezoidal sum of `expDatum` is `2π · expDatum(0) = 2π(7 + 3i)`. -/
theorem trapezoidalSum_expDatum : trapezoidalSum expDatum 1 = 2 * Real.pi * (7 + 3 * Complex.I) := by
  simp only [trapezoidalSum, expDatum, Finset.sum_range_one]
  norm_num; ring

/-- `‖c π‖ = ‖c‖ π`. -/
theorem norm_mul_pi (c : ℂ) : ‖c * (Real.pi : ℂ)‖ = ‖c‖ * Real.pi := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- **PA-T through the statement constant** at `cos3`, `N = 3`, every `a > 0`: `|I_3 − I| = 14π`. The two sides have
ratio `(1 + e^{−6a})/(1 − e^{−3a}) → 1` as `a → ∞`: the constant `4π` and the rate `e^{aN}` are both tested. -/
theorem trapezoid_cos3 (h : TrapezoidalRuleStatement) (a : ℝ) (ha : 0 < a) :
    14 * Real.pi ≤ 4 * Real.pi * (7 * Real.cosh (3 * a)) / (Real.exp (a * 3) - 1) := by
  have h1 := h cos3 a (7 * Real.cosh (3 * a)) 3 ha (by norm_num) (cos3_periodicAnalyticOn a ha)
  rw [trapezoidalSum_cos3, integral_cos3, sub_zero, norm_mul_pi, Complex.norm_ofNat, Nat.cast_ofNat] at h1
  exact h1

/-- **PA-T through the statement constant** at `expDatum`, `N = 1`, every `a > 0`: `|I_1 − I| = 2π√13` (a non-real
coefficient and a nonzero mean). -/
theorem trapezoid_expDatum (h : TrapezoidalRuleStatement) (a : ℝ) (ha : 0 < a) :
    2 * Real.pi * Real.sqrt 13 ≤ 4 * Real.pi * (Real.sqrt 13 * Real.exp a + 5) / (Real.exp (a * 1) - 1) := by
  have h1 := h expDatum a (Real.sqrt 13 * Real.exp a + 5) 1 ha (by norm_num) (expDatum_periodicAnalyticOn a ha)
  rw [trapezoidalSum_expDatum, integral_expDatum,
    show 2 * (Real.pi : ℂ) * (7 + 3 * Complex.I) - 10 * Real.pi = 2 * (2 + 3 * Complex.I) * (Real.pi : ℂ) by ring,
    norm_mul_pi, norm_mul, norm_two_add_three_I, Complex.norm_ofNat, Nat.cast_one] at h1
  linarith

/-- **PA-C through the statement constant** at `cos3`, `k = 3`, every `a > 0`: the coefficient is `7π` and the bound
is `7π (1 + e^{−6a})`, sharp as `a → ∞`. -/
theorem fourierCoeff_cos3 (h : FourierCoeffStripStatement) (a : ℝ) (ha : 0 < a) :
    7 * Real.pi ≤ 2 * Real.pi * (7 * Real.cosh (3 * a)) * Real.exp (-(a * 3)) := by
  have h1 := h cos3 a (7 * Real.cosh (3 * a)) 3 ha (cos3_periodicAnalyticOn a ha)
  rw [integral_cos3_three, norm_mul_pi, Complex.norm_ofNat, Int.cast_ofNat, abs_of_pos (by norm_num)] at h1
  exact h1

/-- **PA-C through the statement constant** at `cos3`, `k = −3`: the same conclusion as at `k = 3` (tests `|k|`). -/
theorem fourierCoeff_cos3_neg (h : FourierCoeffStripStatement) (a : ℝ) (ha : 0 < a) :
    7 * Real.pi ≤ 2 * Real.pi * (7 * Real.cosh (3 * a)) * Real.exp (-(a * 3)) := by
  have h1 := h cos3 a (7 * Real.cosh (3 * a)) (-3) ha (cos3_periodicAnalyticOn a ha)
  rw [integral_cos3_neg_three, norm_mul_pi, Complex.norm_ofNat, Int.cast_neg, Int.cast_ofNat, abs_neg,
    abs_of_pos (by norm_num)] at h1
  exact h1

/-- **PA-C through the statement constant** at `expDatum`, `k = 1`, every `a > 0`: the coefficient has modulus `2π√13`
and the bound is `2π(√13 + 5e^{−a})`, sharp as `a → ∞`. -/
theorem fourierCoeff_expDatum (h : FourierCoeffStripStatement) (a : ℝ) (ha : 0 < a) :
    2 * Real.pi * Real.sqrt 13 ≤ 2 * Real.pi * (Real.sqrt 13 * Real.exp a + 5) * Real.exp (-(a * 1)) := by
  have h1 := h expDatum a (Real.sqrt 13 * Real.exp a + 5) 1 ha (expDatum_periodicAnalyticOn a ha)
  rw [integral_expDatum_one,
    show 2 * (Real.pi : ℂ) * (2 + 3 * Complex.I) = 2 * (2 + 3 * Complex.I) * (Real.pi : ℂ) by ring,
    norm_mul_pi, norm_mul, norm_two_add_three_I, Complex.norm_ofNat, Int.cast_one, abs_one] at h1
  linarith

/-- **LC-1 through the statement constant** at `t = 1`, `n = 5`, `η = 2`. -/
theorem lightCone_five (h : LatticeKernel1LightConeStatement) :
    ‖latticeKernel1 1 5‖ ≤ 2 * Real.pi * Real.exp (Real.sinh 2 - 10) := by
  have h1 := h 1 2 5 (by norm_num)
  rw [Int.cast_ofNat, abs_one, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5),
    show (5 : ℝ) * 2 = 10 by norm_num] at h1
  exact h1

/-- **LC-1 through the statement constant** at `t = −1`, `n = −5`, `η = 2`: the same bound (tests `|t|` and `|n|`). -/
theorem lightCone_five_neg (h : LatticeKernel1LightConeStatement) :
    ‖latticeKernel1 (-1) (-5)‖ ≤ 2 * Real.pi * Real.exp (Real.sinh 2 - 10) := by
  have h1 := h (-1) 2 (-5) (by norm_num)
  rw [Int.cast_neg, Int.cast_ofNat, abs_neg, abs_neg, abs_one, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5),
    show (5 : ℝ) * 2 = 10 by norm_num] at h1
  exact h1

/-- `100 < e⁶`. -/
theorem hundred_lt_exp_six : (100 : ℝ) < Real.exp 6 := by
  have h2 := Real.quadratic_le_exp_of_nonneg (x := 2) (by norm_num)
  have h6 : Real.exp 6 = Real.exp 2 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h6]
  calc (100 : ℝ) < 5 ^ 3 := by norm_num
    _ ≤ Real.exp 2 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3

/-- The bound of `lightCone_five` is in the non-trivial regime: below `2π/100`. -/
theorem lightCone_five_nontrivial : 2 * Real.pi * Real.exp (Real.sinh 2 - 10) < 2 * Real.pi / 100 := by
  have he : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hs : Real.sinh 2 < 4 := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-2)]
  have h1 : Real.exp (Real.sinh 2 - 10) < Real.exp (-6) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-6) * Real.exp 6 = 1 := by rw [← Real.exp_add]; norm_num
  have h3 := hundred_lt_exp_six
  have h4 : Real.exp (-6) < 1 / 100 := by nlinarith [Real.exp_pos (-6)]
  nlinarith [Real.pi_pos]

/-- **LC-1 through the statement constant** at `t = 0`, `n = 0`, `η = 0`. -/
theorem lightCone_origin (h : LatticeKernel1LightConeStatement) : ‖latticeKernel1 0 0‖ ≤ 2 * Real.pi := by
  have h1 := h 0 0 0 le_rfl
  rw [Int.cast_zero, abs_zero, zero_mul, zero_mul, sub_zero, Real.exp_zero, mul_one] at h1
  exact h1

/-- The bound of `lightCone_origin` is attained: `‖I(0, 0)‖ = 2π`. -/
theorem norm_latticeKernel1_zero_zero : ‖latticeKernel1 0 0‖ = 2 * Real.pi := by
  rw [latticeKernel1_zero_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Bite on the bound.** `cos3` is not bounded by `1` on the strip of half-width `1/2`: `cos3 0 = 7`. -/
theorem cos3_not_bounded_by_one : ¬ PeriodicAnalyticOn cos3 (1 / 2) 1 := by
  intro h
  have h0 := h.2.2 0 (zero_mem_openStrip _ (by norm_num))
  simp [cos3] at h0

/-- **Bite on the period.** `e^{iz/2}` has period `4π`, not `2π`: no strip of positive half-width and no bound
make it admissible. -/
theorem halfExp_not_periodic (a M : ℝ) (ha : 0 < a) :
    ¬ PeriodicAnalyticOn (fun z => Complex.exp (Complex.I * z / 2)) a M := by
  intro h
  have h0 := h.2.1 0 (zero_mem_openStrip a ha)
  simp only [zero_add, mul_zero, zero_div, Complex.exp_zero] at h0
  rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) / 2 = Real.pi * Complex.I by push_cast; ring,
    Complex.exp_pi_mul_I] at h0
  norm_num at h0

/-- **Bite: `0 ≤ η` is needed in LC-1.** At `t = 1`, `n = 0`, `η = −1` the bound would say
`3π/2 ≤ ‖I(1, 0)‖ ≤ 2π e^{−sinh 1} < π`. -/
theorem lightCone_eta_neg_false :
    ¬ ‖latticeKernel1 1 0‖ ≤ 2 * Real.pi * Real.exp (|(1 : ℝ)| * Real.sinh (-1) - |((0 : ℤ) : ℝ)| * (-1)) := by
  have hl := latticeKernel1_zero_freq_lower 1
  have hs : (1 : ℝ) ≤ Real.sinh 1 := Real.self_le_sinh_iff.mpr zero_le_one
  have h1 : Real.exp (|(1 : ℝ)| * Real.sinh (-1) - |((0 : ℤ) : ℝ)| * (-1)) ≤ Real.exp (-1) := by
    rw [Real.exp_le_exp, Real.sinh_neg]; simp
  have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_one_gt_d9
  have h4 : Real.exp (-1) < 1 / 2 := by nlinarith [Real.exp_pos (-1)]
  have hpi := Real.pi_pos
  exact not_le.mpr (by nlinarith)

/-- **Bite: `0 < a` is needed.** For `a ≤ 0` the strip is empty and every function is admissible with every bound. -/
theorem periodicAnalyticOn_of_nonpos (v : ℂ → ℂ) (a M : ℝ) (ha : a ≤ 0) : PeriodicAnalyticOn v a M := by
  have he : ∀ z, z ∉ openStrip a := fun z hz => absurd (lt_of_lt_of_le hz ha) (not_lt.mpr (abs_nonneg _))
  exact ⟨fun z hz => absurd hz (he z), fun z hz => absurd hz (he z), fun z hz => absurd hz (he z)⟩

/-! ## Data for the planted controls (`docs/replay/plants/2026-11-16-PA/`) -/

/-- A non-analytic function with the real-axis values of `cos3`, bounded by `7` on all of `ℂ`. -/
noncomputable def cosRe3 : ℂ → ℂ := fun z => 7 * Complex.cos (3 * (z.re : ℂ))

/-- On the real axis `cosRe3 = cos3`. -/
theorem cosRe3_ofReal (θ : ℝ) : cosRe3 (θ : ℂ) = cos3 (θ : ℂ) := by simp [cosRe3, cos3]

/-- `cosRe3` is `2π`-periodic on all of `ℂ`. -/
theorem cosRe3_periodic (z : ℂ) : cosRe3 (z + ((2 * Real.pi : ℝ) : ℂ)) = cosRe3 z := by
  have h := Complex.cos_add_nat_mul_two_pi (3 * (z.re : ℂ)) 3
  simp only [cosRe3, Complex.add_re, Complex.ofReal_re]
  rw [← h]
  congr 2; push_cast; ring

/-- `cosRe3` is bounded by `7` on all of `ℂ`. -/
theorem norm_cosRe3_le (z : ℂ) : ‖cosRe3 z‖ ≤ 7 := by
  have h := norm_cos_le_cosh (3 * (z.re : ℂ))
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.ofReal_im, mul_zero, Complex.im_ofNat, Complex.ofReal_re,
    zero_mul, add_zero, Real.cosh_zero] at h
  simp only [cosRe3, norm_mul, Complex.norm_ofNat]
  linarith

/-- The 3-point trapezoidal sum of `cosRe3` is that of `cos3`. -/
theorem trapezoidalSum_cosRe3 : trapezoidalSum cosRe3 3 = 14 * Real.pi := by
  rw [← trapezoidalSum_cos3]
  simp only [trapezoidalSum, cosRe3_ofReal]

/-- `∫_0^{2π} cosRe3 = 0`. -/
theorem integral_cosRe3 : ∫ θ in (0 : ℝ)..(2 * Real.pi), cosRe3 (θ : ℂ) = 0 := by
  simp_rw [cosRe3_ofReal]
  exact integral_cos3

/-- The coefficient of `cosRe3` at `k = 3` is `7π`. -/
theorem integral_cosRe3_three :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), cosRe3 (θ : ℂ) * Complex.exp (↑(-(((3 : ℤ) : ℝ) * θ)) * Complex.I) =
      7 * Real.pi := by
  simp_rw [cosRe3_ofReal]
  exact integral_cos3_three

/-- `e^{iz/2}`: entire, bounded on every strip, of period `4π` (the function of `halfExp_not_periodic`). -/
noncomputable def halfExp : ℂ → ℂ := fun z => Complex.exp (Complex.I * z / 2)

/-- `halfExp` is entire. -/
theorem halfExp_differentiable : Differentiable ℂ halfExp := by unfold halfExp; fun_prop

/-- `halfExp` is bounded by `e⁵` on the strip of half-width `10`. -/
theorem norm_halfExp_le (z : ℂ) (hz : z ∈ openStrip 10) : ‖halfExp z‖ ≤ Real.exp 5 := by
  have hz' : |z.im| < 10 := hz
  rw [halfExp, Complex.norm_exp, Real.exp_le_exp]
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  linarith [neg_abs_le z.im]

/-- The 1-point trapezoidal sum of `halfExp` is `2π`. -/
theorem trapezoidalSum_halfExp : trapezoidalSum halfExp 1 = 2 * Real.pi := by
  simp [trapezoidalSum, halfExp]

/-- `∫_0^{2π} e^{iθ/2} dθ = 4i`. -/
theorem integral_halfExp : ∫ θ in (0 : ℝ)..(2 * Real.pi), halfExp (θ : ℂ) = 4 * Complex.I := by
  have hc : (Complex.I / 2 : ℂ) ≠ 0 := by simp
  have hf : (fun θ : ℝ => halfExp (θ : ℂ)) = fun θ : ℝ => Complex.exp (Complex.I / 2 * (θ : ℂ)) := by
    funext θ; simp only [halfExp]; congr 1; ring
  rw [hf, integral_exp_mul_complex hc,
    show Complex.I / 2 * ((2 * Real.pi : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-4 : ℂ) * Complex.I_sq

/-- `∫_0^{2π} e^{iθ/2} e^{−iθ} dθ = −4i`, in the shape PA-C produces at `k = 1`. -/
theorem integral_halfExp_one :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), halfExp (θ : ℂ) * Complex.exp (↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I) =
      -(4 * Complex.I) := by
  have hc : (-(Complex.I / 2) : ℂ) ≠ 0 := by simp
  have hf : (fun θ : ℝ => halfExp (θ : ℂ) * Complex.exp (↑(-(((1 : ℤ) : ℝ) * θ)) * Complex.I)) =
      fun θ : ℝ => Complex.exp (-(Complex.I / 2) * (θ : ℂ)) := by
    funext θ; simp only [halfExp]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hf, integral_exp_mul_complex hc,
    show -(Complex.I / 2) * ((2 * Real.pi : ℝ) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (4 : ℂ) * Complex.I_sq

/-- `∫_{−π}^{π} cos k · e^{ik} dk = π`. -/
theorem integral_cos_mul_exp :
    ∫ k in (-Real.pi)..Real.pi, (Real.cos k : ℂ) * Complex.exp (↑k * Complex.I) = Real.pi := by
  have h2 := integral_exp_int_mul 2 (by norm_num)
  have hpt : ∀ k : ℝ, (Real.cos k : ℂ) * Complex.exp (↑k * Complex.I) =
      1 / 2 + 1 / 2 * Complex.exp (↑(((2 : ℤ) : ℝ) * k) * Complex.I) := by
    intro k
    have e : Complex.exp (↑(((2 : ℤ) : ℝ) * k) * Complex.I) =
        Complex.exp (↑k * Complex.I) * Complex.exp (↑k * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e' : Complex.exp (-↑k * Complex.I) * Complex.exp (↑k * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_cos, Complex.cos, e]
    linear_combination (1 / 2 : ℂ) * e'
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun _ : ℝ => (1 / 2 : ℂ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun k : ℝ =>
      1 / 2 * Complex.exp (↑(((2 : ℤ) : ℝ) * k) * Complex.I)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, h2, intervalIntegral.integral_const]
  simp
  ring

/-- `‖I(t, 1) − iπt‖ ≤ 2πt²` for `|t| ≤ 1`: first-order expansion of `e^{it cos k}`. -/
theorem latticeKernel1_one_approx (t : ℝ) (ht : |t| ≤ 1) :
    ‖latticeKernel1 t 1 - Real.pi * t * Complex.I‖ ≤ 2 * Real.pi * t ^ 2 := by
  have h1 := integral_exp_int_mul 1 one_ne_zero
  have hR : ∀ k : ℝ, ‖(Complex.exp (↑(t * Real.cos k) * Complex.I) - 1 - ↑(t * Real.cos k) * Complex.I) *
      Complex.exp (↑k * Complex.I)‖ ≤ t ^ 2 := by
    intro k
    have hx : ‖(↑(t * Real.cos k) : ℂ) * Complex.I‖ = |t| * |Real.cos k| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hc := Real.abs_cos_le_one k
    have hle : |t| * |Real.cos k| ≤ 1 := by nlinarith [abs_nonneg t, abs_nonneg (Real.cos k)]
    have h := Complex.norm_exp_sub_one_sub_id_le (hx.trans_le hle)
    rw [hx] at h
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    refine h.trans ?_
    rw [mul_pow, sq_abs]
    have hc2 : |Real.cos k| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos k)]
    nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg t)]
  have hdec : ∀ k : ℝ, Complex.exp (↑(t * Real.cos k + 1 * k) * Complex.I) =
      Complex.exp (↑(((1 : ℤ) : ℝ) * k) * Complex.I) +
        (t * Complex.I) * ((Real.cos k : ℂ) * Complex.exp (↑k * Complex.I)) +
        (Complex.exp (↑(t * Real.cos k) * Complex.I) - 1 - ↑(t * Real.cos k) * Complex.I) *
          Complex.exp (↑k * Complex.I) := by
    intro k
    rw [show (↑(t * Real.cos k + 1 * k) : ℂ) * Complex.I = ↑(t * Real.cos k) * Complex.I + ↑k * Complex.I by
      push_cast; ring, Complex.exp_add, Int.cast_one, one_mul]
    push_cast; ring
  have hint : latticeKernel1 t 1 - Real.pi * t * Complex.I =
      ∫ k in (-Real.pi)..Real.pi, (Complex.exp (↑(t * Real.cos k) * Complex.I) - 1 -
        ↑(t * Real.cos k) * Complex.I) * Complex.exp (↑k * Complex.I) := by
    rw [latticeKernel1]
    simp_rw [hdec]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), h1, intervalIntegral.integral_const_mul,
      integral_cos_mul_exp]
    ring
  rw [hint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi) (fun k _ => hR k)
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity)] at hb
  linarith

/-- `‖I(1/4, 1)‖ ≥ π/8`: the kernel does not vanish strictly outside the light cone `|n| ≤ |t|`. -/
theorem latticeKernel1_quarter_one_lower : Real.pi / 8 ≤ ‖latticeKernel1 (1 / 4) 1‖ := by
  have h := latticeKernel1_one_approx (1 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have h2 := norm_sub_norm_le ((Real.pi : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I) (latticeKernel1 (1 / 4) 1)
  rw [norm_sub_rev] at h2
  have h3 : ‖(Real.pi : ℂ) * ((1 / 4 : ℝ) : ℂ) * Complex.I‖ = Real.pi / 4 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos (by norm_num)]
    ring
  have hpi := Real.pi_pos
  nlinarith

end OscInt.API.PeriodicAnalyticSanity
