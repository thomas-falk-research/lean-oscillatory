/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.SecondDerivSharpSanity

/-! # Second sanity layer for the batch-VC2 statement constants

Answers the blind pre-proof review of batch VC2: mutations of the frozen statements of
`OscInt/Statements/SecondDerivSharp.lean` that the first layer (`OscInt/Front/SecondDerivSharpSanity.lean`) does not
detect. Same discipline (`docs/lessons.md`, rules 8 and 9): a theorem about a frozen statement takes that statement
constant as its only statement hypothesis and concludes on closed data; everything else is an unconditional lemma on
data (fixed numbers and explicit functions). No statement of the batch is proved or used otherwise, and nothing here
bounds `vdc2Profile w` (written `A(w)`) or `∫ e^{if}` for general `w` or `f`.
Planted copies and witnesses of this layer: `docs/replay/plants/2026-11-16-VC2-second/`.

Written in scratch by an agent of the lead; lead, agent and reviewers are AI agents of one model family.

What the first layer could not see, and the datum added here:
* **The power of `λ` and of `μ`.** The first layer had one scaled datum (`λ = μ = 100` on `[−1/10, 1/10]`, left side
  `≥ 0.175`), which refutes `μ^e` in VC2-K only for `e < −0.65`, and no exponent above `−1/2`. Here, by the linear
  changes of variable `x = 10u` and `x = u/10` in `quad_norm_lower` (fixed numbers; `smallCurv_integral_eq`,
  `largeCurv_integral_eq`): the **small curvature** `λ = 1/100` on `[−21, 21]`, where the integral has modulus
  `≥ 33` and the bounds read `A(w)·10` (VC2-S) and `35` (VC2-K); the **large curvature** `λ = 100` on
  `[−21/100, 21/100]`, modulus `≥ 33/100`, bounds `A(w)/10` and `7/20`. Each instance is given in the literal form of
  the statement and simplified. Exponents above `−1/2` are tested at the first datum, below `−1/2` at the second:
  with these certified values, VC2-K with `μ^e` in place of `μ^{−1/2}` is refuted for `e > −0.4872` and for
  `e < −0.5128`; VC2-S with `/λ^e` in place of `/√λ` is refuted, with the trivial bound `A ≤ 26/5` of the witness
  files, for `e < 0.4013` and for `e > 0.5988`. Exponents in between are not separated from the true one by these data.
* **Sharper certified constants** (no new analysis: the polynomials of the first layer, not rounded to `33/10`):
  `A(441/200) ≥ 3.35007` (exact value of the polynomial bound: `profilePrim_value`; strictly above `67/20`) and
  `|∫_{−21/10}^{21/10} e^{ix²/2} dx| ≥ 3.358` (from `Re ≥ 2.566`, `Im ≥ 2.1666`). Through the constants: VC2-N is
  within 4.3% of a value of `A`, VC2-K within 4.1% of a value of the integral, VC2-S forces `sup_{[0, π]} A ≥ 3.358`
  (van der Corput's constant is `3.3643…`).
* **A phase whose second derivative is not constant**: `f = x²/2 + x⁴/12` (`f′ = x + x³/3`, `f″ = 1 + x²`), which
  satisfies the hypotheses of VC2-S and VC2-K with `λ = μ = 1` on every interval, with strict inequality away from
  `0` (`quartic_rate_not_exact`, `quartic_second_not_exact`). The instances on `[−c, c]` are stated in the literal
  form; the integral is not evaluated, so they carry no numerical test: their point is that the hypotheses are used
  as inequalities.
* Data for the planted controls only (last section): `(1/100)^{−1/3} ≤ 5`, `(1/100)^{1/4} ≥ 1/4`,
  `100^{−3/5} ≤ 1/15`, `100^{3/5} > 520/33`.

What this layer still cannot see (verdicts NOT DETECTED in the plant record): the range `[0, π]` of `w` in VC2-S
against `[0, 441/200]` (needs an upper bound for `A` on an interval, a piece of VC2-N); `f` against `f′` inside the
exponential of VC2-S at the data of the two layers; the integrand `e^{ix²/2}` against `e^{ix²}` in VC2-A (needs an
upper bound for an oscillatory integral); the weight of `∫|ψ′|` in the amplitude norm of VC2-K (needs a cut-off
amplitude with a certified left side above `1.75`).
-/

namespace OscInt.API.SecondDerivSharpSanity2

open OscInt.Statements OscInt.API.SecondDerivSharpSanity Set

/-! ## A. The power of `λ` and `μ`: the quadratic datum under two linear changes of variable -/

/-- `√(1/100) = 1/10`. -/
theorem sqrt_hundredth : Real.sqrt (1 / 100) = 1 / 10 := by
  rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `(1/100)^{−1/2} = 10`, in the shape of VC2-K. -/
theorem rpow_neg_half_hundredth : (1 / 100 : ℝ) ^ (-(1 : ℝ) / 2) = 10 := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, sqrt_hundredth]
  norm_num

/-- **Small curvature, change of variable `x = 10u`.**
`∫_{−21}^{21} e^{i(1/100)x²/2} dx = 10 ∫_{−21/10}^{21/10} e^{iu²/2} du`. -/
theorem smallCurv_integral_eq :
    ∫ x in (-21 : ℝ)..21, Complex.exp (((1 / 100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) =
      (10 : ℝ) • ∫ u in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (-21 : ℝ)) (b := 21)
    (fun u : ℝ => Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) (1 / 10)
  have e1 : (1 / 10 : ℝ) * (-21) = -(21 / 10) := by norm_num
  have e2 : (1 / 10 : ℝ) * 21 = 21 / 10 := by norm_num
  rw [e1, e2] at h
  rw [← h, smul_smul]
  have hf : ∀ x : ℝ, ((1 / 10 * x) ^ 2 / 2 : ℝ) = 1 / 100 * x ^ 2 / 2 := fun x => by ring
  simp only [hf]
  norm_num

/-- **Large curvature, change of variable `x = u/10`.**
`∫_{−21/100}^{21/100} e^{i·100x²/2} dx = (1/10) ∫_{−21/10}^{21/10} e^{iu²/2} du`. -/
theorem largeCurv_integral_eq :
    ∫ x in (-(21 / 100 : ℝ))..(21 / 100), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) =
      (1 / 10 : ℝ) • ∫ u in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (-(21 / 100) : ℝ)) (b := 21 / 100)
    (fun u : ℝ => Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) 10
  have e1 : (10 : ℝ) * (-(21 / 100)) = -(21 / 10) := by norm_num
  have e2 : (10 : ℝ) * (21 / 100) = 21 / 10 := by norm_num
  rw [e1, e2] at h
  rw [← h, smul_smul]
  have hf : ∀ x : ℝ, ((10 * x) ^ 2 / 2 : ℝ) = 100 * x ^ 2 / 2 := fun x => by ring
  simp only [hf]
  norm_num

/-- **A1. Certified value at small curvature.** `33 ≤ |∫_{−21}^{21} e^{i(1/100)x²/2} dx|` (true value `33.6141…`;
ten times `quad_norm_lower`). -/
theorem smallCurv_norm_lower :
    330 / 10 ≤ ‖∫ x in (-21 : ℝ)..21, Complex.exp (((1 / 100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  rw [smallCurv_integral_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
  linarith [quad_norm_lower]

/-- **A2. Certified value at large curvature, at the extremal width.**
`33/100 ≤ |∫_{−21/100}^{21/100} e^{i·100x²/2} dx|` (true value `0.336141…`; a tenth of `quad_norm_lower`). -/
theorem largeCurv_norm_lower :
    33 / 100 ≤
      ‖∫ x in (-(21 / 100 : ℝ))..(21 / 100), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  rw [largeCurv_integral_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
  linarith [quad_norm_lower]

/-- The left side of VC2-K at the small-curvature datum (`p = 0`, `ψ = 1`) is the integral of `smallCurv_norm_lower`. -/
theorem oscInt_smallCurv :
    oscInt (fun x => 1 / 100 * x ^ 2 / 2 + 0 * x) (fun _ => 1) (-21) 21 =
      ∫ x in (-21 : ℝ)..21, Complex.exp (((1 / 100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  unfold oscInt
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [zero_mul, add_zero, mul_one]

/-- The left side of VC2-K at the large-curvature datum (`p = 0`, `ψ = 1`) is the integral of `largeCurv_norm_lower`. -/
theorem oscInt_largeCurv :
    oscInt (fun x => 100 * x ^ 2 / 2 + 0 * x) (fun _ => 1) (-(21 / 100)) (21 / 100) =
      ∫ x in (-(21 / 100 : ℝ))..(21 / 100), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  unfold oscInt
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [zero_mul, add_zero, mul_one]

/-- The left side of VC2-K at the quadratic datum on `[−21/10, 21/10]` (`p = 0`, `ψ = 1`). -/
theorem oscInt_quad :
    oscInt (fun x => x ^ 2 / 2 + 0 * x) (fun _ => 1) (-(21 / 10)) (21 / 10) =
      ∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  unfold oscInt
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [zero_mul, add_zero, mul_one]

/-- The bound of VC2-K at `μ = 1/100`, `ampNorm = 1` is `35`. -/
theorem smallCurv_bound_value : (7 / 2 : ℝ) * (1 / 100 : ℝ) ^ (-(1 : ℝ) / 2) * 1 = 35 := by
  rw [rpow_neg_half_hundredth]
  norm_num

/-- The bound of VC2-K at `μ = 100`, `ampNorm = 1` is `7/20`. -/
theorem largeCurv_bound_value : (7 / 2 : ℝ) * (100 : ℝ) ^ (-(1 : ℝ) / 2) * 1 = 7 / 20 := by
  rw [rpow_neg_half_hundred]
  norm_num

/-! ## A4. Sharper certified constants from the polynomials of the first layer -/

/-- The exact value of the polynomial bound of the first layer: `profilePrim(21/10) − profilePrim(0)`
(`1.6750378…`; twice it is `3.3500756…`). -/
theorem profilePrim_value :
    profilePrim (21 / 10) - profilePrim 0 = 5988260236461868197 / 3575000000000000000 := by
  unfold profilePrim
  norm_num

/-- **Certified value, not rounded.** `3.35007 ≤ A(441/200)` (true value `3.35396…`). -/
theorem vdc2Profile_lower_sharp : 335007 / 100000 ≤ vdc2Profile (441 / 200) := by
  have h := sub_le_integral_of_le (F := profilePrim) (P := fun u => sinLow (441 / 200 - u ^ 2 / 2))
    (g := fun u => Real.sin (441 / 200 - u ^ 2 / 2)) (a := 0) (b := 21 / 10) (by norm_num)
    profilePrim_hasDerivAt (by unfold sinLow; fun_prop) (by fun_prop)
    (fun u hu => sinLow_le_sin _ (by nlinarith [hu.1, hu.2]))
  rw [profilePrim_value] at h
  unfold vdc2Profile
  rw [sqrt_two_mul_w]
  linarith

/-- `67/20 ≤ A(441/200)`. -/
theorem vdc2Profile_lower_67 : 67 / 20 ≤ vdc2Profile (441 / 200) := by
  linarith [vdc2Profile_lower_sharp]

/-- `67/20 < A(441/200)`, strictly (margin `7 · 10⁻⁵`). -/
theorem vdc2Profile_gt_67 : 67 / 20 < vdc2Profile (441 / 200) := by
  linarith [vdc2Profile_lower_sharp]

/-- `2.566 ≤ Re ∫_{−21/10}^{21/10} e^{ix²/2} dx` (true value `2.5698…`; the polynomial bound gives `2.56602…`). -/
theorem quad_re_lower_sharp :
    1283 / 500 ≤ (∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).re := by
  rw [re_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_re]
  have h := sub_le_integral_of_le (F := cosPrim) (P := fun x => cosLow (x ^ 2 / 2))
    (g := fun x => Real.cos (x ^ 2 / 2)) (a := -(21 / 10)) (b := 21 / 10) (by norm_num) cosPrim_hasDerivAt
    (by unfold cosLow; fun_prop) (by fun_prop) (fun x _ => cosLow_le_cos _ (by positivity))
  have hv : (1283 / 500 : ℝ) ≤ cosPrim (21 / 10) - cosPrim (-(21 / 10)) := by
    unfold cosPrim
    norm_num
  linarith

/-- `2.1666 ≤ Im ∫_{−21/10}^{21/10} e^{ix²/2} dx` (true value `2.1674…`; the polynomial bound gives `2.16669…`). -/
theorem quad_im_lower_sharp :
    10833 / 5000 ≤ (∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).im := by
  rw [im_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_im]
  have h := sub_le_integral_of_le (F := sinPrim) (P := fun x => sinLow (x ^ 2 / 2))
    (g := fun x => Real.sin (x ^ 2 / 2)) (a := -(21 / 10)) (b := 21 / 10) (by norm_num) sinPrim_hasDerivAt
    (by unfold sinLow; fun_prop) (by fun_prop) (fun x _ => sinLow_le_sin _ (by positivity))
  have hv : (10833 / 5000 : ℝ) ≤ sinPrim (21 / 10) - sinPrim (-(21 / 10)) := by
    unfold sinPrim
    norm_num
  linarith

/-- **Certified value, not rounded.** `3.358 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|` (true value `3.36141…`;
`2.566² + 2.1666² = 11.2785… ≥ 3.358² = 11.2761…`). -/
theorem quad_norm_lower_sharp :
    1679 / 500 ≤ ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ :=
  le_norm_of_re_im (by norm_num) (by norm_num) (by norm_num) quad_re_lower_sharp quad_im_lower_sharp

/-- `67/20 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|`. -/
theorem quad_norm_lower_67 :
    67 / 20 ≤ ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  linarith [quad_norm_lower_sharp]

/-- `67/20 < |∫_{−21/10}^{21/10} e^{ix²/2} dx|`, strictly (margin `0.008`). -/
theorem quad_norm_gt_67 :
    67 / 20 < ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  linarith [quad_norm_lower_sharp]

/-! ## B1. A phase whose second derivative is not constant: `f = x²/2 + x⁴/12` -/

/-- The quartic datum `x ↦ x²/2 + x⁴/12` has derivative `x ↦ x + x³/3` on every interval. -/
theorem quartic_hasDerivOn (a b : ℝ) :
    HasDerivOn (fun x => x ^ 2 / 2 + x ^ 4 / 12) (fun x => x + x ^ 3 / 3) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2 + x ^ 4 / 12) (x + x ^ 3 / 3) x := fun x => by
    have h := (hasDerivAt_monomial (1 / 2) 1 x).fun_add (hasDerivAt_monomial (1 / 12) 3 x)
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- `x ↦ x + x³/3` has derivative `x ↦ 1 + x²` on every interval. -/
theorem quarticDeriv_hasDerivOn (a b : ℝ) : HasDerivOn (fun x => x + x ^ 3 / 3) (fun x => 1 + x ^ 2) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x + x ^ 3 / 3) (1 + x ^ 2) x := fun x => by
    have h := (hasDerivAt_monomial 1 0 x).fun_add (hasDerivAt_monomial (1 / 3) 2 x)
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- `x ↦ x + x³/3` increases at rate `1` on every interval: for `x ≤ y`,
`y − x + (y³ − x³)/3 ≥ y − x` because the cube is monotone (`y³ − x³ = (y − x)(y² + xy + x²)`). -/
theorem quartic_increases (a b : ℝ) : DerivIncreasesAtRate (fun x => x + x ^ 3 / 3) a b 1 := by
  intro x _ y _ hxy
  have h : 0 ≤ (y - x) * (y ^ 2 + x * y + x ^ 2) :=
    mul_nonneg (sub_nonneg.2 hxy) (by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y])
  show 1 * (y - x) ≤ y + y ^ 3 / 3 - (x + x ^ 3 / 3)
  nlinarith [h]

/-- `1 ≤ |1 + x²|`: the second derivative of the quartic datum has modulus at least `1`. -/
theorem quartic_second_ge (x : ℝ) : 1 ≤ |1 + x ^ 2| := by
  rw [abs_of_pos (by positivity)]
  nlinarith [sq_nonneg x]

/-- **Bite.** The rate of the quartic datum is not exactly `1` on `(−1, 1)`: the rate hypothesis of VC2-S is used
as an inequality (at `x = 0`, `y = 1/2`: `1/2 < 1/2 + 1/24`). -/
theorem quartic_rate_not_exact :
    ¬ ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, x ≤ y → 1 * (y - x) = y + y ^ 3 / 3 - (x + x ^ 3 / 3) := by
  intro h
  have h1 := h 0 ⟨by norm_num, by norm_num⟩ (1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
  norm_num at h1

/-- **Bite.** The second derivative of the quartic datum does not have constant modulus `1` on `(−1, 1)`: the
lower bound of VC2-K is used as an inequality (at `x = 1/2`: `|1 + 1/4| = 5/4`). -/
theorem quartic_second_not_exact : ¬ ∀ x ∈ Ioo (-1 : ℝ) 1, |1 + x ^ 2| = 1 := by
  intro h
  have h1 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [abs_of_pos (by norm_num)] at h1
  norm_num at h1

/-! ## Through the statement constants -/

/-- **VC2-S at small curvature, literal** (`λ = 1/100`, `f = (1/100)x²/2` on `[−21, 21]`). -/
theorem sharp_smallCurv_literal (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in (-21 : ℝ)..21, Complex.exp (((1 / 100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        vdc2Profile w / Real.sqrt (1 / 100) :=
  h (fun x => 1 / 100 * x ^ 2 / 2) (fun x => 1 / 100 * x) (-21) 21 (1 / 100) (by norm_num) (by norm_num)
    (scaled_hasDerivOn _ _ _) (scaled_increases _ _ _)

/-- **VC2-S at small curvature, with the certified value**: `33 ≤ A(w)/√(1/100)` for some `w ∈ [0, π]`. -/
theorem sharp_smallCurv (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 33 ≤ vdc2Profile w / Real.sqrt (1 / 100) := by
  obtain ⟨w, hw, hle⟩ := sharp_smallCurv_literal h
  exact ⟨w, hw, by linarith [smallCurv_norm_lower]⟩

/-- **VC2-S at small curvature, simplified** (`√(1/100) = 1/10`): `33/10 ≤ A(w)` for some `w ∈ [0, π]`, the same
conclusion as at `λ = 1` (`sharp_profile_large`): the factor `10` of the integral is the factor `λ^{−1/2}`. -/
theorem sharp_smallCurv_simplified (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 33 / 10 ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := sharp_smallCurv h
  rw [sqrt_hundredth] at hle
  have h2 : vdc2Profile w / (1 / 10) = 10 * vdc2Profile w := by ring
  exact ⟨w, hw, by linarith⟩

/-- **VC2-S at large curvature, literal** (`λ = 100`, `f = 100x²/2` on `[−21/100, 21/100]`). -/
theorem sharp_largeCurv_literal (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in (-(21 / 100 : ℝ))..(21 / 100), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        vdc2Profile w / Real.sqrt 100 :=
  h (fun x => 100 * x ^ 2 / 2) (fun x => 100 * x) (-(21 / 100)) (21 / 100) 100 (by norm_num) (by norm_num)
    (scaled_hasDerivOn _ _ _) (scaled_increases _ _ _)

/-- **VC2-S at large curvature, with the certified value**: `33/100 ≤ A(w)/√100` for some `w ∈ [0, π]`. -/
theorem sharp_largeCurv (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 33 / 100 ≤ vdc2Profile w / Real.sqrt 100 := by
  obtain ⟨w, hw, hle⟩ := sharp_largeCurv_literal h
  exact ⟨w, hw, by linarith [largeCurv_norm_lower]⟩

/-- **VC2-S at large curvature, simplified** (`√100 = 10`): `33/10 ≤ A(w)` for some `w ∈ [0, π]`. -/
theorem sharp_largeCurv_simplified (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 33 / 10 ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := sharp_largeCurv h
  rw [sqrt_hundred] at hle
  have h2 : vdc2Profile w / 10 = 1 / 10 * vdc2Profile w := by ring
  exact ⟨w, hw, by linarith⟩

/-- **VC2-S bites, not rounded**: it forces `A(w) ≥ 3.358` for some `w ∈ [0, π]` (van der Corput's constant is
`3.3643…`). -/
theorem sharp_profile_large_sharp (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 1679 / 500 ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := sharp_quadratic h (21 / 10) (by norm_num)
  exact ⟨w, hw, quad_norm_lower_sharp.trans hle⟩

/-- **VC2-S at the quartic phase, literal** (`λ = 1`, `f = x²/2 + x⁴/12` on `[−c, c]`; the rate is not exact). -/
theorem sharp_quartic (h : SecondDerivSharpStatement) (c : ℝ) (hc : 0 ≤ c) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in (-c)..c, Complex.exp (((x ^ 2 / 2 + x ^ 4 / 12 : ℝ) : ℂ) * Complex.I)‖ ≤
        vdc2Profile w / Real.sqrt 1 :=
  h (fun x => x ^ 2 / 2 + x ^ 4 / 12) (fun x => x + x ^ 3 / 3) (-c) c 1 (by linarith) one_pos
    (quartic_hasDerivOn _ _) (quartic_increases _ _)

/-- **VC2-A at `w = 441/200`, not rounded**: `3.35007 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|` (which
`quad_norm_lower_sharp` proves directly with `3.358`: the instance is consistent). -/
theorem attained_at_sharp (h : SecondDerivAttainedStatement) :
    335007 / 100000 ≤
      ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  have h1 := h (441 / 200) (by norm_num)
  rw [sqrt_two_mul_w] at h1
  exact vdc2Profile_lower_sharp.trans h1

/-- **VC2-N is within 4.3% of a value of `A`**: `67/20 < A(441/200) ≤ 7/2`. -/
theorem profile_within_sharp (h : Vdc2ProfileBoundStatement) :
    67 / 20 < vdc2Profile (441 / 200) ∧ vdc2Profile (441 / 200) ≤ 7 / 2 :=
  ⟨vdc2Profile_gt_67, h (441 / 200) ⟨by norm_num, by linarith [Real.pi_gt_three]⟩⟩

/-- **VC2-K at small curvature, literal** (`φ = (1/100)x²/2`, `μ = 1/100`, `p = 0`, `ψ = 1` on `[−21, 21]`). -/
theorem sevenHalves_smallCurv_literal (h : SecondDerivSevenHalvesStatement) :
    ‖oscInt (fun x => 1 / 100 * x ^ 2 / 2 + 0 * x) (fun _ => 1) (-21) 21‖ ≤
      (7 / 2 : ℝ) * (1 / 100 : ℝ) ^ (-(1 : ℝ) / 2) * ampNorm (fun _ => 1) (fun _ => 0) (-21) 21 :=
  h (fun x => 1 / 100 * x ^ 2 / 2) (fun x => 1 / 100 * x) (fun _ => 1 / 100) (fun _ => 1) (fun _ => 0) (-21) 21
    (1 / 100) 0 (by norm_num) (by norm_num) (scaled_hasDerivOn _ _ _) (scaledLinear_hasDerivOn _ _ _)
    (fun x _ => by simp) (sanity_amplitude_one _ _).1

/-- **VC2-K at small curvature, with the certified value**: `33 ≤ (7/2)·(1/100)^{−1/2}·1` (which is `33 ≤ 35`:
`smallCurv_bound_value`). -/
theorem sevenHalves_smallCurv (h : SecondDerivSevenHalvesStatement) :
    33 ≤ (7 / 2 : ℝ) * (1 / 100 : ℝ) ^ (-(1 : ℝ) / 2) * 1 := by
  have h1 := sevenHalves_smallCurv_literal h
  rw [(sanity_amplitude_one _ _).2, oscInt_smallCurv] at h1
  linarith [smallCurv_norm_lower]

/-- **VC2-K at small curvature, simplified**: `|∫_{−21}^{21} e^{i(1/100)x²/2} dx| ≤ 35` (and the left side is at
least `33` by `smallCurv_norm_lower`). -/
theorem sevenHalves_smallCurv_simplified (h : SecondDerivSevenHalvesStatement) :
    ‖∫ x in (-21 : ℝ)..21, Complex.exp (((1 / 100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 35 := by
  have h1 := sevenHalves_smallCurv_literal h
  rw [(sanity_amplitude_one _ _).2, oscInt_smallCurv, smallCurv_bound_value] at h1
  exact h1

/-- **VC2-K at large curvature, literal** (`φ = 100x²/2`, `μ = 100`, `p = 0`, `ψ = 1` on `[−21/100, 21/100]`). -/
theorem sevenHalves_largeCurv_literal (h : SecondDerivSevenHalvesStatement) :
    ‖oscInt (fun x => 100 * x ^ 2 / 2 + 0 * x) (fun _ => 1) (-(21 / 100)) (21 / 100)‖ ≤
      (7 / 2 : ℝ) * (100 : ℝ) ^ (-(1 : ℝ) / 2) * ampNorm (fun _ => 1) (fun _ => 0) (-(21 / 100)) (21 / 100) :=
  h (fun x => 100 * x ^ 2 / 2) (fun x => 100 * x) (fun _ => 100) (fun _ => 1) (fun _ => 0) (-(21 / 100))
    (21 / 100) 100 0 (by norm_num) (by norm_num) (scaled_hasDerivOn _ _ _) (scaledLinear_hasDerivOn _ _ _)
    (fun x _ => by simp) (sanity_amplitude_one _ _).1

/-- **VC2-K at large curvature, with the certified value**: `33/100 ≤ (7/2)·100^{−1/2}·1` (which is
`33/100 ≤ 7/20`: `largeCurv_bound_value`). -/
theorem sevenHalves_largeCurv (h : SecondDerivSevenHalvesStatement) :
    33 / 100 ≤ (7 / 2 : ℝ) * (100 : ℝ) ^ (-(1 : ℝ) / 2) * 1 := by
  have h1 := sevenHalves_largeCurv_literal h
  rw [(sanity_amplitude_one _ _).2, oscInt_largeCurv] at h1
  linarith [largeCurv_norm_lower]

/-- **VC2-K at large curvature, simplified**: `|∫_{−21/100}^{21/100} e^{i·100x²/2} dx| ≤ 7/20` (and the left side
is at least `33/100` by `largeCurv_norm_lower`). -/
theorem sevenHalves_largeCurv_simplified (h : SecondDerivSevenHalvesStatement) :
    ‖∫ x in (-(21 / 100 : ℝ))..(21 / 100), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 20 := by
  have h1 := sevenHalves_largeCurv_literal h
  rw [(sanity_amplitude_one _ _).2, oscInt_largeCurv, largeCurv_bound_value] at h1
  exact h1

/-- **VC2-K is within 4.1% of a value of the integral**: `3.358 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx| ≤ 7/2`. -/
theorem sevenHalves_quad_window (h : SecondDerivSevenHalvesStatement) :
    1679 / 500 ≤ ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ∧
      ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 :=
  ⟨quad_norm_lower_sharp, sevenHalves_quadratic h (21 / 10) (by norm_num)⟩

/-- **VC2-K at the quartic phase, literal** (`φ = x²/2 + x⁴/12`, `φ″ = 1 + x²`, `μ = 1`, `p = 0`, `ψ = 1` on
`[−c, c]`; `|φ″|` is not constant). -/
theorem sevenHalves_quartic (h : SecondDerivSevenHalvesStatement) (c : ℝ) (hc : 0 ≤ c) :
    ‖oscInt (fun x => x ^ 2 / 2 + x ^ 4 / 12 + 0 * x) (fun _ => 1) (-c) c‖ ≤
      (7 / 2 : ℝ) * (1 : ℝ) ^ (-(1 : ℝ) / 2) * ampNorm (fun _ => 1) (fun _ => 0) (-c) c :=
  h (fun x => x ^ 2 / 2 + x ^ 4 / 12) (fun x => x + x ^ 3 / 3) (fun x => 1 + x ^ 2) (fun _ => 1) (fun _ => 0) (-c)
    c 1 0 (by linarith) one_pos (quartic_hasDerivOn _ _) (quarticDeriv_hasDerivOn _ _)
    (fun x _ => quartic_second_ge x) (sanity_amplitude_one _ _).1

/-! ## Data for the planted controls only -/

/-- `(x^r)^n = x^{rn}` for `x ≥ 0` and a natural number `n`. -/
theorem rpow_pow_nat {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (n : ℕ) : (x ^ r) ^ n = x ^ (r * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- `(1/100)^{−1/3} ≤ 5` (it is `100^{1/3} = 4.6415…`; its cube is `100 ≤ 125`). -/
theorem rpow_hundredth_neg_third_le : (1 / 100 : ℝ) ^ (-(1 : ℝ) / 3) ≤ 5 := by
  have h3 : ((1 / 100 : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = 100 := by
    rw [rpow_pow_nat (by norm_num), show (-(1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  by_contra hlt
  rw [not_le] at hlt
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hlt.le 3
  rw [h3] at h5
  norm_num at h5

/-- `1/4 ≤ (1/100)^{1/4}` (it is `0.31622…`; its fourth power is `1/100 ≥ 1/256`). -/
theorem rpow_hundredth_quarter_ge : 1 / 4 ≤ (1 / 100 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h4 : ((1 / 100 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 1 / 100 := by
    rw [rpow_pow_nat (by norm_num), show ((1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  by_contra hlt
  rw [not_le] at hlt
  have h5 := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) ((1 : ℝ) / 4)) hlt.le 4
  rw [h4] at h5
  norm_num at h5

/-- `100^{−3/5} ≤ 1/15` (it is `0.063095…`; its fifth power is `10⁻⁶ ≤ 15⁻⁵`). -/
theorem rpow_hundred_neg_three_fifths_le : (100 : ℝ) ^ (-(3 : ℝ) / 5) ≤ 1 / 15 := by
  have h5 : ((100 : ℝ) ^ (-(3 : ℝ) / 5)) ^ 5 = 1 / 1000000 := by
    rw [rpow_pow_nat (by norm_num), show (-(3 : ℝ) / 5) * ((5 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  by_contra hlt
  rw [not_le] at hlt
  have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 15) hlt.le 5
  rw [h5] at h6
  norm_num at h6

/-- `520/33 < 100^{3/5}` (it is `15.8489…`; its fifth power is `10⁶ > (520/33)⁵ = 971509.4…`). -/
theorem rpow_hundred_three_fifths_gt : 520 / 33 < (100 : ℝ) ^ ((3 : ℝ) / 5) := by
  have h5 : ((100 : ℝ) ^ ((3 : ℝ) / 5)) ^ 5 = 1000000 := by
    rw [rpow_pow_nat (by norm_num), show ((3 : ℝ) / 5) * ((5 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  by_contra hle
  rw [not_lt] at hle
  have h6 := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 100) ((3 : ℝ) / 5)) hle 5
  rw [h5] at h6
  norm_num at h6

end OscInt.API.SecondDerivSharpSanity2
