/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.SecondDerivSharp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Sanity theorems through the batch-VC2 statement constants (the sharp second-derivative bound)

As for the earlier batches (`docs/lessons.md`, rules 8 and 9): every theorem about a statement of batch VC2
takes that statement constant as its only statement hypothesis, discharges its hypotheses on closed data and
concludes its conclusion there. No statement of the batch is proved or used otherwise, and nothing here bounds
`vdc2Profile w` (written `A(w)`), or `∫ e^{if}`, for general `w` or `f`: every unconditional lemma is about fixed
numbers and explicit functions. Planted copies and witnesses: `docs/replay/plants/2026-11-16-VC2/`.

Written by an agent of the lead in scratch, with the statement text copied verbatim at the top of its file because
the statement module did not exist yet; the lead removed that copy, added the import and changed three lines of
this comment (the title, the word "draft" and the path of the plant record) when the batch entered the repository,
and changed nothing else.

Tools (no object of the batch): the Taylor bounds `sinLow t ≤ sin t` (degree 7) and `cosLow t ≤ cos t` (degree 6) for
`t ≥ 0`, proved by four integrations from `1 − t²/2 ≤ cos t`; `F b − F a ≤ ∫_a^b g` when `F′ = P ≤ g`; real and
imaginary parts of an interval integral.

Data:
* The quadratic phase `x ↦ x²/2` (`f′ = x`, rate exactly `1`), its scalings `x ↦ λx²/2` (rate exactly `λ`) and the
  concave phase `x ↦ −x²/2` (`φ″ = −1`), on every interval.
* Certified values at `c = 21/10`, `w = c²/2 = 441/200`: `33/10 ≤ A(441/200)` (true value `3.35396…`; the degree-7
  bound integrated exactly gives `3.35007…`) and `33/10 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|` (true value `3.36141…`;
  proved directly from `Re ≥ 64/25`, `Im ≥ 54/25`, not through `A`).
* Small data: `A(0) = 0`; `A(1/2) ≤ 1`; `2 cos(1/2) ≤ |∫_{−1}^{1} e^{ix²/2} dx|`; the scaled integral over
  `[−1/10, 1/10]` with `λ = 100`; the ramp amplitude `ψ(x) = 1 − x` on `[0, 1]` (`ψ(1) = 0`, `ampNorm = 1`) with
  `7/16 ≤ |∫_0^1 e^{ix²/2}(1 − x) dx|`.
* VC2-S at the quadratic phase on `[−c, c]`, at the scaled phase (`λ = 100`: the bound is `A(w)/10`), on a degenerate
  interval, and with the certified value: it forces `sup_{[0, π]} A ≥ 33/10`.
* VC2-A at `w = 441/200` (consistent with the direct bound) and at `w = 0`; unconditionally, the instance at
  `w = 1/2` is true with a gap of `3/4` (`attained_half_check`).
* VC2-N at `w = 441/200`: `0.94 · 7/2 ≤ A(441/200) ≤ 7/2`, so `7/2` is within 6% of a value of `A`.
* VC2-K at `φ = x²/2`, with the linear term `p = 3`, at `φ = −x²/2` (tests `|φ″|`), at the scaled phase (`μ = 100`:
  the bound is `7/20`, against a left side `≥ 0.175`) and with the ramp amplitude (tests `ampNorm`).
* Bite: the zero phase does not increase at rate `1` (`zero_not_increases`).
* Data for the planted controls only (last section): the zero phase and `|∫_a^b 1| = b − a`; the trivial bound
  `|∫_{−s}^{s} e^{ix²/2} dx| ≤ 2s ≤ 3` at `s = √(441/200)`.

What this layer cannot see: the sign of the curvature in VC2-S (the statement for decreasing `f′` is the conjugate
one) and the range `[0, π]` of `w` in VC2-N from above (`A ≤ 3.3643…` on all of `[0, ∞)`); see the plant record.
-/

namespace OscInt.API.SecondDerivSharpSanity

open OscInt.Statements Set

/-! ## Tools: polynomial bounds for `sin` and `cos`, integrals with an explicit antiderivative -/

/-- A function vanishing at `0` whose derivative is nonnegative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_deriv_nonneg {g g' : ℝ → ℝ} (h0 : g 0 = 0) (hd : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, 0 ≤ t → 0 ≤ g' t) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g t := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
    rw [(hd x).deriv]
    rw [interior_Ici] at hx
    exact hg' x (le_of_lt hx)
  have h := hmono self_mem_Ici ht ht
  rwa [h0] at h

/-- The derivative of the monomial `c x^{n+1}`, in the shape used for the explicit antiderivatives below. -/
theorem hasDerivAt_monomial (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => c * x ^ (n + 1)) (c * ((n + 1 : ℝ) * x ^ n)) x := by
  have h := (hasDerivAt_pow (n + 1) x).const_mul c
  simpa using h

/-- `t − t³/6 ≤ sin t` for `t ≥ 0`. -/
theorem sub_cube_le_sin (t : ℝ) (ht : 0 ≤ t) : t - t ^ 3 / 6 ≤ Real.sin t := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin t - (t - t ^ 3 / 6))
      (Real.cos t - (1 - t ^ 2 / 2)) t := by
    intro t
    have h := (Real.hasDerivAt_sin t).fun_sub
      ((hasDerivAt_monomial 1 0 t).fun_add (hasDerivAt_monomial (-1 / 6) 2 t))
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  have h := nonneg_of_deriv_nonneg (by simp) hd
    (fun t _ => by linarith [Real.one_sub_sq_div_two_le_cos (x := t)]) t ht
  linarith

/-- `cos t ≤ 1 − t²/2 + t⁴/24` for `t ≥ 0`. -/
theorem cos_le_deg_four (t : ℝ) (ht : 0 ≤ t) : Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (Real.sin t - (t - t ^ 3 / 6)) t := by
    intro t
    have h := (((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_monomial (-1 / 2) 1 t)).fun_add
      (hasDerivAt_monomial (1 / 24) 3 t)).fun_sub (Real.hasDerivAt_cos t)
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  have h := nonneg_of_deriv_nonneg (by simp) hd (fun t ht => by linarith [sub_cube_le_sin t ht]) t ht
  linarith

/-- `sin t ≤ t − t³/6 + t⁵/120` for `t ≥ 0`. -/
theorem sin_le_deg_five (t : ℝ) (ht : 0 ≤ t) : Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
    intro t
    have h := (((hasDerivAt_monomial 1 0 t).fun_add (hasDerivAt_monomial (-1 / 6) 2 t)).fun_add
      (hasDerivAt_monomial (1 / 120) 4 t)).fun_sub (Real.hasDerivAt_sin t)
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  have h := nonneg_of_deriv_nonneg (by simp) hd (fun t ht => by linarith [cos_le_deg_four t ht]) t ht
  linarith

/-- The Taylor polynomial of `cos` of degree 6: a lower bound of `cos` on `[0, ∞)` (`cosLow_le_cos`). -/
noncomputable def cosLow (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720

/-- The Taylor polynomial of `sin` of degree 7: a lower bound of `sin` on `[0, ∞)` (`sinLow_le_sin`). -/
noncomputable def sinLow (t : ℝ) : ℝ := t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040

/-- `1 − t²/2 + t⁴/24 − t⁶/720 ≤ cos t` for `t ≥ 0`. -/
theorem cosLow_le_cos (t : ℝ) (ht : 0 ≤ t) : cosLow t ≤ Real.cos t := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.cos t - cosLow t)
      (t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) t := by
    intro t
    have h := (Real.hasDerivAt_cos t).fun_sub ((((hasDerivAt_const t (1 : ℝ)).fun_add
      (hasDerivAt_monomial (-1 / 2) 1 t)).fun_add (hasDerivAt_monomial (1 / 24) 3 t)).fun_add
      (hasDerivAt_monomial (-1 / 720) 5 t))
    convert h using 1
    · funext s
      unfold cosLow
      ring
    · push_cast
      ring
  have h := nonneg_of_deriv_nonneg (by simp [cosLow]) hd (fun t ht => by linarith [sin_le_deg_five t ht]) t ht
  linarith

/-- `t − t³/6 + t⁵/120 − t⁷/5040 ≤ sin t` for `t ≥ 0`. -/
theorem sinLow_le_sin (t : ℝ) (ht : 0 ≤ t) : sinLow t ≤ Real.sin t := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin t - sinLow t) (Real.cos t - cosLow t) t := by
    intro t
    have h := (Real.hasDerivAt_sin t).fun_sub ((((hasDerivAt_monomial 1 0 t).fun_add
      (hasDerivAt_monomial (-1 / 6) 2 t)).fun_add (hasDerivAt_monomial (1 / 120) 4 t)).fun_add
      (hasDerivAt_monomial (-1 / 5040) 6 t))
    convert h using 1
    · funext s
      unfold sinLow
      ring
    · unfold cosLow
      push_cast
      ring
  have h := nonneg_of_deriv_nonneg (by simp [sinLow]) hd (fun t ht => by linarith [cosLow_le_cos t ht]) t ht
  linarith

/-- If `P ≤ g` on `[a, b]` and `F` is an antiderivative of `P`, then `F b − F a ≤ ∫_a^b g`. -/
theorem sub_le_integral_of_le {F P g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hF : ∀ x, HasDerivAt F (P x) x)
    (hP : Continuous P) (hg : Continuous g) (h : ∀ x ∈ Icc a b, P x ≤ g x) : F b - F a ≤ ∫ x in a..b, g x := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hP.intervalIntegrable a b)]
  exact intervalIntegral.integral_mono_on hab (hP.intervalIntegrable a b) (hg.intervalIntegrable a b) h

/-- The real part of the interval integral of a continuous complex function. -/
theorem re_intervalIntegral {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    (∫ x in a..b, F x).re = ∫ x in a..b, (F x).re :=
  (Complex.reCLM.intervalIntegral_comp_comm (hF.intervalIntegrable a b)).symm

/-- The imaginary part of the interval integral of a continuous complex function. -/
theorem im_intervalIntegral {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    (∫ x in a..b, F x).im = ∫ x in a..b, (F x).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (hF.intervalIntegrable a b)).symm

/-- A complex number with `p ≤ Re z`, `q ≤ Im z`, `p, q ≥ 0` and `r² ≤ p² + q²` has modulus at least `r`. -/
theorem le_norm_of_re_im {z : ℂ} {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : r ^ 2 ≤ p ^ 2 + q ^ 2)
    (h1 : p ≤ z.re) (h2 : q ≤ z.im) : r ≤ ‖z‖ := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg z, mul_le_mul h1 h1 hp (hp.trans h1), mul_le_mul h2 h2 hq (hq.trans h2)]

/-- `7/8 ≤ cos (1/2)`. -/
theorem cos_half_lower : 7 / 8 ≤ Real.cos (1 / 2) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := 1 / 2)
  norm_num at h
  linarith

/-- `√100 = 10`. -/
theorem sqrt_hundred : Real.sqrt 100 = 10 := by
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `100^{−1/2} = 1/10`, in the shape of VC2-K. -/
theorem rpow_neg_half_hundred : (100 : ℝ) ^ (-(1 : ℝ) / 2) = 1 / 10 := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, sqrt_hundred]
  norm_num

/-! ## The data: quadratic phases -/

/-- `A(0) = 0`. -/
theorem vdc2Profile_zero : vdc2Profile 0 = 0 := by
  simp [vdc2Profile]

/-- `√(2w) = 21/10` at `w = 441/200`. -/
theorem sqrt_two_mul_w : Real.sqrt (2 * (441 / 200)) = 21 / 10 := by
  rw [show (2 * (441 / 200) : ℝ) = (21 / 10) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `√(2w) = 1` at `w = 1/2`. -/
theorem sqrt_two_mul_half : Real.sqrt (2 * (1 / 2)) = 1 := by
  rw [show (2 * (1 / 2) : ℝ) = 1 by norm_num]
  exact Real.sqrt_one

/-- The scaled quadratic datum `x ↦ λ x²/2` has derivative `x ↦ λ x` on every interval. -/
theorem scaled_hasDerivOn (lam a b : ℝ) : HasDerivOn (fun x => lam * x ^ 2 / 2) (fun x => lam * x) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => lam * x ^ 2 / 2) (lam * x) x := fun x => by
    have h := ((hasDerivAt_pow 2 x).const_mul lam).div_const 2
    convert h using 1
    norm_num
    ring
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- `x ↦ λ x` has derivative `λ` on every interval. -/
theorem scaledLinear_hasDerivOn (lam a b : ℝ) : HasDerivOn (fun x => lam * x) (fun _ => lam) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => lam * x) lam x := fun x => by
    simpa using (hasDerivAt_id' x).const_mul lam
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- `x ↦ λ x` increases at rate (exactly) `λ` on every interval. -/
theorem scaled_increases (lam a b : ℝ) : DerivIncreasesAtRate (fun x => lam * x) a b lam := by
  intro x _ y _ _
  exact le_of_eq (by ring)

/-- The quadratic datum `x ↦ x²/2` has derivative `x ↦ x` on every interval. -/
theorem quad_hasDerivOn (a b : ℝ) : HasDerivOn (fun x => x ^ 2 / 2) (fun x => x) a b := by
  have h := scaled_hasDerivOn 1 a b
  simpa using h

/-- `x ↦ x` has derivative `1` on every interval. -/
theorem id_hasDerivOn (a b : ℝ) : HasDerivOn (fun x => x) (fun _ => 1) a b := by
  have h := scaledLinear_hasDerivOn 1 a b
  simpa using h

/-- `x ↦ x` increases at rate (exactly) `1` on every interval. -/
theorem quad_increases (a b : ℝ) : DerivIncreasesAtRate (fun x => x) a b 1 := by
  intro x _ y _ _
  exact le_of_eq (by ring)

/-- The concave datum `x ↦ −x²/2` has derivative `x ↦ −x` on every interval. -/
theorem negQuad_hasDerivOn (a b : ℝ) : HasDerivOn (fun x => -(x ^ 2 / 2)) (fun x => -x) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-x) x := fun x => by
    have h := ((hasDerivAt_pow 2 x).div_const 2).fun_neg
    convert h using 1
    norm_num
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- `x ↦ −x` has derivative `−1` on every interval. -/
theorem negId_hasDerivOn (a b : ℝ) : HasDerivOn (fun x => -x) (fun _ => -1) a b := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -x) (-1) x := fun x => (hasDerivAt_id' x).fun_neg
  exact ⟨fun x _ => (hd x).continuousAt.continuousWithinAt, fun x _ => hd x⟩

/-- An antiderivative of `u ↦ sinLow (441/200 − u²/2)` (exact rational coefficients). -/
noncomputable def profilePrim (u : ℝ) : ℝ :=
  821548785505653513 / 1024000000000000000 * u + 3101050253131849 / 30720000000000000 * u ^ 3 -
    10912994726067 / 512000000000000 * u ^ 5 - 5709340213 / 4300800000000 * u ^ 7 + 743477 / 6144000000 * u ^ 9 +
    114481 / 3379200000 * u ^ 11 - 49 / 13312000 * u ^ 13 + 1 / 9676800 * u ^ 15

/-- `profilePrim′(u) = sinLow (441/200 − u²/2)`. -/
theorem profilePrim_hasDerivAt (u : ℝ) : HasDerivAt profilePrim (sinLow (441 / 200 - u ^ 2 / 2)) u := by
  have h := (((((((hasDerivAt_monomial (821548785505653513 / 1024000000000000000) 0 u).fun_add
    (hasDerivAt_monomial (3101050253131849 / 30720000000000000) 2 u)).fun_add
    (hasDerivAt_monomial (-10912994726067 / 512000000000000) 4 u)).fun_add
    (hasDerivAt_monomial (-5709340213 / 4300800000000) 6 u)).fun_add
    (hasDerivAt_monomial (743477 / 6144000000) 8 u)).fun_add
    (hasDerivAt_monomial (114481 / 3379200000) 10 u)).fun_add
    (hasDerivAt_monomial (-49 / 13312000) 12 u)).fun_add (hasDerivAt_monomial (1 / 9676800) 14 u)
  convert h using 1
  · funext s
    unfold profilePrim
    ring
  · unfold sinLow
    push_cast
    ring

/-- **Certified value.** `33/10 ≤ A(441/200)` (the true value is `3.35396…`; the polynomial bound gives
`3.35007…`, margin `0.050` over `33/10`). -/
theorem vdc2Profile_lower : 33 / 10 ≤ vdc2Profile (441 / 200) := by
  have h := sub_le_integral_of_le (F := profilePrim) (P := fun u => sinLow (441 / 200 - u ^ 2 / 2))
    (g := fun u => Real.sin (441 / 200 - u ^ 2 / 2)) (a := 0) (b := 21 / 10) (by norm_num)
    profilePrim_hasDerivAt (by unfold sinLow; fun_prop) (by fun_prop)
    (fun u hu => sinLow_le_sin _ (by nlinarith [hu.1, hu.2]))
  have hv : (33 / 20 : ℝ) ≤ profilePrim (21 / 10) - profilePrim 0 := by
    unfold profilePrim
    norm_num
  unfold vdc2Profile
  rw [sqrt_two_mul_w]
  linarith

/-- `A(1/2) ≤ 1` (the true value is `0.64781…`): `sin(1/2 − u²/2) ≤ 1/2` on `[0, 1]`. -/
theorem vdc2Profile_half_le : vdc2Profile (1 / 2) ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun u => Real.sin (1 / 2 - u ^ 2 / 2)) (g := fun _ => (1 / 2 : ℝ)) (a := 0) (b := 1) zero_le_one
    ((by fun_prop : Continuous fun u : ℝ => Real.sin (1 / 2 - u ^ 2 / 2)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)
    (fun u hu => (Real.sin_le (by nlinarith [hu.1, hu.2])).trans (by nlinarith [hu.1, hu.2]))
  rw [intervalIntegral.integral_const] at h
  unfold vdc2Profile
  rw [sqrt_two_mul_half]
  norm_num at h
  linarith

/-- An antiderivative of `x ↦ cosLow (x²/2)`. -/
noncomputable def cosPrim (x : ℝ) : ℝ := x - x ^ 5 / 40 + x ^ 9 / 3456 - x ^ 13 / 599040

/-- `cosPrim′(x) = cosLow (x²/2)`. -/
theorem cosPrim_hasDerivAt (x : ℝ) : HasDerivAt cosPrim (cosLow (x ^ 2 / 2)) x := by
  have h := (((hasDerivAt_monomial 1 0 x).fun_add (hasDerivAt_monomial (-1 / 40) 4 x)).fun_add
    (hasDerivAt_monomial (1 / 3456) 8 x)).fun_add (hasDerivAt_monomial (-1 / 599040) 12 x)
  convert h using 1
  · funext s
    unfold cosPrim
    ring
  · unfold cosLow
    push_cast
    ring

/-- An antiderivative of `x ↦ sinLow (x²/2)`. -/
noncomputable def sinPrim (x : ℝ) : ℝ := x ^ 3 / 6 - x ^ 7 / 336 + x ^ 11 / 42240 - x ^ 15 / 9676800

/-- `sinPrim′(x) = sinLow (x²/2)`. -/
theorem sinPrim_hasDerivAt (x : ℝ) : HasDerivAt sinPrim (sinLow (x ^ 2 / 2)) x := by
  have h := (((hasDerivAt_monomial (1 / 6) 2 x).fun_add (hasDerivAt_monomial (-1 / 336) 6 x)).fun_add
    (hasDerivAt_monomial (1 / 42240) 10 x)).fun_add (hasDerivAt_monomial (-1 / 9676800) 14 x)
  convert h using 1
  · funext s
    unfold sinPrim
    ring
  · unfold sinLow
    push_cast
    ring

/-- `64/25 ≤ Re ∫_{−21/10}^{21/10} e^{ix²/2} dx` (true value `2.5698…`; the polynomial bound gives `2.5660…`). -/
theorem quad_re_lower :
    64 / 25 ≤ (∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).re := by
  rw [re_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_re]
  have h := sub_le_integral_of_le (F := cosPrim) (P := fun x => cosLow (x ^ 2 / 2))
    (g := fun x => Real.cos (x ^ 2 / 2)) (a := -(21 / 10)) (b := 21 / 10) (by norm_num) cosPrim_hasDerivAt
    (by unfold cosLow; fun_prop) (by fun_prop) (fun x _ => cosLow_le_cos _ (by positivity))
  have hv : (64 / 25 : ℝ) ≤ cosPrim (21 / 10) - cosPrim (-(21 / 10)) := by
    unfold cosPrim
    norm_num
  linarith

/-- `54/25 ≤ Im ∫_{−21/10}^{21/10} e^{ix²/2} dx` (true value `2.1674…`; the polynomial bound gives `2.1666…`). -/
theorem quad_im_lower :
    54 / 25 ≤ (∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).im := by
  rw [im_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_im]
  have h := sub_le_integral_of_le (F := sinPrim) (P := fun x => sinLow (x ^ 2 / 2))
    (g := fun x => Real.sin (x ^ 2 / 2)) (a := -(21 / 10)) (b := 21 / 10) (by norm_num) sinPrim_hasDerivAt
    (by unfold sinLow; fun_prop) (by fun_prop) (fun x _ => sinLow_le_sin _ (by positivity))
  have hv : (54 / 25 : ℝ) ≤ sinPrim (21 / 10) - sinPrim (-(21 / 10)) := by
    unfold sinPrim
    norm_num
  linarith

/-- **Certified value.** `33/10 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|` (true value `3.36141…`; proved directly from
the real and imaginary parts, `(64/25)² + (54/25)² = 11.2192 ≥ 10.89`, not through `A`). -/
theorem quad_norm_lower :
    33 / 10 ≤ ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ :=
  le_norm_of_re_im (by norm_num) (by norm_num) (by norm_num) quad_re_lower quad_im_lower

/-- **Small interval.** `2 cos(1/2) ≤ |∫_{−1}^{1} e^{ix²/2} dx|` (real part; `1.7551…` against the true `1.9778…`). -/
theorem quad_one_lower :
    2 * Real.cos (1 / 2) ≤ ‖∫ x in (-1 : ℝ)..1, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [re_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_re]
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := fun _ => Real.cos (1 / 2))
    (g := fun x => Real.cos (x ^ 2 / 2)) (a := -1) (b := 1) (by norm_num) (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => Real.cos (x ^ 2 / 2)).intervalIntegrable _ _)
    (fun x hx => Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
      (by nlinarith [hx.1, hx.2]))
  rw [intervalIntegral.integral_const] at h
  norm_num at h
  linarith

/-- The scaled datum: `(2/10) cos(1/2) ≤ |∫_{−1/10}^{1/10} e^{i·100x²/2} dx|` (true value `0.19778…`). -/
theorem scaled_tenth_lower :
    2 / 10 * Real.cos (1 / 2) ≤
      ‖∫ x in (-(1 / 10 : ℝ))..(1 / 10), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [re_intervalIntegral (by fun_prop)]
  simp only [Complex.exp_ofReal_mul_I_re]
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := fun _ => Real.cos (1 / 2))
    (g := fun x => Real.cos (100 * x ^ 2 / 2)) (a := -(1 / 10)) (b := 1 / 10) (by norm_num)
    (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => Real.cos (100 * x ^ 2 / 2)).intervalIntegrable _ _)
    (fun x hx => Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
      (by nlinarith [hx.1, hx.2]))
  rw [intervalIntegral.integral_const] at h
  norm_num at h
  linarith

/-- The instance of VC2-A at `w = 1/2` is true: `A(1/2) ≤ 1 < 2 cos(1/2) ≤ |∫_{−1}^{1} e^{ix²/2} dx|`, with a strict
gap (unconditional; used against the plant that reverses the inequality). -/
theorem attained_half_check :
    vdc2Profile (1 / 2) + 3 / 4 ≤ ‖∫ x in (-1 : ℝ)..1, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  linarith [vdc2Profile_half_le, quad_one_lower, cos_half_lower]

/-- The ramp amplitude `ψ(x) = 1 − x` on `[0, 1]`, which vanishes at the right end point. -/
theorem ramp_amplitudeOn : AmplitudeOn (fun x => ((1 - x : ℝ) : ℂ)) (fun _ => -1) 0 1 := by
  refine ⟨by fun_prop, fun x _ => ?_, continuous_const.intervalIntegrable _ _⟩
  have h := ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)).ofReal_comp
  simpa using h

/-- `|ψ(1)| + ∫_0^1 |ψ′| = 1` for the ramp. -/
theorem ampNorm_ramp : ampNorm (fun x => ((1 - x : ℝ) : ℂ)) (fun _ => -1) 0 1 = 1 := by
  simp [ampNorm]

/-- `7/16 ≤ |∫_0^1 e^{ix²/2} (1 − x) dx|` (true value `0.49757…`): the real part is at least `(7/8) ∫_0^1 (1 − x)`. -/
theorem ramp_lower : 7 / 16 ≤ ‖oscInt (fun x => x ^ 2 / 2 + 0 * x) (fun x => ((1 - x : ℝ) : ℂ)) 0 1‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  unfold oscInt
  rw [re_intervalIntegral (by fun_prop)]
  simp only [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero]
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 7 / 8 * x - 7 / 16 * x ^ 2) (7 / 8 * (1 - x)) x := by
    intro x
    have h := (hasDerivAt_monomial (7 / 8) 0 x).fun_add (hasDerivAt_monomial (-7 / 16) 1 x)
    convert h using 1
    · funext s
      ring
    · push_cast
      ring
  have h := sub_le_integral_of_le (F := fun x : ℝ => 7 / 8 * x - 7 / 16 * x ^ 2) (P := fun x => 7 / 8 * (1 - x))
    (g := fun x => Real.cos (x ^ 2 / 2) * (1 - x)) (a := 0) (b := 1) zero_le_one hF (by fun_prop)
    (by fun_prop) (fun x hx => mul_le_mul_of_nonneg_right (cos_half_lower.trans
      (Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by linarith [Real.pi_gt_three])
        (by nlinarith [hx.1, hx.2]))) (by linarith [hx.2]))
  norm_num at h
  linarith

/-- **Bite.** The zero phase does not increase at rate `1` on `(0, 1)`: the rate hypothesis carries content. -/
theorem zero_not_increases : ¬ DerivIncreasesAtRate (fun _ => 0) 0 1 1 := by
  intro h
  have h1 := h (1 / 4) ⟨by norm_num, by norm_num⟩ (3 / 4) ⟨by norm_num, by norm_num⟩ (by norm_num)
  norm_num at h1

/-! ## Through the statement constants -/

/-- **VC2-S at the quadratic phase** (`λ = 1`, `[−c, c]`): `|∫_{−c}^{c} e^{ix²/2} dx| ≤ A(w)` for some `w ∈ [0, π]`. -/
theorem sharp_quadratic (h : SecondDerivSharpStatement) (c : ℝ) (hc : 0 ≤ c) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in (-c)..c, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := h (fun x => x ^ 2 / 2) (fun x => x) (-c) c 1 (by linarith) one_pos
    (quad_hasDerivOn _ _) (quad_increases _ _)
  rw [Real.sqrt_one, div_one] at hle
  exact ⟨w, hw, hle⟩

/-- **VC2-S at the scaled phase** (`λ = 100`, `[−c/10, c/10]`): the bound is `A(w)/10` (tests the power of `λ`). -/
theorem sharp_scaled (h : SecondDerivSharpStatement) (c : ℝ) (hc : 0 ≤ c) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in (-(c / 10))..(c / 10), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ vdc2Profile w / 10 := by
  obtain ⟨w, hw, hle⟩ := h (fun x => 100 * x ^ 2 / 2) (fun x => 100 * x) (-(c / 10)) (c / 10) 100 (by linarith)
    (by norm_num) (scaled_hasDerivOn _ _ _) (scaled_increases _ _ _)
  rw [sqrt_hundred] at hle
  exact ⟨w, hw, hle⟩

/-- **VC2-S on a degenerate interval** (`a = b`): the conclusion is `0 ≤ A(w)` for some `w ∈ [0, π]`. -/
theorem sharp_degenerate (h : SecondDerivSharpStatement) (a : ℝ) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 0 ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := h (fun x => x ^ 2 / 2) (fun x => x) a a 1 le_rfl one_pos
    (quad_hasDerivOn _ _) (quad_increases _ _)
  rw [intervalIntegral.integral_same, norm_zero, Real.sqrt_one, div_one] at hle
  exact ⟨w, hw, hle⟩

/-- **VC2-S bites**: with the certified value at `c = 21/10` it forces `A(w) ≥ 33/10` for some `w ∈ [0, π]`. -/
theorem sharp_profile_large (h : SecondDerivSharpStatement) :
    ∃ w ∈ Icc (0 : ℝ) Real.pi, 33 / 10 ≤ vdc2Profile w := by
  obtain ⟨w, hw, hle⟩ := sharp_quadratic h (21 / 10) (by norm_num)
  exact ⟨w, hw, quad_norm_lower.trans hle⟩

/-- **VC2-A at `w = 441/200`**: with the certified value of `A` it gives `33/10 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|`
(which `quad_norm_lower` proves directly: the instance is consistent). -/
theorem attained_at (h : SecondDerivAttainedStatement) :
    33 / 10 ≤ ‖∫ x in (-(21 / 10 : ℝ))..(21 / 10), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  have h1 := h (441 / 200) (by norm_num)
  rw [sqrt_two_mul_w] at h1
  exact vdc2Profile_lower.trans h1

/-- **VC2-A at `w = 0`**: `A(0) ≤ 0` (an empty interval; `vdc2Profile_zero` says `A(0) = 0`). -/
theorem attained_zero (h : SecondDerivAttainedStatement) : vdc2Profile 0 ≤ 0 := by
  have h1 := h 0 le_rfl
  simpa using h1

/-- **VC2-N at `w = 441/200`**: `A(441/200) ≤ 7/2`. -/
theorem profile_le (h : Vdc2ProfileBoundStatement) : vdc2Profile (441 / 200) ≤ 7 / 2 :=
  h (441 / 200) ⟨by norm_num, by linarith [Real.pi_gt_three]⟩

/-- **VC2-N is within 6% of a value of `A`**: `0.94 · 7/2 ≤ A(441/200) ≤ 7/2`. -/
theorem profile_within (h : Vdc2ProfileBoundStatement) :
    94 / 100 * (7 / 2) ≤ vdc2Profile (441 / 200) ∧ vdc2Profile (441 / 200) ≤ 7 / 2 :=
  ⟨by linarith [vdc2Profile_lower], profile_le h⟩

/-- **VC2-K at the quadratic phase** (`φ = x²/2`, `μ = 1`, `p = 0`, `ψ = 1`): `|∫_{−c}^{c} e^{ix²/2} dx| ≤ 7/2`. -/
theorem sevenHalves_quadratic (h : SecondDerivSevenHalvesStatement) (c : ℝ) (hc : 0 ≤ c) :
    ‖∫ x in (-c)..c, Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 := by
  have h1 := h (fun x => x ^ 2 / 2) (fun x => x) (fun _ => 1) (fun _ => 1) (fun _ => 0) (-c) c 1 0 (by linarith)
    one_pos (quad_hasDerivOn _ _) (id_hasDerivOn _ _) (fun x _ => by simp) (sanity_amplitude_one _ _).1
  rw [(sanity_amplitude_one _ _).2, Real.one_rpow] at h1
  simpa [oscInt] using h1

/-- **VC2-K with a linear term** (`p = 3`): `|∫_{−c}^{c} e^{i(x²/2 + 3x)} dx| ≤ 7/2`. -/
theorem sevenHalves_linear (h : SecondDerivSevenHalvesStatement) (c : ℝ) (hc : 0 ≤ c) :
    ‖∫ x in (-c)..c, Complex.exp (((x ^ 2 / 2 + 3 * x : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 := by
  have h1 := h (fun x => x ^ 2 / 2) (fun x => x) (fun _ => 1) (fun _ => 1) (fun _ => 0) (-c) c 1 3 (by linarith)
    one_pos (quad_hasDerivOn _ _) (id_hasDerivOn _ _) (fun x _ => by simp) (sanity_amplitude_one _ _).1
  rw [(sanity_amplitude_one _ _).2, Real.one_rpow] at h1
  simpa [oscInt] using h1

/-- **VC2-K with `φ″ = −1`** (`φ = −x²/2`; tests the absolute value): `|∫_{−c}^{c} e^{−ix²/2} dx| ≤ 7/2`. -/
theorem sevenHalves_neg (h : SecondDerivSevenHalvesStatement) (c : ℝ) (hc : 0 ≤ c) :
    ‖∫ x in (-c)..c, Complex.exp (((-(x ^ 2 / 2) : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 2 := by
  have h1 := h (fun x => -(x ^ 2 / 2)) (fun x => -x) (fun _ => -1) (fun _ => 1) (fun _ => 0) (-c) c 1 0
    (by linarith) one_pos (negQuad_hasDerivOn _ _) (negId_hasDerivOn _ _) (fun x _ => by simp)
    (sanity_amplitude_one _ _).1
  rw [(sanity_amplitude_one _ _).2, Real.one_rpow] at h1
  simpa [oscInt] using h1

/-- **VC2-K at the scaled phase** (`φ = 100x²/2`, `μ = 100`, `[−1/10, 1/10]`): the bound is `7/20` (tests the power
of `μ`; the left side is at least `(2/10) cos(1/2) ≥ 0.175` by `scaled_tenth_lower`). -/
theorem sevenHalves_scaled (h : SecondDerivSevenHalvesStatement) :
    ‖∫ x in (-(1 / 10 : ℝ))..(1 / 10), Complex.exp (((100 * x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 7 / 20 := by
  have h1 := h (fun x => 100 * x ^ 2 / 2) (fun x => 100 * x) (fun _ => 100) (fun _ => 1) (fun _ => 0) (-(1 / 10))
    (1 / 10) 100 0 (by norm_num) (by norm_num) (scaled_hasDerivOn _ _ _) (scaledLinear_hasDerivOn _ _ _)
    (fun x _ => by simp) (sanity_amplitude_one _ _).1
  rw [(sanity_amplitude_one _ _).2, rpow_neg_half_hundred] at h1
  have h2 : (7 / 2 : ℝ) * (1 / 10) * 1 = 7 / 20 := by norm_num
  rw [h2] at h1
  simpa [oscInt] using h1

/-- **VC2-K with the ramp amplitude** (`ψ(x) = 1 − x` on `[0, 1]`, `ψ(1) = 0`, `∫|ψ′| = 1`; tests `ampNorm`): the
bound is `7/2` (and the left side is at least `7/16` by `ramp_lower`). -/
theorem sevenHalves_ramp (h : SecondDerivSevenHalvesStatement) :
    ‖oscInt (fun x => x ^ 2 / 2 + 0 * x) (fun x => ((1 - x : ℝ) : ℂ)) 0 1‖ ≤ 7 / 2 := by
  have h1 := h (fun x => x ^ 2 / 2) (fun x => x) (fun _ => 1) (fun x => ((1 - x : ℝ) : ℂ)) (fun _ => -1) 0 1 1 0
    zero_le_one one_pos (quad_hasDerivOn _ _) (id_hasDerivOn _ _) (fun x _ => by simp) ramp_amplitudeOn
  rw [ampNorm_ramp, Real.one_rpow] at h1
  linarith

/-! ## Data for the planted controls only -/

/-- The zero phase has derivative `0` on every interval. -/
theorem zero_hasDerivOn (a b : ℝ) : HasDerivOn (fun _ => 0) (fun _ => 0) a b :=
  ⟨continuousOn_const, fun x _ => hasDerivAt_const x 0⟩

/-- The constant `0` increases at rate `0` (and at no positive rate on a non-trivial interval). -/
theorem zero_increases (a b : ℝ) : DerivIncreasesAtRate (fun _ => 0) a b 0 := by
  intro x _ y _ _
  simp

/-- `|∫_{−s}^{s} e^{ix²/2} dx| ≤ 3` at `s = √(441/200)` (true value `2.8124…`; the trivial bound `2s ≤ 3`). -/
theorem quad_sqrt_norm_le :
    ‖∫ x in (-Real.sqrt (441 / 200))..(Real.sqrt (441 / 200)),
      Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 3 := by
  have hs : Real.sqrt (441 / 200) ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.sqrt (441 / 200))
    (b := Real.sqrt (441 / 200)) (C := 1) (f := fun x : ℝ => Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I))
    (fun x _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  rw [abs_of_nonneg (by linarith [Real.sqrt_nonneg (441 / 200 : ℝ)])] at h
  linarith

/-- `|∫_a^b e^{i·0} dx| = b − a` for `a ≤ b`. -/
theorem norm_integral_exp_zero (a b : ℝ) (hab : a ≤ b) :
    ‖∫ _x in a..b, Complex.exp (((0 : ℝ) : ℂ) * Complex.I)‖ = b - a := by
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
  rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one, abs_of_nonneg (sub_nonneg.2 hab)]

end OscInt.API.SecondDerivSharpSanity
