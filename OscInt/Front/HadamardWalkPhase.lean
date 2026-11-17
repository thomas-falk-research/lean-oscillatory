/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.HadamardWalk

/-!
# Batch HW, part HW2: the phase and the amplitude of the Hadamard walk (route `docs/proof-HW.md`, H4 and H5)

`hadamardPhaseFacts`: the derivative chain `ω → ω′ → ω″ → ω‴` of the dispersion relation
`ω(k) = arcsin(sin k / √2)` and the two lower bounds `|ω″| ≥ 2/(3√3)` where `|sin k| ≥ 1/√2`, `|ω‴| ≥ 1/(2√2)`
where `|cos k| ≥ 1/√2`.

`hadamardAmplitudeFacts`: the derivative of the amplitude `g(k) = 1/√(2 (1 + cos² k))` and the exact value of its
amplitude norm on the four arcs of length `π/2` (the integral of `|g′|` is split at the midpoint of the arc, where
`g′` changes sign; the arcs around `π` and `3π/2` are the arcs around `0` and `π/2` moved by the period `π`).
-/

namespace OscInt.HadamardWalkAux

open OscInt.Statements OscInt.Blueprint.HadamardWalk

/-! ## The phase -/

/-- `1 + cos² k > 0`. -/
theorem hwPh_u_pos (k : ℝ) : 0 < 1 + Real.cos k ^ 2 := by positivity

/-- `√(1 + cos² k) > 0`. -/
theorem hwPh_r_pos (k : ℝ) : 0 < Real.sqrt (1 + Real.cos k ^ 2) := Real.sqrt_pos.mpr (hwPh_u_pos k)

/-- `√(1 + cos² k) ^ 2 = 1 + cos² k`. -/
theorem hwPh_r_sq (k : ℝ) : Real.sqrt (1 + Real.cos k ^ 2) ^ 2 = 1 + Real.cos k ^ 2 :=
  Real.sq_sqrt (hwPh_u_pos k).le

/-- `√2 > 0`. -/
theorem hwPh_sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- `√2 ^ 2 = 2`. -/
theorem hwPh_sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√3 > 0`. -/
theorem hwPh_sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `√3 ^ 2 = 3`. -/
theorem hwPh_sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The derivative of `1 + cos² k` is `−2 sin k cos k`. -/
theorem hwPh_hasDerivAt_u (k : ℝ) :
    HasDerivAt (fun x : ℝ => 1 + Real.cos x ^ 2) (-(2 * (Real.sin k * Real.cos k))) k := by
  have h := ((Real.hasDerivAt_cos k).fun_pow 2).const_add 1
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- The derivative of `√(1 + cos² k)` is `−sin k cos k / √(1 + cos² k)`. -/
theorem hwPh_hasDerivAt_r (k : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 + Real.cos x ^ 2))
      (-(Real.sin k * Real.cos k) / Real.sqrt (1 + Real.cos k ^ 2)) k := by
  have h := (hwPh_hasDerivAt_u k).sqrt (hwPh_u_pos k).ne'
  convert h using 1
  have hr := hwPh_r_pos k
  field_simp

/-- `ω′ = cos k / √(1 + cos² k)`. -/
theorem hwPh_hasDerivAt_dispersion (k : ℝ) : HasDerivAt hadamardDispersion (hwD1 k) k := by
  have hs2 := hwPh_sqrt_two_pos
  have hs2sq := hwPh_sqrt_two_sq
  have hsc := Real.sin_sq_add_cos_sq k
  have hlt : (Real.sin k / Real.sqrt 2) ^ 2 < 1 := by
    rw [div_pow, hs2sq]
    nlinarith [sq_nonneg (Real.cos k)]
  have hne1 : Real.sin k / Real.sqrt 2 ≠ -1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hne2 : Real.sin k / Real.sqrt 2 ≠ 1 := by
    intro h
    rw [h] at hlt
    norm_num at hlt
  have h1 : HasDerivAt (fun x : ℝ => Real.sin x / Real.sqrt 2) (Real.cos k / Real.sqrt 2) k :=
    (Real.hasDerivAt_sin k).div_const _
  have h2 : HasDerivAt (Real.arcsin ∘ fun x : ℝ => Real.sin x / Real.sqrt 2)
      (1 / Real.sqrt (1 - (Real.sin k / Real.sqrt 2) ^ 2) * (Real.cos k / Real.sqrt 2)) k :=
    HasDerivAt.comp k (Real.hasDerivAt_arcsin hne1 hne2) h1
  have hkey : Real.sqrt (1 - (Real.sin k / Real.sqrt 2) ^ 2) =
      Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 := by
    rw [← Real.sqrt_div (hwPh_u_pos k).le]
    congr 1
    rw [div_pow, hs2sq]
    linarith
  have hr := hwPh_r_pos k
  have h3 : HasDerivAt (Real.arcsin ∘ fun x : ℝ => Real.sin x / Real.sqrt 2) (hwD1 k) k := by
    convert h2 using 1
    rw [hkey, hwD1]
    field_simp
  exact h3

/-- `ω″ = −sin k / (1 + cos² k)^{3/2}`. -/
theorem hwPh_hasDerivAt_D1 (k : ℝ) : HasDerivAt hwD1 (hwD2 k) k := by
  have h : HasDerivAt (fun x : ℝ => Real.cos x / Real.sqrt (1 + Real.cos x ^ 2))
      ((-Real.sin k * Real.sqrt (1 + Real.cos k ^ 2) -
        Real.cos k * (-(Real.sin k * Real.cos k) / Real.sqrt (1 + Real.cos k ^ 2))) /
          Real.sqrt (1 + Real.cos k ^ 2) ^ 2) k :=
    (Real.hasDerivAt_cos k).fun_div (hwPh_hasDerivAt_r k) (hwPh_r_pos k).ne'
  have hr := hwPh_r_pos k
  have hr2 := hwPh_r_sq k
  have hu := hwPh_u_pos k
  have h3 : HasDerivAt (fun x : ℝ => Real.cos x / Real.sqrt (1 + Real.cos x ^ 2)) (hwD2 k) k := by
    convert h using 1
    rw [hwD2, hr2]
    field_simp
    linear_combination (Real.sin k) * hr2
  exact h3

/-- The derivative of `(1 + cos² k)^{3/2}` is `−3 sin k cos k √(1 + cos² k)`. -/
theorem hwPh_hasDerivAt_ur (k : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + Real.cos x ^ 2) * Real.sqrt (1 + Real.cos x ^ 2))
      (-(3 * (Real.sin k * Real.cos k) * Real.sqrt (1 + Real.cos k ^ 2))) k := by
  have h := (hwPh_hasDerivAt_u k).fun_mul (hwPh_hasDerivAt_r k)
  have hr := hwPh_r_pos k
  have hr2 := hwPh_r_sq k
  convert h using 1
  field_simp
  linear_combination (-(Real.sin k * Real.cos k)) * hr2

/-- `ω‴ = −cos k (4 − 2 cos² k) / (1 + cos² k)^{5/2}`. -/
theorem hwPh_hasDerivAt_D2 (k : ℝ) : HasDerivAt hwD2 (hwD3 k) k := by
  have hr := hwPh_r_pos k
  have hr2 := hwPh_r_sq k
  have hu := hwPh_u_pos k
  have hsc := Real.sin_sq_add_cos_sq k
  have h : HasDerivAt (fun x : ℝ => -Real.sin x / ((1 + Real.cos x ^ 2) * Real.sqrt (1 + Real.cos x ^ 2)))
      ((-Real.cos k * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)) -
        -Real.sin k * (-(3 * (Real.sin k * Real.cos k) * Real.sqrt (1 + Real.cos k ^ 2)))) /
          ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)) ^ 2) k :=
    (Real.hasDerivAt_sin k).neg.fun_div (hwPh_hasDerivAt_ur k) (mul_pos hu hr).ne'
  have h3 : HasDerivAt (fun x : ℝ => -Real.sin x / ((1 + Real.cos x ^ 2) * Real.sqrt (1 + Real.cos x ^ 2)))
      (hwD3 k) k := by
    convert h using 1
    have hs2 : Real.sin k ^ 2 = 1 - Real.cos k ^ 2 := by linarith
    rw [hwD3, mul_pow, hr2]
    field_simp
    rw [hs2]
    linear_combination (4 * Real.cos k - 2 * Real.cos k ^ 3) * hr2
  exact h3

/-- `|ω″| ≥ 2/(3√3)` where `|sin k| ≥ 1/√2`. -/
theorem hwPh_D2_lower (k : ℝ) (h : 1 / Real.sqrt 2 ≤ |Real.sin k|) : 2 / (3 * Real.sqrt 3) ≤ |hwD2 k| := by
  have ht := hwPh_sqrt_two_pos
  have ht2 := hwPh_sqrt_two_sq
  have hw := hwPh_sqrt_three_pos
  have hr := hwPh_r_pos k
  have hu := hwPh_u_pos k
  have hsc := Real.sin_sq_add_cos_sq k
  have ha0 : 0 ≤ |Real.sin k| := abs_nonneg _
  have ha : 1 ≤ |Real.sin k| * Real.sqrt 2 := by rwa [div_le_iff₀ ht] at h
  have hs2 : 1 / 2 ≤ Real.sin k ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have hu' : 1 + Real.cos k ^ 2 ≤ 3 / 2 := by linarith
  have hrt : Real.sqrt (1 + Real.cos k ^ 2) * Real.sqrt 2 ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_mul hu.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1 : (1 + Real.cos k ^ 2) * (Real.sqrt (1 + Real.cos k ^ 2) * Real.sqrt 2) ≤ 3 / 2 * Real.sqrt 3 :=
    mul_le_mul hu' hrt (by positivity) (by norm_num)
  have h2 : 2 * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)) * 1 ≤
      2 * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)) * (|Real.sin k| * Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have h3 := mul_le_mul_of_nonneg_left h1 ha0
  rw [hwD2, abs_div, abs_neg, abs_of_pos (mul_pos hu hr), div_le_div_iff₀ (by positivity) (mul_pos hu hr)]
  nlinarith

/-- `|ω‴| ≥ 1/(2√2)` where `|cos k| ≥ 1/√2`. -/
theorem hwPh_D3_lower (k : ℝ) (h : 1 / Real.sqrt 2 ≤ |Real.cos k|) : 1 / (2 * Real.sqrt 2) ≤ |hwD3 k| := by
  have ht := hwPh_sqrt_two_pos
  have ht2 := hwPh_sqrt_two_sq
  have hr := hwPh_r_pos k
  have hu := hwPh_u_pos k
  have ha0 : 0 ≤ |Real.cos k| := abs_nonneg _
  have ha1 : |Real.cos k| ≤ 1 := Real.abs_cos_le_one k
  have hsq : Real.cos k ^ 2 = |Real.cos k| ^ 2 := (sq_abs _).symm
  have ha : 1 ≤ |Real.cos k| * Real.sqrt 2 := by rwa [div_le_iff₀ ht] at h
  have ht3 : Real.sqrt 2 ≤ 2 := by nlinarith
  have hhalf : 1 / 2 ≤ |Real.cos k| := by nlinarith
  have hu2 : 1 + Real.cos k ^ 2 ≤ 2 := by nlinarith
  have hrt : Real.sqrt (1 + Real.cos k ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hu2
  have hpos : 0 < 4 - 2 * Real.cos k ^ 2 := by linarith
  have hpoly : 1 + Real.cos k ^ 2 ≤ |Real.cos k| * (4 - 2 * Real.cos k ^ 2) := by
    rw [hsq]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1)
      (show 0 ≤ 2 * |Real.cos k| ^ 2 + 3 * |Real.cos k| - 1 by nlinarith)]
  have hden : 0 < (1 + Real.cos k ^ 2) ^ 2 * Real.sqrt (1 + Real.cos k ^ 2) := by positivity
  have h1 : (1 + Real.cos k ^ 2) ^ 2 * Real.sqrt (1 + Real.cos k ^ 2) ≤
      (2 * (1 + Real.cos k ^ 2)) * Real.sqrt 2 := by
    refine mul_le_mul ?_ hrt hr.le (by positivity)
    nlinarith
  have h2 : (2 * (1 + Real.cos k ^ 2)) * Real.sqrt 2 ≤
      (2 * (|Real.cos k| * (4 - 2 * Real.cos k ^ 2))) * Real.sqrt 2 :=
    mul_le_mul_of_nonneg_right (by linarith) ht.le
  rw [hwD3, abs_div, abs_neg, abs_mul, abs_of_pos hpos, abs_of_pos hden,
    div_le_div_iff₀ (by positivity) hden]
  linarith

/-- **H-phase** The derivative chain of the dispersion relation and the two lower bounds. -/
theorem hadamardPhaseFacts : HadamardPhaseFacts :=
  ⟨hwPh_hasDerivAt_dispersion, hwPh_hasDerivAt_D1, hwPh_hasDerivAt_D2, hwPh_D2_lower, hwPh_D3_lower⟩

/-! ## The amplitude -/

/-- The amplitude as a real function, `g(k) = 1 / √(2 (1 + cos² k))`. -/
noncomputable def hwAmp_g (k : ℝ) : ℝ := 1 / Real.sqrt (2 * (1 + Real.cos k ^ 2))

/-- Its derivative, `g′(k) = sin k cos k / (√2 (1 + cos² k)^{3/2})`. -/
noncomputable def hwAmp_g' (k : ℝ) : ℝ :=
  Real.sin k * Real.cos k / (Real.sqrt 2 * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)))

/-- `g′` is the derivative of `g`. -/
theorem hwAmp_hasDerivAt_g (k : ℝ) : HasDerivAt hwAmp_g (hwAmp_g' k) k := by
  have ht := hwPh_sqrt_two_pos
  have hr := hwPh_r_pos k
  have hr2 := hwPh_r_sq k
  have hu := hwPh_u_pos k
  have h1 : HasDerivAt (fun x : ℝ => Real.sqrt 2 * Real.sqrt (1 + Real.cos x ^ 2))
      (Real.sqrt 2 * (-(Real.sin k * Real.cos k) / Real.sqrt (1 + Real.cos k ^ 2))) k :=
    (hwPh_hasDerivAt_r k).const_mul _
  have h2 : HasDerivAt (fun x : ℝ => 1 / (Real.sqrt 2 * Real.sqrt (1 + Real.cos x ^ 2)))
      ((0 * (Real.sqrt 2 * Real.sqrt (1 + Real.cos k ^ 2)) -
        1 * (Real.sqrt 2 * (-(Real.sin k * Real.cos k) / Real.sqrt (1 + Real.cos k ^ 2)))) /
          (Real.sqrt 2 * Real.sqrt (1 + Real.cos k ^ 2)) ^ 2) k :=
    (hasDerivAt_const k (1 : ℝ)).fun_div h1 (mul_pos ht hr).ne'
  have hfun : hwAmp_g = fun x : ℝ => 1 / (Real.sqrt 2 * Real.sqrt (1 + Real.cos x ^ 2)) := by
    funext x
    rw [hwAmp_g, Real.sqrt_mul (by norm_num)]
  rw [hfun]
  convert h2 using 1
  rw [hwAmp_g']
  field_simp
  linear_combination (Real.sin k * Real.cos k) * hr2

/-- `g′` is continuous. -/
theorem hwAmp_continuous_g' : Continuous hwAmp_g' := by
  have h : Continuous (fun k : ℝ =>
      Real.sin k * Real.cos k / (Real.sqrt 2 * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2)))) := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun x => ?_)
    exact (mul_pos hwPh_sqrt_two_pos (mul_pos (hwPh_u_pos x) (hwPh_r_pos x))).ne'
  exact h

/-- `|g′(k)|` as the norm of the complex derivative of the amplitude. -/
theorem hwAmp_norm_deriv (k : ℝ) : ‖hwAmp' k‖ = |hwAmp_g' k| := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  rfl

/-- `g(k)` as the norm of the complex amplitude. -/
theorem hwAmp_norm (k : ℝ) : ‖hwAmp k‖ = hwAmp_g k := by
  have h : ‖hwAmp k‖ = |hwAmp_g k| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    rfl
  rw [h]
  exact abs_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))

/-- `k ↦ |g′(k)|` is interval integrable. -/
theorem hwAmp_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ‖hwAmp' x‖) MeasureTheory.volume a b := by
  have h : (fun x : ℝ => ‖hwAmp' x‖) = fun x : ℝ => |hwAmp_g' x| := funext hwAmp_norm_deriv
  rw [h]
  exact (continuous_abs.comp hwAmp_continuous_g').intervalIntegrable a b

/-- Where `sin k cos k ≥ 0` on `[a, b]`, the variation of `g` is `g(b) − g(a)`. -/
theorem hwAmp_integral_of_nonneg {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, 0 ≤ Real.sin x * Real.cos x) :
    ∫ x in a..b, ‖hwAmp' x‖ = hwAmp_g b - hwAmp_g a := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hwAmp_hasDerivAt_g x)
    (hwAmp_continuous_g'.intervalIntegrable a b)]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le hab] at hx
  have hpos : 0 ≤ hwAmp_g' x :=
    div_nonneg (h x hx) (mul_pos hwPh_sqrt_two_pos (mul_pos (hwPh_u_pos x) (hwPh_r_pos x))).le
  show ‖hwAmp' x‖ = hwAmp_g' x
  rw [hwAmp_norm_deriv, abs_of_nonneg hpos]

/-- Where `sin k cos k ≤ 0` on `[a, b]`, the variation of `g` is `g(a) − g(b)`. -/
theorem hwAmp_integral_of_nonpos {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, Real.sin x * Real.cos x ≤ 0) :
    ∫ x in a..b, ‖hwAmp' x‖ = hwAmp_g a - hwAmp_g b := by
  have h1 : ∫ x in a..b, ‖hwAmp' x‖ = ∫ x in a..b, -hwAmp_g' x := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hneg : hwAmp_g' x ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (h x hx)
        (mul_pos hwPh_sqrt_two_pos (mul_pos (hwPh_u_pos x) (hwPh_r_pos x))).le
    show ‖hwAmp' x‖ = -hwAmp_g' x
    rw [hwAmp_norm_deriv, abs_of_nonpos hneg]
  rw [h1, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hwAmp_hasDerivAt_g x)
      (hwAmp_continuous_g'.intervalIntegrable a b)]
  ring

/-- `g(0) = 1/2`. -/
theorem hwAmp_g_zero : hwAmp_g 0 = 1 / 2 := by
  have h : Real.sqrt (2 * (1 + Real.cos 0 ^ 2)) = 2 := by
    rw [Real.cos_zero, show (2 : ℝ) * (1 + 1 ^ 2) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hwAmp_g, h]

/-- `g(π/4) = 1/√3`. -/
theorem hwAmp_g_pi_div_four : hwAmp_g (Real.pi / 4) = 1 / Real.sqrt 3 := by
  have h : 2 * (1 + Real.cos (Real.pi / 4) ^ 2) = 3 := by
    rw [Real.cos_pi_div_four, div_pow, hwPh_sqrt_two_sq]
    norm_num
  rw [hwAmp_g, h]

/-- `g(−π/4) = 1/√3`. -/
theorem hwAmp_g_neg_pi_div_four : hwAmp_g (-(Real.pi / 4)) = 1 / Real.sqrt 3 := by
  rw [← hwAmp_g_pi_div_four, hwAmp_g, hwAmp_g, Real.cos_neg]

/-- `g(π/2) = 1/√2`. -/
theorem hwAmp_g_pi_div_two : hwAmp_g (Real.pi / 2) = 1 / Real.sqrt 2 := by
  have h : 2 * (1 + Real.cos (Real.pi / 2) ^ 2) = 2 := by
    rw [Real.cos_pi_div_two]
    norm_num
  rw [hwAmp_g, h]

/-- `g(3π/4) = 1/√3`. -/
theorem hwAmp_g_three_pi_div_four : hwAmp_g (3 * Real.pi / 4) = 1 / Real.sqrt 3 := by
  rw [← hwAmp_g_pi_div_four, hwAmp_g, hwAmp_g, show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, neg_sq]

/-- The amplitude norm on the arc `[−π/4, π/4]` is `√3 − 1`. -/
theorem hwAmp_ampNorm_cos_arc : ampNorm hwAmp hwAmp' (-(Real.pi / 4)) (Real.pi / 4) = Real.sqrt 3 - 1 := by
  have hpi := Real.pi_pos
  have h1 : ∫ x in (-(Real.pi / 4))..0, ‖hwAmp' x‖ = hwAmp_g (-(Real.pi / 4)) - hwAmp_g 0 :=
    hwAmp_integral_of_nonpos (by linarith) (fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 (by linarith [hx.1]))
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1]) (by linarith [hx.2])))
  have h2 : ∫ x in (0 : ℝ)..(Real.pi / 4), ‖hwAmp' x‖ = hwAmp_g (Real.pi / 4) - hwAmp_g 0 :=
    hwAmp_integral_of_nonneg (by linarith) (fun x hx =>
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2]))
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1]) (by linarith [hx.2])))
  have hw := hwPh_sqrt_three_pos
  have hw2 := hwPh_sqrt_three_sq
  rw [ampNorm, hwAmp_norm,
    ← intervalIntegral.integral_add_adjacent_intervals (hwAmp_intervalIntegrable _ 0)
      (hwAmp_intervalIntegrable 0 _),
    h1, h2, hwAmp_g_zero, hwAmp_g_pi_div_four, hwAmp_g_neg_pi_div_four]
  field_simp
  linear_combination (-2 : ℝ) * hw2

/-- The amplitude norm on the arc `[π/4, 3π/4]` is `√2 − 1/√3`. -/
theorem hwAmp_ampNorm_sin_arc :
    ampNorm hwAmp hwAmp' (Real.pi / 4) (3 * Real.pi / 4) = Real.sqrt 2 - 1 / Real.sqrt 3 := by
  have hpi := Real.pi_pos
  have h1 : ∫ x in (Real.pi / 4)..(Real.pi / 2), ‖hwAmp' x‖ = hwAmp_g (Real.pi / 2) - hwAmp_g (Real.pi / 4) :=
    hwAmp_integral_of_nonneg (by linarith) (fun x hx =>
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2]))
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1]) hx.2))
  have h2 : ∫ x in (Real.pi / 2)..(3 * Real.pi / 4), ‖hwAmp' x‖ =
      hwAmp_g (Real.pi / 2) - hwAmp_g (3 * Real.pi / 4) :=
    hwAmp_integral_of_nonpos (by linarith) (fun x hx =>
      mul_nonpos_of_nonneg_of_nonpos
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2]))
        (Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2])))
  have ht := hwPh_sqrt_two_pos
  have ht2 := hwPh_sqrt_two_sq
  have hw := hwPh_sqrt_three_pos
  rw [ampNorm, hwAmp_norm,
    ← intervalIntegral.integral_add_adjacent_intervals (hwAmp_intervalIntegrable _ (Real.pi / 2))
      (hwAmp_intervalIntegrable (Real.pi / 2) _),
    h1, h2, hwAmp_g_pi_div_two, hwAmp_g_pi_div_four, hwAmp_g_three_pi_div_four]
  field_simp
  linear_combination (-Real.sqrt 3) * ht2

/-- The amplitude norm is invariant under the shift of the arc by `π`. -/
theorem hwAmp_ampNorm_add_pi (a b : ℝ) :
    ampNorm hwAmp hwAmp' (a + Real.pi) (b + Real.pi) = ampNorm hwAmp hwAmp' a b := by
  have h0 : ∀ x : ℝ, hwAmp (x + Real.pi) = hwAmp x := by
    intro x
    rw [hwAmp, hwAmp, Real.cos_add_pi, neg_sq]
  have h1 : ∀ x : ℝ, hwAmp' (x + Real.pi) = hwAmp' x := by
    intro x
    rw [hwAmp', hwAmp', Real.cos_add_pi, Real.sin_add_pi, neg_sq, neg_mul_neg]
  rw [ampNorm, ampNorm, h0, ← intervalIntegral.integral_comp_add_right (fun x : ℝ => ‖hwAmp' x‖) Real.pi]
  simp only [h1]

/-- **H-amp** The amplitude: its derivative, and its amplitude norm on the four arcs of length `π/2`. -/
theorem hadamardAmplitudeFacts : HadamardAmplitudeFacts := by
  refine ⟨fun k => (hwAmp_hasDerivAt_g k).ofReal_comp, hwAmp_ampNorm_cos_arc.le, hwAmp_ampNorm_sin_arc.le, ?_, ?_⟩
  · have h := hwAmp_ampNorm_add_pi (-(Real.pi / 4)) (Real.pi / 4)
    rw [show -(Real.pi / 4) + Real.pi = 3 * Real.pi / 4 by ring,
      show Real.pi / 4 + Real.pi = 5 * Real.pi / 4 by ring] at h
    rw [h]
    exact hwAmp_ampNorm_cos_arc.le
  · have h := hwAmp_ampNorm_add_pi (Real.pi / 4) (3 * Real.pi / 4)
    rw [show Real.pi / 4 + Real.pi = 5 * Real.pi / 4 by ring,
      show 3 * Real.pi / 4 + Real.pi = 7 * Real.pi / 4 by ring] at h
    rw [h]
    exact hwAmp_ampNorm_sin_arc.le

end OscInt.HadamardWalkAux
