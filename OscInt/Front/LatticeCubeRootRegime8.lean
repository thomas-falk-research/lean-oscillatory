/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeCubeRoot

/-!
# Batch LE2, part P-r8: the regime `t ≥ 8`, conditional on the piece bounds

Route `docs/proof-LE2.md` (P-arc, P-r8 and the revision after the route referee). With `τ = t^{−1/3} ∈ (0, 1/2]`
(`t τ³ = 1`) the goal is `‖I(t, tv)‖ ≤ C* τ`, `C* = 8(1 + √7)/3`:
* `v ≥ 1 − 2τ²`: P-cap high with `δ = 2τ²` (or P-cap whole when `v − δ ≥ 1`); `π − 2 arcsin(v − δ) ≤ 4 arcsin(√2 τ)
  ≤ 2πτ` (chord with `b = √2/2`). Total `≤ (2π + 8/3)τ`.
* `1/2 ≤ v < 1 − 2τ²`: P-band high with `δ = (3/2)τ²`, P-arc 3 (antitone `arcsin s + (4√2/3)√(1 − s)`) and the
  derivative-free P-arc 5; the bound is exactly `C* τ`.
* `0 ≤ v ≤ δ`: P-band low and the chord `arcsin y ≤ (8/7) y` on `[0, 3/4]`: `≤ (184/21)τ`.
* `δ ≤ v ≤ 1/2`: P-band high. Deviation from the route (no convexity in `v`): convexity of `arcsin` on `[0, 1]`
  (from the concavity of `sin`) gives window monotonicity, `arcsin(v + δ) − arcsin(v − δ) ≤ Q(δ)` with
  `Q(d) = arcsin(1/2 + d) − arcsin(1/2 − d)`, and `Q(d) ≤ 2.692 d` (chord to `7/8` on the right, tangent at `1/2` on the
  left); with `2/(tv) ≤ 2/(tδ)` the total is `≤ (8.076τ − 4τ² + 20/3)τ ≤ 9.705τ`.
-/

namespace OscInt.LatticeCubeRootAux.R8

open OscInt.Statements OscInt.Blueprint.LatticeCubeRoot Real Set

/-- `arcsin` is convex on `[0, 1]` (from the concavity of `sin` on `[0, π]`). -/
theorem arcsin_convexOn : ConvexOn ℝ (Icc (0 : ℝ) 1) arcsin := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hX0 := arcsin_nonneg.mpr hx.1
  have hY0 := arcsin_nonneg.mpr hy.1
  have hX1 := arcsin_le_pi_div_two x
  have hY1 := arcsin_le_pi_div_two y
  have hpi := pi_pos
  have hc := strictConcaveOn_sin_Icc.concaveOn.2 (x := arcsin x) (y := arcsin y)
    ⟨hX0, by linarith⟩ ⟨hY0, by linarith⟩ ha hb hab
  simp only [smul_eq_mul, sin_arcsin (by linarith [hx.1]) hx.2, sin_arcsin (by linarith [hy.1]) hy.2] at hc
  rw [arcsin_le_iff_le_sin ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2, hy.2]⟩
    ⟨by nlinarith, by nlinarith⟩]
  exact hc

/-- Chord through the origin. -/
theorem arcsin_le_chord {y b : ℝ} (hy : 0 ≤ y) (hyb : y ≤ b) (hb1 : b ≤ 1) (hb : 0 < b) :
    arcsin y ≤ y / b * arcsin b := by
  have hl0 : 0 ≤ y / b := div_nonneg hy hb.le
  have hl1 : y / b ≤ 1 := (div_le_one hb).mpr hyb
  have h := arcsin_convexOn.2 (x := 0) (y := b) ⟨le_refl 0, zero_le_one⟩ ⟨hb.le, hb1⟩
    (sub_nonneg.mpr hl1) hl0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, arcsin_zero] at h
  rwa [div_mul_cancel₀ y hb.ne'] at h

/-- `arcsin(3/4) ≤ 6/7` (`sin x ≥ x − x³/6`). -/
theorem arcsin_three_quarters_le : arcsin (3 / 4) ≤ 6 / 7 := by
  have hpi := pi_gt_d2
  rw [arcsin_le_iff_le_sin ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩]
  have := sin_ge_sub_cube (x := 6 / 7) (by norm_num)
  linarith

/-- `arcsin(7/8) ≤ 11/10` (`sin x ≥ x − x³/6`). -/
theorem arcsin_seven_eighths_le : arcsin (7 / 8) ≤ 11 / 10 := by
  have hpi := pi_gt_d2
  rw [arcsin_le_iff_le_sin ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩]
  have := sin_ge_sub_cube (x := 11 / 10) (by norm_num)
  linarith

/-- `arcsin(1/2) = π/6`. -/
theorem arcsin_half : arcsin (1 / 2) = π / 6 := by
  rw [← sin_pi_div_six, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-- Chord with `b = 3/4`: `arcsin y ≤ (8/7) y` on `[0, 3/4]`. -/
theorem arcsin_le_eight_sevenths {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 3 / 4) : arcsin y ≤ 8 / 7 * y := by
  have h := arcsin_le_chord hy hy1 (by norm_num) (by norm_num)
  have h2 := arcsin_three_quarters_le
  have : y / (3 / 4) * arcsin (3 / 4) ≤ y / (3 / 4) * (6 / 7) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- `arcsin(√2 τ) ≤ π τ / 2` for `0 ≤ τ ≤ 1/2`. -/
theorem arcsin_sqrt_two_mul_le {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) : arcsin (√2 * τ) ≤ π * τ / 2 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hb : arcsin (√2 / 2) = π / 4 := by
    rw [← sin_pi_div_four, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]
  have h := arcsin_le_chord (y := √2 * τ) (b := √2 / 2) (by positivity) (by nlinarith)
    (by nlinarith) (by positivity)
  rw [hb] at h
  have : √2 * τ / (√2 / 2) = 2 * τ := by field_simp
  rw [this] at h
  linarith

/-- Window monotonicity from convexity. -/
theorem arcsin_window_mono {v w δ : ℝ} (hδ : 0 < δ) (h0 : δ ≤ v) (hvw : v ≤ w) (h1 : w + δ ≤ 1) :
    arcsin (v + δ) - arcsin (v - δ) ≤ arcsin (w + δ) - arcsin (w - δ) := by
  have hc := arcsin_convexOn
  have m : ∀ x, δ ≤ x → x ≤ w → x - δ ∈ Icc (0 : ℝ) 1 ∧ x + δ ∈ Icc (0 : ℝ) 1 := fun x hx hxw =>
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨hv1, hv2⟩ := m v h0 hvw
  obtain ⟨hw1, hw2⟩ := m w (h0.trans hvw) le_rfl
  have s1 := hc.secant_mono hv1 hv2 hw2 (by linarith) (by linarith) (by linarith)
  have s2 := hc.secant_mono hw2 hv1 hw1 (by linarith) (by linarith) (by linarith)
  have e1 : v + δ - (v - δ) = 2 * δ := by ring
  have e2 : w - δ - (w + δ) = -(2 * δ) := by ring
  have e3 : v - δ - (w + δ) = -(w - v + 2 * δ) := by ring
  have e4 : w + δ - (v - δ) = w - v + 2 * δ := by ring
  rw [e1, e4] at s1
  rw [e2, e3] at s2
  rw [div_neg, div_neg, neg_le_neg_iff, div_le_div_iff₀ (by linarith) (by linarith)] at s2
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at s1
  have hp : 0 < w - v + 2 * δ := by linarith
  nlinarith

/-- The window at `1/2`: `arcsin(1/2 + d) − arcsin(1/2 − d) ≤ 2.692 d` for `0 < d ≤ 3/8`. -/
theorem arcsin_window_half {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 3 / 8) :
    arcsin (1 / 2 + d) - arcsin (1 / 2 - d) ≤ 673 / 250 * d := by
  have hc := arcsin_convexOn
  have hl0 : 0 ≤ 8 * d / 3 := by positivity
  have hl1 : 1 - 8 * d / 3 ≥ 0 := by linarith
  have h1 := hc.2 (x := 1 / 2) (y := 7 / 8) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    hl1 hl0 (by ring)
  simp only [smul_eq_mul] at h1
  rw [show (1 - 8 * d / 3) * (1 / 2) + 8 * d / 3 * (7 / 8) = 1 / 2 + d by ring, arcsin_half] at h1
  have hder := hasDerivAt_arcsin (x := 1 / 2) (by norm_num) (by norm_num)
  have h2 := hc.slope_le_of_hasDerivAt (x := 1 / 2 - d) (y := 1 / 2) ⟨by linarith, by linarith⟩
    ⟨by norm_num, by norm_num⟩ (by linarith) hder
  rw [slope_def_field, arcsin_half, show (1 : ℝ) / 2 - (1 / 2 - d) = d by ring] at h2
  have hsq : (0.866 : ℝ) ≤ √(1 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h3 : 1 / √(1 - (1 / 2 : ℝ) ^ 2) ≤ 1 / 0.866 := one_div_le_one_div_of_le (by norm_num) hsq
  rw [div_le_iff₀ hd] at h2
  have h4 := arcsin_seven_eighths_le
  have hpi := pi_gt_d4
  nlinarith

/-- The derivative of `s ↦ arcsin s + (4√2/3)√(1 − s)` is `≤ 0` on `(1/8, 1)`. -/
theorem arc_sqrt_deriv_nonpos {x : ℝ} (hx : x ∈ Ioo (1 / 8 : ℝ) 1) :
    1 / √(1 - x ^ 2) + 4 * √2 / 3 * (-1 / (2 * √(1 - x))) ≤ 0 := by
  obtain ⟨h1, h2⟩ := hx
  have hA : 0 < √(1 - x) := Real.sqrt_pos.mpr (by linarith)
  have hB : 0 < √(1 + x) := Real.sqrt_pos.mpr (by linarith)
  have hAB : √(1 - x ^ 2) = √(1 - x) * √(1 + x) := by
    rw [← Real.sqrt_mul (by linarith)]; ring_nf
  have hRB : (3 / 2 : ℝ) ≤ √2 * √(1 + x) := by
    rw [← Real.sqrt_mul (by norm_num), Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
  rw [hAB]
  have e : 1 / (√(1 - x) * √(1 + x)) + 4 * √2 / 3 * (-1 / (2 * √(1 - x)))
      = (3 - 2 * (√2 * √(1 + x))) / (3 * (√(1 - x) * √(1 + x))) := by
    field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- P-arc 3: `s ↦ arcsin s + (4√2/3)√(1 − s)` is antitone on `[1/8, 1]`. -/
theorem arc_sqrt_antitone :
    AntitoneOn (fun s => arcsin s + 4 * √2 / 3 * √(1 - s)) (Icc (1 / 8 : ℝ) 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x =>
    1 / √(1 - x ^ 2) + 4 * √2 / 3 * (-1 / (2 * √(1 - x)))) (convex_Icc _ _) ?_ ?_ ?_
  · exact (continuous_arcsin.add (continuous_const.mul
      (continuous_const.sub continuous_id).sqrt)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hd1 := hasDerivAt_arcsin (x := x) (by linarith [hx.1]) (by linarith [hx.2])
    have hd2 := ((hasDerivAt_id x).const_sub 1).sqrt (by simp; linarith [hx.2])
    exact ((hd1.add (hd2.const_mul (4 * √2 / 3))).hasDerivWithinAt)
  · intro x hx
    rw [interior_Icc] at hx
    exact arc_sqrt_deriv_nonpos hx

/-- P-arc 3, the square-root comparison. -/
theorem arcsin_sub_le_sqrt {x y : ℝ} (hx : 1 / 8 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    arcsin y - arcsin x ≤ 4 * √2 / 3 * (√(1 - x) - √(1 - y)) := by
  have := arc_sqrt_antitone ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  simp only at this
  linarith

/-- P-arc 5, derivative-free (revision). -/
theorem parc5 {a b x Δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ^ 2 = Δ + 3 / 2) (hb2 : b ^ 2 = Δ - 3 / 2)
    (hΔ : 2 ≤ Δ) (hx : 0 ≤ x) (hx2 : x ^ 2 * Δ = 2) :
    8 * √2 / 3 * (a - b) - x ^ 2 ≤ 8 / 3 * (√7 - 1) - 1 := by
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ √2 := Real.sqrt_nonneg _
  have hs1 : (7 / 4 : ℝ) ≤ √7 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : √7 ≤ 3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hab : √7 * Δ / 4 ≤ a * b := by
    have h1 : (√7 * Δ / 4) ^ 2 ≤ (a * b) ^ 2 := by
      rw [mul_pow, ha2, hb2]; nlinarith
    nlinarith [mul_nonneg ha hb]
  have hsum : (4 + √7) ≤ (a + b) ^ 2 * x ^ 2 := by nlinarith
  have hy : 3 * √2 ≤ (√7 - 1) * (a + b) * x := by
    have h1 : (3 * √2) ^ 2 ≤ ((√7 - 1) * (a + b) * x) ^ 2 := by
      have e : ((√7 - 1) * (a + b) * x) ^ 2 = (√7 - 1) ^ 2 * ((a + b) ^ 2 * x ^ 2) := by ring
      rw [e]
      have e2 : (√7 - 1) ^ 2 = 8 - 2 * √7 := by nlinarith
      rw [e2]
      nlinarith
    have h2 : 0 ≤ (√7 - 1) * (a + b) * x := by
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hx
    nlinarith
  have hpos : 0 < a + b := by nlinarith
  have hdiff : (a - b) * (a + b) = 3 := by nlinarith
  have hx1 : x ≤ 1 := by nlinarith
  have hmain : 8 * √2 / 3 * (a - b) ≤ 8 / 3 * (√7 - 1) * x := by
    have : 8 * √2 / 3 * (a - b) * (a + b) ≤ 8 / 3 * (√7 - 1) * x * (a + b) := by
      rw [mul_assoc, hdiff]; nlinarith
    exact le_of_mul_le_mul_right this hpos
  nlinarith

/-- The cap arc: `π − 2 arcsin w ≤ 2πτ` when `1 − 4τ² ≤ w`. -/
theorem cap_arc_le {τ w : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) (hw : 1 - 4 * τ ^ 2 ≤ w) :
    π - 2 * arcsin w ≤ 2 * π * τ := by
  set u := arcsin (√2 * τ) with hu
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsin : sin u = √2 * τ := sin_arcsin (by nlinarith [Real.sqrt_nonneg 2]) (by nlinarith)
  have hcos : sin (π / 2 - 2 * u) = 1 - 4 * τ ^ 2 := by
    rw [sin_pi_div_two_sub, cos_two_mul, cos_sq', hsin]; nlinarith
  have hu0 : 0 ≤ u := arcsin_nonneg.mpr (by positivity)
  have hu1 := arcsin_le_pi_div_two (√2 * τ)
  have harc : arcsin (1 - 4 * τ ^ 2) = π / 2 - 2 * u := by
    rw [← hcos, arcsin_sin (by linarith) (by linarith)]
  have hmono := arcsin_le_arcsin hw
  have := arcsin_sqrt_two_mul_le h0 h1
  linarith

/-- Regime `v ≥ 1 − 2τ²` (cap or whole interval). -/
theorem case_cap (hCH : CapHighFacts) (hW : WholeFacts) {t τ v : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : t * τ ^ 3 = 1) (hv : 1 - 2 * τ ^ 2 ≤ v) :
    ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + √7) / 3 * τ := by
  have ht0 : 0 < t := by nlinarith [pow_pos hτ0 3]
  have hu : 4 ≤ t * τ := by nlinarith [pow_pos hτ0 2]
  have hC : 9.72 ≤ 8 * (1 + √7) / 3 := by
    have : (2.645 : ℝ) ≤ √7 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  have hv2 : 1 / 2 ≤ v := by nlinarith
  rcases le_or_gt 1 (v - 2 * τ ^ 2) with h | h
  · refine (hW t v ht0 (by nlinarith)).trans ?_
    have e1 : 2 / (t * (v - 1)) ≤ τ := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t * τ) (by linarith : 0 ≤ v - 1 - 2 * τ ^ 2)]
    have e2 : 2 / (t * v * (v + 1)) ≤ τ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t * τ - 4) (by nlinarith : (0 : ℝ) ≤ v * (v + 1) - 2)]
    nlinarith
  · refine (hCH t v (2 * τ ^ 2) ht0 (by positivity) (by nlinarith) h).trans ?_
    have e1 : 4 / (t * (2 * τ ^ 2)) = 2 * τ := by
      rw [div_eq_iff (by positivity)]; linear_combination -4 * ht
    have e2 : 2 / (t * v * (v + 1)) ≤ 2 / 3 * τ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t * τ - 4) (by nlinarith : (0 : ℝ) ≤ v * (v + 1) - 3 / 4)]
    have e3 := cap_arc_le hτ0.le hτ (w := v - 2 * τ ^ 2) (by linarith)
    have hpi := pi_lt_d2
    rw [e1]
    nlinarith

/-- The band term of the extremal regime, rescaled: with `Δ = (1 − v)/τ² ≥ 2`,
`2(arcsin(v + δ) − arcsin(v − δ)) − 2τ³/(1 − v) ≤ (A − 1)τ`. -/
theorem band_extremal {τ v : ℝ} (hτ0 : 0 < τ) (hv : 1 / 2 ≤ v) (hv1 : v < 1 - 2 * τ ^ 2) :
    2 * (arcsin (v + 3 / 2 * τ ^ 2) - arcsin (v - 3 / 2 * τ ^ 2)) - 2 * τ ^ 3 / (1 - v) ≤
      (8 / 3 * (√7 - 1) - 1) * τ := by
  have h1v : 0 < 1 - v := by nlinarith
  have harc := arcsin_sub_le_sqrt (x := v - 3 / 2 * τ ^ 2) (y := v + 3 / 2 * τ ^ 2) (by nlinarith)
    (by nlinarith) (by nlinarith)
  set p := √(1 - (v - 3 / 2 * τ ^ 2)) with hp
  set q := √(1 - (v + 3 / 2 * τ ^ 2)) with hq
  have hp2 : p ^ 2 = 1 - (v - 3 / 2 * τ ^ 2) := Real.sq_sqrt (by nlinarith)
  have hq2 : q ^ 2 = 1 - (v + 3 / 2 * τ ^ 2) := Real.sq_sqrt (by nlinarith)
  set Δ := (1 - v) / τ ^ 2 with hΔ
  have hΔ2 : 2 ≤ Δ := by rw [hΔ, le_div_iff₀ (by positivity)]; linarith
  set x := √(2 / Δ) with hx
  have hx2 : x ^ 2 = 2 / Δ := Real.sq_sqrt (by positivity)
  have hP := parc5 (a := p / τ) (b := q / τ) (x := x) (Δ := Δ) (by positivity) (by positivity)
    (by rw [div_pow, hp2, hΔ]; field_simp; ring) (by rw [div_pow, hq2, hΔ]; field_simp; ring) hΔ2
    (Real.sqrt_nonneg _) (by rw [hx2]; field_simp)
  have hxe : 2 * τ ^ 3 / (1 - v) = τ * x ^ 2 := by
    rw [hx2, hΔ]; field_simp
  have hpq : 8 * √2 / 3 * (p / τ - q / τ) * τ = 8 * √2 / 3 * (p - q) := by
    field_simp
  rw [hxe]
  have := mul_le_mul_of_nonneg_right hP hτ0.le
  nlinarith

/-- `9.7218 < C*`. -/
theorem cstar_lower : (9.7218 : ℝ) < 8 * (1 + √7) / 3 := by
  have : (2.6457 : ℝ) < √7 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- Regime `1/2 ≤ v < 1 − 2τ²` (band, the extremal regime). -/
theorem case_band_high (hBH : BandHighFacts) {t τ v : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : t * τ ^ 3 = 1) (hv : 1 / 2 ≤ v) (hv1 : v < 1 - 2 * τ ^ 2) :
    ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + √7) / 3 * τ := by
  have ht0 : 0 < t := by nlinarith [pow_pos hτ0 3]
  have hu : 4 ≤ t * τ := by nlinarith [pow_pos hτ0 2]
  refine (hBH t v (3 / 2 * τ ^ 2) ht0 (by positivity) (by nlinarith) (by nlinarith)).trans ?_
  have e1 : 8 / (t * (3 / 2 * τ ^ 2)) = 16 / 3 * τ := by
    rw [div_eq_iff (by positivity)]; linear_combination -8 * ht
  have e2 : 2 / (t * v) ≤ τ := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1v : 0 < 1 - v := by nlinarith
  have e3 : 2 * τ ^ 3 / (1 - v) ≤ 4 / (t * (1 - v ^ 2)) := by
    have h1v2 : 0 < 1 - v ^ 2 := by nlinarith
    rw [div_le_div_iff₀ h1v (mul_pos ht0 h1v2)]
    nlinarith [mul_nonneg h1v.le (by linarith : (0 : ℝ) ≤ 1 - v)]
  have := band_extremal hτ0 hv hv1
  rw [e1]
  have : 8 / 3 * (√7 - 1) - 1 + 16 / 3 + 1 = 8 * (1 + √7) / 3 := by ring
  nlinarith

/-- Regime `0 ≤ v ≤ δ` (band, low velocities). -/
theorem case_band_low (hBL : BandLowFacts) {t τ v : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : t * τ ^ 3 = 1) (hv0 : 0 ≤ v) (hv : v ≤ 3 / 2 * τ ^ 2) :
    ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + √7) / 3 * τ := by
  have ht0 : 0 < t := by nlinarith [pow_pos hτ0 3]
  refine (hBL t v (3 / 2 * τ ^ 2) ht0 hv0 (by positivity) hv (by nlinarith)).trans ?_
  have e1 : 8 / (t * (3 / 2 * τ ^ 2)) = 16 / 3 * τ := by
    rw [div_eq_iff (by positivity)]; linear_combination -8 * ht
  have hτ4 : τ ^ 2 ≤ 1 / 4 := by nlinarith
  have e2 : 0 ≤ 4 / (t * (1 - v ^ 2)) := div_nonneg (by norm_num) (mul_nonneg ht0.le (by nlinarith))
  have a1 := arcsin_le_eight_sevenths (y := v + 3 / 2 * τ ^ 2) (by positivity) (by nlinarith)
  have a2 := arcsin_le_eight_sevenths (y := 3 / 2 * τ ^ 2 - v) (by linarith) (by nlinarith)
  have a3 : arcsin (v - 3 / 2 * τ ^ 2) = -arcsin (3 / 2 * τ ^ 2 - v) := by
    rw [← arcsin_neg]; ring_nf
  have hC := cstar_lower
  rw [e1, a3]
  nlinarith

/-- Regime `δ ≤ v ≤ 1/2` (band, high velocities, small `v`). -/
theorem case_band_mid (hBH : BandHighFacts) {t τ v : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : t * τ ^ 3 = 1) (hv0 : 3 / 2 * τ ^ 2 ≤ v) (hv : v ≤ 1 / 2) :
    ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + √7) / 3 * τ := by
  have ht0 : 0 < t := by nlinarith [pow_pos hτ0 3]
  have hτ2 : 0 < τ ^ 2 := by positivity
  refine (hBH t v (3 / 2 * τ ^ 2) ht0 (by positivity) hv0 (by nlinarith)).trans ?_
  have e1 : 8 / (t * (3 / 2 * τ ^ 2)) = 16 / 3 * τ := by
    rw [div_eq_iff (by positivity)]; linear_combination -8 * ht
  have e2 : 2 / (t * v) ≤ 4 / 3 * τ := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hv0 (by positivity : (0 : ℝ) ≤ t * τ)]
  have e3 : 4 * τ ^ 3 ≤ 4 / (t * (1 - v ^ 2)) := by
    have h1v2 : 0 < 1 - v ^ 2 := by nlinarith
    rw [le_div_iff₀ (mul_pos ht0 h1v2)]; nlinarith [mul_nonneg ht0.le (pow_pos hτ0 3).le]
  have w1 := arcsin_window_mono (v := v) (w := 1 / 2) (δ := 3 / 2 * τ ^ 2) (by positivity) hv0 hv
    (by nlinarith)
  have w2 := arcsin_window_half (d := 3 / 2 * τ ^ 2) (by positivity) (by nlinarith)
  have hC := cstar_lower
  rw [e1]
  nlinarith [mul_nonneg hτ0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - τ)]

/-- `τ = t^{−1/3}`: `0 < τ`, `t τ³ = 1`, `τ ≤ 1/2` for `t ≥ 8`. -/
theorem tau_facts {t : ℝ} (ht : 8 ≤ t) :
    0 < t ^ (-(1 : ℝ) / 3) ∧ t * (t ^ (-(1 : ℝ) / 3)) ^ 3 = 1 ∧ t ^ (-(1 : ℝ) / 3) ≤ 1 / 2 := by
  have ht0 : 0 < t := by linarith
  have h0 : 0 < t ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos ht0 _
  have h3 : t * (t ^ (-(1 : ℝ) / 3)) ^ 3 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num [Real.rpow_neg_one, ht0.ne']
  refine ⟨h0, h3, ?_⟩
  by_contra h
  have h' : (1 / 2 : ℝ) ^ 3 < (t ^ (-(1 : ℝ) / 3)) ^ 3 :=
    pow_lt_pow_left₀ (not_le.mp h) (by norm_num) (by norm_num)
  nlinarith

/-- **P-r8** from the piece bounds. -/
theorem regime8_of (hBL : BandLowFacts) (hBH : BandHighFacts) (hCH : CapHighFacts) (hW : WholeFacts) :
    Regime8Facts := by
  intro t v ht hv0
  obtain ⟨hτ0, h3, hτ⟩ := tau_facts ht
  rcases le_or_gt (1 - 2 * (t ^ (-(1 : ℝ) / 3)) ^ 2) v with h | h
  · exact case_cap hCH hW hτ0 hτ h3 h
  rcases le_or_gt (1 / 2) v with h' | h'
  · exact case_band_high hBH hτ0 hτ h3 h' h
  rcases le_or_gt v (3 / 2 * (t ^ (-(1 : ℝ) / 3)) ^ 2) with h'' | h''
  · exact case_band_low hBL hτ0 hτ h3 hv0 h''
  · exact case_band_mid hBH hτ0 hτ h3 h''.le h'.le

end OscInt.LatticeCubeRootAux.R8
