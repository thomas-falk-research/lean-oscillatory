/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeCubeRoot

/-!
# Batch LE2, part P-r38: times `3 ≤ t ≤ 8` (route `docs/proof-LE2.md`)

`Regime38Facts` from the piece bounds P-band (low), P-cap (low, high) and P-cap whole, with `δ = 1/2`. Each sub-range
of `v ≥ 0` gives `‖I(t, tv)‖ ≤ A + B/t` with rational `A, B ≥ 0` (`v ≥ 3/2` whole; `1/2 ≤ v < 3/2` cap high;
`1/4 ≤ v < 1/2` cap low; `1/8 ≤ v < 1/4` and `0 ≤ v < 1/8` band low, the split of the route referee's MAJOR fix).
With `s = t^{1/3} ∈ [3^{1/3}, 2]`, `t^{1/3}(A + B/t) = As + Bs^{−2}` is convex in `s`, so it is at most its larger end
value; all end values are below `97/10 < C*` (`3^{1/3} < 13/9`, `π < 22/7`, `√7 > 211/80`). No integrals.
-/

namespace OscInt.LatticeCubeRootAux.R38

open OscInt.Statements OscInt.Blueprint.LatticeCubeRoot Real Set

/-- `arcsin x ≤ y` from the cubic lower bound of `sin y`. -/
theorem arcsin_le_of_cube {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy2 : y ≤ 3 / 2)
    (h : x ≤ y - y ^ 3 / 6) : arcsin x ≤ y := by
  rw [arcsin_le_iff_le_sin ⟨by linarith, hx1⟩ ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩]
  exact h.trans (sin_ge_sub_cube hy)

/-- `arcsin (1/2) = π/6`. -/
theorem arcsin_half : arcsin (1 / 2) = π / 6 := by
  rw [← sin_pi_div_six, arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-- `π < 22/7`. -/
theorem pi_lt_22_7 : π < 22 / 7 := by linarith [pi_lt_d4]

/-- `t^{−1/3}` as the inverse of `s = t^{1/3}`, with `s³ = t`. -/
theorem cube_root_facts {t : ℝ} (ht : 0 < t) :
    0 < t ^ ((1 : ℝ) / 3) ∧ (t ^ ((1 : ℝ) / 3)) ^ 3 = t ∧ t ^ (-(1 : ℝ) / 3) = (t ^ ((1 : ℝ) / 3))⁻¹ := by
  refine ⟨rpow_pos_of_pos ht _, ?_, ?_⟩
  · rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num
  · rw [← rpow_neg ht.le]; norm_num [neg_div]

/-- `s ≤ b` from `s³ ≤ b³` for `0 ≤ b`. -/
theorem le_of_cube_le {s b : ℝ} (hb : 0 ≤ b) (h : s ^ 3 ≤ b ^ 3) : s ≤ b := by
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) hb (by norm_num : (3 : ℕ) ≠ 0)
  linarith

/-- **End-point bound.** If `t^{1/3}(A + B/t) ≤ M` at `t = 3` (with `3^{1/3} < 13/9`) and at `t = 8`, then on all of
`[3, 8]`, by convexity of `s ↦ As + Bs^{−2}`. -/
theorem endpoint_bound {A B M t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h3 : 3 ≤ t) (h8 : t ≤ 8)
    (e3 : 13 / 9 * (A + B / 3) ≤ M) (e8 : 2 * (A + B / 8) ≤ M) :
    A + B / t ≤ M * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  obtain ⟨hs0, hs3, hneg⟩ := cube_root_facts ht
  obtain ⟨ha0, ha3, -⟩ := cube_root_facts (show (0 : ℝ) < 3 by norm_num)
  set s := t ^ ((1 : ℝ) / 3)
  set a := (3 : ℝ) ^ ((1 : ℝ) / 3)
  have has : a ≤ s := rpow_le_rpow (by norm_num) h3 (by norm_num)
  have hs2 : s ≤ 2 := le_of_cube_le (by norm_num) (by rw [hs3]; norm_num; exact h8)
  have ha13 : a ≤ 13 / 9 := le_of_cube_le (by norm_num) (by rw [ha3]; norm_num)
  have hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  have hf : ConvexOn ℝ (Ioi 0) (fun x : ℝ => A * x + B * x ^ (-2 : ℤ)) := by
    have := ((convexOn_id (convex_Ioi (0 : ℝ))).smul hA).add ((convexOn_zpow (𝕜 := ℝ) (-2)).smul hB)
    convert this using 1
    ext x
    simp [smul_eq_mul]
  have key := hf.le_max_of_mem_Icc (mem_Ioi.2 ha0) (show (2 : ℝ) ∈ Ioi 0 by norm_num) ⟨has, hs2⟩
  simp only [hz] at key
  have fa : A * a + B * (a ^ 2)⁻¹ ≤ M := by
    have e : A * a + B * (a ^ 2)⁻¹ = a * (A + B / 3) := by rw [← ha3]; field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right ha13 (show 0 ≤ A + B / 3 by positivity)]
  have f2 : A * 2 + B * ((2 : ℝ) ^ 2)⁻¹ ≤ M := by linarith
  have hsM : A * s + B * (s ^ 2)⁻¹ ≤ M := key.trans (max_le fa f2)
  rw [hneg, ← hs3, ← div_eq_mul_inv, le_div_iff₀ hs0]
  have e : (A + B / s ^ 3) * s = A * s + B * (s ^ 2)⁻¹ := by field_simp
  linarith

/-- `c/(t·w) ≤ (c/w₀)/t` for `0 < w₀ ≤ w`, `0 ≤ c`, `0 < t`. -/
theorem div_mul_le {c t w w₀ : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (hw₀ : 0 < w₀) (hw : w₀ ≤ w) :
    c / (t * w) ≤ c / w₀ / t := by
  rw [div_div, mul_comm w₀ t]
  exact div_le_div_of_nonneg_left hc (mul_pos ht hw₀) (mul_le_mul_of_nonneg_left hw ht.le)

/-- `v ≥ 3/2` (P-cap whole): `‖I‖ ≤ 20/(3t)`. -/
theorem case_whole (hW : WholeFacts) {t v : ℝ} (h3 : 3 ≤ t) (h8 : t ≤ 8) (hv : 3 / 2 ≤ v) :
    ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  have h := hW t v ht (by linarith)
  have h1 := div_mul_le (c := 2) (by norm_num) ht (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤ v - 1 by linarith)
  have h2 := div_mul_le (c := 2) (by norm_num) ht (by norm_num : (0 : ℝ) < 3 / 4)
    (show 3 / 4 ≤ v * (v + 1) by nlinarith)
  rw [← mul_assoc] at h2
  have hE := endpoint_bound (A := 0) (B := 20 / 3) (M := 97 / 10) le_rfl (by norm_num) h3 h8
    (by norm_num) (by norm_num)
  have e : (2 : ℝ) / (1 / 2) / t + 2 / (3 / 4) / t = 0 + 20 / 3 / t := by ring
  linarith

/-- `1/2 ≤ v < 3/2` (P-cap high, `δ = 1/2`): `‖I‖ ≤ π + 32/(3t)`. -/
theorem case_cap_high (hCH : CapHighFacts) {t v : ℝ} (h3 : 3 ≤ t) (h8 : t ≤ 8) (hv : 1 / 2 ≤ v)
    (hv' : v < 3 / 2) : ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  have h := hCH t v (1 / 2) ht (by norm_num) hv (by linarith)
  have ha : 0 ≤ arcsin (v - 1 / 2) := arcsin_nonneg.2 (by linarith)
  have h2 := div_mul_le (c := 2) (by norm_num) ht (by norm_num : (0 : ℝ) < 3 / 4)
    (show 3 / 4 ≤ v * (v + 1) by nlinarith)
  rw [← mul_assoc] at h2
  have hE := endpoint_bound (A := 22 / 7) (B := 32 / 3) (M := 97 / 10) (by norm_num) (by norm_num) h3 h8
    (by norm_num) (by norm_num)
  have e : (4 : ℝ) / (t * (1 / 2)) + 2 / (3 / 4) / t = 32 / 3 / t := by field_simp; ring
  linarith [pi_lt_22_7]

/-- `1/4 ≤ v < 1/2` (P-cap low, `δ = 1/2`): `‖I‖ ≤ π + 2/3 + 20/(3t)`. -/
theorem case_cap_low (hCL : CapLowFacts) {t v : ℝ} (h3 : 3 ≤ t) (h8 : t ≤ 8) (hv : 1 / 4 ≤ v)
    (hv' : v < 1 / 2) : ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  have h := hCL t v (1 / 2) ht (by linarith) (by norm_num) hv'.le (by linarith)
  have hneg : arcsin (v - 1 / 2) = -arcsin (1 / 2 - v) := by rw [← arcsin_neg]; ring_nf
  have ha : arcsin (1 / 2 - v) ≤ 1 / 3 :=
    (arcsin_le_arcsin (by linarith : 1 / 2 - v ≤ 1 / 4)).trans (arcsin_le_of_cube (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
  have h2 : 2 / (3 / 2) / t ≤ 2 / (t * (1 + v)) := by
    rw [div_div, mul_comm (3 / 2) t]
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos ht (by linarith))
      (mul_le_mul_of_nonneg_left (by linarith) ht.le)
  have hE := endpoint_bound (A := 22 / 7 + 2 / 3) (B := 20 / 3) (M := 97 / 10) (by norm_num) (by norm_num)
    h3 h8 (by norm_num) (by norm_num)
  have e : (4 : ℝ) / (t * (1 / 2)) - 2 / (3 / 2) / t = 20 / 3 / t := by field_simp; ring
  linarith [pi_lt_22_7]

/-- The band tail: `8/(tδ) − 4/(t(1 − v²)) ≤ 12/t` for `δ = 1/2`, `0 ≤ v < 1`. -/
theorem band_tail {t v : ℝ} (ht : 0 < t) (hv : 0 ≤ v) (hv1 : v < 1) :
    8 / (t * (1 / 2)) - 4 / (t * (1 - v ^ 2)) ≤ 12 / t := by
  have h : 4 / t ≤ 4 / (t * (1 - v ^ 2)) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos ht (by nlinarith))
      (mul_le_of_le_one_right ht.le (by nlinarith))
  have e : (8 : ℝ) / (t * (1 / 2)) = 16 / t := by field_simp; ring
  have e' : (16 : ℝ) / t - 4 / t = 12 / t := by ring
  linarith

/-- `1/8 ≤ v < 1/4` (P-band low, `δ = 1/2`): `‖I‖ ≤ 2(6/7 + 2/5) + 12/t`. -/
theorem case_band_mid (hBL : BandLowFacts) {t v : ℝ} (h3 : 3 ≤ t) (h8 : t ≤ 8) (hv : 1 / 8 ≤ v)
    (hv' : v < 1 / 4) : ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  have h := hBL t v (1 / 2) ht (by linarith) (by norm_num) (by linarith) (by linarith)
  have hneg : arcsin (v - 1 / 2) = -arcsin (1 / 2 - v) := by rw [← arcsin_neg]; ring_nf
  have ha : arcsin (v + 1 / 2) ≤ 6 / 7 :=
    (arcsin_le_arcsin (by linarith : v + 1 / 2 ≤ 3 / 4)).trans (arcsin_le_of_cube (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
  have hb : arcsin (1 / 2 - v) ≤ 2 / 5 :=
    (arcsin_le_arcsin (by linarith : 1 / 2 - v ≤ 3 / 8)).trans (arcsin_le_of_cube (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
  have hT := band_tail ht (by linarith) (by linarith : v < 1)
  have hE := endpoint_bound (A := 2 * (6 / 7 + 2 / 5)) (B := 12) (M := 97 / 10) (by norm_num) (by norm_num)
    h3 h8 (by norm_num) (by norm_num)
  linarith

/-- `0 ≤ v < 1/8` (P-band low, `δ = 1/2`): `‖I‖ ≤ 2(17/25 + π/6) + 12/t`. -/
theorem case_band_low (hBL : BandLowFacts) {t v : ℝ} (h3 : 3 ≤ t) (h8 : t ≤ 8) (hv : 0 ≤ v)
    (hv' : v < 1 / 8) : ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) := by
  have ht : 0 < t := by linarith
  have h := hBL t v (1 / 2) ht hv (by norm_num) (by linarith) (by linarith)
  have hneg : arcsin (v - 1 / 2) = -arcsin (1 / 2 - v) := by rw [← arcsin_neg]; ring_nf
  have ha : arcsin (v + 1 / 2) ≤ 17 / 25 :=
    (arcsin_le_arcsin (by linarith : v + 1 / 2 ≤ 5 / 8)).trans (arcsin_le_of_cube (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
  have hb : arcsin (1 / 2 - v) ≤ π / 6 := arcsin_half ▸ arcsin_le_arcsin (by linarith)
  have hT := band_tail ht hv (by linarith : v < 1)
  have hE := endpoint_bound (A := 2 * (17 / 25 + 11 / 21)) (B := 12) (M := 97 / 10) (by norm_num) (by norm_num)
    h3 h8 (by norm_num) (by norm_num)
  linarith [pi_lt_22_7]

/-- **P-r38 from the pieces.** -/
theorem regime38_of (hBL : BandLowFacts) (hCL : CapLowFacts) (hCH : CapHighFacts) (hW : WholeFacts) :
    Regime38Facts := by
  intro t v h3 h8 hv
  have hs : (211 / 80 : ℝ) ≤ sqrt 7 := by rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (97 / 10 : ℝ) ≤ 8 * (1 + sqrt 7) / 3 := by linarith
  have hpos : 0 ≤ t ^ (-(1 : ℝ) / 3) := (rpow_pos_of_pos (by linarith) _).le
  suffices h : ‖latticeKernel1 t (t * v)‖ ≤ 97 / 10 * t ^ (-(1 : ℝ) / 3) from
    h.trans (mul_le_mul_of_nonneg_right hC hpos)
  rcases le_or_gt (1 / 2) v with hv2 | hv2
  · rcases le_or_gt (3 / 2) v with hv3 | hv3
    · exact case_whole hW h3 h8 hv3
    · exact case_cap_high hCH h3 h8 hv2 hv3
  · rcases le_or_gt (1 / 4) v with hv4 | hv4
    · exact case_cap_low hCL h3 h8 hv4 hv2
    · rcases le_or_gt (1 / 8) v with hv8 | hv8
      · exact case_band_mid hBL h3 h8 hv8 hv4
      · exact case_band_low hBL h3 h8 hv hv8

end OscInt.LatticeCubeRootAux.R38
