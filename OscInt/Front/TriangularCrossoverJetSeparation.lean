/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# Batch A5U, part A6: `JetSeparationFacts`

Route: `docs/proof-A5U.md`, section 3 (packet X2), in a direct form. Put `s = √ε`, `v = |u|`,
`p₄ = B + D u²/2`, `p₃ = B u + D u³/6`, `p₂ = A + B u²/2 + D u⁴/24`, and suppose all three alternatives fail:
`|g₂| ≤ η s⁴`, `|g₃| ≤ η s³`, `|g₄| ≤ η s²`. Then `|p₄| ≤ η s² + L v⁴`, `|p₃| ≤ η s³ + L v⁵`,
`|p₂| ≤ η s⁴ + L v⁶`. Constants: `c = min(1, c_B/(2 d_max))`, `η = min(c_B/8, d_min c³/24)` and, for given `L`,
`δ = min(1, (c_B/16)/(L+1), (d_min/24)/(L+1), (c_B/16)/(K(c_B + d_max)+1))`.
* From `D u³/3 = u p₄ − p₃`: `d_min v³/3 ≤ η(v s² + s³) + 2 L v⁵`.
* If `v ≥ c s`: `η(v s² + s³) ≤ d_min v³/12` and `2 L v⁵ ≤ d_min v³/12`, impossible for `v > 0`.
* If `v < c s`: `|B| ≤ |p₄| + |D| v²/2 ≤ (7/16) c_B s²` and `|A| ≤ (c_B + d_max) s⁴`, so `K |A| ≤ c_B s²/16`,
  against `c_B s² − K|A| ≤ |B|`.
The hypothesis `|A| ≤ δ⁴` is not needed.
-/

namespace OscInt.A5UAux

/-- `|p| ≤ e + r` from `|g − p| ≤ r` and `|g| ≤ e`. -/
theorem a5uG2_abs_tri {p g r e : ℝ} (h1 : |g - p| ≤ r) (h2 : |g| ≤ e) : |p| ≤ e + r := by
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The case `v ≥ c s` is impossible. -/
theorem a5uG2_sep_case1 {dmin η c L δ s v d : ℝ} (hdmin : 0 < dmin) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hη2 : η ≤ dmin * c ^ 3 / 24) (hL : 0 ≤ L) (hLδ : L * δ ^ 2 ≤ dmin / 24) (hs : 0 < s)
    (hv : c * s ≤ v) (hvδ : v ≤ δ) (hD : dmin ≤ d)
    (hI : d * v ^ 3 / 3 ≤ v * (η * s ^ 2 + L * v ^ 4) + η * (s ^ 2 * s) + L * v ^ 5) : False := by
  have hcs : 0 < c * s := mul_pos hc0 hs
  have hv0 : 0 < v := lt_of_lt_of_le hcs hv
  have hη0 : 0 ≤ v * s ^ 2 + s ^ 2 * s := by positivity
  have k0 : (c * s) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hcs.le hv 2
  have k1 : c ^ 3 * (v * s ^ 2) ≤ v ^ 3 := by
    have : c * v * (c * s) ^ 2 ≤ v * v ^ 2 :=
      mul_le_mul (mul_le_of_le_one_left hv0.le hc1) k0 (by positivity) hv0.le
    nlinarith [this]
  have k2 : c ^ 3 * (s ^ 2 * s) ≤ v ^ 3 := by
    have := pow_le_pow_left₀ hcs.le hv 3
    nlinarith [this]
  have k3 : η * (v * s ^ 2 + s ^ 2 * s) ≤ dmin * v ^ 3 / 12 := by
    calc η * (v * s ^ 2 + s ^ 2 * s) ≤ dmin * c ^ 3 / 24 * (v * s ^ 2 + s ^ 2 * s) :=
          mul_le_mul_of_nonneg_right hη2 hη0
      _ = dmin / 24 * (c ^ 3 * (v * s ^ 2) + c ^ 3 * (s ^ 2 * s)) := by ring
      _ ≤ dmin / 24 * (v ^ 3 + v ^ 3) := mul_le_mul_of_nonneg_left (add_le_add k1 k2) (by positivity)
      _ = dmin * v ^ 3 / 12 := by ring
  have k4 : 2 * L * v ^ 5 ≤ dmin * v ^ 3 / 12 := by
    have hv2 : v ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hv0.le hvδ 2
    have : L * v ^ 2 ≤ dmin / 24 := (mul_le_mul_of_nonneg_left hv2 hL).trans hLδ
    nlinarith [pow_pos hv0 3]
  have k5 : dmin * v ^ 3 ≤ d * v ^ 3 := mul_le_mul_of_nonneg_right hD (by positivity)
  nlinarith [pow_pos hv0 3]

/-- The case `v < c s` is impossible. -/
theorem a5uG2_sep_case2 {cB K dmax η c L δ s v a b d P2 P4 : ℝ} (hcB : 0 < cB) (hK : 0 ≤ K) (hc1 : c ≤ 1)
    (hcD : dmax * c ^ 2 ≤ cB / 2) (hη1 : η ≤ cB / 8) (hL : 0 ≤ L) (hLδ : L * δ ^ 2 ≤ cB / 16)
    (hKδ : K * (cB + dmax) * δ ^ 2 ≤ cB / 16) (hs : 0 < s) (hsδ : s ≤ δ) (hv0 : 0 ≤ v) (hv : v < c * s)
    (hd0 : 0 ≤ d) (hd : d ≤ dmax) (ha0 : 0 ≤ a)
    (hP4 : P4 ≤ η * s ^ 2 + L * v ^ 4) (hP2 : P2 ≤ η * s ^ 4 + L * v ^ 6)
    (hB : b ≤ P4 + d * v ^ 2 / 2) (hA : a ≤ P2 + b * v ^ 2 / 2 + d * v ^ 4 / 24)
    (hcon : cB * s ^ 2 - K * a ≤ b) : False := by
  have hvs : v ≤ s := hv.le.trans (mul_le_of_le_one_left hs.le hc1)
  have hv2 : v ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ hv0 hv.le 2
  have hs2 : s ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hs.le hsδ 2
  have hdmax : 0 ≤ dmax := hd0.trans hd
  have e1 : d * v ^ 2 ≤ cB / 2 * s ^ 2 := by
    calc d * v ^ 2 ≤ dmax * (c * s) ^ 2 := mul_le_mul hd hv2 (by positivity) hdmax
      _ = dmax * c ^ 2 * s ^ 2 := by ring
      _ ≤ cB / 2 * s ^ 2 := mul_le_mul_of_nonneg_right hcD (by positivity)
  have e2 : L * v ^ 4 ≤ cB / 16 * s ^ 2 := by
    have h4 : v ^ 4 ≤ s ^ 2 * s ^ 2 := by rw [← pow_add]; exact pow_le_pow_left₀ hv0 hvs 4
    have : L * s ^ 2 ≤ cB / 16 := (mul_le_mul_of_nonneg_left hs2 hL).trans hLδ
    nlinarith [mul_le_mul_of_nonneg_left h4 hL, pow_pos hs 2]
  have e3 : η * s ^ 2 ≤ cB / 8 * s ^ 2 := mul_le_mul_of_nonneg_right hη1 (by positivity)
  have hb : b ≤ 7 * cB / 16 * s ^ 2 := by linarith
  have f1 : L * v ^ 6 ≤ cB / 16 * s ^ 4 := by
    have h6 : v ^ 6 ≤ s ^ 2 * s ^ 4 := by rw [← pow_add]; exact pow_le_pow_left₀ hv0 hvs 6
    have : L * s ^ 2 ≤ cB / 16 := (mul_le_mul_of_nonneg_left hs2 hL).trans hLδ
    nlinarith [mul_le_mul_of_nonneg_left h6 hL, pow_pos hs 4]
  have f2 : b * v ^ 2 ≤ 7 * cB / 16 * s ^ 2 * s ^ 2 :=
    mul_le_mul hb (pow_le_pow_left₀ hv0 hvs 2) (by positivity) (by positivity)
  have f3 : d * v ^ 4 ≤ dmax * s ^ 4 := mul_le_mul hd (pow_le_pow_left₀ hv0 hvs 4) (by positivity) hdmax
  have f4 : η * s ^ 4 ≤ cB / 8 * s ^ 4 := mul_le_mul_of_nonneg_right hη1 (by positivity)
  have ha : a ≤ (cB + dmax) * s ^ 4 := by nlinarith
  have g1 : K * a ≤ cB / 16 * s ^ 2 := by
    calc K * a ≤ K * ((cB + dmax) * s ^ 4) := mul_le_mul_of_nonneg_left ha hK
      _ = K * (cB + dmax) * s ^ 2 * s ^ 2 := by ring
      _ ≤ K * (cB + dmax) * δ ^ 2 * s ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity)) (by positivity)
      _ ≤ cB / 16 * s ^ 2 := mul_le_mul_of_nonneg_right hKδ (by positivity)
  nlinarith [pow_pos hs 2]

/-- `|x − y| ≤ |x| + |y|`. -/
theorem a5uG2_abs_sub_le (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

/-- `|D| |u|³/3 ≤ |u| |p₄| + |p₃|` from `D u³/3 = u p₄ − p₃`. -/
theorem a5uG2_cubic_id (B D u : ℝ) :
    |D| * |u| ^ 3 / 3 ≤ |u| * |B + D * u ^ 2 / 2| + |B * u + D * u ^ 3 / 6| := by
  have h := a5uG2_abs_sub_le (u * (B + D * u ^ 2 / 2)) (B * u + D * u ^ 3 / 6)
  rw [show u * (B + D * u ^ 2 / 2) - (B * u + D * u ^ 3 / 6) = D * u ^ 3 / 3 by ring, abs_mul] at h
  rwa [abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h

/-- The separation, for constants satisfying the inequalities of the choice. -/
theorem a5uG2_sep_core {cB K dmin dmax η c L δ : ℝ} (hcB : 0 < cB) (hK : 0 ≤ K) (hdmin : 0 < dmin)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hcD : dmax * c ^ 2 ≤ cB / 2) (hη1 : η ≤ cB / 8)
    (hη2 : η ≤ dmin * c ^ 3 / 24) (hL : 0 ≤ L) (hδ0 : 0 < δ) (hLδ1 : L * δ ^ 2 ≤ cB / 16)
    (hLδ2 : L * δ ^ 2 ≤ dmin / 24) (hKδ : K * (cB + dmax) * δ ^ 2 ≤ cB / 16)
    (ε A B D u g₂ g₃ g₄ : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ ^ 2) (hu : |u| ≤ δ) (hD1 : dmin ≤ |D|)
    (hD2 : |D| ≤ dmax) (hcon : cB * ε - K * |A| ≤ |B|)
    (h2 : |g₂ - (A + B * u ^ 2 / 2 + D * u ^ 4 / 24)| ≤ L * u ^ 6)
    (h3 : |g₃ - (B * u + D * u ^ 3 / 6)| ≤ L * |u| ^ 5) (h4 : |g₄ - (B + D * u ^ 2 / 2)| ≤ L * u ^ 4) :
    η * ε ^ 2 < |g₂| ∨ η * (ε * √ε) < |g₃| ∨ η * ε < |g₄| := by
  by_contra hneg
  simp only [not_or, not_lt] at hneg
  obtain ⟨k2, k3, k4⟩ := hneg
  have hs : 0 < √ε := Real.sqrt_pos.2 hε
  have hss : √ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hsδ : √ε ≤ δ := by
    have := Real.sqrt_le_sqrt hεδ
    rwa [Real.sqrt_sq hδ0.le] at this
  have hv2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have hv4 : u ^ 4 = |u| ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  have hv6 : u ^ 6 = |u| ^ 6 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  rw [← hss] at k2 k3 k4 hcon
  rw [Real.sqrt_sq hs.le] at k3
  have p4 := a5uG2_abs_tri h4 k4
  have p3 := a5uG2_abs_tri h3 k3
  have p2 := a5uG2_abs_tri h2 k2
  rw [hv4] at p4
  rw [hv6] at p2
  have hI : |D| * |u| ^ 3 / 3 ≤ |u| * (η * √ε ^ 2 + L * |u| ^ 4) + η * (√ε ^ 2 * √ε) + L * |u| ^ 5 := by
    have := a5uG2_cubic_id B D u
    nlinarith [mul_le_mul_of_nonneg_left p4 (abs_nonneg u)]
  rcases le_or_gt (c * √ε) |u| with h | h
  · exact a5uG2_sep_case1 hdmin hc0 hc1 hη2 hL hLδ2 hs h hu hD1 hI
  · have hB : |B| ≤ |B + D * u ^ 2 / 2| + |D| * |u| ^ 2 / 2 := by
      have := a5uG2_abs_sub_le (B + D * u ^ 2 / 2) (D * u ^ 2 / 2)
      have e : |D * u ^ 2 / 2| = |D| * |u| ^ 2 / 2 := by
        rw [abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rwa [add_sub_cancel_right, e] at this
    have hA : |A| ≤ |A + B * u ^ 2 / 2 + D * u ^ 4 / 24| + |B| * |u| ^ 2 / 2 + |D| * |u| ^ 4 / 24 := by
      have h1 := a5uG2_abs_sub_le (A + B * u ^ 2 / 2 + D * u ^ 4 / 24) (B * u ^ 2 / 2 + D * u ^ 4 / 24)
      have h2 := a5uG2_abs_sub_le (B * u ^ 2 / 2) (-(D * u ^ 4 / 24))
      rw [show A + B * u ^ 2 / 2 + D * u ^ 4 / 24 - (B * u ^ 2 / 2 + D * u ^ 4 / 24) = A by ring] at h1
      rw [sub_neg_eq_add, abs_neg, abs_div, abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 24)] at h2
      linarith
    exact a5uG2_sep_case2 hcB hK hc1 hcD hη1 hL hLδ1 hKδ hs hsδ (abs_nonneg u) h (abs_nonneg D) hD2
      (abs_nonneg A) p4 (by rw [show √ε ^ 4 = (√ε ^ 2) ^ 2 by ring]; exact p2) hB hA hcon

/-- `x z ≤ y` from `z ≤ y / (x + 1)`, `x, y ≥ 0`. -/
theorem a5uG2_mul_le_of_le_div {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≤ y / (x + 1)) : x * z ≤ y := by
  calc x * z ≤ x * (y / (x + 1)) := mul_le_mul_of_nonneg_left hz hx
    _ ≤ y := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith

/-- **A6** `JetSeparationFacts`. -/
theorem jetSeparation : OscInt.Blueprint.A5U.JetSeparationFacts := by
  intro cB K dmin dmax hcB hK hdmin hdd
  have hdmax : 0 < dmax := lt_of_lt_of_le hdmin hdd
  set c := min 1 (cB / (2 * dmax)) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcD : dmax * c ^ 2 ≤ cB / 2 := by
    have h1 : c ^ 2 ≤ c := by nlinarith
    have h2 : dmax * c ≤ cB / 2 := by
      calc dmax * c ≤ dmax * (cB / (2 * dmax)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hdmax.le
        _ = cB / 2 := by field_simp
    nlinarith
  refine ⟨min (cB / 8) (dmin * c ^ 3 / 24), lt_min (by positivity) (by positivity), fun L hL => ?_⟩
  have hτ : 0 < min (min (cB / 16 / (L + 1)) (dmin / 24 / (L + 1))) (cB / 16 / (K * (cB + dmax) + 1)) :=
    lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨min 1 (min (min (cB / 16 / (L + 1)) (dmin / 24 / (L + 1))) (cB / 16 / (K * (cB + dmax) + 1))),
    lt_min one_pos hτ, min_le_left _ _, ?_⟩
  set δ := min 1 (min (min (cB / 16 / (L + 1)) (dmin / 24 / (L + 1))) (cB / 16 / (K * (cB + dmax) + 1)))
  have hδ0 : 0 < δ := lt_min one_pos hτ
  have hδ2 : δ ^ 2 ≤ min (min (cB / 16 / (L + 1)) (dmin / 24 / (L + 1))) (cB / 16 / (K * (cB + dmax) + 1)) := by
    have : δ ^ 2 ≤ δ := by nlinarith [min_le_left 1 (min (min (cB / 16 / (L + 1)) (dmin / 24 / (L + 1)))
      (cB / 16 / (K * (cB + dmax) + 1)))]
    exact this.trans (min_le_right _ _)
  have hLδ1 := a5uG2_mul_le_of_le_div hL (by positivity) (hδ2.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hLδ2 := a5uG2_mul_le_of_le_div hL (by positivity) (hδ2.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hKδ := a5uG2_mul_le_of_le_div (by positivity) (by positivity) (hδ2.trans (min_le_right _ _))
  intro ε A B D u g₂ g₃ g₄ hε hεδ _ hu hD1 hD2 hcon h2 h3 h4
  exact a5uG2_sep_core hcB hK hdmin hc0 hc1 hcD (min_le_left _ _) (min_le_right _ _) hL hδ0 hLδ1 hLδ2
    (by simpa only [mul_assoc] using hKδ) ε A B D u g₂ g₃ g₄ hε hεδ hu hD1 hD2 hcon h2 h3 h4

end OscInt.A5UAux
