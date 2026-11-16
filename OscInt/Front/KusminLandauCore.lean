/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.KusminLandau
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Batch KL, part K-core: Landau's inequality on differences with `k = 0` (route `docs/proof-KL.md`)

Summation by parts with the weights `ζ(x) = 1/(e(x) − 1) = −1/2 − (cot(πx)/2)·i`, written with `cos/sin`
throughout. The weight is defined by its closed form and `ζ(x)·(e(x) − 1) = 1` is checked on real and imaginary
parts; the summation by parts is an induction stated for `N + 1`.
-/

namespace OscInt.KusminLandauAux

open OscInt.Statements OscInt.Blueprint.KusminLandau

/-- The cotangent `cot(πx)`, written `cos(πx)/sin(πx)`. -/
noncomputable def klCore_q (x : ℝ) : ℝ := Real.cos (Real.pi * x) / Real.sin (Real.pi * x)

/-- The weight `ζ(x) = 1/(e(x) − 1)` in closed form, `−1/2 − (cot(πx)/2)·i`. -/
noncomputable def klCore_zeta (x : ℝ) : ℂ := -(1 / 2 : ℂ) - ((klCore_q x / 2 : ℝ) : ℂ) * Complex.I

/-- `sin(πx) > 0` for `0 < x < 1`. -/
theorem klCore_sin_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < Real.sin (Real.pi * x) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])

/-- The weight identity `ζ(x)·(e(x) − 1) = 1` when `sin(πx) ≠ 0`. -/
theorem klCore_zeta_mul (x : ℝ) (hs : Real.sin (Real.pi * x) ≠ 0) :
    klCore_zeta x * (Complex.exp (↑(2 * Real.pi * x) * Complex.I) - 1) = 1 := by
  have h2 : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
  have hss := Real.sin_sq_add_cos_sq (Real.pi * x)
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h2, Real.cos_two_mul, Real.sin_two_mul]
  apply Complex.ext
  · simp only [klCore_zeta, klCore_q, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    field_simp
    nlinarith
  · simp only [klCore_zeta, klCore_q, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    field_simp
    linear_combination (-2 * Real.cos (Real.pi * x)) * hss

/-- `‖ζ(x)‖ = 1/(2 sin πx)` when `sin(πx) > 0`. -/
theorem klCore_norm_zeta (x : ℝ) (hs : 0 < Real.sin (Real.pi * x)) :
    ‖klCore_zeta x‖ = 1 / (2 * Real.sin (Real.pi * x)) := by
  have hss := Real.sin_sq_add_cos_sq (Real.pi * x)
  have h : ‖klCore_zeta x‖ ^ 2 = (1 / (2 * Real.sin (Real.pi * x))) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [klCore_zeta, klCore_q, Complex.mul_re, Complex.sub_re, Complex.neg_re,
      Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    field_simp
    nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- `‖1 + ζ(x)‖ = 1/(2 sin πx)` when `sin(πx) > 0`. -/
theorem klCore_norm_one_add_zeta (x : ℝ) (hs : 0 < Real.sin (Real.pi * x)) :
    ‖1 + klCore_zeta x‖ = 1 / (2 * Real.sin (Real.pi * x)) := by
  have hss := Real.sin_sq_add_cos_sq (Real.pi * x)
  have h : ‖1 + klCore_zeta x‖ ^ 2 = (1 / (2 * Real.sin (Real.pi * x))) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [klCore_zeta, klCore_q, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.add_re,
      Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    field_simp
    nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- `‖ζ(x) − ζ(y)‖ = |cot πx − cot πy|/2`. -/
theorem klCore_norm_zeta_sub (x y : ℝ) :
    ‖klCore_zeta x - klCore_zeta y‖ = |klCore_q x - klCore_q y| / 2 := by
  have h : klCore_zeta x - klCore_zeta y = (((klCore_q y - klCore_q x) / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [klCore_zeta]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_sub_comm]
  norm_num

/-- `cot(π·)` is nonincreasing on `(0, 1)`. -/
theorem klCore_q_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : klCore_q y ≤ klCore_q x := by
  have hsx := klCore_sin_pos hx (lt_of_le_of_lt hxy hy)
  have hsy := klCore_sin_pos (lt_of_lt_of_le hx hxy) hy
  have hd : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  unfold klCore_q
  rw [div_le_div_iff₀ hsy hsx]
  linarith

/-- The half-angle comparison `(1 + cos πx)/sin πx = cot(πx/2) ≤ cot(πλ/2)` for `λ ≤ x < 1`. -/
theorem klCore_half_plus {lam x : ℝ} (hl : 0 < lam) (hx : lam ≤ x) (hx1 : x < 1) :
    (1 + Real.cos (Real.pi * x)) / Real.sin (Real.pi * x) ≤
      Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) := by
  have hpi := Real.pi_pos
  have hsx := klCore_sin_pos (lt_of_lt_of_le hl hx) hx1
  have hsa : 0 < Real.sin (Real.pi * lam / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hch : 0 ≤ Real.cos (Real.pi * x / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hd : 0 ≤ Real.sin (Real.pi * x / 2 - Real.pi * lam / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  rw [Real.sin_sub] at hd
  have h2 : Real.pi * x = 2 * (Real.pi * x / 2) := by ring
  rw [div_le_div_iff₀ hsx hsa, h2, Real.cos_two_mul, Real.sin_two_mul]
  nlinarith [mul_nonneg hch hd]

/-- The half-angle comparison `(1 − cos πx)/sin πx = tan(πx/2) ≤ cot(πλ/2)` for `0 < x ≤ 1 − λ`. -/
theorem klCore_half_minus {lam x : ℝ} (hl : 0 < lam) (hx0 : 0 < x) (hx : x ≤ 1 - lam) :
    (1 - Real.cos (Real.pi * x)) / Real.sin (Real.pi * x) ≤
      Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) := by
  have h := klCore_half_plus (x := 1 - x) hl (by linarith) (by linarith)
  have e : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
  rw [e, Real.cos_pi_sub, Real.sin_pi_sub] at h
  exact h

/-- Summation by parts: if `E n = z n * (E (n + 1) − E n)` for `n ≤ N`, the sum of `E 0, …, E (N + 1)` is
`(1 + z N) E (N + 1) − z 0 E 0 − Σ_{n < N} (z (n + 1) − z n) E (n + 1)`. -/
theorem klCore_sbp (z E : ℕ → ℂ) (N : ℕ) (h : ∀ n < N + 1, E n = z n * (E (n + 1) - E n)) :
    ∑ n ∈ Finset.range (N + 2), E n =
      (1 + z N) * E (N + 1) - z 0 * E 0 - ∑ n ∈ Finset.range N, (z (n + 1) - z n) * E (n + 1) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
    linear_combination h 0 (by norm_num)
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun n hn => h n (by omega)), Finset.sum_range_succ]
    linear_combination h (N + 1) (by omega)

/-- The terms satisfy `E n = ζ(d n) (E (n + 1) − E n)` with `d n = c (n + 1) − c n`, when `sin(π d n) ≠ 0`. -/
theorem klCore_term (c : ℕ → ℝ) (n : ℕ) (hs : Real.sin (Real.pi * (c (n + 1) - c n)) ≠ 0) :
    Complex.exp (↑(2 * Real.pi * c n) * Complex.I) = klCore_zeta (c (n + 1) - c n) *
      (Complex.exp (↑(2 * Real.pi * c (n + 1)) * Complex.I) - Complex.exp (↑(2 * Real.pi * c n) * Complex.I)) := by
  have e : Complex.exp (↑(2 * Real.pi * c (n + 1)) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * c n) * Complex.I) *
        Complex.exp (↑(2 * Real.pi * (c (n + 1) - c n)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  linear_combination (-Complex.exp (↑(2 * Real.pi * c n) * Complex.I)) * klCore_zeta_mul _ hs

/-- The bound after summation by parts: two end weights and the variation of `cot(π d_n)`. -/
theorem klCore_abel_bound (c : ℕ → ℝ) (M : ℕ)
    (hd : ∀ n < M + 1, 0 < c (n + 1) - c n ∧ c (n + 1) - c n < 1) :
    ‖expSum c (M + 1)‖ ≤ 1 / (2 * Real.sin (Real.pi * (c (M + 1) - c M))) +
      1 / (2 * Real.sin (Real.pi * (c 1 - c 0))) +
      ∑ n ∈ Finset.range M, |klCore_q (c (n + 2) - c (n + 1)) - klCore_q (c (n + 1) - c n)| / 2 := by
  have hE : ∀ n : ℕ, ‖Complex.exp (↑(2 * Real.pi * c n) * Complex.I)‖ = 1 := fun n =>
    Complex.norm_exp_ofReal_mul_I _
  have hsbp := klCore_sbp (fun n => klCore_zeta (c (n + 1) - c n))
    (fun n => Complex.exp (↑(2 * Real.pi * c n) * Complex.I)) M
    (fun n hn => klCore_term c n (klCore_sin_pos (hd n hn).1 (hd n hn).2).ne')
  have hM := hd M (Nat.lt_succ_self M)
  have h0 := hd 0 (Nat.succ_pos M)
  unfold expSum
  rw [hsbp]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul, hE, mul_one, klCore_norm_one_add_zeta _ (klCore_sin_pos hM.1 hM.2)]
  · rw [norm_mul, hE, mul_one, klCore_norm_zeta _ (klCore_sin_pos h0.1 h0.2)]
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, hE, mul_one, klCore_norm_zeta_sub]

/-- `1 ≤ cot(πλ/2)` for `0 < λ ≤ 1/2`. -/
theorem klCore_one_le {lam : ℝ} (hl : 0 < lam) (hl2 : lam ≤ 1 / 2) :
    1 ≤ Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) := by
  have h := klCore_half_plus (x := 1 / 2) hl hl2 (by norm_num)
  have e : Real.pi * (1 / 2) = Real.pi / 2 := by ring
  rw [e, Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  simpa using h

/-- **K-core** Landau's inequality on differences with `k = 0`. -/
theorem klCoreFacts : KLCoreFacts := by
  intro c N lam hl hl2 hD
  obtain ⟨hmono, hrange⟩ := hD
  have hr : ∀ n < N, lam ≤ c (n + 1) - c n ∧ c (n + 1) - c n ≤ 1 - lam := fun n hn => by
    have := hrange n hn
    rw [Int.cast_zero, zero_add, zero_add] at this
    exact this
  rcases N with _ | M
  · have h1 : expSum c 0 = Complex.exp (↑(2 * Real.pi * c 0) * Complex.I) := by
      unfold expSum
      rw [zero_add, Finset.sum_range_one]
    rw [h1, Complex.norm_exp_ofReal_mul_I]
    exact klCore_one_le hl hl2
  · have hpos : ∀ n < M + 1, 0 < c (n + 1) - c n ∧ c (n + 1) - c n < 1 := fun n hn =>
      ⟨lt_of_lt_of_le hl (hr n hn).1, by linarith [(hr n hn).2]⟩
    have hM := hr M (Nat.lt_succ_self M)
    have h0 := hr 0 (Nat.succ_pos M)
    have hsM := klCore_sin_pos (hpos M (Nat.lt_succ_self M)).1 (hpos M (Nat.lt_succ_self M)).2
    have hs0 := klCore_sin_pos (hpos 0 (Nat.succ_pos M)).1 (hpos 0 (Nat.succ_pos M)).2
    refine (klCore_abel_bound c M hpos).trans ?_
    rcases hmono with hinc | hdec
    · have hsum : ∑ n ∈ Finset.range M, |klCore_q (c (n + 2) - c (n + 1)) - klCore_q (c (n + 1) - c n)| / 2 =
          (klCore_q (c 1 - c 0) - klCore_q (c (M + 1) - c M)) / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_range_sub' (fun n => klCore_q (c (n + 1) - c n)) M]
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' : n + 1 < M + 1 := Nat.succ_lt_succ (Finset.mem_range.1 hn)
        rw [abs_of_nonpos (sub_nonpos.2 (klCore_q_anti (hpos n (by omega)).1 (hinc n hn')
          (hpos (n + 1) hn').2))]
        ring
      have hA := klCore_half_plus hl h0.1 (hpos 0 (Nat.succ_pos M)).2
      have hB := klCore_half_minus hl (hpos M (Nat.lt_succ_self M)).1 hM.2
      rw [hsum]
      have e : 1 / (2 * Real.sin (Real.pi * (c (M + 1) - c M))) + 1 / (2 * Real.sin (Real.pi * (c 1 - c 0))) +
          (klCore_q (c 1 - c 0) - klCore_q (c (M + 1) - c M)) / 2 =
          ((1 + Real.cos (Real.pi * (c 1 - c 0))) / Real.sin (Real.pi * (c 1 - c 0)) +
            (1 - Real.cos (Real.pi * (c (M + 1) - c M))) / Real.sin (Real.pi * (c (M + 1) - c M))) / 2 := by
        unfold klCore_q
        field_simp
        ring
      rw [e]
      linarith
    · have hsum : ∑ n ∈ Finset.range M, |klCore_q (c (n + 2) - c (n + 1)) - klCore_q (c (n + 1) - c n)| / 2 =
          (klCore_q (c (M + 1) - c M) - klCore_q (c 1 - c 0)) / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_range_sub (fun n => klCore_q (c (n + 1) - c n)) M]
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' : n + 1 < M + 1 := Nat.succ_lt_succ (Finset.mem_range.1 hn)
        rw [abs_of_nonneg (sub_nonneg.2 (klCore_q_anti (hpos (n + 1) hn').1 (hdec n hn')
          (hpos n (by omega)).2))]
      have hA := klCore_half_plus hl hM.1 (hpos M (Nat.lt_succ_self M)).2
      have hB := klCore_half_minus hl (hpos 0 (Nat.succ_pos M)).1 h0.2
      rw [hsum]
      have e : 1 / (2 * Real.sin (Real.pi * (c (M + 1) - c M))) + 1 / (2 * Real.sin (Real.pi * (c 1 - c 0))) +
          (klCore_q (c (M + 1) - c M) - klCore_q (c 1 - c 0)) / 2 =
          ((1 + Real.cos (Real.pi * (c (M + 1) - c M))) / Real.sin (Real.pi * (c (M + 1) - c M)) +
            (1 - Real.cos (Real.pi * (c 1 - c 0))) / Real.sin (Real.pi * (c 1 - c 0))) / 2 := by
        unfold klCore_q
        field_simp
        ring
      rw [e]
      linarith

end OscInt.KusminLandauAux
