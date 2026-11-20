/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing

/-!
# Batch FR, part F-images: the bound for a sum over the images `r + mN`, `m ≠ 0` (route `docs/proof-FR.md`)

A statement about series with no kernel in it. The term at `m = 0` is removed from the `HasSum`; the terms with
`m ≥ 1` are dominated by `A e^{−rη} q^m` and those with `m ≤ −1` by `A e^{rη} q^{|m|}`, `q = e^{−ηN}`; the two
geometric series add up to `2A cosh(rη) / (e^{ηN} − 1)`.
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

/-- The two-sided geometric majorant with constants `P` (for `m ≥ 1`) and `Q` (for `m ≤ −1`) and no term at `0`. -/
theorem imageSum_hasSum_majorant (P Q : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℤ => if m = 0 then (0 : ℝ) else if 0 < m then P * q ^ m.natAbs else Q * q ^ m.natAbs)
      ((P + Q) * (q * (1 - q)⁻¹)) := by
  have hgeoP : HasSum (fun n : ℕ => P * q * q ^ n) (P * q * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (P * q)
  have hgeoQ : HasSum (fun n : ℕ => Q * q * q ^ n) (Q * q * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Q * q)
  have hpos : HasSum (fun n : ℕ => if ((n : ℤ) + 1) = 0 then (0 : ℝ) else
      if 0 < ((n : ℤ) + 1) then P * q ^ ((n : ℤ) + 1).natAbs else Q * q ^ ((n : ℤ) + 1).natAbs)
      (P * q * (1 - q)⁻¹) := by
    refine hgeoP.congr_fun fun n => ?_
    have h0 : ((n : ℤ) + 1) ≠ 0 := by omega
    have h2 : 0 < ((n : ℤ) + 1) := by omega
    have h1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [h0, h2, ↓reduceIte, h1, pow_succ]
    ring
  have hneg : HasSum (fun n : ℕ => if (-((n : ℤ) + 1)) = 0 then (0 : ℝ) else
      if 0 < (-((n : ℤ) + 1)) then P * q ^ (-((n : ℤ) + 1)).natAbs else Q * q ^ (-((n : ℤ) + 1)).natAbs)
      (Q * q * (1 - q)⁻¹) := by
    refine hgeoQ.congr_fun fun n => ?_
    have h0 : (-((n : ℤ) + 1)) ≠ 0 := by omega
    have h2 : ¬ 0 < (-((n : ℤ) + 1)) := by omega
    have h1 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [h0, h2, ↓reduceIte, h1, pow_succ]
    ring
  have h := HasSum.of_add_one_of_neg_add_one
    (f := fun m : ℤ => if m = 0 then (0 : ℝ) else if 0 < m then P * q ^ m.natAbs else Q * q ^ m.natAbs) hpos hneg
  simp only [↓reduceIte, add_zero] at h
  have hval : (P + Q) * (q * (1 - q)⁻¹) = P * q * (1 - q)⁻¹ + Q * q * (1 - q)⁻¹ := by ring
  rw [hval]
  exact h

/-- `(A e^{−y} + A e^{y}) q / (1 − q)` with `q = e^{−x}` is `2A cosh y / (e^x − 1)`. -/
theorem imageSum_majorant_value (A y : ℝ) {x : ℝ} (hx : 0 < x) :
    (A * Real.exp (-y) + A * Real.exp y) * (Real.exp (-x) * (1 - Real.exp (-x))⁻¹)
      = 2 * A * Real.cosh y / (Real.exp x - 1) := by
  have hE : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hE1 : Real.exp x - 1 ≠ 0 := (sub_pos.mpr hE).ne'
  have hq : Real.exp (-x) * (1 - Real.exp (-x))⁻¹ = (Real.exp x - 1)⁻¹ := by
    rw [Real.exp_neg]
    have h1 : 1 - (Real.exp x)⁻¹ = (Real.exp x - 1) * (Real.exp x)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hE0, one_mul]
    rw [h1, mul_inv, inv_inv, mul_comm (Real.exp x - 1)⁻¹, ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
  rw [hq, Real.cosh_eq, div_eq_mul_inv]
  ring

/-- For `m ≥ 1` the bound at the site `r + mN` is at most `A e^{−rη} q^m`, `q = e^{−ηN}`. -/
theorem imageSum_term_pos (A η : ℝ) (N : ℕ) (r m : ℤ) (hA : 0 ≤ A) (hη : 0 < η) (hm : 0 < m) :
    A * Real.exp (-(|((r + m * (N : ℤ) : ℤ) : ℝ)| * η))
      ≤ A * Real.exp (-((r : ℝ) * η)) * Real.exp (-(η * (N : ℝ))) ^ m.natAbs := by
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  have hk : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos hm]
  have habs : (r : ℝ) + (m : ℝ) * (N : ℝ) ≤ |((r + m * (N : ℤ) : ℤ) : ℝ)| := by
    have h := le_abs_self (((r + m * (N : ℤ) : ℤ) : ℝ))
    push_cast at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_right habs hη.le
  rw [hk]
  linarith

/-- For `m ≤ −1` the bound at the site `r + mN` is at most `A e^{rη} q^{|m|}`, `q = e^{−ηN}`. -/
theorem imageSum_term_neg (A η : ℝ) (N : ℕ) (r m : ℤ) (hA : 0 ≤ A) (hη : 0 < η) (hm : m < 0) :
    A * Real.exp (-(|((r + m * (N : ℤ) : ℤ) : ℝ)| * η))
      ≤ A * Real.exp ((r : ℝ) * η) * Real.exp (-(η * (N : ℝ))) ^ m.natAbs := by
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  have hk : ((m.natAbs : ℕ) : ℝ) = -(m : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_neg hm, Int.cast_neg]
  have habs : -((r : ℝ) + (m : ℝ) * (N : ℝ)) ≤ |((r + m * (N : ℤ) : ℤ) : ℝ)| := by
    have h := neg_le_abs (((r + m * (N : ℤ) : ℤ) : ℝ))
    push_cast at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_right habs hη.le
  rw [hk]
  linarith

/-- **F-images** The sum over the images `r + mN`, `m ≠ 0`, is at most `2A cosh(rη) / (e^{ηN} − 1)`. -/
theorem imageSumFacts : ImageSumFacts := by
  intro g A η N r S hA hη hN hg hS
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hx : 0 < η * (N : ℝ) := mul_pos hη hNpos
  -- subtract the term at `0`
  have hzero : HasSum (fun m : ℤ => if m = 0 then g r else 0) (g r) := hasSum_ite_eq 0 (g r)
  have hdiff := hS.sub hzero
  -- dominate by the two-sided geometric majorant
  have hq0 : 0 ≤ Real.exp (-(η * (N : ℝ))) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(η * (N : ℝ))) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hmaj := imageSum_hasSum_majorant (A * Real.exp (-((r : ℝ) * η))) (A * Real.exp ((r : ℝ) * η)) hq0 hq1
  rw [imageSum_majorant_value A ((r : ℝ) * η) hx] at hmaj
  refine hdiff.norm_le_of_bounded hmaj ?_
  intro m
  by_cases hm : m = 0
  · subst hm
    simp
  · simp only [hm, ↓reduceIte, sub_zero]
    by_cases hpos : 0 < m
    · simp only [hpos, ↓reduceIte]
      exact (hg (r + m * (N : ℤ))).trans (imageSum_term_pos A η N r m hA hη hpos)
    · simp only [hpos, ↓reduceIte]
      have hneg : m < 0 := by omega
      exact (hg (r + m * (N : ℤ))).trans (imageSum_term_neg A η N r m hA hη hneg)

end OscInt.FiniteRingAux
