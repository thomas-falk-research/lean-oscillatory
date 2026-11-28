/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# Batch A5U, part A5: `EvenJetTaylorFacts`

Route: `stmts/proof-A5U-draft.md`, section 3. Write `d j = iteratedDeriv j g`.
* On the open interval `I = (−a, a)`, `d j` has derivative `d (j+1)` (`iteratedDerivWithin_of_isOpen`).
* Evenness near `0` and `iteratedDeriv_comp_neg` give `d j 0 = (−1)^j d j 0`, so the odd jets vanish.
* One mean value step (`Convex.norm_image_sub_le_of_norm_deriv_le` on `[0, x]`): if `f 0 = 0` and
  `|f'(y)| ≤ L |y|^k` on `I`, then `|f x| ≤ L |x|^{k+1}` on `I`. No factorials are needed.
* Seven steps, from `|d 8| ≤ L`, through the remainders `d 7`, `d 6 − D`, `d 5 − D u`, `d 4 − (B + D u²/2)`,
  `d 3 − (B u + D u³/6)`, `d 2 − (A + B u²/2 + D u⁴/24)`, each vanishing at `0` because the odd jets do.
-/

namespace OscInt.A5UAux

open Set
open scoped ContDiff

/-- `|y| ≤ |u|` on `[0, u]` (unordered). -/
theorem a5uG2_abs_le_of_mem_uIcc {u y : ℝ} (hy : y ∈ uIcc 0 u) : |y| ≤ |u| := by
  rcases le_total 0 u with h | h
  · rw [uIcc_of_le h] at hy
    rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIcc_of_ge h] at hy
    rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

/-- One mean value step: `f 0 = 0` and `|f'(y)| ≤ L |y|^k` on `(−a, a)` give `|f x| ≤ L |x|^{k+1}`. -/
theorem a5uG2_step {a L : ℝ} {f F : ℝ → ℝ} (k m : ℕ) (hm : k + 1 = m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Ioo (-a) a, HasDerivAt f (F y) y) (hb : ∀ y ∈ Ioo (-a) a, |F y| ≤ L * |y| ^ k)
    (h0 : f 0 = 0) : ∀ x ∈ Ioo (-a) a, |f x| ≤ L * |x| ^ m := by
  subst hm
  intro x hx
  have h0a : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hsub : uIcc 0 x ⊆ Ioo (-a) a := (ordConnected_Ioo).uIcc_subset h0a hx
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := uIcc 0 x) (x := 0) (y := x)
    (C := L * |x| ^ k) (fun y hy => (hd y (hsub hy)).differentiableAt)
    (fun y hy => by
      rw [(hd y (hsub hy)).deriv, Real.norm_eq_abs]
      exact (hb y (hsub hy)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (a5uG2_abs_le_of_mem_uIcc hy) k) hL))
    (convex_uIcc 0 x) left_mem_uIcc right_mem_uIcc
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at key
  rw [pow_succ, ← mul_assoc]
  exact key

/-- On the open interval, `iteratedDeriv j g` has derivative `iteratedDeriv (j + 1) g`. -/
theorem a5uG2_hasDerivAt_iter {g : ℝ → ℝ} {a : ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo (-a) a)) (j : ℕ) :
    ∀ x ∈ Ioo (-a) a, HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g x) x := by
  intro x hx
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j g (Ioo (-a) a)) (Ioo (-a) a) :=
    hg.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top j))
      (isOpen_Ioo.uniqueDiffOn)
  have h2 : DifferentiableOn ℝ (iteratedDeriv j g) (Ioo (-a) a) :=
    h1.congr (fun y hy => (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm)
  have h3 := (h2 x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  rw [iteratedDeriv_succ]
  exact h3.hasDerivAt

/-- The odd jets of an even function vanish at `0`. -/
theorem a5uG2_odd_jet {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ x ∈ Ioo (-a) a, g (-x) = g x) (j : ℕ)
    (hj : Odd j) : iteratedDeriv j g 0 = 0 := by
  have hmem : Ioo (-a) a ∈ nhds (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith, ha⟩
  have hev' : g =ᶠ[nhds 0] fun x => g (-x) :=
    Filter.mem_of_superset hmem (fun x hx => (hev x hx).symm)
  have h := hev'.iteratedDeriv_eq j
  rw [iteratedDeriv_comp_neg, neg_zero, hj.neg_one_pow, smul_eq_mul] at h
  linarith

/-- `(D x)' = D`. -/
theorem a5uG2_poly1 (D y : ℝ) : HasDerivAt (fun x => D * x) D y := by
  simpa using (hasDerivAt_id y).const_mul D

/-- `(B + D x²/2)' = D x`. -/
theorem a5uG2_poly2 (B D y : ℝ) : HasDerivAt (fun x => B + D * x ^ 2 / 2) (D * y) y := by
  have := (((hasDerivAt_pow 2 y).const_mul D).div_const 2).const_add B
  convert this using 1; push_cast; ring

/-- `(B x + D x³/6)' = B + D x²/2`. -/
theorem a5uG2_poly3 (B D y : ℝ) : HasDerivAt (fun x => B * x + D * x ^ 3 / 6) (B + D * y ^ 2 / 2) y := by
  have := (a5uG2_poly1 B y).add (((hasDerivAt_pow 3 y).const_mul D).div_const 6)
  convert this using 1; push_cast; ring

/-- `(A + B x²/2 + D x⁴/24)' = B x + D x³/6`. -/
theorem a5uG2_poly4 (A B D y : ℝ) :
    HasDerivAt (fun x => A + B * x ^ 2 / 2 + D * x ^ 4 / 24) (B * y + D * y ^ 3 / 6) y := by
  have := ((((hasDerivAt_pow 2 y).const_mul B).div_const 2).const_add A).add
    (((hasDerivAt_pow 4 y).const_mul D).div_const 24)
  convert this using 1; push_cast; ring

/-- The seven remainder bounds. -/
theorem a5uG2_jets {g : ℝ → ℝ} {a L : ℝ} (ha : 0 < a) (hg : ContDiffOn ℝ ∞ g (Ioo (-a) a))
    (hev : ∀ x ∈ Ioo (-a) a, g (-x) = g x) (hL : ∀ x ∈ Ioo (-a) a, |iteratedDeriv 8 g x| ≤ L) :
    ∀ u ∈ Ioo (-a) a,
      |iteratedDeriv 2 g u -
          (iteratedDeriv 2 g 0 + iteratedDeriv 4 g 0 * u ^ 2 / 2 + iteratedDeriv 6 g 0 * u ^ 4 / 24)| ≤
        L * |u| ^ 6 ∧
      |iteratedDeriv 3 g u - (iteratedDeriv 4 g 0 * u + iteratedDeriv 6 g 0 * u ^ 3 / 6)| ≤ L * |u| ^ 5 ∧
      |iteratedDeriv 4 g u - (iteratedDeriv 4 g 0 + iteratedDeriv 6 g 0 * u ^ 2 / 2)| ≤ L * |u| ^ 4 := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0 ⟨by linarith, ha⟩)
  set A := iteratedDeriv 2 g 0
  set B := iteratedDeriv 4 g 0
  set D := iteratedDeriv 6 g 0
  have hd := a5uG2_hasDerivAt_iter hg
  have o3 := a5uG2_odd_jet ha hev 3 (by decide)
  have o5 := a5uG2_odd_jet ha hev 5 (by decide)
  have o7 := a5uG2_odd_jet ha hev 7 (by decide)
  have s7 := a5uG2_step 0 1 rfl hL0 (hd 7) (fun y hy => by rw [pow_zero, mul_one]; exact hL y hy) o7
  have s6 := a5uG2_step (f := fun x => iteratedDeriv 6 g x - D) 1 2 rfl hL0
    (fun y hy => (hd 6 y hy).sub_const D) s7 (by simp [D])
  have s5 := a5uG2_step (f := fun x => iteratedDeriv 5 g x - D * x) 2 3 rfl hL0
    (fun y hy => (hd 5 y hy).sub (a5uG2_poly1 D y)) s6 (by simp [o5])
  have s4 := a5uG2_step (f := fun x => iteratedDeriv 4 g x - (B + D * x ^ 2 / 2)) 3 4 rfl hL0
    (fun y hy => (hd 4 y hy).sub (a5uG2_poly2 B D y)) s5 (by simp [B])
  have s3 := a5uG2_step (f := fun x => iteratedDeriv 3 g x - (B * x + D * x ^ 3 / 6)) 4 5 rfl hL0
    (fun y hy => (hd 3 y hy).sub (a5uG2_poly3 B D y)) s4 (by simp [o3])
  have s2 := a5uG2_step (f := fun x => iteratedDeriv 2 g x - (A + B * x ^ 2 / 2 + D * x ^ 4 / 24)) 5 6 rfl
    hL0 (fun y hy => (hd 2 y hy).sub (a5uG2_poly4 A B D y)) s3 (by simp [A])
  exact fun u hu => ⟨s2 u hu, s3 u hu, s4 u hu⟩

/-- **A5** `EvenJetTaylorFacts`. -/
theorem evenJetTaylor : OscInt.Blueprint.A5U.EvenJetTaylorFacts := by
  intro g a L ha hg hev hL u hu
  obtain ⟨h2, h3, h4⟩ := a5uG2_jets ha hg hev hL u hu
  refine ⟨?_, h3, ?_⟩
  · rwa [pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 6)] at h2
  · rwa [pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 4)] at h4

end OscInt.A5UAux
