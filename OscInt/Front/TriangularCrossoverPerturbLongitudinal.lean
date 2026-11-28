/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# Batch A5U, part A10: `PerturbLongitudinalFacts`

Route: `stmts/proof-A5U-draft.md`, section 5. Let `φ(x) = e (cos 2x − 1)` and `P = φ ∘ fst`.
* `φ^{(n+1)}(x) = e 2^{n+1} cos(2x + (n+1)π/2)` (induction), so `|φ^{(j)}| ≤ 2^j |e|` for `j ≥ 1`, and
  `|φ| ≤ 2|e|`; hence `|φ^{(j)}| ≤ 16 |e|` for `j ≤ 4`.
* On the open interval `(−2a, 2a)`, where the reduced function is smooth, `iteratedDeriv` is additive
  (`iteratedDerivWithin_add`, `iteratedDerivWithin_of_isOpen`): this is the first claim.
* `P` does not depend on `k.2`: `fderiv P k (0, 1) = 0`, so the transverse derivative and `dd · (0,1) (0,1)` of the
  phase are unchanged; `‖D^i P‖ ≤ ‖φ^{(i)}‖ ‖fst‖^i ≤ 16|e|` (`ContinuousLinearMap.iteratedFDeriv_comp_right`).
-/

namespace OscInt.A5UAux

open Set OscInt.Statements OscInt.Blueprint.K2
open scoped ContDiff

/-- `(K cos(2x + c))' = 2K cos(2x + c + π/2)`. -/
theorem a5uG2_hasDerivAt_cos2 (K c x : ℝ) :
    HasDerivAt (fun x => K * Real.cos (2 * x + c)) (K * 2 * Real.cos (2 * x + c + Real.pi / 2)) x := by
  have h := (((hasDerivAt_id x).const_mul 2).add_const c).cos.const_mul K
  simp only [id] at h
  convert h using 1
  rw [Real.cos_add_pi_div_two]
  ring

/-- `φ^{(n+1)}(x) = e 2^{n+1} cos(2x + (n+1)π/2)` for `φ(x) = e (cos 2x − 1)`. -/
theorem a5uG2_iteratedDeriv_phi (e : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun x => e * (Real.cos (2 * x) - 1)) =
      fun x => e * 2 ^ (n + 1) * Real.cos (2 * x + (n + 1 : ℕ) * (Real.pi / 2)) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext x
    have h := (a5uG2_hasDerivAt_cos2 e 0 x).sub_const e
    have h' : HasDerivAt (fun x => e * (Real.cos (2 * x) - 1)) (e * 2 * Real.cos (2 * x + 0 + Real.pi / 2)) x := by
      convert h using 1
      funext y
      rw [add_zero]
      ring
    rw [h'.deriv]
    push_cast
    ring_nf
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [(a5uG2_hasDerivAt_cos2 (e * 2 ^ (n + 1)) _ x).deriv]
    push_cast
    ring_nf

/-- `|φ^{(j)}| ≤ 2^j |e|` for `j ≥ 1`. -/
theorem a5uG2_phi_bound (e : ℝ) (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    |iteratedDeriv j (fun x => e * (Real.cos (2 * x) - 1)) x| ≤ 2 ^ j * |e| := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  rw [a5uG2_iteratedDeriv_phi, abs_mul, abs_mul, abs_pow, abs_two, mul_comm (|e|)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- `|φ^{(j)}| ≤ 16 |e|` for `j ≤ 4`. -/
theorem a5uG2_phi_bound16 (e : ℝ) (j : ℕ) (hj : j ≤ 4) (x : ℝ) :
    |iteratedDeriv j (fun x => e * (Real.cos (2 * x) - 1)) x| ≤ 16 * |e| := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [iteratedDeriv_zero, abs_mul, mul_comm]
    have : |Real.cos (2 * x) - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (2 * x), Real.cos_le_one (2 * x)]
    nlinarith [abs_nonneg e]
  · refine (a5uG2_phi_bound e j hj1 x).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg e))
    calc (2 : ℝ) ^ j ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hj
      _ = 16 := by norm_num

/-- `φ` is smooth. -/
theorem a5uG2_phi_smooth (e : ℝ) : ContDiff ℝ ∞ (fun x : ℝ => e * (Real.cos (2 * x) - 1)) :=
  contDiff_const.mul ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub contDiff_const)

/-- The first claim: the reduced derivatives change by `φ^{(j)}`. -/
theorem a5uG2_reduced_diff {a e : ℝ} {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} (hQ : ContDiff ℝ ∞ Q)
    (hys : ContDiffOn ℝ ∞ ys (Ioo (-2 * a) (2 * a))) (j : ℕ) (hj : 1 ≤ j) (x : ℝ)
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    |iteratedDeriv j (fun x => Q (x, ys x) + e * (Real.cos (2 * x) - 1)) x -
        iteratedDeriv j (fun x => Q (x, ys x)) x| ≤ 2 ^ j * |e| := by
  set U := Ioo (-2 * a) (2 * a)
  have hf : ContDiffOn ℝ ∞ (fun x => Q (x, ys x)) U := hQ.comp_contDiffOn (contDiffOn_id.prodMk hys)
  have hjle : ((j : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hadd := iteratedDerivWithin_add (n := j) hx isOpen_Ioo.uniqueDiffOn
    ((hf x hx).of_le hjle) (((a5uG2_phi_smooth e).contDiffAt.of_le hjle).contDiffWithinAt)
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioo hx, iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDerivWithin_of_isOpen isOpen_Ioo hx] at hadd
  have hadd' : iteratedDeriv j (fun x => Q (x, ys x) + e * (Real.cos (2 * x) - 1)) x =
      iteratedDeriv j (fun x => Q (x, ys x)) x + iteratedDeriv j (fun x => e * (Real.cos (2 * x) - 1)) x :=
    hadd
  rw [hadd', add_sub_cancel_left]
  exact a5uG2_phi_bound e j hj x

/-- The perturbation `P = φ ∘ fst` has `fderiv P k v = φ'(k.1) v.1`. -/
theorem a5uG2_fderiv_P (e : ℝ) (k v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) k v =
      deriv (fun x => e * (Real.cos (2 * x) - 1)) k.1 * v.1 := by
  have hφ : DifferentiableAt ℝ (fun x : ℝ => e * (Real.cos (2 * x) - 1)) k.1 :=
    ((a5uG2_phi_smooth e).differentiable (by simp)) _
  have h := hφ.hasDerivAt.comp_hasFDerivAt k (hasFDerivAt_fst (𝕜 := ℝ) (p := k))
  rw [show (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) =
    (fun x : ℝ => e * (Real.cos (2 * x) - 1)) ∘ Prod.fst from rfl, h.fderiv]
  simp [mul_comm]

/-- The perturbed phase is smooth, with unchanged transverse derivative. -/
theorem a5uG2_fderiv_perturb {e : ℝ} {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ ∞ Q) (k : ℝ × ℝ) :
    fderiv ℝ (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) k (0, 1) = fderiv ℝ Q k (0, 1) := by
  have hP : ContDiff ℝ ∞ (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) :=
    (a5uG2_phi_smooth e).comp contDiff_fst
  rw [show (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) =
    Q + (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) from rfl,
    fderiv_add (hQ.differentiable (by simp) k) (hP.differentiable (by simp) k),
    add_apply, a5uG2_fderiv_P, mul_zero, add_zero]

/-- `‖D^i P‖ ≤ 16 |e|` for `i ≤ 4`. -/
theorem a5uG2_norm_iteratedFDeriv_P (e : ℝ) (i : ℕ) (hi : i ≤ 4) (k : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) k‖ ≤ 16 * |e| := by
  rw [show (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) =
    (fun x : ℝ => e * (Real.cos (2 * x) - 1)) ∘ (ContinuousLinearMap.fst ℝ ℝ ℝ) from rfl,
    (ContinuousLinearMap.fst ℝ ℝ ℝ).iteratedFDeriv_comp_right (a5uG2_phi_smooth e) k
      (WithTop.coe_le_coe.2 le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have h16 := a5uG2_phi_bound16 e i hi ((ContinuousLinearMap.fst ℝ ℝ ℝ) k)
  calc _ ≤ |iteratedDeriv i (fun x => e * (Real.cos (2 * x) - 1)) ((ContinuousLinearMap.fst ℝ ℝ ℝ) k)| * 1 :=
        mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ ≤ 16 * |e| := by rw [mul_one]; exact h16

/-- The derivative bound `D + 16 |e|` for the perturbed phase. -/
theorem a5uG2_perturb_D {e D : ℝ} {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ ∞ Q) (i : ℕ) (hi : i ≤ 4) (k : ℝ × ℝ)
    (hk : ‖iteratedFDeriv ℝ i Q k‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) k‖ ≤ D + 16 * |e| := by
  have hP : ContDiff ℝ ∞ (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) :=
    (a5uG2_phi_smooth e).comp contDiff_fst
  have hile : ((i : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  rw [show (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) =
    Q + (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) from rfl,
    iteratedFDeriv_add_apply (hQ.contDiffAt.of_le hile) (hP.contDiffAt.of_le hile)]
  exact (norm_add_le _ _).trans (add_le_add hk (a5uG2_norm_iteratedFDeriv_P e i hi k))

/-- **A10** `PerturbLongitudinalFacts`. -/
theorem perturbLongitudinal : OscInt.Blueprint.A5U.PerturbLongitudinalFacts := by
  intro m a b μ ν D e Q ys ⟨hQ, hys, hcrit, hdd, hD, _⟩
  refine ⟨fun j hj x hx => a5uG2_reduced_diff hQ hys j hj x hx, fun ν' hν' => ?_⟩
  have hP : ContDiff ℝ ∞ (fun k : ℝ × ℝ => e * (Real.cos (2 * k.1) - 1)) :=
    (a5uG2_phi_smooth e).comp contDiff_fst
  have hdd' : ∀ k, dd (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) k (0, 1) (0, 1) = dd Q k (0, 1) (0, 1) := by
    intro k
    simp only [dd, a5uG2_fderiv_perturb hQ]
  refine ⟨hQ.add hP, hys, fun x hx => ?_, fun x hx y hy => ?_, fun i hi x hx y hy => ?_, hν'⟩
  · exact ⟨(hcrit x hx).1, by rw [a5uG2_fderiv_perturb hQ]; exact (hcrit x hx).2⟩
  · rw [hdd']; exact hdd x hx y hy
  · exact a5uG2_perturb_D hQ i hi _ (hD i hi x hx y hy)

end OscInt.A5UAux
