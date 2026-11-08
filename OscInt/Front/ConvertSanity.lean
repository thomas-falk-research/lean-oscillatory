/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Convert
import OscInt.D4.Sanity
import OscInt.StationaryPhase.Implicit

/-!
# Front-end batch 2: derivative-level sanity checks

Answers the blind statement referees' MINORs and NITs (`review/2026-11-07-API2-pre-proof-answers.md`). Everything
here uses the batch-2 *definitions* (`hessianMatrix`, `FoldOrNondegMatrix`, `FoldCondSpan`, the front-end hypotheses
as written in `OscInt/Statements/Convert.lean`) on explicit phases, computed through the session-2 lemmas
`OscInt.StationaryPhase.ImplicitAux.dd_eq_iteratedFDeriv`, `ddd_eq_iteratedFDeriv` and explicit derivatives; no
batch-2 theorem is used, so these checks are independent of the bridges.

* `hessian_fold`, `hessian_mixed`: the Hessian matrix of x³ + y² and of x² + 3xy + 5y² (distinct, nonzero
  off-diagonal entries `3, 3`: pins the entry order and the factor of `iteratedFDeriv`).
* `foldOrNondegMatrix_fold`: FE-S3's hypothesis holds for the fold x³ + y² at every point.
* `not_foldOrNondegMatrix_quartic`: bite, x⁴ + y² at 0 (third derivative vanishes on the kernel).
* `d4FE_hyps_generic`, `d4FE_hyps_elliptic`: FE-S4.1′'s derivative hypotheses for x³ + 2x²y + 3xy² + 5y³
  (coefficients `(1, 2, 3, 5)`) and x³ − 3xy², and `d4FE_reversed_fails`: the reversed coefficients `(5, 3, 2, 1)`
  (same discriminant) violate the identity, so the coefficient order is pinned.
* `ker_nonsymm`, `foldCondSpan_right_kernel`: `toLin'` is the right kernel (a non-symmetric rank-one matrix whose
  left and right kernels differ).
* `isolated_bite`: the derivative of x²y vanishes on the whole line `(0, t)` (C6's right side fails for disc 0).
* `ampBound_iff_written_out`: the front ends' amplitude hypothesis is `AmpBound` written out.
-/

namespace OscInt.API.ConvertSanity

open OscInt.Statements OscInt.StationaryPhase.ImplicitAux OscInt.D4

theorem iteratedFDeriv_two_eq_dd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k a b : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 f k ![a, b] = dd f k b a :=
  (dd_eq_iteratedFDeriv (N := 2) hf le_rfl k b a).symm

theorem iteratedFDeriv_three_diag {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 3 f) (k a : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 f k ![a, a, a] = ddd f k a a a :=
  (ddd_eq_iteratedFDeriv (N := 3) hf le_rfl k a a a).symm

theorem hessian_fold (k : ℝ × ℝ) :
    hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) k = !![6 * k.1, 0; 0, 2] := by
  have h := iteratedFDeriv_two_eq_dd (f := fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) (by fun_prop) k
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, sanity_dd_fold, coordVec]

theorem dd_mixed (k v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2) k v w =
      (2 * v.1 + 3 * v.2) * w.1 + (3 * v.1 + 10 * v.2) * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2) y v) =
      fun y => (2 * 1 * v.1 + 3 * v.2) * y.1 + (3 * v.1 + 2 * 5 * v.2) * y.2 := by
    funext y
    have := fd_genQuad 1 3 5 y v
    simp only [one_mul] at this
    rw [this]
  rw [dd, this, sanity_fd_lin]; ring

theorem hessian_mixed (k : ℝ × ℝ) :
    hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2) k = !![2, 3; 3, 10] ∧
      (hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2) k).det = 11 := by
  have h : hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2) k = !![2, 3; 3, 10] := by
    have h := iteratedFDeriv_two_eq_dd (f := fun k : ℝ × ℝ => k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2)
      (by fun_prop) k
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, dd_mixed, coordVec]
  refine ⟨h, ?_⟩
  rw [h, Matrix.det_fin_two]; norm_num

theorem third_fold (k : ℝ × ℝ) (e : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 3 (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) k ![ofFin2 e, ofFin2 e, ofFin2 e] = 6 * e 0 ^ 3 := by
  rw [iteratedFDeriv_three_diag (f := fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) (by fun_prop), sanity_ddd_fold]; simp [ofFin2]; ring

theorem foldOrNondegMatrix_fold (k : ℝ × ℝ) : FoldOrNondegMatrix (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) k := by
  unfold FoldOrNondegMatrix
  simp only [third_fold, hessian_fold]
  by_cases hk : k.1 = 0
  · rw [hk, mul_zero]
    exact (sanity_FoldCondSpan).1
  · left
    rw [Matrix.det_fin_two]; simp; exact hk

theorem fd_quartic (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v = 4 * y.1 ^ 3 * v.1 + 2 * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2)
      ((4 * y.1 ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 4).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2) using 1
    ext <;> simp
  rw [h.fderiv]; simp

theorem fd_cube_lin (y w : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2) y w = 3 * a * y.1 ^ 2 * w.1 + b * w.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2)
      ((3 * a * y.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul b) using 1
    ext <;> simp; ring
  rw [h.fderiv]; simp

theorem dd_quartic (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v w = 12 * y.1 ^ 2 * v.1 * w.1 + 2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v) =
      fun y => (4 * v.1) * y.1 ^ 3 + (2 * v.2) * y.2 := by funext y; rw [fd_quartic]; ring
  rw [dd, this, fd_cube_lin]; ring

theorem ddd_quartic_zero (u v w : ℝ × ℝ) : ddd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) 0 u v w = 0 := by
  have : (fun y : ℝ × ℝ => dd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y u v) =
      fun y => (12 * u.1 * v.1) * y.1 ^ 2 + 2 * u.2 * v.2 := by funext y; rw [dd_quartic]; ring
  rw [ddd, this]
  have h : HasFDerivAt (fun y : ℝ × ℝ => (12 * u.1 * v.1) * y.1 ^ 2 + 2 * u.2 * v.2)
      ((2 * (12 * u.1 * v.1) * (0 : ℝ × ℝ).1) • ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2).const_mul (12 * u.1 * v.1)).add_const
      (2 * u.2 * v.2) using 1
    ext <;> simp
  rw [h.fderiv]; simp

/-- Bite: at `0`, x⁴ + y² has a rank-one Hessian whose kernel is the x-axis, and its third derivative vanishes. -/
theorem not_foldOrNondegMatrix_quartic : ¬ FoldOrNondegMatrix (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) 0 := by
  have hH : hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) 0 = !![(0 : ℝ), 0; 0, 2] := by
    have h := iteratedFDeriv_two_eq_dd (f := fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) (by fun_prop) 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, dd_quartic, coordVec]
  have hT : ∀ e : Fin 2 → ℝ, iteratedFDeriv ℝ 3 (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) 0
      ![ofFin2 e, ofFin2 e, ofFin2 e] = 0 := fun e => by
    rw [iteratedFDeriv_three_diag (f := fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) (by fun_prop), ddd_quartic_zero]
  unfold FoldOrNondegMatrix
  rw [hH]
  rintro (h | ⟨e, -, -, hTe⟩)
  · simp [Matrix.det_fin_two] at h
  · exact hTe (hT e)

/-- The amplitude hypothesis of the front ends is `AmpBound` written out (referee A, NIT 7). -/
theorem ampBound_iff_written_out (n : ℕ) (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ) (M : ℝ) :
    (ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) ↔ AmpBound n K A M :=
  Iff.rfl

theorem iteratedFDeriv_two_genCubic_zero (a b c d : ℝ) : iteratedFDeriv ℝ 2 (genCubic a b c d) 0 = 0 := by
  ext m
  have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
  rw [hm, iteratedFDeriv_two_eq_dd ((genCubic_contDiff a b c d).of_le (by norm_num)), dd_genCubic_zero]
  simp

theorem third_genCubic (a b c d x y : ℝ) :
    iteratedFDeriv ℝ 3 (genCubic a b c d) 0 ![(x, y), (x, y), (x, y)] =
      6 * (a * x ^ 3 + b * x ^ 2 * y + c * x * y ^ 2 + d * y ^ 3) := by
  rw [iteratedFDeriv_three_diag ((genCubic_contDiff a b c d).of_le (by norm_num)), ddd_genCubic]; ring

/-- FE-S4.1′'s derivative hypotheses for x³ + 2x²y + 3xy² + 5y³ (`disc = −367`). -/
theorem d4FE_hyps_generic :
    ContDiff ℝ 4 (genCubic 1 2 3 5) ∧ iteratedFDeriv ℝ 2 (genCubic 1 2 3 5) 0 = 0 ∧
      (∀ x y : ℝ, iteratedFDeriv ℝ 3 (genCubic 1 2 3 5) 0 ![(x, y), (x, y), (x, y)] =
        6 * (1 * x ^ 3 + 2 * x ^ 2 * y + 3 * x * y ^ 2 + 5 * y ^ 3)) ∧
      (Cubic.mk (1 : ℝ) 2 3 5).discr ≠ 0 :=
  ⟨genCubic_contDiff 1 2 3 5, iteratedFDeriv_two_genCubic_zero 1 2 3 5, fun x y => third_genCubic 1 2 3 5 x y,
    by rw [sanity_discr_values.1]; norm_num⟩

/-- FE-S4.1′'s derivative hypotheses for the elliptic umbilic x³ − 3xy² (`disc = 108`). -/
theorem d4FE_hyps_elliptic :
    ContDiff ℝ 4 (genCubic 1 0 (-3) 0) ∧ iteratedFDeriv ℝ 2 (genCubic 1 0 (-3) 0) 0 = 0 ∧
      (∀ x y : ℝ, iteratedFDeriv ℝ 3 (genCubic 1 0 (-3) 0) 0 ![(x, y), (x, y), (x, y)] =
        6 * (1 * x ^ 3 + 0 * x ^ 2 * y + (-3) * x * y ^ 2 + 0 * y ^ 3)) ∧
      (Cubic.mk (1 : ℝ) 0 (-3) 0).discr ≠ 0 :=
  ⟨genCubic_contDiff 1 0 (-3) 0, iteratedFDeriv_two_genCubic_zero 1 0 (-3) 0,
    fun x y => third_genCubic 1 0 (-3) 0 x y, by rw [sanity_discr_values.2.2]; norm_num⟩

/-- Bite: the reversed coefficients `(5, 3, 2, 1)` (same discriminant) do not satisfy the identity for
x³ + 2x²y + 3xy² + 5y³, so FE-S4.1′ pins the order `x³, x²y, xy², y³`. -/
theorem d4FE_reversed_fails :
    ¬ ∀ x y : ℝ, iteratedFDeriv ℝ 3 (genCubic 1 2 3 5) 0 ![(x, y), (x, y), (x, y)] =
      6 * (5 * x ^ 3 + 3 * x ^ 2 * y + 2 * x * y ^ 2 + 1 * y ^ 3) := by
  intro h
  have := h 1 0
  rw [third_genCubic] at this
  norm_num at this

/-- A non-symmetric rank-one matrix: right kernel `span {(2, −1)}`, left kernel `span {(3, −1)}`. -/
theorem ker_nonsymm :
    LinearMap.ker (Matrix.toLin' !![(1 : ℝ), 2; 3, 6]) = Submodule.span ℝ {![2, -1]} := by
  ext e
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨-e 1, ?_⟩
    ext i; fin_cases i <;> simp; linarith
  · rintro ⟨a, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- `FoldCondSpan` reads `T` on the right kernel: a `T` vanishing on the right kernel `(2, −1)` but not on the left
kernel `(3, −1)` fails, and `T e = e₀³` (nonzero at `(2, −1)`) holds. -/
theorem foldCondSpan_right_kernel :
    FoldCondSpan !![(1 : ℝ), 2; 3, 6] (fun e => e 0 ^ 3) ∧
      ¬ FoldCondSpan !![(1 : ℝ), 2; 3, 6] (fun e => e 0 + 2 * e 1) := by
  refine ⟨Or.inr ⟨![2, -1], by simp, ker_nonsymm, by norm_num⟩, ?_⟩
  rintro (h | ⟨e, he, hker, hT⟩)
  · simp [Matrix.det_fin_two] at h; norm_num at h
  · have : e ∈ Submodule.span ℝ {(![2, -1] : Fin 2 → ℝ)} := by
      rw [← ker_nonsymm, hker]; exact Submodule.mem_span_singleton_self e
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp this
    apply hT; simp; ring

/-- C6 bite on the derivative side: x²y (`disc = 0`) has zero derivative at every point `(0, t)`. -/
theorem isolated_bite (t : ℝ) : fderiv ℝ (cubicForm (0, 1, 0, 0)) (0, t) = 0 := by
  have : cubicForm (0, 1, 0, 0) = genCubic 0 1 0 0 := rfl
  ext <;> simp [this, fd_genCubic]

end OscInt.API.ConvertSanity
