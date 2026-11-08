/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt

/-!
# Front ends on phases given only by a formula (P1 acceptance)

The user's hypotheses below are Mathlib terms only (`ContDiff`, `tsupport`, `iteratedFDeriv`, `Metric.closedBall`,
continuous linear functionals); no `dd`, `ddd`, `AmpBound` or `cubicCoeffs` appears in any statement here. The
derivative data are computed from polynomial expansions along lines (`OscInt.API.Poly`), checked by `ring`.

* `consumer_d4_formula`: the uniform D4 bound t^{−2/3} for φ(x, y) = x³ − 3xy² + x⁴ (elliptic umbilic, disc 108),
  from FE-S4.1′ (`OscInt.API.d4BoundFE`).
* `consumer_fold_formula`: the uniform fold bound m^{−5/6} for Ψ(x, y) = x³ + y² on the unit ball, uniformly over
  linear terms of norm ≤ 1, from FE-S3 (`OscInt.API.foldFE`).
-/

open OscInt.Statements OscInt.API.Poly

/-- `![v, v] = fun _ => v` and `![v, v, v] = fun _ => v`, to feed the diagonal helper. -/
theorem consumer_diag2 (v : ℝ × ℝ) : (![v, v] : Fin 2 → ℝ × ℝ) = fun _ => v := by
  funext i; fin_cases i <;> rfl

theorem consumer_diag3 (v : ℝ × ℝ) : (![v, v, v] : Fin 3 → ℝ × ℝ) = fun _ => v := by
  funext i; fin_cases i <;> rfl

/-- The D4 phase, by formula. -/
noncomputable def d4Phase : ℝ × ℝ → ℝ := fun k => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2 + k.1 ^ 4

theorem d4Phase_line (v : ℝ × ℝ) (t : ℝ) :
    d4Phase ((0 : ℝ × ℝ) + t • v) =
      ∑ i : Fin 5, (![0, 0, 0, v.1 ^ 3 - 3 * v.1 * v.2 ^ 2, v.1 ^ 4] : Fin 5 → ℝ) i * t ^ (i : ℕ) := by
  simp [d4Phase, Fin.sum_univ_five]; ring

theorem consumer_d4_formula :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ t →
      ‖∫ κ : ℝ × ℝ, Complex.exp (↑(t * d4Phase κ + L κ) * Complex.I) * A κ‖ ≤ C * M * t ^ (-(2 : ℝ) / 3) := by
  have hC : ContDiff ℝ 5 d4Phase := by unfold d4Phase; fun_prop
  have h2 : iteratedFDeriv ℝ 2 d4Phase 0 = 0 := by
    refine iteratedFDeriv_two_eq_zero_of_diag (hC.contDiffAt.of_le (by norm_num)) fun v => ?_
    rw [consumer_diag2, iteratedFDeriv_diag_of_poly hC 0 v _ (d4Phase_line v) 2 (by norm_num)]; simp
  have h3 : ∀ x y : ℝ, iteratedFDeriv ℝ 3 d4Phase 0 ![(x, y), (x, y), (x, y)] =
      6 * (1 * x ^ 3 + 0 * x ^ 2 * y + (-3) * x * y ^ 2 + 0 * y ^ 3) := fun x y => by
    rw [consumer_diag3, iteratedFDeriv_diag_of_poly hC 0 (x, y) _ (d4Phase_line (x, y)) 3 (by norm_num)]
    simp [Nat.factorial]; ring
  exact OscInt.API.d4BoundFE d4Phase 1 0 (-3) 0 (hC.of_le (by norm_num)) h2 h3 (by norm_num [Cubic.discr])

/-- The fold phase, by formula. -/
noncomputable def foldPhase : ℝ × ℝ → ℝ := fun k => k.1 ^ 3 + k.2 ^ 2

theorem foldPhase_line (k v : ℝ × ℝ) (t : ℝ) :
    foldPhase (k + t • v) = ∑ i : Fin 4,
      (![k.1 ^ 3 + k.2 ^ 2, 3 * k.1 ^ 2 * v.1 + 2 * k.2 * v.2, 3 * k.1 * v.1 ^ 2 + v.2 ^ 2, v.1 ^ 3] : Fin 4 → ℝ) i *
        t ^ (i : ℕ) := by
  simp [foldPhase, Fin.sum_univ_four]; ring

theorem foldPhase_matrix (k : ℝ × ℝ) : FoldOrNondegMatrix foldPhase k := by
  have hC : ContDiff ℝ 4 foldPhase := by unfold foldPhase; fun_prop
  have hC2 : ContDiffAt ℝ 2 foldPhase k := hC.contDiffAt.of_le (by norm_num)
  have d2 : ∀ v : ℝ × ℝ, iteratedFDeriv ℝ 2 foldPhase k ![v, v] = 2 * (3 * k.1 * v.1 ^ 2 + v.2 ^ 2) := fun v => by
    rw [consumer_diag2, iteratedFDeriv_diag_of_poly hC k v _ (foldPhase_line k v) 2 (by norm_num)]; simp
  have hH : hessianMatrix foldPhase k = !![6 * k.1, 0; 0, 2] := by
    rw [hessianMatrix_eq_of_diag hC2 (d2 (1, 0)) (d2 (0, 1)) (d2 (1, 1))]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  have hT : ∀ e : Fin 2 → ℝ, iteratedFDeriv ℝ 3 foldPhase k ![ofFin2 e, ofFin2 e, ofFin2 e] = 6 * e 0 ^ 3 :=
    fun e => by
      rw [consumer_diag3, iteratedFDeriv_diag_of_poly hC k _ _ (foldPhase_line k (ofFin2 e)) 3 (by norm_num)]
      simp [ofFin2, Nat.factorial]
  unfold FoldOrNondegMatrix
  simp only [hT, hH]
  by_cases hk : k.1 = 0
  · rw [hk, mul_zero]
    refine foldCondSpan_of_rankOne (fun h => by simpa using congrFun (congrFun h 1) 1)
      (by simp [Matrix.det_fin_two]) fun e he hHe => ?_
    have h1 : e 1 = 0 := by
      have := congrFun hHe 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h0 : e 0 ≠ 0 := fun h0 => he (by funext i; fin_cases i <;> simp [h0, h1])
    simpa using h0
  · left
    rw [Matrix.det_fin_two]; simpa using hk

theorem consumer_fold_formula :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ Metric.closedBall (0 : (ℝ × ℝ) →L[ℝ] ℝ) 1 → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (foldPhase k + L k)) * Complex.I) * A k‖ ≤
        C * M * m ^ (-(5 : ℝ) / 6) :=
  OscInt.API.foldFE foldPhase _ _ (by unfold foldPhase; fun_prop) (isCompact_closedBall 0 1)
    (isCompact_closedBall 0 1) fun k _ => foldPhase_matrix k
