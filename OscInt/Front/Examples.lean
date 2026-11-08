/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.Convert
import OscInt.Front.ConvertSanity
import OscInt.Front.Poly

/-!
# Front-end batch 2: non-vacuity through the bridges (post-proof)

Answers the post-proof and adversarial referees (`review/2026-11-07-API2-answers.md`, m6; post-proof B, MINOR 2):
every front end is applied to an explicit phase, so its hypotheses are shown satisfiable and its conclusion is
reached; bites show the hypotheses can fail.

* `fe21_instance`, `fe21_grad`, `fe21_grad_bite`: FE-S2.1 for Ψ = k₁ on the unit ball with c = 1 (`‖DΨ + 0‖ = 1`);
  bite: with `L = −fst` the gradient bound fails (`‖DΨ + L‖ = 0`).
* `fe22_instance`, `hessian_saddle`: FE-S2.2 for the saddle k₁² − k₂² (Hessian matrix `diag(2, −2)`, det −4).
* `fe41_hyperbolic`: FE-S4.1′ for the generic hyperbolic cubic x³ + 2x²y + 3xy² + 5y³ (disc −367); the elliptic case
  is `examples/consumer/ConsumerFormula.lean`.
* `c8_values`: C8 on the gradient (3, 4): max-norm operator norm 7, `GradLower … 5` holds and `GradLower … 5.1` fails
  (the Euclidean length is 5).
-/

namespace OscInt.API.Examples

open OscInt.Statements OscInt.API.Poly

theorem fderiv_fst' (k : ℝ × ℝ) : fderiv ℝ (fun k : ℝ × ℝ => k.1) k = ContinuousLinearMap.fst ℝ ℝ ℝ :=
  (hasFDerivAt_fst).fderiv

theorem fe21_grad (k : ℝ × ℝ) : (1 : ℝ) ≤ ‖fderiv ℝ (fun k : ℝ × ℝ => k.1) k + 0‖ := by
  rw [fderiv_fst', add_zero, NormAux.norm_prod_functional]; simp

theorem fe21_grad_bite (k : ℝ × ℝ) :
    ‖fderiv ℝ (fun k : ℝ × ℝ => k.1) k + -ContinuousLinearMap.fst ℝ ℝ ℝ‖ < 1 := by
  rw [fderiv_fst', add_neg_cancel, norm_zero]; norm_num

/-- FE-S2.1 applied to Ψ = k₁ (N = 1, K the unit ball, c = 1, the linear term `0`). -/
theorem fe21_instance :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ), ContDiff ℝ 1 A → tsupport A ⊆ Metric.closedBall 0 1 →
      (∀ j ≤ 1, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (k.1 + (0 : (ℝ × ℝ) →L[ℝ] ℝ) k)) * Complex.I) * A k‖ ≤ C * M / m ^ 1 := by
  obtain ⟨C, hC⟩ := nonStationaryFE 1 (fun k : ℝ × ℝ => k.1) (Metric.closedBall 0 1) 1 (by fun_prop)
    (isCompact_closedBall 0 1) one_pos
  exact ⟨C, fun A M m hA hs hb hm => hC A M 0 m hA hs hb (fun k _ => fe21_grad k) hm⟩

theorem saddle_line (k v : ℝ × ℝ) (t : ℝ) :
    (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) (k + t • v) = ∑ i : Fin 3,
      (![k.1 ^ 2 - k.2 ^ 2, 2 * k.1 * v.1 - 2 * k.2 * v.2, v.1 ^ 2 - v.2 ^ 2] : Fin 3 → ℝ) i * t ^ (i : ℕ) := by
  simp [Fin.sum_univ_three]; ring

theorem hessian_saddle (k : ℝ × ℝ) : hessianMatrix (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) k = !![2, 0; 0, -2] := by
  have hC : ContDiff ℝ 3 (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) := by fun_prop
  have d2 : ∀ v : ℝ × ℝ, iteratedFDeriv ℝ 2 (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) k ![v, v] =
      2 * (v.1 ^ 2 - v.2 ^ 2) := fun v => by
    rw [show (![v, v] : Fin 2 → ℝ × ℝ) = fun _ => v from by funext i; fin_cases i <;> rfl,
      iteratedFDeriv_diag_of_poly hC k v _ (saddle_line k v) 2 (by norm_num)]
    simp
  rw [hessianMatrix_eq_of_diag (hC.contDiffAt.of_le (by norm_num)) (d2 (1, 0)) (d2 (0, 1)) (d2 (1, 1))]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- FE-S2.2 applied to the saddle on the unit ball, uniformly over linear terms of norm ≤ 1. -/
theorem fe22_instance :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ Metric.closedBall (0 : (ℝ × ℝ) →L[ℝ] ℝ) 1 → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (k.1 ^ 2 - k.2 ^ 2 + L k)) * Complex.I) * A k‖ ≤ C * M / m :=
  stationaryPhaseFE (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) _ _ (by fun_prop) (isCompact_closedBall 0 1)
    (isCompact_closedBall 0 1) fun _ _ k _ _ => by rw [hessian_saddle, Matrix.det_fin_two]; norm_num

/-- FE-S4.1′ applied to the hyperbolic umbilic x³ + 2x²y + 3xy² + 5y³ (disc −367). -/
theorem fe41_hyperbolic :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ t →
      ‖∫ κ : ℝ × ℝ, Complex.exp (↑(t * OscInt.D4.genCubic 1 2 3 5 κ + L κ) * Complex.I) * A κ‖ ≤
        C * M * t ^ (-(2 : ℝ) / 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := ConvertSanity.d4FE_hyps_generic
  exact d4BoundFE _ 1 2 3 5 h1 h2 h3 h4

/-- C8 on the gradient (3, 4): the max-norm operator norm is 7, the Euclidean length 5 (`GradLower` holds for 5,
fails for 5.1). -/
theorem c8_values (k : ℝ × ℝ) :
    ‖fderiv ℝ (fun x : ℝ × ℝ => 3 * x.1 + 4 * x.2) k‖ = 7 ∧
      GradLower (fun x : ℝ × ℝ => 3 * x.1 + 4 * x.2) 0 k 5 ∧
      ¬ GradLower (fun x : ℝ × ℝ => 3 * x.1 + 4 * x.2) 0 k (51 / 10) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [NormAux.norm_prod_functional, sanity_fd_lin, sanity_fd_lin]; norm_num
  · simp only [GradLower, sanity_fd_lin]; norm_num
  · simp only [GradLower, sanity_fd_lin]; norm_num

end OscInt.API.Examples
