/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.GlobalSanity

/-! # GD-N through the statement constant on a phase that is `C⁴` only on `U`

Review follow-up b2 (`review/2026-11-08-GD-post-proof-answers.md`). `globalNondeg_quad` uses a polynomial phase, so a
plant replacing `ContDiffOn ℝ 4 Ψ U` by `ContDiff ℝ 4 Ψ` (or `U` by `Set.univ`) is still discharged there. Here the
phase is `Ψ = x² + 3xy + 5y² + |x − 3|`: on `U = B(0, 2)` (max norm, so `|x| < 2`) it equals the polynomial
`x² + 3xy + 5y² + 3 − x`, hence it is `C⁴` on `U` with `det H = 11` on `K = B̄(0, 1)`; along `x = 3` it is not
differentiable, so `ContDiff ℝ 1 Ψ` is false (`localPhase_not_contDiff`). Planted copies with compiler output:
`docs/replay/plants/2026-11-08-GDN-local/`.
-/

namespace OscInt.API.GlobalSanity

open OscInt.Statements OscInt.API.ConvertSanity Filter Topology

/-- `Ψ = x² + 3xy + 5y² + |x − 3|`: smooth on `{x < 3}`, not differentiable on `{x = 3}`. -/
noncomputable def localPhase (k : ℝ × ℝ) : ℝ := quadPhase k + |k.1 - 3|

/-- The polynomial that `localPhase` equals on `{x < 3}`. -/
def localPhaseSmooth (k : ℝ × ℝ) : ℝ := quadPhase k + (-1 * k.1 + 3)

theorem localPhaseSmooth_contDiff : ContDiff ℝ 4 localPhaseSmooth := by
  unfold localPhaseSmooth quadPhase; fun_prop

theorem localPhase_eq_of_lt {k : ℝ × ℝ} (hk : k.1 < 3) : localPhase k = localPhaseSmooth k := by
  unfold localPhase localPhaseSmooth
  rw [abs_of_neg (by linarith)]; ring

theorem fst_lt_of_mem_ball {k : ℝ × ℝ} (hk : k ∈ Metric.ball (0 : ℝ × ℝ) 2) : k.1 < 3 := by
  rw [mem_ball_zero_iff] at hk
  have h1 : |k.1| < 2 := lt_of_le_of_lt (norm_fst_le k) hk
  linarith [le_abs_self k.1]

theorem localPhase_eventuallyEq {k : ℝ × ℝ} (hk : k ∈ Metric.ball (0 : ℝ × ℝ) 2) :
    localPhase =ᶠ[𝓝 k] localPhaseSmooth :=
  Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hk) fun _ hy => localPhase_eq_of_lt (fst_lt_of_mem_ball hy)

theorem localPhase_contDiffOn : ContDiffOn ℝ 4 localPhase (Metric.ball 0 2) :=
  localPhaseSmooth_contDiff.contDiffOn.congr fun _ hk => localPhase_eq_of_lt (fst_lt_of_mem_ball hk)

/-- `localPhase (t + 3, 0) − quadPhase (t + 3, 0) = |t|`, so `localPhase` is not differentiable at `(3, 0)`. -/
theorem localPhase_not_contDiff : ¬ ContDiff ℝ 1 localPhase := by
  intro h
  have hq : Differentiable ℝ quadPhase := by unfold quadPhase; fun_prop
  have hl : Differentiable ℝ localPhase := h.differentiable one_ne_zero
  have hd : DifferentiableAt ℝ (fun t : ℝ => localPhase (t + 3, 0) - quadPhase (t + 3, 0)) 0 := by
    fun_prop
  have he : (fun t : ℝ => localPhase (t + 3, 0) - quadPhase (t + 3, 0)) = (abs : ℝ → ℝ) := by
    funext t; simp [localPhase]
  exact not_differentiableAt_abs_zero (he ▸ hd)

/-- The hypotheses of the two smoothness plants are false for `localPhase`: plant (a), `ContDiff ℝ 4 Ψ`. -/
theorem localPhase_not_contDiff_four : ¬ ContDiff ℝ 4 localPhase :=
  fun h => localPhase_not_contDiff (h.of_le (by norm_num))

/-- Plant (b), `ContDiffOn ℝ 4 Ψ Set.univ`. -/
theorem localPhase_not_contDiffOn_univ : ¬ ContDiffOn ℝ 4 localPhase Set.univ :=
  fun h => localPhase_not_contDiff_four (contDiffOn_univ.mp h)

theorem iteratedFDeriv_two_affine (k a b : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (fun k : ℝ × ℝ => -1 * k.1 + 3) k ![a, b] = 0 := by
  rw [iteratedFDeriv_two_eq_dd (by fun_prop), dd]
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => -1 * k.1 + 3) y b) = fun _ => -1 * b.1 := by
    funext y; exact sanity_fd_lin_const y b (-1) 3
  rw [this]; simp

theorem hessian_localPhaseSmooth (k : ℝ × ℝ) : hessianMatrix localPhaseSmooth k = hessianMatrix quadPhase k := by
  have hq : ContDiff ℝ 2 quadPhase := by unfold quadPhase; fun_prop
  have ha : ContDiff ℝ 2 (fun k : ℝ × ℝ => -1 * k.1 + 3) := by fun_prop
  ext i j
  have hs : localPhaseSmooth = quadPhase + fun k : ℝ × ℝ => -1 * k.1 + 3 := rfl
  simp only [hessianMatrix, Matrix.of_apply]
  rw [hs, iteratedFDeriv_add_apply hq.contDiffAt ha.contDiffAt, _root_.add_apply,
    iteratedFDeriv_two_affine, add_zero]

/-- On the open ball the Hessian of `localPhase` is that of `x² + 3xy + 5y²`: `det = 11`. -/
theorem det_hessian_localPhase {k : ℝ × ℝ} (hk : k ∈ Metric.ball (0 : ℝ × ℝ) 2) :
    (hessianMatrix localPhase k).det = 11 := by
  have h : hessianMatrix localPhase k = hessianMatrix localPhaseSmooth k := by
    unfold hessianMatrix; rw [((localPhase_eventuallyEq hk).iteratedFDeriv ℝ 2).eq_of_nhds]
  rw [h, hessian_localPhaseSmooth]; unfold quadPhase; exact (hessian_mixed k).2

theorem localPhase_nondeg (k : ℝ × ℝ) (hk : k ∈ Metric.closedBall (0 : ℝ × ℝ) 1) :
    (hessianMatrix localPhase k).det ≠ 0 := by
  rw [det_hessian_localPhase (Metric.closedBall_subset_ball (by norm_num) hk)]; norm_num

/-- **GD-N through the statement constant, `C⁴` only on `U`.** `Ψ = x² + 3xy + 5y² + |x − 3|`, `K = B̄(0, 1)`,
`U = B(0, 2)`, all linear terms. Plants detected (besides those of `globalNondeg_quad`): `ContDiffOn ℝ 4 Ψ U ↦
ContDiff ℝ 4 Ψ` and `ContDiffOn ℝ 4 Ψ U ↦ ContDiffOn ℝ 4 Ψ Set.univ` (`localPhase_not_contDiff`). Not detected:
weakening plants. -/
theorem globalNondeg_local (h : GlobalNondegStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (localPhase k + L k)) * Complex.I) * A k‖ ≤ C * M / m :=
  h localPhase (Metric.closedBall 0 1) (Metric.ball 0 2)
    (isCompact_closedBall _ _) Metric.isOpen_ball (Metric.closedBall_subset_ball (by norm_num))
    localPhase_contDiffOn localPhase_nondeg

end OscInt.API.GlobalSanity
