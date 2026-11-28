/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.StationaryPhase.Family
import OscInt.StationaryPhase.Change

/-!
# Batch A5U, part A13: `LocalTransferFacts`

Route: `docs/proof-A5U.md`, section 5. For `σ = ±1` let `L = σ · id` (a linear equivalence
of `ℝ²` with `|det L| = 1` and `‖L‖ ≤ 1`). For an amplitude `A'` on `closedBall (σ k₀ + c) δ`:
* the affine change `κ = c + L k` (`OscInt.StationaryPhase.affineChange`) turns `oscInt2 (φ + lin y) A'` into
  `oscInt2 (φ (c + L ·) + lin y (c + L ·)) A`, `A = A' (c + L ·)`;
* `φ (c + L k) = φ k` and `lin y (c + L k) = lin (σ y) k + lin y c`, so the phase is `φ + lin (σ y)` up to a
  constant, which only multiplies the integral by a unimodular factor;
* `A` satisfies `AmpBound 2` on the preimage of the ball, which is `closedBall k₀ δ`, with the same `M`
  (`OscInt.StationaryPhase.ampBoundAffine`, `max 1 ‖L‖ = 1`).
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements

/-- Adding a real constant to the phase multiplies `oscInt2` by a unimodular factor. -/
theorem a5uG2_norm_oscInt2_add_const (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (c₀ : ℝ) :
    ‖oscInt2 (fun k => Q k + c₀) A‖ = ‖oscInt2 Q A‖ := by
  unfold oscInt2
  have h : (fun k => Complex.exp (↑(Q k + c₀) * Complex.I) * A k) =
      fun k => Complex.exp (↑c₀ * Complex.I) * (Complex.exp (↑(Q k) * Complex.I) * A k) := by
    funext k
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  rw [h, integral_const_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The transfer along `κ ↦ c + L κ` for a linear equivalence `L = σ · id` with `|det L| = 1`, `‖L‖ ≤ 1`. -/
theorem a5uG2_transfer_of (φ : ℝ × ℝ → ℝ) (k₀ c : ℝ × ℝ) (σ δ B : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hLσ : ∀ κ, L κ = σ • κ) (hσ : |σ| = 1) (hdet : |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| = 1)
    (hnorm : ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 1) (hφ : ∀ κ, φ (σ • κ + c) = φ κ)
    (hB : ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M →
      ‖oscInt2 (fun κ => φ κ + lin y κ) A‖ ≤ B * M)
    (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (hA : AmpBound 2 (Metric.closedBall (σ • k₀ + c) δ) A M) :
    ‖oscInt2 (fun κ => φ κ + lin y κ) A‖ ≤ B * M := by
  have hA' := OscInt.StationaryPhase.ampBoundAffine 2 _ A M c L hA
  have hpre : (fun k => c + L k) ⁻¹' Metric.closedBall (σ • k₀ + c) δ = Metric.closedBall k₀ δ := by
    ext k
    simp only [mem_preimage, Metric.mem_closedBall, hLσ, dist_eq_norm]
    rw [show c + σ • k - (σ • k₀ + c) = σ • (k - k₀) by
      rw [smul_sub]; abel, norm_smul, Real.norm_eq_abs, hσ, one_mul]
  have hmax : max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 * M = M := by
    rw [max_eq_left hnorm, one_pow, one_mul]
  rw [hpre, hmax] at hA'
  rw [OscInt.StationaryPhase.affineChange _ A c L, hdet, Complex.ofReal_one, one_mul]
  have hph : (fun k => φ (c + L k) + lin y (c + L k)) = fun k => (φ k + lin (σ • y) k) + lin y c := by
    funext k
    rw [hLσ, add_comm c, hφ]
    simp only [lin, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hph, a5uG2_norm_oscInt2_add_const]
  exact hB _ M (σ • y) hA'

/-- `|det id| = 1` on `ℝ²`. -/
theorem a5uG2_det_refl :
    |LinearMap.det ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| = 1 := by
  rw [show (((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
    LinearMap.id from rfl, LinearMap.det_id, abs_one]

/-- `|det (−id)| = 1` on `ℝ²`. -/
theorem a5uG2_det_neg :
    |LinearMap.det ((ContinuousLinearEquiv.neg ℝ : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| = 1 := by
  rw [show (((ContinuousLinearEquiv.neg ℝ : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
    (-1 : ℝ) • LinearMap.id by ext <;> simp, LinearMap.det_smul, LinearMap.det_id, Module.finrank_prod,
    Module.finrank_self]
  norm_num

/-- `‖−id‖ ≤ 1` on `ℝ²`. -/
theorem a5uG2_norm_neg : ‖((ContinuousLinearEquiv.neg ℝ : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 1 := by
  rw [show ((ContinuousLinearEquiv.neg ℝ : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
    -ContinuousLinearMap.id ℝ (ℝ × ℝ) by ext <;> simp, norm_neg]
  exact ContinuousLinearMap.norm_id_le

/-- **A13** `LocalTransferFacts`. -/
theorem localTransfer : OscInt.Blueprint.A5U.LocalTransferFacts := by
  intro φ k₀ c σ δ B hσ hφ hB A M y hA
  rcases hσ with rfl | rfl
  · exact a5uG2_transfer_of φ k₀ c 1 δ B (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)) (fun κ => by simp)
      (by simp) a5uG2_det_refl ContinuousLinearMap.norm_id_le hφ hB A M y hA
  · exact a5uG2_transfer_of φ k₀ c (-1) δ B (ContinuousLinearEquiv.neg ℝ) (fun κ => by simp)
      (by simp) a5uG2_det_neg a5uG2_norm_neg hφ hB A M y hA

end OscInt.A5UAux
