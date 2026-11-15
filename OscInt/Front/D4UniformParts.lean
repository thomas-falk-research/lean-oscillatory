/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.D4UniformAssembly
import OscInt.D4.Final
import OscInt.D4.LimitFinal

/-! # Batch D4U, parts P-radius and P-linear (route `docs/proof-D4U.md`) -/

namespace OscInt.D4UniformAux

open Filter Topology OscInt.Statements OscInt.Blueprint.D4Uniform

/-- **P-radius** proved from S4.1′ (`OscInt.d4BoundNe`, at `y = 0`) and S4.2 (`OscInt.d4Limit`). -/
theorem commonRadius : CommonRadiusFacts := by
  intro φ hφ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hφ
  obtain ⟨δ₁, hδ₁, C₁, hB⟩ := OscInt.d4BoundNe φ h1 h4 h5
  obtain ⟨δ₂, hδ₂, hL⟩ := OscInt.d4Limit φ h1 h2 h3 h4 h5
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max C₁ 0, le_max_right _ _, ?_, ?_⟩
  · intro A M t hA ht
    have hA1 : AmpBound 2 (Metric.closedBall 0 δ₁) A M :=
      ⟨hA.1, hA.2.1.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)), hA.2.2⟩
    have h := hB A M 0 t hA1 ht
    have hlin : (fun κ => t * φ κ + lin 0 κ) = fun κ => t * φ κ := by funext κ; simp [lin]
    rw [hlin] at h
    have hM : 0 ≤ M := Aux.ampBound_nonneg hA
    have ht0 : 0 ≤ t ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) ht0)
  · intro A M hA
    exact hL A M ⟨hA.1, hA.2.1.trans (Metric.closedBall_subset_closedBall (min_le_right _ _)), hA.2.2⟩

theorem integrable_osc {Q : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ} {N : ℝ} (hQ : Continuous Q)
    (hK : IsCompact K) (hF : AmpBound 2 K F N) :
    MeasureTheory.Integrable (fun k => Complex.exp (↑(Q k) * Complex.I) * F k) := by
  have hc : HasCompactSupport F := hK.of_isClosed_subset (isClosed_tsupport _) hF.2.1
  have hcont : Continuous (fun k => Complex.exp (↑(Q k) * Complex.I) * F k) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hQ).mul continuous_const)).mul hF.1.continuous
  have hcs : HasCompactSupport (fun k => Complex.exp (↑(Q k) * Complex.I) * F k) :=
    IsCompact.of_isClosed_subset hc (isClosed_tsupport _) tsupport_mul_subset_right
  exact hcont.integrable_of_hasCompactSupport hcs

/-- **P-linear**. -/
theorem linear : LinearFacts := by
  intro Q K A B M M' hQ hK hA hB
  unfold oscInt2
  rw [← MeasureTheory.integral_sub (integrable_osc hQ hK hA) (integrable_osc hQ hK hB)]
  congr 1
  funext k
  simp only [Pi.sub_apply]
  ring

end OscInt.D4UniformAux
