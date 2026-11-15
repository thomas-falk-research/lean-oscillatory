/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4Uniform

/-!
# Batch D4U: the assembly of S4.2U and S4.2O from the parts (route `docs/proof-D4U.md`)

Compiled before any part was proved (first in `Blueprint/D4Uniform.lean` at 378d5ae; moved here unchanged, so that the
blueprint library holds definitions only, as for the other batches).
-/

namespace OscInt.D4UniformAux

open Filter Topology OscInt.Statements OscInt.Blueprint.D4Uniform

theorem Aux.ampBound_nonneg {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound 2 K A M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0 (by norm_num) 0)

/-- The error of the limit is controlled on a net: the core estimate of the assembly. -/
theorem Aux.err_split (hL : LinearFacts) {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {A b : ℝ × ℝ → ℂ} {M M' : ℝ} (hA : AmpBound 2 K A M) (hb : AmpBound 2 K b M') (t : ℝ) (c : ℂ) :
    ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) A - c * A 0 =
      (((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) b - c * b 0) +
        (((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) (A - b) - c * (A - b) 0) := by
  rw [hL (fun κ => t * φ κ) K A b M M' (continuous_const.mul hφ) hK hA hb, Pi.sub_apply]
  ring

/-- **S4.2U** from P-radius and P-linear. -/
theorem d4LimitUniform_of (hR : CommonRadiusFacts) (hL : LinearFacts) : D4LimitUniformStatement := by
  intro φ hφ
  obtain ⟨δ, hδ, C, hC0, hB, hlim⟩ := hR φ hφ
  have hφc : Continuous φ := hφ.1.continuous
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) δ) := isCompact_closedBall 0 δ
  refine ⟨δ, hδ, fun S hS ε hε => ?_⟩
  set c : ℂ := (d4Constant (cubicCoeffs φ) : ℂ)
  have hD : 0 < C + ‖c‖ + 1 := by positivity
  set η : ℝ := ε / (2 * (C + ‖c‖ + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨F, hF, hFS, hcov⟩ := hS.2 η hη
  have hev : ∀ᶠ t : ℝ in atTop, ∀ b ∈ F,
      ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) b - c * b 0‖ < ε / 2 := by
    rw [Filter.eventually_all_finite hF]
    intro b hb
    obtain ⟨M, hM⟩ := hS.1 b (hFS hb)
    have := (hlim b M hM).sub_const (c * b 0)
    rw [sub_self] at this
    exact (tendsto_iff_norm_sub_tendsto_zero.mp this |>.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).mono
      (fun t ht => by simpa using ht)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 1))
  refine ⟨T₀, fun t ht A hA => ?_⟩
  obtain ⟨hnet, ht1⟩ := hT₀ t ht
  obtain ⟨b, hbF, hAb⟩ := hcov A hA
  obtain ⟨MA, hMA⟩ := hS.1 A hA
  obtain ⟨Mb, hMb⟩ := hS.1 b (hFS hbF)
  rw [Aux.err_split hL hφc hK hMA hMb t c]
  have h1 := hnet b hbF
  have h2 : ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) (A - b)‖ ≤ C * η := by
    have ht0 : 0 < t := by linarith
    have hbd := hB (A - b) η t hAb ht1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc t ^ ((2 : ℝ) / 3) * ‖oscInt2 (fun κ => t * φ κ) (A - b)‖
        ≤ t ^ ((2 : ℝ) / 3) * (C * η * t ^ (-(2 : ℝ) / 3)) := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = C * η * (t ^ ((2 : ℝ) / 3) * t ^ (-(2 : ℝ) / 3)) := by ring
      _ = C * η := by rw [← Real.rpow_add ht0]; norm_num
  have h3 : ‖c * (A - b) 0‖ ≤ ‖c‖ * η := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := hAb.2.2 0 (by norm_num) 0
    rwa [norm_iteratedFDeriv_zero] at this
  have heta : (C + ‖c‖ + 1) * η = ε / 2 := by
    rw [hη_def]; field_simp
  have hsum : C * η + ‖c‖ * η < ε / 2 := by nlinarith [heta, hη]
  calc ‖_ + _‖ ≤ ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) b - c * b 0‖ +
        ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) (A - b) - c * (A - b) 0‖ := norm_add_le _ _
    _ ≤ ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) b - c * b 0‖ + (C * η + ‖c‖ * η) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h2 h3)
    _ < ε := by linarith [h1, hsum]

/-- **S4.2O** from S4.2U and P-mod. -/
theorem d4LimitOffset_of (hU : D4LimitUniformStatement) (hM : ModulationFacts) : D4LimitOffsetStatement := by
  intro φ hφ
  obtain ⟨δ, hδ, hU'⟩ := hU φ hφ
  refine ⟨δ, hδ, fun A M hA R ε hε => ?_⟩
  obtain ⟨T, hT⟩ := hU' _ (hM δ A M R hδ hA) ε hε
  refine ⟨T, fun t ht y hy => ?_⟩
  have h := hT t ht _ ⟨y, hy, rfl⟩
  have hint : oscInt2 (fun κ => t * φ κ + lin y κ) A =
      oscInt2 (fun κ => t * φ κ) (fun κ => Complex.exp (↑(lin y κ) * Complex.I) * A κ) := by
    unfold oscInt2
    congr 1
    funext κ
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h0 : Complex.exp (↑(lin y 0) * Complex.I) * A 0 = A 0 := by
    simp [lin]
  rw [hint]
  rwa [h0] at h

end OscInt.D4UniformAux
