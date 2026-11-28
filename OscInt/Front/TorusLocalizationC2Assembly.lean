/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.TorusLocalizationC2

/-!
# Batch LOC2: the lead's assembly from the blueprint parts

K2-FQ from `LocCoefFacts` (explicit summable coefficients, nearest-integer offsets) and `LocExpansionFacts` (the torus
expansion for a continuous cutoff). As K2's `torusLocalization_of`, with `n = round(t p)` and `δ = t p − n`.
-/

namespace OscInt.LOC2Aux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.LOC2

/-- K2-FQ from the coefficient bound and the expansion. -/
theorem torusLocalizationC2_of (hC : LocCoefFacts) (hE : LocExpansionFacts) : TorusLocalizationC2Statement := by
  intro χ hχ hsupp Ψ t p B hΨ hper1 hper2 hB
  set n : ℤ × ℤ := (round (t * p.1), round (t * p.2)) with hn
  set δ : ℝ × ℝ := (t * p.1 - round (t * p.1), t * p.2 - round (t * p.2)) with hδ
  have hδ1 : |δ.1| ≤ 1 / 2 := abs_sub_round _
  have hδ2 : |δ.2| ≤ 1 / 2 := abs_sub_round _
  obtain ⟨hsum, hle⟩ := hC χ hχ hsupp δ hδ1 hδ2
  set c : ℤ × ℤ → ℂ := fun j => ∫ k in torusBox, χ k *
    Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I) with hc
  set g : ℝ × ℝ → ℂ := fun k =>
    Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  have hexp := hE χ hχ.continuous hsupp δ hsum g hgc
  have hloc : (∫ k in torusBox, χ k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)) =
      ∫ k in torusBox, χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) * g k := by
    congr 1; funext k
    have hr : t * (Ψ k + lin p k) =
        (δ.1 * k.1 + δ.2 * k.2) + (t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) := by
      simp only [hδ, hn, lin]
      ring
    simp only [hg]
    rw [hr, Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]
  have hK : ∀ j : ℤ × ℤ, ‖∫ k in torusBox,
      Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k‖ ≤ B := by
    intro j
    have := hB (n.1 + j.1, n.2 + j.2)
    convert this using 3
    funext k
    simp only [hg]
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  set f : ℤ × ℤ → ℂ := fun j => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * c j *
    ∫ k in torusBox, Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k with hf
  have hfle : ∀ j, ‖f j‖ ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := by
    intro j
    simp only [hf, norm_mul]
    have h4 : ‖((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ)‖ = (4 * Real.pi ^ 2 : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h4]
    have := hK j
    have hc0 : 0 ≤ ‖c j‖ := norm_nonneg _
    have hpi : 0 ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ := by positivity
    calc (4 * Real.pi ^ 2 : ℝ)⁻¹ * ‖c j‖ * ‖∫ k in torusBox,
          Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k‖
        ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * ‖c j‖ * B := by gcongr
      _ = (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := by ring
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hK 0)
  have hsumf : Summable (fun j => ‖f j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hfle (hsum.mul_left _)
  rw [hloc, ← hexp.tsum_eq]
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  calc ‖∑' j, f j‖ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hsumf
    _ ≤ ∑' j, (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := hsumf.tsum_le_tsum hfle (hsum.mul_left _)
    _ = (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ∑' j, ‖c j‖ := tsum_mul_left
    _ ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * (4 * Real.pi ^ 2 * locConstC2 χ) := by gcongr
    _ = locConstC2 χ * B := by field_simp

end OscInt.LOC2Aux
