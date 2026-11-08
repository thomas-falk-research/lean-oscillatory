/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeExplicit

/-!
# Batch LE: the lead's assembly against the blueprint (route `docs/proof-LE.md`)

T0E from the parts P-angle, P-vdc2, P-vdc3 (split of `[−π, π]` into five pieces of length `π/2`), and T6E from T0E and
T6F. Compiled before any part was proved.
-/

namespace OscInt.LatticeExplicitAux

open Set OscInt.Statements OscInt.Blueprint

/-- The integrand of `latticeKernel1`. -/
noncomputable def lkf (t ξ : ℝ) (k : ℝ) : ℂ := Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)

theorem lkf_continuous (t ξ : ℝ) : Continuous (lkf t ξ) := by unfold lkf; fun_prop

theorem lkf_ii (t ξ a b : ℝ) : IntervalIntegrable (lkf t ξ) MeasureTheory.volume a b :=
  (lkf_continuous t ξ).intervalIntegrable a b

/-- `[−π, π]` as five pieces of length `π/2`. -/
theorem split_five (t ξ : ℝ) :
    latticeKernel1 t ξ = (∫ k in (-Real.pi)..(-(3 * Real.pi / 4)), Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)) +
      (∫ k in (-(3 * Real.pi / 4))..(-(Real.pi / 4)), Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)) +
      (∫ k in (-(Real.pi / 4))..(Real.pi / 4), Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)) +
      (∫ k in (Real.pi / 4)..(3 * Real.pi / 4), Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)) +
      (∫ k in (3 * Real.pi / 4)..Real.pi, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)) := by
  have h : ∀ a b : ℝ, IntervalIntegrable (fun k : ℝ => Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I))
      MeasureTheory.volume a b := lkf_ii t ξ
  rw [intervalIntegral.integral_add_adjacent_intervals (h _ _) (h _ _),
    intervalIntegral.integral_add_adjacent_intervals (h _ _) (h _ _),
    intervalIntegral.integral_add_adjacent_intervals (h _ _) (h _ _),
    intervalIntegral.integral_add_adjacent_intervals (h _ _) (h _ _)]
  rfl

/-- The angle condition on each piece, from P-angle. -/
theorem angles (hA : LEAngleFacts) :
    (∀ x ∈ Ioo (-Real.pi) (-(3 * Real.pi / 4)), (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.cos x|) ∧
    (∀ x ∈ Ioo (-(3 * Real.pi / 4)) (-(Real.pi / 4)), (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.sin x|) ∧
    (∀ x ∈ Ioo (-(Real.pi / 4)) (Real.pi / 4), (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.cos x|) ∧
    (∀ x ∈ Ioo (Real.pi / 4) (3 * Real.pi / 4), (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.sin x|) ∧
    (∀ x ∈ Ioo (3 * Real.pi / 4) Real.pi, (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.cos x|) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have := hA (x + Real.pi) (abs_le.mpr ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    rw [Real.cos_add_pi] at this
    exact this.trans (neg_le_abs _)
  · have := hA (x + Real.pi / 2) (abs_le.mpr ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    rw [Real.cos_add_pi_div_two] at this
    exact this.trans (neg_le_abs _)
  · exact (hA x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)).trans (le_abs_self _)
  · have := hA (x - Real.pi / 2) (abs_le.mpr ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    rw [Real.cos_sub_pi_div_two] at this
    exact this.trans (le_abs_self _)
  · have := hA (x - Real.pi) (abs_le.mpr ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    rw [Real.cos_sub_pi] at this
    exact this.trans (neg_le_abs _)

/-- **T0E** from the parts. -/
theorem t0e_of (hA : LEAngleFacts) (h2 : LEPiece2Facts) (h3 : LEPiece3Facts) : LatticeKernel1ExplicitStatement := by
  intro t ξ ht
  have hp := Real.pi_pos
  obtain ⟨a1, a2, a3, a4, a5⟩ := angles hA
  have b1 := h2 t ξ _ _ ht (by linarith) a1
  have b2 := h3 t ξ _ _ ht (by linarith) a2
  have b3 := h2 t ξ _ _ ht (by linarith) a3
  have b4 := h3 t ξ _ _ ht (by linarith) a4
  have b5 := h2 t ξ _ _ ht (by linarith) a5
  rw [split_five]
  set f : ℝ → ℂ := fun k => Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)
  set I1 := ∫ k in (-Real.pi)..(-(3 * Real.pi / 4)), f k
  set I2 := ∫ k in (-(3 * Real.pi / 4))..(-(Real.pi / 4)), f k
  set I3 := ∫ k in (-(Real.pi / 4))..(Real.pi / 4), f k
  set I4 := ∫ k in (Real.pi / 4)..(3 * Real.pi / 4), f k
  set I5 := ∫ k in (3 * Real.pi / 4)..Real.pi, f k
  linarith [norm_add_le (I1 + I2 + I3 + I4) I5, norm_add_le (I1 + I2 + I3) I4, norm_add_le (I1 + I2) I3,
    norm_add_le I1 I2]

/-- **T6E** from T0E and T6F. -/
theorem t6e_of (h0 : LatticeKernel1ExplicitStatement) (hF : LatticeKernelFactorStatement) :
    LatticeLaplacianExplicitStatement := by
  intro t x ht
  have ht0 : 0 < t := by linarith
  set A : ℝ := 24 * (2 : ℝ) ^ ((1 : ℝ) / 4)
  set B : ℝ := 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hle : t ^ (-(1 : ℝ) / 2) ≤ t ^ (-(1 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have hf : ∀ ξ : ℝ, ‖latticeKernel1 t ξ‖ ≤ (A + B) * t ^ (-(1 : ℝ) / 3) := fun ξ => by
    have := h0 t ξ ht0
    nlinarith [Real.rpow_nonneg ht0.le (-(1 : ℝ) / 3)]
  have hsq : (t ^ (-(1 : ℝ) / 3)) ^ 2 = t ^ (-(2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  rw [hF t x, norm_mul]
  calc ‖latticeKernel1 t (x.1 : ℝ)‖ * ‖latticeKernel1 t (x.2 : ℝ)‖
      ≤ ((A + B) * t ^ (-(1 : ℝ) / 3)) * ((A + B) * t ^ (-(1 : ℝ) / 3)) :=
        mul_le_mul (hf _) (hf _) (norm_nonneg _) (by positivity)
    _ = (A + B) ^ 2 * t ^ (-(2 : ℝ) / 3) := by rw [← hsq]; ring

end OscInt.LatticeExplicitAux
