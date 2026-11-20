/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.HadamardWalk

/-!
# Batch HW: the lead's assembly against the blueprint (route `docs/proof-HW.md`)

HW-R from the kernel at times `0`, `1` and its recursion in time, by induction; HW-D from HW-R, HW-K, the kernel at
time `0` and one arithmetic fact; HW-L from HW-D and the decomposition of a walk into translated walks from point
states. HW-K itself is a part. Written after the stamp of the review answers
(`stamps/20261117T010311Z-a93c4e1e44f7`) and compiled before any part was proved.
-/

namespace OscInt.HadamardWalkAux

open OscInt.Statements OscInt.Blueprint.HadamardWalk

/-- `√2 · √2 = 2` in `ℂ`. -/
theorem hw_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `√2 ≠ 0` in `ℂ`. -/
theorem hw_sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- `(√2)⁻¹ · (√2)⁻¹ = 1/2` in `ℂ`. -/
theorem hw_inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, hw_sqrt_two_mul_self]; norm_num

/-- **HW-R** from the kernel at times `0`, `1` and its recursion, by induction on the time. -/
theorem hadamardKernelFormula_of (h : HadamardKernelRecFacts) : HadamardKernelStatement := by
  intro a b t
  induction t with
  | zero =>
    intro x
    simp only [hadamardWalk, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      hadamardStep, pointState, zero_add, h.1, h.2.1, mul_zero, add_zero]
    by_cases h1 : x + 1 = 0 <;> by_cases h2 : x - 1 = 0 <;> simp [h1, h2]
  | succ t ih =>
    intro x
    have hstep : hadamardWalk (pointState a b) (t + 1 + 1) x =
        hadamardStep (hadamardWalk (pointState a b) (t + 1)) x := by
      simp only [hadamardWalk, Function.iterate_succ_apply']
    rw [hstep]
    simp only [hadamardStep, ih (x + 1), ih (x - 1)]
    have e1 : x + 1 + 1 = x + 2 := by ring
    have e2 : x + 1 - 1 = x := by ring
    have e3 : x - 1 + 1 = x := by ring
    have e4 : x - 1 - 1 = x - 2 := by ring
    have r1 := h.2.2 t (x + 1)
    have r2 := h.2.2 t (x - 1)
    rw [e1, e2] at r1
    rw [e3, e4] at r2
    rw [e1, e2, e3, e4, show t + 1 + 1 = t + 2 from rfl, r1, r2]
    have hc := hw_inv_sqrt_two_mul_self
    refine Prod.ext ?_ ?_
    · simp only [div_eq_mul_inv]
      linear_combination (2 * a * hadamardKernel (t + 1) x) * hc
    · simp only [div_eq_mul_inv]
      linear_combination (2 * b * hadamardKernel (t + 1) x) * hc

/-- One component of HW-R, bounded: `|c/√2 · K₁ + d · K₀| ≤ A (B₁/√2 + B₀)` when `|c|, |d| ≤ A`, `|K₁| ≤ B₁` and
`|K₀| ≤ B₀`. -/
theorem hw_component_le (c d K1 K0 : ℂ) (A B1 B0 : ℝ) (hc : ‖c‖ ≤ A) (hd : ‖d‖ ≤ A) (h1 : ‖K1‖ ≤ B1)
    (h0 : ‖K0‖ ≤ B0) : ‖c / ((Real.sqrt 2 : ℝ) : ℂ) * K1 + d * K0‖ ≤ A * (B1 / Real.sqrt 2 + B0) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hA : 0 ≤ A := (norm_nonneg c).trans hc
  have hB1 : 0 ≤ B1 := (norm_nonneg K1).trans h1
  have hn : ‖c / ((Real.sqrt 2 : ℝ) : ℂ)‖ = ‖c‖ / Real.sqrt 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc ‖c / ((Real.sqrt 2 : ℝ) : ℂ) * K1 + d * K0‖
      ≤ ‖c‖ / Real.sqrt 2 * ‖K1‖ + ‖d‖ * ‖K0‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, hn]
    _ ≤ A / Real.sqrt 2 * B1 + A * B0 := by gcongr
    _ = A * (B1 / Real.sqrt 2 + B0) := by ring

/-- **HW-D** from HW-R, HW-K, the kernel at time `0` and the arithmetic of the two bounds. -/
theorem hadamardDecay_of (hRec : HadamardKernelRecFacts) (hR : HadamardKernelStatement)
    (hK : HadamardKernelBoundStatement) (hA : HadamardDecayArithFacts) : HadamardDecayStatement := by
  intro a b t x ht
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [hR a b s x]
  have hab : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hab' : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have ha : ‖a‖ ≤ ‖a‖ + ‖b‖ := le_add_of_nonneg_right (norm_nonneg b)
  have hb : ‖b‖ ≤ ‖a‖ + ‖b‖ := le_add_of_nonneg_left (norm_nonneg a)
  have hAB : 0 ≤ ‖a‖ + ‖b‖ := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hbound : ∃ B1 B0 : ℝ, (∀ y : ℤ, ‖hadamardKernel (s + 1) y‖ ≤ B1) ∧ (∀ y : ℤ, ‖hadamardKernel s y‖ ≤ B0) ∧
      B1 / Real.sqrt 2 + B0 ≤ 39 * ((s + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      refine ⟨19, 0, fun y => ?_, fun y => by rw [hRec.1 y, norm_zero], ?_⟩
      · have h := hK 1 y le_rfl
        simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
        linarith
      · have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
        have h2 : (19 : ℝ) / Real.sqrt 2 ≤ 19 := div_le_self (by norm_num) h1
        simp only [zero_add, Nat.cast_one, Real.one_rpow, mul_one, add_zero]
        linarith
    · exact ⟨_, _, fun y => hK (s + 1) y (by omega), fun y => hK s y hs, hA s hs⟩
  obtain ⟨B1, B0, h1, h0, hB⟩ := hbound
  constructor
  · calc ‖(a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * hadamardKernel (s + 1) (x + 1) + a * hadamardKernel s x‖
        ≤ (‖a‖ + ‖b‖) * (B1 / Real.sqrt 2 + B0) := hw_component_le _ _ _ _ _ _ _ hab ha (h1 _) (h0 _)
      _ ≤ (‖a‖ + ‖b‖) * (39 * ((s + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) := by gcongr
      _ = 39 * (‖a‖ + ‖b‖) * ((s + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by ring
  · calc ‖(a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * hadamardKernel (s + 1) (x - 1) + b * hadamardKernel s x‖
        ≤ (‖a‖ + ‖b‖) * (B1 / Real.sqrt 2 + B0) := hw_component_le _ _ _ _ _ _ _ hab' hb (h1 _) (h0 _)
      _ ≤ (‖a‖ + ‖b‖) * (39 * ((s + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) := by gcongr
      _ = 39 * (‖a‖ + ‖b‖) * ((s + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) := by ring

/-- **HW-L** from HW-D and the decomposition of the walk into translated walks from point states. -/
theorem hadamardDispersive_of (hD : HadamardDecayStatement) (hL : HadamardLinearFacts) :
    HadamardDispersiveStatement := by
  intro ψ₀ t x hfin ht
  have hsupp : ∀ y : ℤ, y ∉ hfin.toFinset → ψ₀ y = (0, 0) := by
    intro y hy
    by_contra h
    exact hy (hfin.mem_toFinset.mpr h)
  have hsum : ∑ᶠ y : ℤ, (‖(ψ₀ y).1‖ + ‖(ψ₀ y).2‖) = ∑ y ∈ hfin.toFinset, (‖(ψ₀ y).1‖ + ‖(ψ₀ y).2‖) := by
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    rw [Finset.mem_coe, hfin.mem_toFinset]
    intro h0
    apply hy
    show ‖(ψ₀ y).1‖ + ‖(ψ₀ y).2‖ = 0
    rw [h0]
    simp
  rw [hL ψ₀ hfin.toFinset t x hsupp, hsum, Prod.fst_sum, Prod.snd_sum, Finset.mul_sum, Finset.sum_mul]
  constructor
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (hD _ _ t (x - y) ht).1)
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (hD _ _ t (x - y) ht).2)

end OscInt.HadamardWalkAux
