/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.HadamardWalk

/-!
# Batch HW, part HW4: the arithmetic of HW-D and the linear decomposition of a walk (route `docs/proof-HW.md`)

`hadamardDecayArithFacts` (H7): for `t ≥ 1` and `T = t + 1`, with `t ≥ T/2` and `T ≥ 1`,
`t^{−1/2} ≤ √2 T^{−1/2}`, `t^{−1/3} ≤ 1.26 T^{−1/3}`, `T^{−1/2} ≤ T^{−1/3}`, and
`19/√2 + 7√2 + 12 · 1.26 ≤ 39`.

`hadamardLinearFacts` (H8): the step is additive and commutes with translations of the lattice; induction on the
time, for all sites at once.
-/

namespace OscInt.HadamardWalkAux

open OscInt.Statements OscInt.Blueprint.HadamardWalk

/-! ## The arithmetic of HW-D -/

/-- `√2 · √2 = 2` in `ℝ`. -/
theorem hwAr_sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- `√2 ≤ 1.4143`. -/
theorem hwAr_sqrt_two_le : Real.sqrt 2 ≤ 1.4143 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `2^{−1/2} = (√2)⁻¹`. -/
theorem hwAr_two_rpow_neg_half : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]
  congr 1
  ring

/-- `2^{1/3} ≤ 1.26`, because `1.26³ ≥ 2`. -/
theorem hwAr_two_rpow_third_le : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 1.26 := by
  have h1 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ ((1.26 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have h2 : ((1.26 : ℝ) ^ (3 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) = 1.26 :=
    Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h3 : (((3 : ℕ) : ℝ)⁻¹) = (1 : ℝ) / 3 := by norm_num
  rw [h3] at h2
  rw [h2] at h1
  exact h1

/-- `2^{−1/3} = (2^{1/3})⁻¹`. -/
theorem hwAr_two_rpow_neg_third : (2 : ℝ) ^ (-(1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
  rw [← Real.rpow_neg (by norm_num)]
  congr 1
  ring

/-- For `0 < T ≤ 2 t`: `t^{−1/2} ≤ √2 · T^{−1/2}`. -/
theorem hwAr_half_le {t T : ℝ} (hT : 0 < T) (h : T / 2 ≤ t) :
    t ^ (-(1 : ℝ) / 2) ≤ Real.sqrt 2 * T ^ (-(1 : ℝ) / 2) := by
  have h1 : t ^ (-(1 : ℝ) / 2) ≤ (T / 2) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)
  have h2 : (T / 2) ^ (-(1 : ℝ) / 2) = Real.sqrt 2 * T ^ (-(1 : ℝ) / 2) := by
    rw [Real.div_rpow hT.le (by norm_num), hwAr_two_rpow_neg_half, div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  exact h1

/-- For `0 < T ≤ 2 t`: `t^{−1/3} ≤ 1.26 · T^{−1/3}`. -/
theorem hwAr_third_le {t T : ℝ} (hT : 0 < T) (h : T / 2 ≤ t) :
    t ^ (-(1 : ℝ) / 3) ≤ 1.26 * T ^ (-(1 : ℝ) / 3) := by
  have h1 : t ^ (-(1 : ℝ) / 3) ≤ (T / 2) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)
  have h2 : (T / 2) ^ (-(1 : ℝ) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) * T ^ (-(1 : ℝ) / 3) := by
    rw [Real.div_rpow hT.le (by norm_num), hwAr_two_rpow_neg_third, div_inv_eq_mul, mul_comm]
  have h3 : 0 ≤ T ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg hT.le _
  calc t ^ (-(1 : ℝ) / 3) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) * T ^ (-(1 : ℝ) / 3) := h2 ▸ h1
    _ ≤ 1.26 * T ^ (-(1 : ℝ) / 3) := mul_le_mul_of_nonneg_right hwAr_two_rpow_third_le h3

/-- The arithmetic with the four powers as real variables: `a = T^{−1/2}`, `b = T^{−1/3}`, `c = t^{−1/2}`,
`d = t^{−1/3}`, `s = √2`. -/
theorem hwAr_core {a b c d s : ℝ} (hs : s * s = 2) (hs0 : 0 < s) (hs1 : s ≤ 1.4143) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : c ≤ s * a) (hd : d ≤ 1.26 * b) : (7 * a + 12 * b) / s + (7 * c + 12 * d) ≤ 39 * b := by
  have hb : 0 ≤ b := ha.trans hab
  have h1 : (7 * a + 12 * b) / s = (7 * a + 12 * b) * s / 2 := by
    field_simp
    nlinarith [hs]
  have h2 : (7 * a + 12 * b) * s ≤ 19 * b * 1.4143 :=
    mul_le_mul (by linarith) hs1 hs0.le (by linarith)
  have h3 : s * a ≤ 1.4143 * b := mul_le_mul hs1 hab ha (by norm_num)
  rw [h1]
  linarith

/-- **H-arith** The arithmetic of HW-D. -/
theorem hadamardDecayArithFacts : HadamardDecayArithFacts := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hT : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by push_cast; ring
  have hT1 : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by rw [hT]; linarith
  have hT0 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by linarith
  have hhalf : ((t + 1 : ℕ) : ℝ) / 2 ≤ (t : ℝ) := by rw [hT]; linarith
  exact hwAr_core hwAr_sqrt_two_mul_self (Real.sqrt_pos.mpr (by norm_num)) hwAr_sqrt_two_le
    (Real.rpow_nonneg hT0.le _)
    (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num))
    (hwAr_half_le hT0 hhalf) (hwAr_third_le hT0 hhalf)

/-! ## The linear decomposition -/

/-- The step is additive over a finite sum of states. -/
theorem hwLin_step_sum (S : Finset ℤ) (F : ℤ → ℤ → ℂ × ℂ) (x : ℤ) :
    hadamardStep (fun z => ∑ y ∈ S, F y z) x = ∑ y ∈ S, hadamardStep (F y) x := by
  apply Prod.ext
  · simp only [hadamardStep, Prod.fst_sum, Prod.snd_sum]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  · simp only [hadamardStep, Prod.fst_sum, Prod.snd_sum]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- The step commutes with the translations of the lattice. -/
theorem hwLin_step_translate (G : ℤ → ℂ × ℂ) (y x : ℤ) :
    hadamardStep (fun z => G (z - y)) x = hadamardStep G (x - y) := by
  simp only [hadamardStep]
  rw [show x + 1 - y = x - y + 1 by ring, show x - 1 - y = x - y - 1 by ring]

/-- One more step of the walk, applied last. -/
theorem hwLin_walk_succ (ψ₀ : ℤ → ℂ × ℂ) (t : ℕ) :
    hadamardWalk ψ₀ (t + 1) = hadamardStep (hadamardWalk ψ₀ t) :=
  Function.iterate_succ_apply' hadamardStep t ψ₀

/-- A state that vanishes outside `S` is the sum over `S` of its translated point states. -/
theorem hwLin_zero (ψ₀ : ℤ → ℂ × ℂ) (S : Finset ℤ) (h : ∀ y : ℤ, y ∉ S → ψ₀ y = (0, 0)) (x : ℤ) :
    ψ₀ x = ∑ y ∈ S, pointState (ψ₀ y).1 (ψ₀ y).2 (x - y) := by
  rw [Finset.sum_eq_single x]
  · simp [pointState]
  · intro y _ hyx
    have hne : x - y ≠ 0 := fun h0 => hyx (by omega)
    simp [pointState, hne]
  · intro hx
    rw [h x hx]
    simp [pointState]

/-- The decomposition as an equality of states, by induction on the time. -/
theorem hwLin_walk (ψ₀ : ℤ → ℂ × ℂ) (S : Finset ℤ) (h : ∀ y : ℤ, y ∉ S → ψ₀ y = (0, 0)) (t : ℕ) :
    hadamardWalk ψ₀ t = fun x => ∑ y ∈ S, hadamardWalk (pointState (ψ₀ y).1 (ψ₀ y).2) t (x - y) := by
  induction t with
  | zero =>
    funext x
    exact hwLin_zero ψ₀ S h x
  | succ t ih =>
    funext x
    rw [hwLin_walk_succ, ih, hwLin_step_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hwLin_walk_succ]
    exact hwLin_step_translate _ y x

/-- **H-lin** The walk from a state supported in a finite set is the sum of the translated walks from point
states. -/
theorem hadamardLinearFacts : HadamardLinearFacts := by
  intro ψ₀ S t x h
  exact congrFun (hwLin_walk ψ₀ S h t) x

end OscInt.HadamardWalkAux
