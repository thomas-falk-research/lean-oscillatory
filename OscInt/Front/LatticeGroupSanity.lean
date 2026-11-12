/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeGroup
import OscInt.Front.HypercubicSanity

/-! # Sanity theorems through the batch-LS statement constants

As for batches LE, LE2 and HC (lessons 33, 38, 44, 47): every theorem about a frozen statement of
`OscInt/Statements/LatticeGroup.lean` takes that statement constant as its hypothesis (with LS-E supplying a solution
for the closed datum `δ₀`), discharges its hypotheses on closed data and concludes its conclusion there. Planted copies:
`docs/replay/plants/2026-11-12-LS/`.

Data:
* Unconditional: `G_d(0, 0) = 1` for every `d` (pins the normalisation `(2π)^{−d}` and the box); `δ₀` has
  `ℓ¹` norm 1.
* LS-K with LS-E: `G_d(0, x) = δ₀(x)` for every `d` and `x` (a normalisation plant is refuted semantically).
* LS-D with LS-E at `d = 1`, `t = 4`, `x = 0`: `|u(4, 0)| ≤ C*/(4π) < 1` (non-trivial regime, lessons 47); at `d = 2`,
  `t = 4`: `(C*/(2π))²/4 < 1` (a datum with `3 ∤ d`); bite: the bound is false at `t = 0`.
* LS-D′ with LS-E at `d = 1`, `t = 7`: `|u(7, 0)| ≤ (1 + τ)^{1/3}/2 < 1` (non-trivial regime); bite: the bound without
  the `1 +` in `(1 + |t|)` is false at `t = 0`.
* What this layer cannot see: the gauge `e^{−2idt}`, the factor 2 in `K_d(2t, ·)` and the sign of `i` in the equation
  are invisible at `t = 0` and are not tested semantically; a mutation of them makes LS-K false and is caught by its
  proof, not here.
-/

namespace OscInt.API.LatticeGroupSanity

open OscInt.Statements OscInt.API.HypercubicSanity

/-- The datum `δ₀ ∈ ℓ²(ℤ^d)`. -/
noncomputable def delta0 (d : ℕ) : LatticeL2 d := lp.single 2 0 1

theorem delta0_apply (d : ℕ) (y : Fin d → ℤ) : (delta0 d : (Fin d → ℤ) → ℂ) y = if y = 0 then 1 else 0 := by
  simp [delta0, Pi.single_apply]

theorem delta0_hasSum (d : ℕ) : HasSum (fun y : Fin d → ℤ => ‖(delta0 d : (Fin d → ℤ) → ℂ) y‖) 1 := by
  have h := hasSum_single (f := fun y : Fin d → ℤ => ‖(delta0 d : (Fin d → ℤ) → ℂ) y‖) (0 : Fin d → ℤ)
    (fun y hy => by simp [delta0_apply, hy])
  simpa [delta0_apply] using h

theorem delta0_summable (d : ℕ) : Summable (fun y : Fin d → ℤ => ‖(delta0 d : (Fin d → ℤ) → ℂ) y‖) :=
  (delta0_hasSum d).summable

theorem delta0_tsum (d : ℕ) : ∑' y : Fin d → ℤ, ‖(delta0 d : (Fin d → ℤ) → ℂ) y‖ = 1 :=
  (delta0_hasSum d).tsum_eq

/-- **Unconditional**: `G_d(0, 0) = 1`. -/
theorem schrodingerKernel_zero_zero (d : ℕ) : schrodingerKernel d 0 0 = 1 := by
  have h2 : (2 : ℝ) * 0 = 0 := mul_zero 2
  simp only [schrodingerKernel, h2, hypercubicKernel_zero_zero, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  have hpos : (((2 * Real.pi) ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ((2 * Real.pi) ^ d : ℝ) ≠ 0)
  exact inv_mul_cancel₀ hpos

/-- **LS-K with LS-E**: `G_d(0, x) = δ₀(x)`. -/
theorem kernel_zero_time (hE : LatticeSchrodingerExistsStatement) (hK : LatticeSchrodingerKernelStatement)
    (d : ℕ) (x : Fin d → ℤ) : schrodingerKernel d 0 x = if x = 0 then 1 else 0 := by
  obtain ⟨u, hu⟩ := hE d (delta0 d)
  have h := (hK d _ u hu 0 x).2
  rw [hu.1, tsum_eq_single 0 (fun y hy => by simp [delta0_apply, hy])] at h
  simpa [delta0_apply] using h.symm

/-- `C*/(2π) < 31/20`. -/
theorem cstar_div_two_pi_lt : 8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi) < 31 / 20 := by
  have hs : Real.sqrt 7 < 2.6458 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi := Real.pi_gt_d2
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem cstar_div_two_pi_pos : 0 < 8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi) := by positivity

/-- `8^{−1/3} = 1/2`. -/
theorem eight_rpow_neg_third : (8 : ℝ) ^ (-(1 : ℝ) / 3) = 1 / 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg_one]

/-- `8^{−2/3} = 1/4`. -/
theorem eight_rpow_neg_two_thirds' : (8 : ℝ) ^ (-(2 : ℝ) / 3) = 1 / 4 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg, Real.rpow_two]

/-- **LS-D with LS-E** at `d = 1`, `t = 4`, `x = 0`: `|u(4, 0)| ≤ min{1, (C*/(2π))/2}`. -/
theorem dispersive_one (hE : LatticeSchrodingerExistsStatement) (hD : LatticeSchrodingerDispersiveStatement) :
    ∃ u : ℝ → LatticeL2 1, IsLatticeSchrodingerSolution 1 (delta0 1) u ∧
      ‖u 4 0‖ ≤ 8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi) / 2 := by
  obtain ⟨u, hu⟩ := hE 1 (delta0 1)
  refine ⟨u, hu, ?_⟩
  have h := hD 1 _ u hu (delta0_summable 1) 4 0 (by norm_num)
  rw [delta0_tsum, mul_one, show (2 * |(4 : ℝ)|) = 8 by norm_num,
    show (-((1 : ℕ) : ℝ) / 3) = -(1 : ℝ) / 3 by norm_num, eight_rpow_neg_third, pow_one] at h
  exact h.trans ((min_le_right _ _).trans (le_of_eq (by ring)))

/-- The bound of `dispersive_one` is below the trivial bound 1. -/
theorem dispersive_one_nontrivial : 8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi) / 2 < 1 := by
  have := cstar_div_two_pi_lt
  linarith

/-- **LS-D with LS-E** at `d = 2`, `t = 4`, `x = 0`: `|u(4, 0)| ≤ (C*/(2π))²/4` (a datum with `3 ∤ d`). -/
theorem dispersive_two (hE : LatticeSchrodingerExistsStatement) (hD : LatticeSchrodingerDispersiveStatement) :
    ∃ u : ℝ → LatticeL2 2, IsLatticeSchrodingerSolution 2 (delta0 2) u ∧
      ‖u 4 0‖ ≤ (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 2 / 4 := by
  obtain ⟨u, hu⟩ := hE 2 (delta0 2)
  refine ⟨u, hu, ?_⟩
  have h := hD 2 _ u hu (delta0_summable 2) 4 0 (by norm_num)
  rw [delta0_tsum, mul_one, show (2 * |(4 : ℝ)|) = 8 by norm_num,
    show (-((2 : ℕ) : ℝ) / 3) = -(2 : ℝ) / 3 by norm_num, eight_rpow_neg_two_thirds'] at h
  exact h.trans ((min_le_right _ _).trans (le_of_eq (by ring)))

theorem dispersive_two_nontrivial : (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 2 / 4 < 1 := by
  have h := cstar_div_two_pi_lt
  have h0 := cstar_div_two_pi_pos
  nlinarith

/-- **Bite: `t ≠ 0` is needed in LS-D.** For any solution with datum `δ₀` in `d = 1`, the LS-D bound at `t = 0` and
`x = 0` is false: the left side is `|δ₀(0)| = 1` and the right side is `min 1 (c · 0^{−1/3}) · 1 = 0`. -/
theorem dispersive_false_at_zero (u : ℝ → LatticeL2 1) (hu : IsLatticeSchrodingerSolution 1 (delta0 1) u) :
    ¬ ‖u 0 0‖ ≤ min 1 ((8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 1 * (2 * |(0 : ℝ)|) ^ (-((1 : ℕ) : ℝ) / 3)) *
        ∑' y : Fin 1 → ℤ, ‖(delta0 1 : (Fin 1 → ℤ) → ℂ) y‖ := by
  rw [hu.1, delta0_tsum, delta0_apply]
  simp only [ite_true, norm_one, abs_zero, mul_zero]
  rw [Real.zero_rpow (by norm_num), mul_zero, min_eq_right zero_le_one, zero_mul]
  norm_num

/-- `τ = (C*/(2π))³/2` satisfies `1 + τ < 8`. -/
theorem one_add_tau_lt : 1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2 < 8 := by
  have h := cstar_div_two_pi_lt
  have h0 := cstar_div_two_pi_pos
  have h3 : (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 < (31 / 20) ^ 3 := pow_lt_pow_left₀ h h0.le (by norm_num)
  nlinarith

/-- **LS-D′ with LS-E** at `d = 1`, `t = 7`, `x = 0`: `|u(7, 0)| ≤ (1 + τ)^{1/3}/2`. -/
theorem decay_seven (hE : LatticeSchrodingerExistsStatement) (hD' : LatticeSchrodingerDecayStatement) :
    ∃ u : ℝ → LatticeL2 1, IsLatticeSchrodingerSolution 1 (delta0 1) u ∧
      ‖u 7 0‖ ≤ (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ ((1 : ℝ) / 3) / 2 := by
  obtain ⟨u, hu⟩ := hE 1 (delta0 1)
  refine ⟨u, hu, ?_⟩
  have h := hD' 1 _ u hu (delta0_summable 1) 7 0
  rw [delta0_tsum, mul_one, show (1 + |(7 : ℝ)|) = 8 by norm_num,
    show (-((1 : ℕ) : ℝ) / 3) = -(1 : ℝ) / 3 by norm_num, eight_rpow_neg_third,
    show ((1 : ℕ) : ℝ) / 3 = (1 : ℝ) / 3 by norm_num] at h
  exact h.trans (le_of_eq (by ring))

/-- The bound of `decay_seven` is below the trivial bound 1. -/
theorem decay_seven_nontrivial :
    (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ ((1 : ℝ) / 3) / 2 < 1 := by
  have h := one_add_tau_lt
  have hpos : 0 ≤ 1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2 := by positivity
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have := Real.rpow_lt_rpow hpos h (by norm_num : (0 : ℝ) < 1 / 3)
  rw [h8] at this
  linarith

/-- **Bite: the `1 +` in `(1 + |t|)` is needed in LS-D′.** At `t = 0` the bound `(1 + τ)^{1/3} |0|^{−1/3} ‖δ₀‖_1` is
`0`, but `|u(0, 0)| = 1`. -/
theorem decay_false_without_one (u : ℝ → LatticeL2 1) (hu : IsLatticeSchrodingerSolution 1 (delta0 1) u) :
    ¬ ‖u 0 0‖ ≤ (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ (((1 : ℕ) : ℝ) / 3) *
        |(0 : ℝ)| ^ (-((1 : ℕ) : ℝ) / 3) * ∑' y : Fin 1 → ℤ, ‖(delta0 1 : (Fin 1 → ℤ) → ℂ) y‖ := by
  rw [hu.1, delta0_tsum, delta0_apply]
  simp only [ite_true, norm_one, abs_zero]
  rw [Real.zero_rpow (by norm_num), mul_zero, zero_mul]
  norm_num

/-- **LS-D′ with LS-E at `t = 0`** (consistency): `|δ₀(0)| = 1 ≤ (1 + τ)^{d/3}` for `d = 3`. -/
theorem decay_zero_three (hE : LatticeSchrodingerExistsStatement) (hD' : LatticeSchrodingerDecayStatement) :
    1 ≤ (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ (((3 : ℕ) : ℝ) / 3) := by
  obtain ⟨u, hu⟩ := hE 3 (delta0 3)
  have h := hD' 3 _ u hu (delta0_summable 3) 0 0
  rw [hu.1, delta0_tsum, delta0_apply, abs_zero, add_zero, Real.one_rpow, mul_one, mul_one] at h
  simpa using h

end OscInt.API.LatticeGroupSanity
