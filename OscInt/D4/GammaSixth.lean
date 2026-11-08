/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4ClosedForm

/-!
# S4.4, part E7: `√π Γ(1/6) = √3 Γ(1/3)² / 2^{1/3}`

Legendre duplication at `s = 1/6` (`Real.Gamma_mul_Gamma_add_half`): `Γ(1/6) Γ(2/3) = Γ(1/3) 2^{2/3} √π`; Euler
reflection at `s = 1/3` (`Real.Gamma_mul_Gamma_one_sub`): `Γ(1/3) Γ(2/3) = π / sin(π/3) = 2π/√3`. Eliminating
`Γ(2/3)` gives the identity.
-/

namespace OscInt.D4

open OscInt.Blueprint

/-- **E7** -/
theorem gammaSixth : GammaSixthFacts := by
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 6)
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at hdup
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show Real.pi * (1 / 3) = Real.pi / 3 by ring,
    Real.sin_pi_div_three] at hrefl
  have hG13 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := by positivity
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) * 2 ^ ((2 : ℝ) / 3) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h2p : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  -- `Γ(2/3) = 2π / (√3 Γ(1/3))`
  have hG : Real.Gamma (2 / 3) * (Real.sqrt 3 * Real.Gamma (1 / 3)) = 2 * Real.pi := by
    field_simp at hrefl; linear_combination hrefl
  unfold GammaSixthFacts
  rw [eq_div_iff h2p.ne']
  -- multiply through by `Γ(2/3) > 0`
  apply mul_right_cancel₀ hG23.ne'
  calc Real.sqrt Real.pi * Real.Gamma (1 / 6) * 2 ^ ((1 : ℝ) / 3) * Real.Gamma (2 / 3)
      = Real.sqrt Real.pi * 2 ^ ((1 : ℝ) / 3) * (Real.Gamma (1 / 6) * Real.Gamma (2 / 3)) := by ring
    _ = Real.Gamma (1 / 3) * (Real.sqrt Real.pi * Real.sqrt Real.pi) *
          (2 ^ ((1 : ℝ) / 3) * 2 ^ ((2 : ℝ) / 3)) := by rw [hdup]; ring
    _ = Real.sqrt 3 * Real.Gamma (1 / 3) ^ 2 * Real.Gamma (2 / 3) := by
      rw [hsp, h2]
      linear_combination (-(Real.Gamma (1 / 3))) * hG

end OscInt.D4
