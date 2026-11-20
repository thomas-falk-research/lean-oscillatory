/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.KusminLandau
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Batch KL: the lead's assembly against the blueprint (route `docs/proof-KL.md`)

KL-D from the core (subtract `k·n`); KL-C from KL-D (`cot x ≤ 1/x`); KL-F from KL-D and the mean-value part.
Compiled before any part was proved.
-/

namespace OscInt.KusminLandauAux

open OscInt.Statements OscInt.Blueprint.KusminLandau

/-- Subtracting `k·n` from `c_n` changes no term of the exponential sum. -/
theorem expSum_sub_int_mul (c : ℕ → ℝ) (N : ℕ) (k : ℤ) :
    expSum (fun n => c n - (k : ℝ) * (n : ℝ)) N = expSum c N := by
  unfold expSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have h : (↑(2 * Real.pi * (c n - (k : ℝ) * (n : ℝ))) : ℂ) * Complex.I =
      ↑(2 * Real.pi * c n) * Complex.I - ((k * (n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- **KL-D from the core** (reduction to `k = 0`). -/
theorem kusminLandau_of (h : KLCoreFacts) : KusminLandauStatement := by
  intro c N k lam hl hl2 hd
  rw [← expSum_sub_int_mul c N k]
  have e : ∀ m : ℕ, (c (m + 1) - (k : ℝ) * ((m + 1 : ℕ) : ℝ)) - (c m - (k : ℝ) * (m : ℝ)) =
      (c (m + 1) - c m) - (k : ℝ) := fun m => by push_cast; ring
  refine h _ N lam hl hl2 ⟨?_, ?_⟩
  · rcases hd.1 with h1 | h1
    · left
      intro n hn
      have := h1 n hn
      show (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (c n - (k : ℝ) * (n : ℝ)) ≤
        (c (n + 1 + 1) - (k : ℝ) * ((n + 1 + 1 : ℕ) : ℝ)) - (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ))
      rw [e n, e (n + 1)]
      linarith
    · right
      intro n hn
      have := h1 n hn
      show (c (n + 1 + 1) - (k : ℝ) * ((n + 1 + 1 : ℕ) : ℝ)) - (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤
        (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (c n - (k : ℝ) * (n : ℝ))
      rw [e n, e (n + 1)]
      linarith
  · intro n hn
    have := hd.2 n hn
    show ((0 : ℤ) : ℝ) + lam ≤ (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (c n - (k : ℝ) * (n : ℝ)) ∧
      (c (n + 1) - (k : ℝ) * ((n + 1 : ℕ) : ℝ)) - (c n - (k : ℝ) * (n : ℝ)) ≤ ((0 : ℤ) : ℝ) + 1 - lam
    rw [e n, Int.cast_zero]
    constructor <;> linarith [this.1, this.2]

/-- **KL-C from KL-D**: `cot x ≤ 1/x` on `(0, π/2)`, from `x < tan x`. -/
theorem kusminLandauTwoOverPi_of (h : KusminLandauStatement) : KusminLandauTwoOverPiStatement := by
  intro c N k lam hl hl2 hd
  refine (h c N k lam hl hl2 hd).trans ?_
  have hx0 : 0 < Real.pi * lam / 2 := by positivity
  have hx1 : Real.pi * lam / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * lam / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (Real.pi * lam / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩
  have htan := Real.lt_tan hx0 hx1
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  have hle : Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) ≤ 1 / (Real.pi * lam / 2) := by
    rw [div_le_div_iff₀ hsin hx0]
    linarith
  refine hle.trans_eq ?_
  field_simp

/-- **KL-F from KL-D and the part.** -/
theorem kusminLandauDeriv_of (hD : KLDerivFacts) (h : KusminLandauStatement) : KusminLandauDerivStatement :=
  hD h

end OscInt.KusminLandauAux
