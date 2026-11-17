/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch HW (the Hadamard walk on the line)

Only `import OscInt.API` and Mathlib. Unconditional uses of the theorems of batch HW:
* `hadamard_amplitude_le`: each amplitude of the walk from a normalised point state is at most `39 √2 t^{−1/3}`;
* `hadamard_probability_le`: the probability at a site, `|ψ₁|² + |ψ₂|²`, is at most `2 (39 √2 t^{−1/3})²`, that is
  `6084 t^{−2/3}`: the "peak probability decays like `t^{−2/3}`" of the quantum-walk literature, as an upper bound
  with an explicit (far from sharp) constant, for every `t ≥ 1` and every site;
* the sanity data, now without hypotheses.
-/

open OscInt.Statements OscInt.API

/-- `|a| + |b| ≤ √2` for a normalised coin state. -/
theorem norm_add_norm_le_sqrt_two (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ‖a‖ + ‖b‖ ≤ Real.sqrt 2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- HW-D for a normalised point state: each amplitude is at most `39 √2 t^{−1/3}`. -/
theorem hadamard_amplitude_le (a b : ℂ) (t : ℕ) (x : ℤ) (ht : 1 ≤ t) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖(hadamardWalk (pointState a b) t x).1‖ ≤ 39 * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 3) ∧
      ‖(hadamardWalk (pointState a b) t x).2‖ ≤ 39 * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hD := hadamardDecay a b t x ht
  have hs := norm_add_norm_le_sqrt_two a b h
  have hp : (0 : ℝ) ≤ (t : ℝ) ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg t) _
  have hmono : 39 * (‖a‖ + ‖b‖) * (t : ℝ) ^ (-(1 : ℝ) / 3) ≤ 39 * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 3) := by
    gcongr
  exact ⟨hD.1.trans hmono, hD.2.trans hmono⟩

/-- The probability at a site of the Hadamard walk from a normalised point state is at most
`2 (39 √2 t^{−1/3})²`, for every `t ≥ 1` and every site. -/
theorem hadamard_probability_le (a b : ℂ) (t : ℕ) (x : ℤ) (ht : 1 ≤ t) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖(hadamardWalk (pointState a b) t x).1‖ ^ 2 + ‖(hadamardWalk (pointState a b) t x).2‖ ^ 2 ≤
      2 * (39 * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 := by
  obtain ⟨h1, h2⟩ := hadamard_amplitude_le a b t x ht h
  have e1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

/-- The walk after three steps, through HW-R: the sanity datum now without hypothesis. -/
example (a b : ℂ) (x : ℤ) := HadamardWalkSanity2.hwR_two hadamardKernelFormula a b x
