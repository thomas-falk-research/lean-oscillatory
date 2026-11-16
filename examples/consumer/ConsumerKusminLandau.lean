/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch KL (the Kusmin–Landau inequality)

Only `import OscInt.API` and Mathlib. Unconditional uses of the three theorems of batch KL:
* `linear_phase_sum`: for a linear phase `αn` with `λ ≤ α ≤ 1 − λ`, `|Σ_{n ≤ N} e^{2πiαn}| ≤ cot(πλ/2)` for every `N`
  (a geometric sum, bounded uniformly in `N` by the distance of `α` to the integers);
* `linear_phase_sum_two_over_pi`: the same with the constant `2/(πλ)`;
* the sanity data, now without hypotheses.
-/

open OscInt.Statements OscInt.API

/-- The differences of `n ↦ αn` are constant, hence monotone, and lie in `[λ, 1 − λ]` when `α` does. -/
theorem diffs_linear (α lam : ℝ) (N : ℕ) (h1 : lam ≤ α) (h2 : α ≤ 1 - lam) :
    DiffsMonotoneIn (fun n : ℕ => α * (n : ℝ)) N 0 lam := by
  have e : ∀ m : ℕ, α * ((m + 1 : ℕ) : ℝ) - α * (m : ℝ) = α := fun m => by push_cast; ring
  refine ⟨Or.inl fun n _ => ?_, fun n _ => ?_⟩
  · show α * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) ≤ α * ((n + 1 + 1 : ℕ) : ℝ) - α * ((n + 1 : ℕ) : ℝ)
    rw [e n, e (n + 1)]
  · show ((0 : ℤ) : ℝ) + lam ≤ α * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) ∧
      α * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) ≤ ((0 : ℤ) : ℝ) + 1 - lam
    rw [e n, Int.cast_zero]
    constructor <;> linarith

/-- KL-D for a linear phase: `|Σ_{n ≤ N} e^{2πiαn}| ≤ cot(πλ/2)` whenever `λ ≤ α ≤ 1 − λ`, `0 < λ ≤ 1/2`. -/
theorem linear_phase_sum (α lam : ℝ) (N : ℕ) (hl : 0 < lam) (hl2 : lam ≤ 1 / 2) (h1 : lam ≤ α) (h2 : α ≤ 1 - lam) :
    ‖expSum (fun n : ℕ => α * (n : ℝ)) N‖ ≤ Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) :=
  kusminLandau _ N 0 lam hl hl2 (diffs_linear α lam N h1 h2)

/-- KL-C for a linear phase: the same sum is at most `2/(πλ)`. -/
theorem linear_phase_sum_two_over_pi (α lam : ℝ) (N : ℕ) (hl : 0 < lam) (hl2 : lam ≤ 1 / 2) (h1 : lam ≤ α)
    (h2 : α ≤ 1 - lam) : ‖expSum (fun n : ℕ => α * (n : ℝ)) N‖ ≤ 2 / (Real.pi * lam) :=
  kusminLandauTwoOverPi _ N 0 lam hl hl2 (diffs_linear α lam N h1 h2)

/-- The sanity datum of KL-D, unconditionally: the three-term sum of Landau's sequence at `λ = 1/3` is at most `√3`
(and equals it: the bound is attained there). -/
example : ‖expSum KusminLandauSanity.cThird 2‖ ≤ √3 := KusminLandauSanity.kl_third kusminLandau

/-- The sanity datum of KL-C, unconditionally. -/
example : √13 ≤ 2 / (Real.pi * (1 / 6)) := KusminLandauSanity.klc_six kusminLandauTwoOverPi

/-- The sanity datum of KL-F, unconditionally. -/
example : √2 ≤ Real.cos (Real.pi * (1 / 4) / 2) / Real.sin (Real.pi * (1 / 4) / 2) :=
  KusminLandauSanity.klf_quarter kusminLandauDeriv
