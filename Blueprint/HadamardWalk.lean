/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.HadamardWalk

/-! # Blueprint for batch HW (HW-R, HW-K, HW-D, HW-L): intermediate propositions and five definitions

Route: `docs/proof-HW.md`. Six propositions. HW-K is proved as a part from `HadamardPhaseFacts` and
`HadamardAmplitudeFacts` and the proved S1.2 and S1.3; the assembly `OscInt/Front/HadamardWalkAssembly.lean` proves
HW-R, HW-D and HW-L. The definitions `hwD1`, `hwD2`, `hwD3` (the derivatives of the dispersion relation) and `hwAmp`,
`hwAmp'` (the amplitude and its derivative) are used by the propositions only; no frozen statement mentions them. -/

namespace OscInt.Blueprint.HadamardWalk

open OscInt.Statements

/-- `ω′(k) = cos k / √(1 + cos² k)`. -/
noncomputable def hwD1 (k : ℝ) : ℝ := Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)

/-- `ω″(k) = −sin k / (1 + cos² k)^{3/2}`. -/
noncomputable def hwD2 (k : ℝ) : ℝ := -Real.sin k / ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2))

/-- `ω‴(k) = −cos k (4 − 2 cos² k) / (1 + cos² k)^{5/2}`. -/
noncomputable def hwD3 (k : ℝ) : ℝ :=
  -(Real.cos k * (4 - 2 * Real.cos k ^ 2)) / ((1 + Real.cos k ^ 2) ^ 2 * Real.sqrt (1 + Real.cos k ^ 2))

/-- The amplitude `g(k) = 1 / √(2 (1 + cos² k))`, complex-valued. -/
noncomputable def hwAmp (k : ℝ) : ℂ := ((1 / Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ)

/-- Its derivative `g′(k) = sin k cos k / (√2 (1 + cos² k)^{3/2})`. -/
noncomputable def hwAmp' (k : ℝ) : ℂ :=
  ((Real.sin k * Real.cos k / (Real.sqrt 2 * ((1 + Real.cos k ^ 2) * Real.sqrt (1 + Real.cos k ^ 2))) : ℝ) : ℂ)

/-- **H-rec** The kernel at times `0` and `1` and its recursion in time. -/
def HadamardKernelRecFacts : Prop :=
  (∀ x : ℤ, hadamardKernel 0 x = 0) ∧
  (∀ x : ℤ, hadamardKernel 1 x = if x = 0 then 1 else 0) ∧
  ∀ (t : ℕ) (x : ℤ), hadamardKernel (t + 2) x =
    (hadamardKernel (t + 1) (x + 1) - hadamardKernel (t + 1) (x - 1)) / ((Real.sqrt 2 : ℝ) : ℂ) +
      hadamardKernel t x

/-- **H-phase** The derivative chain of the dispersion relation and the two lower bounds. -/
def HadamardPhaseFacts : Prop :=
  (∀ k : ℝ, HasDerivAt hadamardDispersion (hwD1 k) k) ∧ (∀ k : ℝ, HasDerivAt hwD1 (hwD2 k) k) ∧
  (∀ k : ℝ, HasDerivAt hwD2 (hwD3 k) k) ∧
  (∀ k : ℝ, 1 / Real.sqrt 2 ≤ |Real.sin k| → 2 / (3 * Real.sqrt 3) ≤ |hwD2 k|) ∧
  (∀ k : ℝ, 1 / Real.sqrt 2 ≤ |Real.cos k| → 1 / (2 * Real.sqrt 2) ≤ |hwD3 k|)

/-- **H-amp** The amplitude: its derivative, and its amplitude norm on the four arcs of length `π/2`. -/
def HadamardAmplitudeFacts : Prop :=
  (∀ k : ℝ, HasDerivAt hwAmp (hwAmp' k) k) ∧
  ampNorm hwAmp hwAmp' (-(Real.pi / 4)) (Real.pi / 4) ≤ Real.sqrt 3 - 1 ∧
  ampNorm hwAmp hwAmp' (Real.pi / 4) (3 * Real.pi / 4) ≤ Real.sqrt 2 - 1 / Real.sqrt 3 ∧
  ampNorm hwAmp hwAmp' (3 * Real.pi / 4) (5 * Real.pi / 4) ≤ Real.sqrt 3 - 1 ∧
  ampNorm hwAmp hwAmp' (5 * Real.pi / 4) (7 * Real.pi / 4) ≤ Real.sqrt 2 - 1 / Real.sqrt 3

/-- **H-arith** The arithmetic of HW-D: the bound of HW-R with HW-K at the times `t + 1` and `t`, `t ≥ 1`. -/
def HadamardDecayArithFacts : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    (7 * ((t + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) + 12 * ((t + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) / Real.sqrt 2 +
        (7 * (t : ℝ) ^ (-(1 : ℝ) / 2) + 12 * (t : ℝ) ^ (-(1 : ℝ) / 3)) ≤
      39 * ((t + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)

/-- **H-lin** The walk from a state supported in a finite set `S` is the sum over `S` of the translated walks from
point states. -/
def HadamardLinearFacts : Prop :=
  ∀ (ψ₀ : ℤ → ℂ × ℂ) (S : Finset ℤ) (t : ℕ) (x : ℤ), (∀ y : ℤ, y ∉ S → ψ₀ y = (0, 0)) →
    hadamardWalk ψ₀ t x = ∑ y ∈ S, hadamardWalk (pointState (ψ₀ y).1 (ψ₀ y).2) t (x - y)

end OscInt.Blueprint.HadamardWalk
