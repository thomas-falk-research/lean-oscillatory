/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeCubeRoot

/-! # Blueprint for batch LE2 (T0E′, T6E′): intermediate propositions, definitions only

Route: `docs/proof-LE2.md`. One `…Facts` proposition per part; the assembly
`OscInt/Front/LatticeCubeRootAssembly.lean` proves the statements from them. Notation: `g k = ξ − t sin k` is the
derivative of the phase `t cos k + ξ k`; bounds are stated for `ξ = t * v`. -/

namespace OscInt.Blueprint.LatticeCubeRoot

open OscInt.Statements Real

/-- **P-ibp** One integration by parts with the boundary terms kept, for any phase `φ` with `φ′ = g ≠ 0`. -/
def IbpFacts : Prop :=
  ∀ (φ g g' : ℝ → ℝ) (a b : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, HasDerivAt φ (g x) x) →
    (∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x) →
    ContinuousOn g' (Set.Icc a b) →
    (∀ x ∈ Set.Icc a b, g x ≠ 0) →
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 1 / |g a| + 1 / |g b| + ∫ x in a..b, |g' x| / g x ^ 2

/-- **P-var** The variation integral of `1/g` for the lattice phase on a piece where `sin` is monotone. -/
def VarFacts : Prop :=
  ∀ t ξ a b : ℝ, 0 < t → a ≤ b → (∀ k ∈ Set.Icc a b, ξ - t * sin k ≠ 0) →
    (Set.Icc a b ⊆ Set.Icc (-(π / 2)) (π / 2) →
      ∫ k in a..b, |-(t * cos k)| / (ξ - t * sin k) ^ 2 = 1 / (ξ - t * sin b) - 1 / (ξ - t * sin a)) ∧
    ((Set.Icc a b ⊆ Set.Icc (π / 2) (π + π / 2) ∨ Set.Icc a b ⊆ Set.Icc (-(π + π / 2)) (-(π / 2))) →
      ∫ k in a..b, |-(t * cos k)| / (ξ - t * sin k) ^ 2 = 1 / (ξ - t * sin a) - 1 / (ξ - t * sin b))

/-- **P-band**, low velocities (`v ≤ δ`). -/
def BandLowFacts : Prop :=
  ∀ t v δ : ℝ, 0 < t → 0 ≤ v → 0 < δ → v ≤ δ → v + δ < 1 →
    ‖latticeKernel1 t (t * v)‖ ≤
      2 * (arcsin (v + δ) - arcsin (v - δ)) + 8 / (t * δ) - 4 / (t * (1 - v ^ 2))

/-- **P-band**, high velocities (`δ ≤ v`): the end points `±π` cost `2/(tv)`. -/
def BandHighFacts : Prop :=
  ∀ t v δ : ℝ, 0 < t → 0 < δ → δ ≤ v → v + δ < 1 →
    ‖latticeKernel1 t (t * v)‖ ≤
      2 * (arcsin (v + δ) - arcsin (v - δ)) + 8 / (t * δ) - 4 / (t * (1 - v ^ 2)) + 2 / (t * v)

/-- **P-cap**, low velocities (`v ≤ δ`, `−1 < v − δ`). -/
def CapLowFacts : Prop :=
  ∀ t v δ : ℝ, 0 < t → 0 ≤ v → 0 < δ → v ≤ δ → -1 < v - δ →
    ‖latticeKernel1 t (t * v)‖ ≤ π - 2 * arcsin (v - δ) + 4 / (t * δ) - 2 / (t * (1 + v))

/-- **P-cap**, high velocities (`0 ≤ v − δ < 1`). -/
def CapHighFacts : Prop :=
  ∀ t v δ : ℝ, 0 < t → 0 < δ → δ ≤ v → v - δ < 1 →
    ‖latticeKernel1 t (t * v)‖ ≤ π - 2 * arcsin (v - δ) + 4 / (t * δ) + 2 / (t * v * (v + 1))

/-- **P-cap**, the whole interval when `v > 1` (`g > 0` on `[−π, π]`). -/
def WholeFacts : Prop :=
  ∀ t v : ℝ, 0 < t → 1 < v →
    ‖latticeKernel1 t (t * v)‖ ≤ 2 / (t * (v - 1)) + 2 / (t * v * (v + 1))

/-- **P-r8** Times `t ≥ 8`, `ξ = tv ≥ 0`. -/
def Regime8Facts : Prop :=
  ∀ t v : ℝ, 8 ≤ t → 0 ≤ v → ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3)

/-- **P-r38** Times `3 ≤ t ≤ 8`, `ξ = tv ≥ 0`. -/
def Regime38Facts : Prop :=
  ∀ t v : ℝ, 3 ≤ t → t ≤ 8 → 0 ≤ v → ‖latticeKernel1 t (t * v)‖ ≤ 8 * (1 + sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3)

/-- **P-sym** `I(t, −ξ) = I(t, ξ)`. -/
def SymFacts : Prop :=
  ∀ t ξ : ℝ, latticeKernel1 t (-ξ) = latticeKernel1 t ξ

end OscInt.Blueprint.LatticeCubeRoot
