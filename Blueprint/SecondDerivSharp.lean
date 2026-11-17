/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.SecondDerivSharp

/-! # Blueprint for batch VC2 (VC2-S, VC2-A, VC2-N, VC2-K): intermediate propositions and one definition

Route: `docs/proof-VC2.md`. Five propositions. `Vdc2Side f f' c d lam` describes the phase on one side of its
turning point: `f` continuous on `[c, d]`, with derivative `f′ > 0` on `(c, d)` that increases at rate at least
`lam > 0`. Every sub-interval of a side is a side. No frozen statement mentions the definition. -/

namespace OscInt.Blueprint.SecondDerivSharp

open Set OscInt.Statements

/-- One side of the turning point: `c ≤ d`, `0 < lam`, `f` continuous on `[c, d]` with derivative `f′` on `(c, d)`,
`f′` increases at rate at least `lam` on `(c, d)`, and `f′ > 0` on `(c, d)`. -/
def Vdc2Side (f f' : ℝ → ℝ) (c d lam : ℝ) : Prop :=
  c ≤ d ∧ 0 < lam ∧ ContinuousOn f (Icc c d) ∧ (∀ x ∈ Ioo c d, HasDerivAt f (f' x) x) ∧
    (∀ x ∈ Ioo c d, ∀ y ∈ Ioo c d, x ≤ y → lam * (y - x) ≤ f' y - f' x) ∧ ∀ x ∈ Ioo c d, 0 < f' x

/-- **V-turn** The turning point: a derivative that increases at a positive rate on `(a, b)` is negative before
some `x₀ ∈ [a, b]` and positive after it. -/
def Vdc2TurningPointFacts : Prop :=
  ∀ (f' : ℝ → ℝ) (a b lam : ℝ), a ≤ b → 0 < lam → DerivIncreasesAtRate f' a b lam →
    ∃ x₀ ∈ Icc a b, (∀ x ∈ Ioo a x₀, f' x < 0) ∧ ∀ x ∈ Ioo x₀ b, 0 < f' x

/-- **V-root** On a side the speed dominates the square root of the phase gained:
`2 lam (f(x) − f(c)) ≤ f′(x)²`. -/
def Vdc2RootFacts : Prop :=
  ∀ (f f' : ℝ → ℝ) (c d lam : ℝ), Vdc2Side f f' c d lam → ∀ x ∈ Ioo c d, 2 * lam * (f x - f c) ≤ f' x ^ 2

/-- **V-head** A positive arc that starts at the turning point: if the phase gained on the side is at most
`w ≤ π`, then `∫_c^d sin(w − (f − f(c))) ≤ A(w) / (2 √lam)`, with equality for the quadratic phase. -/
def Vdc2HeadFacts : Prop :=
  ∀ (f f' : ℝ → ℝ) (c d lam w : ℝ), Vdc2Side f f' c d lam → 0 ≤ w → w ≤ Real.pi → f d - f c ≤ w →
    ∫ x in c..d, Real.sin (w - (f x - f c)) ≤ vdc2Profile w / (2 * Real.sqrt lam)

/-- **V-tail** From the start of a negative arc the integral of the cosine never becomes positive:
if `sin(f(c) − α) = 1` then `∫_c^d cos(f − α) ≤ 0`. -/
def Vdc2TailFacts : Prop :=
  ∀ (f f' : ℝ → ℝ) (c d lam α : ℝ), Vdc2Side f f' c d lam → Real.sin (f c - α) = 1 →
    ∫ x in c..d, Real.cos (f x - α) ≤ 0

/-- **V-side** One side: for every rotation `θ` there is `w ∈ [0, π]`, depending on `θ` only, with
`∫_c^d cos(f − f(c) − θ) ≤ A(w) / (2 √lam)` on every side. -/
def Vdc2OneSideFacts : Prop :=
  ∀ θ : ℝ, ∃ w ∈ Icc (0 : ℝ) Real.pi, ∀ (f f' : ℝ → ℝ) (c d lam : ℝ), Vdc2Side f f' c d lam →
    ∫ x in c..d, Real.cos (f x - f c - θ) ≤ vdc2Profile w / (2 * Real.sqrt lam)

end OscInt.Blueprint.SecondDerivSharp
