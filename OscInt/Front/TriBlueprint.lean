/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TriangularAniso

/-! # Batch TRI: blueprint (propositions only)

`docs/proof-TRI.md`, sections 2 to 8, as revised after the route referee (section 9). Each proposition is proved in its
own file; the assembly (`OscInt/Front/TriAssembly.lean`) proves the four frozen statements from them. Nothing here is
proved, and nothing anywhere uses `sorry`: an unfinished part is a hypothesis of the assembly.
-/

namespace OscInt.API.TriBlueprint

open OscInt.Statements
open scoped ContDiff

/-- TRI-X's locus: `(θ, −θ)` or `(−θ, θ)` modulo `2π` in each coordinate, `θ = arccos(−2α)`. -/
def InLocus (α : ℝ) (k : ℝ × ℝ) : Prop :=
  ∃ j₁ j₂ : ℤ,
    k = (Real.arccos (-2 * α) + 2 * Real.pi * j₁, -Real.arccos (-2 * α) + 2 * Real.pi * j₂) ∨
      k = (-Real.arccos (-2 * α) + 2 * Real.pi * j₁, Real.arccos (-2 * α) + 2 * Real.pi * j₂)

/-- The quartic invariant of `IsA3Point`: `D²Ψ[w, w] D⁴Ψ[v⁴] − 3 (D³Ψ[v, v, w])²`. -/
noncomputable def qinv (Ψ : ℝ × ℝ → ℝ) (k v w : ℝ × ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 Ψ k ![w, w] * iteratedFDeriv ℝ 4 Ψ k ![v, v, v, v] -
    3 * iteratedFDeriv ℝ 3 Ψ k ![v, v, w] ^ 2

/-- **P-alg, classification** (`docs/proof-TRI.md`, section 2). -/
def AlgClassify : Prop :=
  ∀ α : ℝ, α ≠ 0 → ∀ k : ℝ × ℝ,
    FoldOrNondeg (triPhase α) k ∨ IsA3Point (triPhase α) k ∨ (|α| = triExceptional ∧ InLocus α k)

/-- **P-alg, the A5 conditions force the locus** (section 2, with the invariance step). -/
def AlgA5 : Prop :=
  ∀ α : ℝ, α ≠ 0 → ∀ k v w : ℝ × ℝ, v ≠ 0 → (∀ z, iteratedFDeriv ℝ 2 (triPhase α) k ![v, z] = 0) →
    iteratedFDeriv ℝ 3 (triPhase α) k ![v, v, v] = 0 → iteratedFDeriv ℝ 2 (triPhase α) k ![w, w] ≠ 0 →
      qinv (triPhase α) k v w = 0 → |α| = triExceptional ∧ InLocus α k

/-- **P-alg, the case `α = 0`** (section 4, last paragraph): a nonzero kernel vector at a point where some
`D²Ψ[w, w] ≠ 0` has a nonzero cubic. -/
def AlgZero : Prop :=
  ∀ k v w : ℝ × ℝ, v ≠ 0 → (∀ z, iteratedFDeriv ℝ 2 (triPhase 0) k ![v, z] = 0) →
    iteratedFDeriv ℝ 2 (triPhase 0) k ![w, w] ≠ 0 → iteratedFDeriv ℝ 3 (triPhase 0) k ![v, v, v] ≠ 0

/-- **P-bridge** (section 4): along any reduced curve, the third and fourth derivatives of the reduced function at
`0` are the cubic `D³Ψ[v³]` and the quartic invariant divided by `D²Ψ[w, w]`. -/
def Bridge : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ), ContDiff ℝ ∞ Ψ →
    (∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0) → iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 → 0 < ε →
      ReducedCurve Ψ k₀ v w ε h →
        iteratedDeriv 3 (reducedFn Ψ k₀ v w h) 0 = iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, v] ∧
          iteratedDeriv 4 (reducedFn Ψ k₀ v w h) 0 = qinv Ψ k₀ v w / iteratedFDeriv ℝ 2 Ψ k₀ ![w, w]

/-- **P-wit, existence** (section 5, step 7, with the device of section 9): every locus point at `|α| = a*` is an
A5 point. -/
def WitA5 : Prop :=
  ∀ α : ℝ, |α| = triExceptional → ∀ k : ℝ × ℝ, InLocus α k → IsA5Point (triPhase α) k

/-- **P-wit, the sextic** (section 5, steps 1 to 6): TRI-W's third conjunct. -/
def WitSextic : Prop :=
  ∀ α : ℝ, |α| = triExceptional → ∀ (ε : ℝ) (h : ℝ → ℝ), 0 < ε →
    ReducedCurve (triPhase α) (Real.arccos (-2 * α), -Real.arccos (-2 * α)) (1, 1) (1, -1) ε h →
      iteratedDeriv 6 (reducedFn (triPhase α) (Real.arccos (-2 * α), -Real.arccos (-2 * α)) (1, 1) (1, -1) h) 0
        = -60 * Real.sqrt 2 * SignType.sign α

end OscInt.API.TriBlueprint
