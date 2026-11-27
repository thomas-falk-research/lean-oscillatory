/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.Cusp

/-!
# Batch TRI: the singularity types of the anisotropic triangular lattice phase (statements only)

Mathematics: `docs/statements.md`, "Batch TRI". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1). A proof on paper exists and is older (an external
derivation, checked by the lead and a referee: `review/2026-11-26-A5-handoff-answers.md`).

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean` and `OscInt/Statements/Cusp.lean`).
* `triPhase α k = cos k₁ + cos k₂ + α cos(k₁ + k₂)`: the band of the square lattice with one diagonal hopping of
  strength `α`, equivalently of the triangular lattice with anisotropic hopping (`α = 1` isotropic).
* `triExceptional = 1/(2√2)`.
* `ReducedCurve Ψ k₀ v w ε h`: `h` is a smooth function with `h 0 = 0` along which the transverse derivative is that
  of the tangent plane, `DΨ(k₀ + u v + h(u) w) w = DΨ(k₀) w` for `|u| < ε` (the transverse critical curve of
  `Ψ − DΨ(k₀)`).
* `reducedFn Ψ k₀ v w h u = Ψ(k₀ + u v + h(u) w) − DΨ(k₀)(u v + h(u) w)`: the phase with its tangent plane removed,
  restricted to that curve (the function of the splitting lemma).
* `IsA5Point Ψ k₀`: the Hessian has rank one with kernel vector `v ≠ 0`, `D²Ψ(k₀)[w, w] ≠ 0`, and for some `ε > 0`
  and some reduced curve `h`, the reduced function has derivatives `1` to `5` zero and `6` nonzero at `0`.

Statements (all for the fixed phase `triPhase α`; the linear term of a lattice kernel does not change derivatives of
order two or more, so these are the types of `triPhase α + p·(·)` at its critical points).
* TRI-K `TriClassificationStatement`: for `α ≠ 0`, every point is A1 or A2 (`FoldOrNondeg`), A3 (`IsA3Point`) or A5
  (`IsA5Point`); in particular there is no point of type A4 or of D type.
* TRI-X `TriA5LocusStatement`: an A5 point occurs only for `|α| = 1/(2√2)`, and only at `(θ, −θ)` or `(−θ, θ)`
  modulo `2π` in each coordinate, with `θ = arccos(−2α)`.
* TRI-W `TriA5WitnessStatement`: for `|α| = 1/(2√2)` the points `(θ, −θ)` and `(−θ, θ)` are A5 points; and with
  `v = (1, 1)`, `w = (1, −1)`, every reduced curve at `(θ, −θ)` gives sixth derivative `−60√2 · sign α` at `0`
  (in the unit kernel coordinate `s = √2 u` the coefficient of `s⁶` is `−sign α/(48√2)`).
* TRI-Q `TriQuarticStatement`: for `α ≠ 0`, at `(π/2, π/2)` with `v = (1, −1)`, `w = (1, 1)` the Hessian kernel
  and the vanishing cubic hold and the reduced quartic `D²Ψ[w, w] D⁴Ψ[v⁴] − 3 (D³Ψ[v, v, w])²` equals `−12`; for
  `0 < |α| ≤ 1/2`, at `(θ, −θ)` with `v = (1, 1)`, `w = (1, −1)` the same hold with the value `12(8α² − 1)`. (In
  the unit kernel coordinate the quartic coefficients are `−1/(32α)` and `(8α² − 1)/(32α)`.)

Modelling choices.
* Points are in `ℝ × ℝ` (not the torus); TRI-X states the locus with integer shifts by `2π`.
* Derivatives are `iteratedFDeriv` applied to `![…]`, as in `IsA3Point`; the phase is smooth, so these are the
  symmetric multilinear derivatives.
* `IsA5Point` asks for some reduced curve; TRI-W's value is stated for every reduced curve. By the implicit function
  theorem the curve is unique near `0` when `D²Ψ[w, w] ≠ 0`; that is not part of the statements.
* The case `α = 0` (four D4 points, product structure) is not stated here.
* Nothing about decay is stated here; the fixed-coupling decay theorem (K2) is a separate batch.
-/

namespace OscInt.Statements

open scoped ContDiff

/-- The anisotropic triangular lattice phase `cos k₁ + cos k₂ + α cos(k₁ + k₂)`. -/
noncomputable def triPhase (α : ℝ) (k : ℝ × ℝ) : ℝ :=
  Real.cos k.1 + Real.cos k.2 + α * Real.cos (k.1 + k.2)

/-- The exceptional coupling `1/(2√2)`. -/
noncomputable def triExceptional : ℝ := 1 / (2 * Real.sqrt 2)

/-- `h` is a smooth transverse critical curve of `Ψ − DΨ(k₀)` through `k₀` on `|u| < ε`. -/
def ReducedCurve (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
    ∀ u : ℝ, |u| < ε → fderiv ℝ Ψ (k₀ + u • v + h u • w) w = fderiv ℝ Ψ k₀ w

/-- The phase with its tangent plane at `k₀` removed, along `u ↦ k₀ + u v + h(u) w`. -/
noncomputable def reducedFn (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  Ψ (k₀ + u • v + h u • w) - fderiv ℝ Ψ k₀ (u • v + h u • w)

/-- `k₀` is an A5 point of `Ψ`: the Hessian has rank one with kernel vector `v ≠ 0`, `D²Ψ(k₀)[w, w] ≠ 0`, and on
some reduced curve the reduced function has derivatives of orders `1` to `5` zero and of order `6` nonzero at `0`. -/
def IsA5Point (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) : Prop :=
  ∃ v w : ℝ × ℝ, v ≠ 0 ∧ (∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0) ∧ iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 ∧
    ∃ ε > 0, ∃ h : ℝ → ℝ, ReducedCurve Ψ k₀ v w ε h ∧
      (∀ j ∈ Finset.Icc 1 5, iteratedDeriv j (reducedFn Ψ k₀ v w h) 0 = 0) ∧
      iteratedDeriv 6 (reducedFn Ψ k₀ v w h) 0 ≠ 0

/-- **TRI-K** Classification of the anisotropic triangular lattice phase: for `α ≠ 0` every point is of type A1 or
A2, A3, or A5 (no A4 and no D-type point). -/
def TriClassificationStatement : Prop :=
  ∀ α : ℝ, α ≠ 0 → ∀ k : ℝ × ℝ,
    FoldOrNondeg (triPhase α) k ∨ IsA3Point (triPhase α) k ∨ IsA5Point (triPhase α) k

theorem statement_pin_TriClassification : TriClassificationStatement = TriClassificationStatement := rfl

/-- **TRI-X** The A5 locus: A5 points of the anisotropic triangular lattice phase occur only for `|α| = 1/(2√2)`, and
only at `(θ, −θ)` or `(−θ, θ)` modulo `2π`, with `θ = arccos(−2α)`. -/
def TriA5LocusStatement : Prop :=
  ∀ α : ℝ, ∀ k : ℝ × ℝ, IsA5Point (triPhase α) k →
    |α| = triExceptional ∧
      ∃ j₁ j₂ : ℤ,
        k = (Real.arccos (-2 * α) + 2 * Real.pi * j₁, -Real.arccos (-2 * α) + 2 * Real.pi * j₂) ∨
          k = (-Real.arccos (-2 * α) + 2 * Real.pi * j₁, Real.arccos (-2 * α) + 2 * Real.pi * j₂)

theorem statement_pin_TriA5Locus : TriA5LocusStatement = TriA5LocusStatement := rfl

/-- **TRI-W** The A5 witness: for `|α| = 1/(2√2)` the points `(θ, −θ)` and `(−θ, θ)`, `θ = arccos(−2α)`, are A5
points, and with `v = (1, 1)`, `w = (1, −1)` every reduced curve at `(θ, −θ)` has reduced sixth derivative
`−60√2 · sign α` at `0`. -/
def TriA5WitnessStatement : Prop :=
  ∀ α : ℝ, |α| = triExceptional →
    IsA5Point (triPhase α) (Real.arccos (-2 * α), -Real.arccos (-2 * α)) ∧
      IsA5Point (triPhase α) (-Real.arccos (-2 * α), Real.arccos (-2 * α)) ∧
      ∀ (ε : ℝ) (h : ℝ → ℝ), 0 < ε →
        ReducedCurve (triPhase α) (Real.arccos (-2 * α), -Real.arccos (-2 * α)) (1, 1) (1, -1) ε h →
          iteratedDeriv 6 (reducedFn (triPhase α) (Real.arccos (-2 * α), -Real.arccos (-2 * α)) (1, 1) (1, -1) h) 0
            = -60 * Real.sqrt 2 * SignType.sign α

theorem statement_pin_TriA5Witness : TriA5WitnessStatement = TriA5WitnessStatement := rfl

/-- **TRI-Q** The reduced quartics: for `α ≠ 0`, at `(π/2, π/2)` with `v = (1, −1)`, `w = (1, 1)` the reduced
quartic is `−12`; for `0 < |α| ≤ 1/2`, at `(θ, −θ)`, `θ = arccos(−2α)`, with `v = (1, 1)`, `w = (1, −1)` it is
`12(8α² − 1)`; in both cases `v` spans the Hessian kernel and the cubic along `v` vanishes. -/
def TriQuarticStatement : Prop :=
  ∀ α : ℝ, α ≠ 0 →
    ((∀ z, iteratedFDeriv ℝ 2 (triPhase α) (Real.pi / 2, Real.pi / 2) ![(1, -1), z] = 0) ∧
      iteratedFDeriv ℝ 3 (triPhase α) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1)] = 0 ∧
      iteratedFDeriv ℝ 2 (triPhase α) (Real.pi / 2, Real.pi / 2) ![(1, 1), (1, 1)] *
          iteratedFDeriv ℝ 4 (triPhase α) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1), (1, -1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase α) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, 1)] ^ 2 = -12) ∧
    (|α| ≤ 1 / 2 →
      let θ := Real.arccos (-2 * α)
      (∀ z, iteratedFDeriv ℝ 2 (triPhase α) (θ, -θ) ![(1, 1), z] = 0) ∧
        iteratedFDeriv ℝ 3 (triPhase α) (θ, -θ) ![(1, 1), (1, 1), (1, 1)] = 0 ∧
        iteratedFDeriv ℝ 2 (triPhase α) (θ, -θ) ![(1, -1), (1, -1)] *
            iteratedFDeriv ℝ 4 (triPhase α) (θ, -θ) ![(1, 1), (1, 1), (1, 1), (1, 1)] -
          3 * iteratedFDeriv ℝ 3 (triPhase α) (θ, -θ) ![(1, 1), (1, 1), (1, -1)] ^ 2 = 12 * (8 * α ^ 2 - 1))

theorem statement_pin_TriQuartic : TriQuarticStatement = TriQuarticStatement := rfl

end OscInt.Statements
