/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.StationaryLeading

/-! # Blueprint for batch SPL (SPL-I, SPL-S, SPL-K, SPL-A): intermediate propositions and three definitions

Route: `docs/proof-SPL.md` (second version, with its addendum and the section "Parts as planned for Lean").
Five propositions. `fresnelE u = e^{iu²/2}`; `splPrimOne = F − L` and `splPrimTwo = u (F − L) + i e` are the first two
primitives of `e` used in the three integrations by parts (`E₁`, `E₂` of the route; the third primitive is `iκ₊`).
No frozen statement mentions these definitions. -/

namespace OscInt.Blueprint.StationaryLeading

open MeasureTheory OscInt.Statements
open scoped ContDiff

/-- `e(u) = e^{iu²/2}`, the integrand of the Fresnel primitive. -/
noncomputable def fresnelE (u : ℝ) : ℂ := Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)

/-- `E₁(u) = F(u) − L`, a primitive of `e`. -/
noncomputable def splPrimOne (u : ℝ) : ℂ := fresnelPrim u - fresnelLimit

/-- `E₂(u) = u (F(u) − L) + i e(u)`, a primitive of `E₁`. -/
noncomputable def splPrimTwo (u : ℝ) : ℂ := (u : ℂ) * (fresnelPrim u - fresnelLimit) + Complex.I * fresnelE u

/-- **P-fresnel** The Fresnel primitive: `F′ = e` on the line, `F` is odd, and `|F(x) − L| ≤ 2/x` for `x > 0`, where
`L = √π (1 + i)/2` is the closed form `fresnelLimit` (so `F(x) → L`: the value of the Fresnel integral). -/
def SplFresnelFacts : Prop :=
  (∀ x : ℝ, HasDerivAt fresnelPrim (fresnelE x) x) ∧ (∀ x : ℝ, fresnelPrim (-x) = -fresnelPrim x) ∧
    ∀ x : ℝ, 0 < x → ‖fresnelPrim x - fresnelLimit‖ ≤ 2 / x

/-- **P-bound** `|F| ≤ 7/4` on the line (from VC2-S and VC2-N for the phase `x²/2` on a symmetric interval). -/
def SplFresnelBoundFacts : Prop := ∀ x : ℝ, ‖fresnelPrim x‖ ≤ 7 / 4

/-- **P-kernel** The kernel and its primitives: `E₁′ = e`, `E₂′ = E₁`, `(iκ₊)′ = E₂` on the line; `|E₁| ≤ 4` and
`|E₂| ≤ 3` on `[0, ∞)`; `κ` is odd, continuous, and `|κ| ≤ 7/8` on the line. -/
def SplKernelFacts : Prop :=
  (∀ u : ℝ, HasDerivAt splPrimOne (fresnelE u) u) ∧ (∀ u : ℝ, HasDerivAt splPrimTwo (splPrimOne u) u) ∧
    (∀ u : ℝ, HasDerivAt (fun v => Complex.I * splKernelPos v) (splPrimTwo u) u) ∧
    (∀ u : ℝ, 0 ≤ u → ‖splPrimOne u‖ ≤ 4) ∧ (∀ u : ℝ, 0 ≤ u → ‖splPrimTwo u‖ ≤ 3) ∧
    (∀ τ : ℝ, splKernel (-τ) = -splKernel τ) ∧ Continuous splKernel ∧ ∀ τ : ℝ, ‖splKernel τ‖ ≤ 7 / 8

/-- **P-line** The identity at `λ = 1`: `∫ g e = 2 L g(0) − i ∫ g‴ κ` for every amplitude. -/
def SplLineFacts : Prop :=
  ∀ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ →
    ∫ u, g u * fresnelE u = 2 * fresnelLimit * g 0 - Complex.I * ∫ t, g₃ t * splKernel t

/-- **P-bump** Point masses for the third derivative: for a continuous odd kernel `k` bounded by `M`, every `τ ≥ 0`
and `ε > 0`, a smooth compactly supported amplitude, not identically zero, has
`(|k(τ)| − ε) ‖g‴‖₁ ≤ |∫ g‴ k|`. -/
def SplBumpFacts : Prop :=
  ∀ (k : ℝ → ℂ) (M τ ε : ℝ), Continuous k → (∀ t, k (-t) = -k t) → (∀ t, ‖k t‖ ≤ M) → 0 ≤ τ → 0 < ε →
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      (‖k τ‖ - ε) * (∫ t, ‖g₃ t‖) ≤ ‖∫ t, g₃ t * k t‖

end OscInt.Blueprint.StationaryLeading
