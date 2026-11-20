import OscInt.Statements.SecondDerivSharp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Batch SPL: the leading term of a quadratic-phase integral with an explicit remainder (statements only)

Mathematics: `docs/statements.md`, "Batch SPL". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

For an amplitude `g` with derivatives `g₁, g₂, g₃` at every point, all four integrable, and `λ > 0`, let
`R(g, λ) = ∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}` (`splRemainder`), and let `κ` be the odd kernel
`κ(τ) = F(τ)/2 + τ e^{iτ²/2}/2 + (iτ²/2)(F(∞) − F(τ))` for `τ ≥ 0` (`splKernel`), where `F(x) = ∫₀ˣ e^{iv²/2} dv`
(`fresnelPrim`) and `F(∞) = √π (1 + i)/2` (`fresnelLimit`).

* SPL-I `StationaryLeadingIdentityStatement`: `R(g, λ) = −i λ^{−3/2} ∫ g₃(t) κ(√λ t) dt`.
* SPL-S `StationaryLeadingStatement`: `|R(g, λ)| ≤ |κ(τ)| ‖g₃‖₁ λ^{−3/2}` for some `τ ≥ 0`.
* SPL-K `StationaryLeadingSevenEighthsStatement`: `|R(g, λ)| ≤ (7/8) ‖g₃‖₁ λ^{−3/2}`.
* SPL-A `StationaryLeadingAttainedStatement`: for every `τ ≥ 0` and `ε > 0` a smooth compactly supported amplitude,
  not identically zero, has `|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g₃‖₁`; so no constant below `sup |κ|` is true in SPL-K.

Modelling choices: the derivatives are given as functions with `HasDerivAt` at every point (no continuity of `g₃` is
asked); integrals over the line are Bochner integrals, so `Integrable g` is what makes `∫ g(u) e^{iλu²/2} du` the
integral it denotes; `F(∞)` is a closed form, not a limit; the kernel is defined by cases at `0`; the power
`λ^{−3/2}` is `Real.rpow`. The identity behind these statements is classical (Erdélyi); nothing is claimed as new.
-/

namespace OscInt.Statements
open MeasureTheory
open scoped ContDiff

/-- `F(x) = ∫₀ˣ e^{iv²/2} dv`, the Fresnel primitive. -/
noncomputable def fresnelPrim (x : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..x, Complex.exp (((v ^ 2 / 2 : ℝ) : ℂ) * Complex.I)

/-- `F(∞) = √π (1 + i)/2`, the limit of the Fresnel primitive at `+∞`. -/
noncomputable def fresnelLimit : ℂ := ((Real.sqrt Real.pi : ℝ) : ℂ) * (1 + Complex.I) / 2

/-- The kernel on the right half-line: `κ₊(τ) = F(τ)/2 + τ e^{iτ²/2}/2 + (iτ²/2)(F(∞) − F(τ))`. -/
noncomputable def splKernelPos (τ : ℝ) : ℂ :=
  fresnelPrim τ / 2 + (τ : ℂ) * Complex.exp (((τ ^ 2 / 2 : ℝ) : ℂ) * Complex.I) / 2 +
    Complex.I * (τ : ℂ) ^ 2 / 2 * (fresnelLimit - fresnelPrim τ)

/-- The kernel `κ`: `κ₊` on `[0, ∞)`, extended to the left as an odd function. -/
noncomputable def splKernel (τ : ℝ) : ℂ := if 0 ≤ τ then splKernelPos τ else -splKernelPos (-τ)

/-- The amplitudes: `g` with derivatives `g₁, g₂, g₃` of orders one to three at every point, all four integrable. -/
def SplAmplitude (g g₁ g₂ g₃ : ℝ → ℂ) : Prop :=
  (∀ x, HasDerivAt g (g₁ x) x) ∧ (∀ x, HasDerivAt g₁ (g₂ x) x) ∧ (∀ x, HasDerivAt g₂ (g₃ x) x) ∧
    Integrable g ∧ Integrable g₁ ∧ Integrable g₂ ∧ Integrable g₃

/-- `R(g, λ) = ∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}`: the integral minus its stationary-phase leading term. -/
noncomputable def splRemainder (g : ℝ → ℂ) (lam : ℝ) : ℂ :=
  (∫ u, g u * Complex.exp (((lam * u ^ 2 / 2 : ℝ) : ℂ) * Complex.I)) -
    g 0 * ((Real.sqrt (2 * Real.pi / lam) : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- **SPL-I** The remainder of the quadratic-phase leading term as an integral of `g‴` against the kernel:
`R(g, λ) = −i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt`. -/
def StationaryLeadingIdentityStatement : Prop :=
  ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
    splRemainder g lam =
      -Complex.I * ((lam ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * ∫ t, g₃ t * splKernel (Real.sqrt lam * t)

theorem statement_pin_StationaryLeadingIdentity :
    StationaryLeadingIdentityStatement = StationaryLeadingIdentityStatement := rfl

/-- **SPL-S** The leading term of the quadratic-phase integral with its remainder bounded through the kernel:
`|R(g, λ)| ≤ |κ(τ)| ‖g‴‖₁ λ^{−3/2}` for some `τ ≥ 0`. -/
def StationaryLeadingStatement : Prop :=
  ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
    ∃ τ : ℝ, 0 ≤ τ ∧ ‖splRemainder g lam‖ ≤ ‖splKernel τ‖ * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)

theorem statement_pin_StationaryLeading : StationaryLeadingStatement = StationaryLeadingStatement := rfl

/-- **SPL-K** The leading term of the quadratic-phase integral with remainder at most `(7/8) ‖g‴‖₁ λ^{−3/2}`. -/
def StationaryLeadingSevenEighthsStatement : Prop :=
  ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
    ‖splRemainder g lam‖ ≤ (7 / 8 : ℝ) * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)

theorem statement_pin_StationaryLeadingSevenEighths :
    StationaryLeadingSevenEighthsStatement = StationaryLeadingSevenEighthsStatement := rfl

/-- **SPL-A** The kernel bound of SPL-S is attained in the limit by smooth compactly supported amplitudes: for
every `τ ≥ 0` and `ε > 0` some such `g ≠ 0` has `|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g‴‖₁`. -/
def StationaryLeadingAttainedStatement : Prop :=
  ∀ τ ε : ℝ, 0 ≤ τ → 0 < ε →
    ∃ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∃ x, g x ≠ 0) ∧
      (‖splKernel τ‖ - ε) * (∫ t, ‖g₃ t‖) ≤ ‖splRemainder g 1‖

theorem statement_pin_StationaryLeadingAttained :
    StationaryLeadingAttainedStatement = StationaryLeadingAttainedStatement := rfl

end OscInt.Statements

/- Attribution, appended after the freeze; not part of the frozen text (stamps/pins.txt).
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: Apache-2.0 -/
