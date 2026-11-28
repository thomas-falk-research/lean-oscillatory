/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.StationaryLeading

/-!
# Batch SPL-N: the best constant of the quadratic-phase remainder, to within 10⁻⁸ (statements only)

Mathematics: `docs/statements.md`, "Batch SPL-N". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1). A proof on paper and an exact rational certificate
are older: an external research packet reviewed in `review/2026-11-28-postK2-packet-answers.md`, and a one-point
Lean prototype of session 15 kept in scratch (`review/2026-11-26-session15-gates-answers.md`, section 4).

Symbols as in batch SPL (`OscInt/Statements/StationaryLeading.lean`): the odd kernel `κ = splKernel`, the remainder
`R(g, λ) = splRemainder g λ`, the amplitude class `SplAmplitude`.

* SPL-NU `SplKernelCapStatement`: `|κ(τ)| ≤ 360987/500000 = 0.721974` for every real `τ`.
* SPL-NL `SplKernelLowerStatement`: `|κ(8123/5000)| > 72197399/10⁸ = 0.72197399`.
* SPL-NK `StationaryLeadingSharpStatement`: `|R(g, λ)| ≤ (360987/500000) ‖g₃‖₁ λ^{−3/2}` (SPL-K with `7/8` replaced).
* SPL-NC `StationaryLeadingSharpnessStatement`: for every `c ≤ 72197399/10⁸` the bound of SPL-NK with constant `c`
  fails for some amplitude and some `λ > 0`.

Together, SPL-NK and SPL-NC place the best constant of SPL-K in `(0.72197399, 0.721974]`. Nothing is said about where
`|κ|` attains its supremum, nor whether it does. Modelling choices as in batch SPL.
-/

namespace OscInt.Statements
open MeasureTheory

/-- **SPL-NU** The kernel is bounded by `360987/500000 = 0.721974`: `|κ(τ)| ≤ 360987/500000` for every real `τ`. -/
def SplKernelCapStatement : Prop :=
  ∀ τ : ℝ, ‖splKernel τ‖ ≤ (360987 / 500000 : ℝ)

theorem statement_pin_SplKernelCap : SplKernelCapStatement = SplKernelCapStatement := rfl

/-- **SPL-NL** The kernel exceeds `72197399/10⁸ = 0.72197399` at `τ = 8123/5000`. -/
def SplKernelLowerStatement : Prop :=
  (72197399 / 100000000 : ℝ) < ‖splKernel (8123 / 5000)‖

theorem statement_pin_SplKernelLower : SplKernelLowerStatement = SplKernelLowerStatement := rfl

/-- **SPL-NK** The leading term of the quadratic-phase integral with remainder at most
`(360987/500000) ‖g‴‖₁ λ^{−3/2}`. -/
def StationaryLeadingSharpStatement : Prop :=
  ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
    ‖splRemainder g lam‖ ≤ (360987 / 500000 : ℝ) * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)

theorem statement_pin_StationaryLeadingSharp : StationaryLeadingSharpStatement = StationaryLeadingSharpStatement :=
  rfl

/-- **SPL-NC** No constant `c ≤ 72197399/10⁸` bounds the remainder: for each such `c` some amplitude and some `λ > 0`
have `|R(g, λ)| > c ‖g‴‖₁ λ^{−3/2}`. -/
def StationaryLeadingSharpnessStatement : Prop :=
  ∀ c : ℝ, c ≤ (72197399 / 100000000 : ℝ) →
    ¬ ∀ (g g₁ g₂ g₃ : ℝ → ℂ) (lam : ℝ), SplAmplitude g g₁ g₂ g₃ → 0 < lam →
      ‖splRemainder g lam‖ ≤ c * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2)

theorem statement_pin_StationaryLeadingSharpness :
    StationaryLeadingSharpnessStatement = StationaryLeadingSharpnessStatement := rfl

end OscInt.Statements
