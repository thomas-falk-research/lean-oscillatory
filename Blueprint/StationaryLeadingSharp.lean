/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.StationaryLeadingSharp

/-!
# Blueprint of batch SPL-N (SPL-NU, SPL-NL, SPL-NK, SPL-NC)

Route: `docs/proof-SPLN.md`. One `…Facts` proposition per part; the lead's assembly
(`OscInt/Front/StationaryLeadingSharpAssembly.lean`) derives the four statements from them and from the proved
batch SPL. `κ₊ = splKernelPos`, `I_j(x) = x^{2j+3} / (2^j j! (2j+1)(2j+2)(2j+3))`.
-/

namespace OscInt.Blueprint.SPLN

open OscInt.Statements
open scoped ContDiff

/-- `I_j(x)`, the Taylor weights of `Φ(x) = ∫₀ˣ (x − v)² e^{iv²/2}/2 dv`. -/
noncomputable def splnI (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j + 3) / (2 ^ j * (j.factorial : ℝ) * ((2 * j + 1) * (2 * j + 2) * (2 * j + 3)))

/-- The polynomial centre `x + iLx²/2 − i Σ_{j<32} i^j I_j(x)` with `L = s(1 + i)/2`, as a function of `s`. -/
noncomputable def splnCentre (s x : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * ((s : ℂ) * (1 + Complex.I) / 2) * (x : ℂ) ^ 2 / 2 -
    Complex.I * ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ)

/-- **N1 + N2** (Taylor enclosure): for `0 ≤ x ≤ 4`, `‖κ₊(x) − centre(√π, x)‖ ≤ 2 I_32(x)`. -/
def SplnTaylorFacts : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 4 → ‖splKernelPos x - splnCentre (Real.sqrt Real.pi) x‖ ≤ 2 * splnI 32 x

/-- **N4** (second derivative): on `(0, ∞)`, `κ₊` has a derivative `κ₁`, which has a derivative `κ₂`, `‖κ₂(x)‖ ≤ 2/x`. -/
def SplnSecondFacts : Prop :=
  ∃ κ₁ κ₂ : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt splKernelPos (κ₁ x) x) ∧ (∀ x, 0 < x → HasDerivAt κ₁ (κ₂ x) x) ∧
    ∀ x, 0 < x → ‖κ₂ x‖ ≤ 2 / x

/-- **N5** (vector interpolation): a complex function with two derivatives on `[a, b]`, `‖f″‖ ≤ M`, is at most
`max(‖f(a)‖, ‖f(b)‖) + M (b − a)²/8` on `[a, b]`. -/
def SplnInterpFacts : Prop :=
  ∀ (f f₁ f₂ : ℝ → ℂ) (a b M : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x) → (∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x) →
    (∀ x ∈ Set.Icc a b, ‖f₂ x‖ ≤ M) →
      ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ max ‖f a‖ ‖f b‖ + M * (b - a) ^ 2 / 8

/-- **N8** (the two branches outside the cells): `‖κ₊‖ ≤ 11/16` on `[0, 1/2]` and `≤ 277/400` on `[4, ∞)`. -/
def SplnBranchFacts : Prop :=
  (∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → ‖splKernelPos x‖ ≤ 11 / 16) ∧
    (∀ x : ℝ, 4 ≤ x → ‖splKernelPos x‖ ≤ 277 / 400)

/-- **N3 + N6 + N7** (the 40 cells): from N1 + N2, N4 and N5, `‖κ₊‖ ≤ 360987/500000` on `[1/2, 4]`. -/
def SplnCellsFacts : Prop :=
  SplnTaylorFacts → SplnSecondFacts → SplnInterpFacts →
    ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 4 → ‖splKernelPos x‖ ≤ 360987 / 500000

/-- **N9** (the lower point): from N1 + N2, `‖κ₊(8123/5000)‖ > 72197399/10⁸`. -/
def SplnLowerFacts : Prop :=
  SplnTaylorFacts → (72197399 / 100000000 : ℝ) < ‖splKernelPos (8123 / 5000)‖

/-- **N10** (nonzero third derivative): a smooth compactly supported amplitude that is not identically zero has
`‖g₃‖₁ > 0` (else `g₃ = 0`, so `g` is a polynomial of degree at most 2 with compact support, so `g = 0`). -/
def SplnThirdPosFacts : Prop :=
  ∀ g g₁ g₂ g₃ : ℝ → ℂ, SplAmplitude g g₁ g₂ g₃ → ContDiff ℝ ∞ g → HasCompactSupport g → (∃ x, g x ≠ 0) →
    0 < ∫ t, ‖g₃ t‖

end OscInt.Blueprint.SPLN
