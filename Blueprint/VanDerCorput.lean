/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen, Thomas Falk III
Modified 2026 by Thomas Falk III: derived from roos-j/lean-oscillatory and adapted to OscInt's frozen
statements; the changes are described in this file's module docstring.
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.VanDerCorput

/-!
# Blueprint for S1 (van der Corput)

Intermediate propositions for the proof of `VdC1Statement`, `VdC2Statement`, `VdC3Statement`. Definitions only.
Each part is proved as `theorem OscInt.VanDerCorput.<part> (hyps) : <Prop>` in its own file under
`OscInt/VanDerCorput/`; the assembly `OscInt/VanDerCorput/Final.lean` combines them.

Route (ported from J. Roos and M. Praveen, `roos-j/lean-oscillatory`, after Stein VIII §1.2):
P1 integration by parts with `u = 1/(iφ')`; P2 integration by parts against `F(x) = ∫_a^x e^{iφ}`;
P0 + P3, P4 splitting at the near-zero of the lower-order derivative.
-/

namespace OscInt.Blueprint

open Set MeasureTheory Complex OscInt.Statements

/-- **P0** (splitting point). If `g` has derivative `g'` on `[a, b]` with `μ ≤ |g'|` on `(a, b)`, then `g` is
monotone or antitone on `[a, b]` and some `d ∈ [a, b]` has `μ |x - d| ≤ |g x|` for all `x ∈ [a, b]`. -/
def SplitFacts : Prop :=
  ∀ (g g' : ℝ → ℝ) (a b μ : ℝ), a ≤ b → 0 < μ → HasDerivOn g g' a b → (∀ x ∈ Ioo a b, μ ≤ |g' x|) →
    (MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b)) ∧
      ∃ d ∈ Icc a b, ∀ x ∈ Icc a b, μ * |x - d| ≤ |g x|

/-- **P1** (first derivative, no amplitude). -/
def VdC1PlainFacts : Prop :=
  ∀ (φ φ' φ'' : ℝ → ℝ) (a b ν : ℝ), a ≤ b → 0 < ν → HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b →
    (MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b)) → (∀ x ∈ Ioo a b, ν ≤ |φ' x|) →
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 3 / ν

/-- **P2** (amplitude transfer). A bound `C` for `∫_a^y e^{iφ}` uniformly in `y ∈ [a, b]` gives
`|∫_a^b e^{iφ} ψ| ≤ C (|ψ(b)| + ∫_a^b |ψ'|)`. -/
def AmplitudeTransferFacts : Prop :=
  ∀ (φ : ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b C : ℝ), a ≤ b → 0 ≤ C → ContinuousOn φ (Icc a b) →
    AmplitudeOn ψ ψ' a b → (∀ y ∈ Icc a b, ‖∫ x in a..y, Complex.exp (↑(φ x) * Complex.I)‖ ≤ C) →
    ‖oscInt φ ψ a b‖ ≤ C * ampNorm ψ ψ' a b

/-- **P3** (second derivative, no amplitude). -/
def VdC2PlainFacts : Prop :=
  ∀ (φ φ' φ'' : ℝ → ℝ) (a b μ : ℝ), a ≤ b → 0 < μ → HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b →
    (∀ x ∈ Ioo a b, μ ≤ |φ'' x|) →
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 8 / √μ

/-- **P4** (third derivative, no amplitude). -/
def VdC3PlainFacts : Prop :=
  ∀ (φ φ' φ'' φ''' : ℝ → ℝ) (a b μ : ℝ), a ≤ b → 0 < μ → HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b →
    HasDerivOn φ'' φ''' a b → (∀ x ∈ Ioo a b, μ ≤ |φ''' x|) →
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 18 * μ ^ (-(1 : ℝ) / 3)

end OscInt.Blueprint
