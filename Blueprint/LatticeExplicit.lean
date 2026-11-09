/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeExplicit

/-! # Blueprint for batch LE (route `docs/proof-LE.md`): the parts of T0E. Definitions only. -/

namespace OscInt.Blueprint

/-- **P-angle** `|x| ≤ π/4 → 2^{−1/2} ≤ cos x`. -/
def LEAngleFacts : Prop :=
  ∀ x : ℝ, |x| ≤ Real.pi / 4 → (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ Real.cos x

/-- **P-vdc2** A piece where `|cos| ≥ 2^{−1/2}`: S1.2 gives `8 · 2^{1/4} t^{−1/2}`. -/
def LEPiece2Facts : Prop :=
  ∀ t ξ a b : ℝ, 0 < t → a ≤ b → (∀ x ∈ Set.Ioo a b, (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.cos x|) →
    ‖∫ k in a..b, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)‖ ≤
      8 * (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2)

/-- **P-vdc3** A piece where `|sin| ≥ 2^{−1/2}`: S1.3 gives `18 · 2^{1/6} t^{−1/3}`. -/
def LEPiece3Facts : Prop :=
  ∀ t ξ a b : ℝ, 0 < t → a ≤ b → (∀ x ∈ Set.Ioo a b, (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ |Real.sin x|) →
    ‖∫ k in a..b, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)‖ ≤
      18 * (2 : ℝ) ^ ((1 : ℝ) / 6) * t ^ (-(1 : ℝ) / 3)

end OscInt.Blueprint
