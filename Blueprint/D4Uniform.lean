/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.D4Uniform

/-!
# Blueprint for batch D4U (S4.2U, S4.2O): the parts of the route (definitions only)

Route: `docs/proof-D4U.md`. S4.2U is the ε/2 argument from S4.1′ (a uniform bound on amplitude differences) and S4.2
(the limit for each centre of a finite net); S4.2O is S4.2U applied to the modulation family `{e^{i y·κ} A : ‖y‖ ≤ R}`.
The assembly below is compiled before any part is proved.
-/

namespace OscInt.Blueprint.D4Uniform

open Filter Topology OscInt.Statements

/-- **P-radius** A common radius for S4.1′ (at `y = 0`) and S4.2, with a nonnegative constant. -/
def CommonRadiusFacts : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, D4LimitPhase φ → ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧
    (∀ (A : ℝ × ℝ → ℂ) (M t : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
      ‖oscInt2 (fun κ => t * φ κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)) ∧
    (∀ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M →
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) A) atTop
        (𝓝 ((d4Constant (cubicCoeffs φ) : ℂ) * A 0)))

/-- **P-linear** `oscInt2` is subtractive on amplitudes with C² budgets on a compact set, for a continuous phase. -/
def LinearFacts : Prop :=
  ∀ (Q : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (A B : ℝ × ℝ → ℂ) (M M' : ℝ), Continuous Q → IsCompact K →
    AmpBound 2 K A M → AmpBound 2 K B M' → oscInt2 Q (A - B) = oscInt2 Q A - oscInt2 Q B

/-- **P-mod** The modulations `{e^{i y·κ} A : ‖y‖ ≤ R}` of an amplitude with a C² budget on `B̄(0, δ)` form a
C²-totally bounded family on `B̄(0, δ)`. -/
def ModulationFacts : Prop :=
  ∀ (δ : ℝ) (A : ℝ × ℝ → ℂ) (M R : ℝ), 0 < δ → AmpBound 2 (Metric.closedBall 0 δ) A M →
    AmpTotallyBounded (Metric.closedBall 0 δ)
      {B | ∃ y : ℝ × ℝ, ‖y‖ ≤ R ∧ B = fun κ => Complex.exp (↑(lin y κ) * Complex.I) * A κ}

end OscInt.Blueprint.D4Uniform
