/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.TriangularDecay

/-!
# Batch LOC2: Fourier localisation on the torus for C² cutoffs, with an explicit constant (statements only)

Mathematics: `docs/statements.md`, "Batch LOC2". Written, stamped and blind-reviewed before any Lean proof of this
statement exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1). A proof on paper is older: an external research
packet reviewed in `review/2026-11-28-postK2-packet-answers.md`.

Symbols as in batch K2 (`torusBox = [−π, π]²`, `lin p k = p·k`), and:
* `boxL2 f = ((2π)^{−2} ∫_{[−π, π]²} |f|²)^{1/2}`, the normalised `L²` norm on the box;
* `boxPartial₁ χ`, `boxPartial₂ χ`: the partial derivatives `∂₁χ`, `∂₂χ`; `boxLaplacian χ = ∂₁²χ + ∂₂²χ`;
* `locConstC2 χ = 4 ((3/2) ‖χ‖ + ‖∂₁χ‖ + ‖∂₂χ‖ + ‖Δχ‖)`, norms `boxL2`.

* K2-FQ `TorusLocalizationC2Statement`: K2-F with `C²` instead of smooth cutoffs and the explicit constant
  `D = locConstC2 χ`: for a `C²` function `χ` with support inside `(−π, π)²`, every continuous biperiodic real phase
  `Ψ`, every real `t`, every `p ∈ ℝ²` and every `B`, if every lattice coefficient `|∫_{[−π, π]²} e^{i(tΨ + n·k)} dk|`
  (`n ∈ ℤ²`) is at most `B`, then `|∫_{[−π, π]²} χ e^{it(Ψ + p·k)} dk| ≤ locConstC2 χ · B`.

Modelling choices. Derivatives are Fréchet derivatives evaluated on the unit vectors; the constant depends on `χ`
only through the four norms. The constant is not claimed to be optimal. Weaker regularity (`H²` with zero traces) is
not stated.
-/

namespace OscInt.Statements
open MeasureTheory
open scoped ContDiff

/-- The normalised `L²` norm on the box: `((2π)^{−2} ∫_{[−π, π]²} |f|²)^{1/2}`. -/
noncomputable def boxL2 (f : ℝ × ℝ → ℂ) : ℝ :=
  Real.sqrt ((1 / (4 * Real.pi ^ 2)) * ∫ k in torusBox, ‖f k‖ ^ 2)

/-- The partial derivative `∂₁χ`. -/
noncomputable def boxPartial₁ (χ : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ := fderiv ℝ χ k (1, 0)

/-- The partial derivative `∂₂χ`. -/
noncomputable def boxPartial₂ (χ : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ := fderiv ℝ χ k (0, 1)

/-- The Laplacian `∂₁²χ + ∂₂²χ`. -/
noncomputable def boxLaplacian (χ : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  iteratedFDeriv ℝ 2 χ k ![(1, 0), (1, 0)] + iteratedFDeriv ℝ 2 χ k ![(0, 1), (0, 1)]

/-- The localisation constant `4 ((3/2) ‖χ‖ + ‖∂₁χ‖ + ‖∂₂χ‖ + ‖Δχ‖)` (normalised `L²` norms on the box). -/
noncomputable def locConstC2 (χ : ℝ × ℝ → ℂ) : ℝ :=
  4 * ((3 / 2) * boxL2 χ + boxL2 (boxPartial₁ χ) + boxL2 (boxPartial₂ χ) + boxL2 (boxLaplacian χ))

/-- **K2-FQ** Fourier localisation for a `C²` cutoff `χ` supported inside `(−π, π)²`, with the explicit constant
`locConstC2 χ`: a bound `B` on every lattice coefficient of `e^{itΨ}` gives `locConstC2 χ · B` at every real velocity. -/
def TorusLocalizationC2Statement : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 2 χ →
    tsupport χ ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi →
    ∀ (Ψ : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) (B : ℝ), Continuous Ψ →
      (∀ k : ℝ × ℝ, Ψ (k.1 + 2 * Real.pi, k.2) = Ψ k) → (∀ k : ℝ × ℝ, Ψ (k.1, k.2 + 2 * Real.pi) = Ψ k) →
      (∀ n : ℤ × ℤ, ‖∫ k in torusBox,
          Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤ B) →
        ‖∫ k in torusBox, χ k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)‖ ≤ locConstC2 χ * B

theorem statement_pin_TorusLocalizationC2 : TorusLocalizationC2Statement = TorusLocalizationC2Statement := rfl

end OscInt.Statements
