/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.TorusLocalizationC2

/-!
# Blueprint of batch LOC2 (K2-FQ): the parts of the route (definitions only)

Route: `docs/proof-LOC2.md`. `c_j(δ) = ∫_box χ e^{i(δ − j)·k}` as in batch K2's P13/P14; `h = χ e^{iδ·k}`;
`g = h − Δh`. Offsets are nearest-integer (`|δᵢ| ≤ 1/2`), not floor offsets.
-/

namespace OscInt.Blueprint.LOC2

open Set MeasureTheory OscInt.Statements

/-- `e^{−ij·k}`, the conjugate lattice character. -/
noncomputable def charNeg (j : ℤ × ℤ) (k : ℝ × ℝ) : ℂ :=
  Complex.exp (↑(-((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2)) * Complex.I)

/-- **Q6** Torus expansion for a continuous cutoff (K2's P14 with `Continuous χ` in place of C^∞). -/
def LocExpansionFacts : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, Continuous χ → tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi →
    ∀ δ : ℝ × ℝ,
      Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖) →
      ∀ g : ℝ × ℝ → ℂ, Continuous g →
        HasSum (fun j : ℤ × ℤ => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) *
            (∫ k in torusBox, χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)) *
            ∫ k in torusBox, Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k)
          (∫ k in torusBox, χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) * g k)

/-- **Q1** Two integrations by parts per coordinate: for `h` of class C² with support inside the open box,
`(1 + |j|²) ∫ h e^{−ij·k} = ∫ (h − Δh) e^{−ij·k}`. -/
def LocIbpFacts : Prop :=
  ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ 2 h → tsupport h ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi →
    ∀ j : ℤ × ℤ, ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2 : ℝ) : ℂ) * (∫ k in torusBox, h k * charNeg j k) =
      ∫ k in torusBox, (h k - boxLaplacian h k) * charNeg j k

/-- **Q2** Bessel's inequality on the box: `Σ_j |∫ g e^{−ij·k}|² ≤ 4π² ∫ |g|²` for continuous `g`. -/
def LocBesselFacts : Prop :=
  ∀ g : ℝ × ℝ → ℂ, Continuous g →
    Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, g k * charNeg j k‖ ^ 2) ∧
      ∑' j : ℤ × ℤ, ‖∫ k in torusBox, g k * charNeg j k‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ∫ k in torusBox, ‖g k‖ ^ 2

/-- **Q3** The shell sum: `Σ_{j ∈ ℤ²} (1 + |j|²)^{−2} ≤ 13`. -/
def LocShellFacts : Prop :=
  Summable (fun j : ℤ × ℤ => ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹) ∧
    ∑' j : ℤ × ℤ, ((1 + (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ^ 2)⁻¹ ≤ 13

/-- **Q5** The Laplacian of `h = χ e^{iδ·k}` for `|δᵢ| ≤ 1/2`: `h` is C², supported where χ is, and
`‖h − Δh‖ ≤ (3/2)‖χ‖ + ‖∂₁χ‖ + ‖∂₂χ‖ + ‖Δχ‖` (normalised `L²` norms on the box). -/
def LocLaplaceFacts : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 2 χ → tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi →
    ∀ δ : ℝ × ℝ, |δ.1| ≤ 1 / 2 → |δ.2| ≤ 1 / 2 →
      let h : ℝ × ℝ → ℂ := fun k => χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I)
      ContDiff ℝ 2 h ∧ tsupport h ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi ∧
        Continuous (fun k => h k - boxLaplacian h k) ∧
        boxL2 (fun k => h k - boxLaplacian h k) ≤
          (3 / 2) * boxL2 χ + boxL2 (boxPartial₁ χ) + boxL2 (boxPartial₂ χ) + boxL2 (boxLaplacian χ)

/-- The explicit coefficient bound: summable `c_j(δ)` with `Σ_j |c_j(δ)| ≤ 4π² · locConstC2 χ` for `|δᵢ| ≤ 1/2`. -/
def LocCoefFacts : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 2 χ → tsupport χ ⊆ Ioo (-Real.pi) Real.pi ×ˢ Ioo (-Real.pi) Real.pi →
    ∀ δ : ℝ × ℝ, |δ.1| ≤ 1 / 2 → |δ.2| ≤ 1 / 2 →
      Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖) ∧
        ∑' j : ℤ × ℤ, ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖ ≤ 4 * Real.pi ^ 2 * locConstC2 χ

/-- **Q4** Cauchy–Schwarz combination: Q1, Q2, Q3 and Q5 give the explicit coefficient bound (`√13 ≤ 4`). -/
def LocCombineFacts : Prop :=
  LocIbpFacts → LocBesselFacts → LocShellFacts → LocLaplaceFacts → LocCoefFacts

end OscInt.Blueprint.LOC2
