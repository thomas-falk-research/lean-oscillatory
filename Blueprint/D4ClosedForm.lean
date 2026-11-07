import OscInt.Statements.D4Limit

/-!
# Blueprint for S4.4 (definitions only)

Route: `docs/proof-S44.md`. Each part is proved as `theorem OscInt.D4.<part> … : <Prop>` under `OscInt/D4/`; the
assembly `OscInt.D4.d4ConstantClosedForm_of` (`OscInt/D4/ClosedForm.lean`) derives
`D4ConstantClosedFormStatement` from E1, E2, E3, E5, E6c, E7.

* `lineCubic q u = C(1, u) = a + b u + c u² + d u³` and `lineMoment q = ∫_ℝ |C(1, u)|^{-2/3} du` (the angular
  integral in the chart `u = tan θ`).
* `lin2 g` is the linear map of `ℝ²` with matrix `[[g₁, g₂], [g₃, g₄]]`, `det2 g` its determinant, and
  `cubicComp q g` the coefficients of `C ∘ lin2 g` (read off from the values at `(1,0), (0,1), (1,1), (1,−1)`).
-/

namespace OscInt.Blueprint

open Set MeasureTheory Filter Topology OscInt.Statements

/-- `C(1, u) = a + b u + c u² + d u³` for `q = (a, b, c, d)`. -/
noncomputable def lineCubic (q : ℝ × ℝ × ℝ × ℝ) (u : ℝ) : ℝ := cubicForm q (1, u)

/-- `∫_ℝ |C(1, u)|^{-2/3} du` (Bochner integral over `ℝ`). -/
noncomputable def lineMoment (q : ℝ × ℝ × ℝ × ℝ) : ℝ := ∫ u : ℝ, |lineCubic q u| ^ (-(2 : ℝ) / 3)

/-- The linear map `z ↦ (g₁ z₁ + g₂ z₂, g₃ z₁ + g₄ z₂)` of `ℝ²`, for `g = (g₁, g₂, g₃, g₄)`. -/
noncomputable def lin2 (g : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (g.1 * z.1 + g.2.1 * z.2, g.2.2.1 * z.1 + g.2.2.2 * z.2)

/-- `det [[g₁, g₂], [g₃, g₄]] = g₁ g₄ − g₂ g₃`. -/
noncomputable def det2 (g : ℝ × ℝ × ℝ × ℝ) : ℝ := g.1 * g.2.2.2 - g.2.1 * g.2.2.1

/-- The coefficients of the binary cubic `z ↦ C(lin2 g z)`: with `f = C ∘ lin2 g`,
`(f(1,0), (f(1,1) − f(1,−1))/2 − f(0,1), (f(1,1) + f(1,−1))/2 − f(1,0), f(0,1))`. -/
noncomputable def cubicComp (q g : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (cubicForm q (lin2 g (1, 0)),
    (cubicForm q (lin2 g (1, 1)) - cubicForm q (lin2 g (1, -1))) / 2 - cubicForm q (lin2 g (0, 1)),
    (cubicForm q (lin2 g (1, 1)) + cubicForm q (lin2 g (1, -1))) / 2 - cubicForm q (lin2 g (1, 0)),
    cubicForm q (lin2 g (0, 1)))

/-- **E1** The cosine moment: `∫₀^∞ cos u · u^{-1/3} du = Γ(2/3)/2` (the `limUnder` value). -/
def CosMomentValueFacts : Prop := cosMoment = Real.Gamma (2 / 3) / 2

/-- **E2** The chart `u = tan θ`: `J(C) = 2 ∫_ℝ |C(1, u)|^{-2/3} du` for `disc ≠ 0`. -/
def AngularLineFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → angularMoment q = 2 * lineMoment q

/-- **E3** `GL₂` covariance of the angular integral: `J(C ∘ g) = J(C)/|det g|` for `disc C ≠ 0`, `det g ≠ 0`. -/
def CovarianceFacts : Prop :=
  ∀ q g : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → det2 g ≠ 0 →
    angularMoment (cubicComp q g) = angularMoment q / |det2 g|

/-- **E5** Normal forms: a cubic with `disc < 0` is `x(x² + y²) = (1, 0, 1, 0)` after a linear change of
variables, one with `disc > 0` is `xy(x + y) = (0, 1, 1, 0)`. -/
def CubicNormalFormFacts : Prop :=
  (∀ q : ℝ × ℝ × ℝ × ℝ, disc q < 0 → ∃ g, det2 g ≠ 0 ∧ cubicComp q g = (1, 0, 1, 0)) ∧
    ∀ q : ℝ × ℝ × ℝ × ℝ, 0 < disc q → ∃ g, det2 g ≠ 0 ∧ cubicComp q g = (0, 1, 1, 0)

/-- **E6a** Beta integral on the half-line: `∫₀^∞ t^{a-1} (1 + t)^{-(a+b)} dt = Γ(a)Γ(b)/Γ(a+b)`. -/
def BetaIoiFacts : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    ∫ t in Ioi (0 : ℝ), t ^ (a - 1) * (1 + t) ^ (-(a + b)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- **E6b** Beta integral on the unit interval: `∫₀¹ x^{a-1} (1 − x)^{b-1} dx = Γ(a)Γ(b)/Γ(a+b)`. -/
def BetaUnitFacts : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- **E6c** The two normal forms: `∫_ℝ (1 + u²)^{-2/3} du = √π Γ(1/6)/Γ(2/3)` and
`∫_ℝ |u + u²|^{-2/3} du = 3 Γ(1/3)²/Γ(2/3)`. -/
def LineMomentValuesFacts : Prop :=
  lineMoment (1, 0, 1, 0) = Real.sqrt Real.pi * Real.Gamma (1 / 6) / Real.Gamma (2 / 3) ∧
    lineMoment (0, 1, 1, 0) = 3 * Real.Gamma (1 / 3) ^ 2 / Real.Gamma (2 / 3)

/-- **E7** Duplication and reflection at `1/6`, `1/3`: `√π Γ(1/6) = √3 Γ(1/3)² / 2^{1/3}`. -/
def GammaSixthFacts : Prop :=
  Real.sqrt Real.pi * Real.Gamma (1 / 6) = Real.sqrt 3 * Real.Gamma (1 / 3) ^ 2 / 2 ^ ((1 : ℝ) / 3)

end OscInt.Blueprint
