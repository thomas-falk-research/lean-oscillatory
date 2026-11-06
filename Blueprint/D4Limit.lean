import OscInt.Statements.D4Limit

/-!
# Blueprint for S4.3 (definitions only)

Route: `docs/proof-S43.md`. Each part is proved as `theorem OscInt.D4.<part> : <Prop>` under `OscInt/D4/`; the
assembly `OscInt.D4.d4ConstantPos_of` (`OscInt/D4/ConstantPos.lean`) derives `D4ConstantPosStatement`. The whole
proof must pass `GammaFree.lean` (no Gamma, Beta or Mellin constant in its transitive closure).

* `circleCubic q θ = C(cos θ, sin θ)` for `q = (a, b, c, d)`.
-/

namespace OscInt.Blueprint

open Set MeasureTheory Filter Topology OscInt.Statements

/-- The cubic on the unit circle, `θ ↦ C(cos θ, sin θ)`. -/
noncomputable def circleCubic (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) : ℝ := cubicForm q (Real.cos θ, Real.sin θ)

/-- **C1** One integration by parts: `∫₀^R cos u · u^{-1/3} du = R^{-1/3} sin R + (1/3) ∫₀^R sin u · u^{-4/3} du`. -/
def CosIBPFacts : Prop :=
  ∀ R : ℝ, 0 < R →
    cosMomentPartial R = R ^ (-(1 : ℝ) / 3) * Real.sin R +
      (1 / 3) * ∫ u in (0 : ℝ)..R, Real.sin u * u ^ (-(4 : ℝ) / 3)

/-- **C2** The sine moment `∫₀^∞ sin u · u^{-4/3} du` converges (as an improper integral) to a positive number
(alternating series: on `[2kπ, 2kπ + 2π]` the positive hump outweighs the negative one because `u^{-4/3}` decreases). -/
def SinMomentFacts : Prop :=
  ∃ S : ℝ, 0 < S ∧ Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, Real.sin u * u ^ (-(4 : ℝ) / 3)) atTop (𝓝 S)

/-- **C3** For `disc q ≠ 0`, the cubic and its derivative on the circle never vanish together (a common zero is a
repeated real linear factor). -/
def CircleNondegFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → ∀ θ : ℝ, circleCubic q θ = 0 → deriv (circleCubic q) θ ≠ 0

/-- **C4** A `C¹` function whose zeros on `[a, b]` are simple has `|g|^{-α}` integrable on `[a, b]` for `0 ≤ α < 1`. -/
def SingularPowerFacts : Prop :=
  ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → ∀ a b : ℝ, a ≤ b → (∀ x ∈ Icc a b, g x ≠ 0 ∨ deriv g x ≠ 0) →
    ∀ α : ℝ, 0 ≤ α → α < 1 → IntervalIntegrable (fun x => |g x| ^ (-α)) volume a b

/-- **C5** For `disc q ≠ 0`, the angular integral is positive once the integrand is integrable. -/
def AngularPosFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 →
    IntervalIntegrable (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) volume 0 (2 * Real.pi) →
      0 < angularMoment q

end OscInt.Blueprint
