import OscInt

/-!
# A downstream use of OscInt

Uses the theorems by their reviewed statement names (`stamps/statements.json`); the types of `OscInt.d4Limit` and
`OscInt.stationaryPhase` *are* `D4LimitStatement` and `StationaryPhaseStatement`, so anything derived from them
inherits OscInt's trust chain. CI checks this project with `tools/oscint_check.py`.
-/

open OscInt.Statements

/-- The two results a downstream dispersive estimate typically needs, as one hypothesis-free fact. -/
theorem consumer_inputs : StationaryPhaseStatement ∧ D4LimitStatement :=
  ⟨OscInt.stationaryPhase, OscInt.d4Limit⟩

/-- Specialisation: the D4 limit for the hyperbolic umbilic `x³ + y³` (hypotheses from OscInt's own sanity theorem). -/
theorem consumer_d4Limit_cubes :
    ∃ δ > 0, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M →
      Filter.Tendsto
        (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * (κ.1 ^ 3 + κ.2 ^ 3)) A)
        Filter.atTop
        (nhds ((d4Constant (cubicCoeffs fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) : ℂ) * A 0)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sanity_D4Limit_hyps
  exact OscInt.d4Limit _ h1 h2 h3 h4 h5

/-- The front end (`OscInt/API.lean`): the D4 limit with its closed-form constant for one `C²` amplitude, without
`AmpBound`: at the elliptic umbilic `x³ − 3xy²` (`disc = 108`) the limit is `√π Γ(1/6)/3 · A(0)`. -/
theorem consumer_elliptic_limit :
    ∃ δ > 0, ∀ A : ℝ × ℝ → ℂ, ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ →
      Filter.Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
          ∫ k : ℝ × ℝ, Complex.exp (↑(t * OscInt.D4.genCubic 1 0 (-3) 0 k) * Complex.I) * A k) Filter.atTop
        (nhds (((Real.sqrt Real.pi * Real.Gamma (1 / 6) / 3 : ℝ) : ℂ) * A 0)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := OscInt.API.Sanity.apiSanity_elliptic_hyps
  obtain ⟨δ, hδ, hlim⟩ := OscInt.API.d4LimitClosedForm _ h1 h2 h3 h4 (by rw [h5]; norm_num)
  refine ⟨δ, hδ, fun A hA hs => ?_⟩
  have := hlim A hA hs
  rwa [h5, OscInt.API.Sanity.apiSanity_elliptic_constant] at this
