import OscInt.Statements.D4

/-!
# S4.1′, S4.2, S4.3, S4.4: D4 bound for both umbilics, limit, and the constant (statements only)

Mathematics: `docs/statements.md`, S4. Decisions: `docs/decisions/2026-11-06-S4.md`.

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean` and `OscInt/Statements/D4.lean`).
* `cubicForm q z = a z₁³ + b z₁²z₂ + c z₁z₂² + d z₂³` for `q = (a, b, c, d)`; with `q = cubicCoeffs φ` it is the
  cubic part of `φ` at `0`.
* `cosMomentPartial R = ∫₀^R cos u · u^{-1/3} du` and `cosMoment = lim_{R→∞} cosMomentPartial R` (`limUnder`; S4.3
  states that the limit exists).
* `angularMoment q = ∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ` (finite iff `C` has only simple real linear factors,
  i.e. `disc q ≠ 0`; S4.3 states integrability).
* `d4Constant q = cosMoment · angularMoment q / 3`, the constant c_C, defined without the Gamma function: in polar
  coordinates `∫₀^∞ e^{isr³} r dr = (1/3)|s|^{-2/3} ∫₀^∞ e^{±iu} u^{-1/3} du`, and `C(−z) = −C(z)` cancels the sine
  part.

Statements.
* S4.1′ `D4BoundNeStatement`: S4.1 with `disc ≠ 0` (hyperbolic D4⁺ and elliptic D4⁻ umbilics).
* S4.2 `D4LimitStatement`: at a critical point (`φ(0) = 0`, `Dφ(0) = 0`, `D²φ(0) = 0`) with `disc ≠ 0`,
  `t^{2/3} ∫ e^{itφ} A → c_C A(0)` as `t → ∞`, for `C²` amplitudes supported near `0`.
* S4.3 `D4ConstantPosStatement`: the improper integral converges, `cosMoment > 0` (the brief's alternating-series
  argument; no Gamma function in the statement), and for `disc q ≠ 0` the angular integrand is integrable and
  `d4Constant q > 0`.
* S4.4 `D4ConstantClosedFormStatement`: `cosMoment = Γ(2/3)/2`, and `c_C = Γ(1/3)²/(√3 |Disc|^{1/6})` for `Disc < 0`
  (the brief's formula), `c_C = Γ(1/3)²/Disc^{1/6}` for `Disc > 0`.

Modelling choices.
* `t ^ ((2 : ℝ) / 3)` is `Real.rpow` (the limit is along `atTop`, so only `t > 0` matters).
* `u ^ (-(1 : ℝ) / 3)` and `|C| ^ (-(2 : ℝ) / 3)` are `Real.rpow`; at `0` they are `0` (`Real.zero_rpow`), a null set.
* No uniformity in a linear term in S4.2 (the brief states the limit without one).
-/

namespace OscInt.Statements

open Filter Topology

/-- The binary cubic `a z₁³ + b z₁²z₂ + c z₁z₂² + d z₂³` with coefficients `q = (a, b, c, d)`. -/
def cubicForm (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  q.1 * z.1 ^ 3 + q.2.1 * z.1 ^ 2 * z.2 + q.2.2.1 * z.1 * z.2 ^ 2 + q.2.2.2 * z.2 ^ 3

/-- **S4.1′** Uniform D4 estimate at both umbilics: as `D4BoundStatement` with `disc ≠ 0`. -/
def D4BoundNeStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → (∀ v w, dd φ 0 v w = 0) → disc (cubicCoeffs φ) ≠ 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_D4BoundNe : D4BoundNeStatement = D4BoundNeStatement := rfl

/-- `∫₀^R cos u · u^{-1/3} du`. -/
noncomputable def cosMomentPartial (R : ℝ) : ℝ := ∫ u in (0 : ℝ)..R, Real.cos u * u ^ (-(1 : ℝ) / 3)

/-- `∫₀^∞ cos u · u^{-1/3} du` as an improper integral. -/
noncomputable def cosMoment : ℝ := limUnder atTop cosMomentPartial

/-- `∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ`. -/
noncomputable def angularMoment (q : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), |cubicForm q (Real.cos θ, Real.sin θ)| ^ (-(2 : ℝ) / 3)

/-- The D4 constant `c_C = (1/3) · ∫₀^∞ cos u · u^{-1/3} du · ∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ`. -/
noncomputable def d4Constant (q : ℝ × ℝ × ℝ × ℝ) : ℝ := cosMoment * angularMoment q / 3

/-- **S4.2** D4 limit: `t^{2/3} ∫ e^{itφ} A → c_C A(0)`. -/
def D4LimitStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → φ 0 = 0 → fderiv ℝ φ 0 = 0 → (∀ v w, dd φ 0 v w = 0) →
    disc (cubicCoeffs φ) ≠ 0 →
    ∃ δ > 0, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M →
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) A) atTop
        (𝓝 ((d4Constant (cubicCoeffs φ) : ℂ) * A 0))

theorem statement_pin_D4Limit : D4LimitStatement = D4LimitStatement := rfl

/-- **S4.3** The constant is positive: the improper integral converges to a positive number, and for `disc ≠ 0`
the angular integrand is integrable and `c_C > 0`. -/
def D4ConstantPosStatement : Prop :=
  Tendsto cosMomentPartial atTop (𝓝 cosMoment) ∧ 0 < cosMoment ∧
    ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 →
      IntervalIntegrable (fun θ => |cubicForm q (Real.cos θ, Real.sin θ)| ^ (-(2 : ℝ) / 3))
        MeasureTheory.volume 0 (2 * Real.pi) ∧ 0 < d4Constant q

theorem statement_pin_D4ConstantPos : D4ConstantPosStatement = D4ConstantPosStatement := rfl

/-- **S4.4** Closed forms: `∫₀^∞ cos u · u^{-1/3} du = Γ(2/3)/2`; `c_C = Γ(1/3)²/(√3 |Disc|^{1/6})` for `Disc < 0`
and `c_C = Γ(1/3)²/Disc^{1/6}` for `Disc > 0`. -/
def D4ConstantClosedFormStatement : Prop :=
  cosMoment = Real.Gamma (2 / 3) / 2 ∧
    (∀ q : ℝ × ℝ × ℝ × ℝ, disc q < 0 →
      d4Constant q = Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * |disc q| ^ ((1 : ℝ) / 6))) ∧
    ∀ q : ℝ × ℝ × ℝ × ℝ, 0 < disc q → d4Constant q = Real.Gamma (1 / 3) ^ 2 / disc q ^ ((1 : ℝ) / 6)

theorem statement_pin_D4ConstantClosedForm :
    D4ConstantClosedFormStatement = D4ConstantClosedFormStatement := rfl

/-! ## Sanity -/

/-- `cubicForm` lists the coefficients in the order of `cubicCoeffs` (`x³, x²y, xy², y³`). -/
theorem sanity_cubicForm (x y : ℝ) :
    cubicForm (1, 2, 3, 5) (x, y) = x ^ 3 + 2 * x ^ 2 * y + 3 * x * y ^ 2 + 5 * y ^ 3 := by
  simp only [cubicForm]; ring

/-- The S4.2 hypotheses are satisfiable: `x³ + y³` has `φ(0) = 0`, `Dφ(0) = 0`, `D²φ(0) = 0`, `disc = −27 ≠ 0`. -/
theorem sanity_D4Limit_hyps :
    ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) ∧ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 = 0 ∧
      fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 = 0 ∧
      (∀ v w, dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 v w = 0) ∧
      disc (cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3)) ≠ 0 := by
  obtain ⟨h1, h2, -, h4⟩ := sanity_D4_hyps
  refine ⟨h1, by simp, ?_, h2, by rw [h4]; norm_num⟩
  ext
  · simp [sanity_fd_cubes]
  · simp [sanity_fd_cubes]

end OscInt.Statements
