import OscInt.Statements.D4Limit

/-!
# S4.2U, S4.2O: the D4 limit uniformly over amplitude families and bounded linear offsets (statements only)

Mathematics: `docs/statements.md`, "Batch D4U". Written and stamped before the blind pre-proof reviews; no Lean proof of
these statements enters the repository before the reviews are answered (`CONTRIBUTING.md`; the departure from
lessons 23 is disclosed there).

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean`, `D4.lean` and `D4Limit.lean`).
* `D4LimitPhase φ`: the phase hypotheses of S4.2 (C⁴, `φ(0) = 0`, `Dφ(0) = 0`, `D²φ(0) = 0`, `disc ≠ 0`).
* `AmpTotallyBounded K S`: every member of `S` has a C² budget on `K`, and for every `η > 0` finitely many members of
  `S` approximate every member within the C² budget `η` on `K` (`AmpBound 2 K (A − b) η`).

Statements.
* S4.2U `D4LimitUniformStatement`: S4.2's limit `t^{2/3} ∫ e^{itφ} A → c_C A(0)` holds uniformly over every family that
  is C²-totally bounded on the ball `B̄(0, δ)`, `δ` depending on `φ` only.
* S4.2O `D4LimitOffsetStatement`: the limit with a linear term, `t^{2/3} ∫ e^{i(tφ + y·κ)} A → c_C A(0)`, uniformly over
  `‖y‖ ≤ R` (max norm), for every fixed C² amplitude supported in `B̄(0, δ)`.

Modelling choices.
* Uniformity in the ε–T form; `T` is any real; `t ^ ((2 : ℝ) / 3)` is `Real.rpow`.
* The offset `lin y` is not multiplied by `t` (a bounded perturbation; the limit value is unchanged).
* No rate and no effective threshold.
-/

namespace OscInt.Statements

/-- The phase hypotheses of S4.2: `φ` is C⁴ with `φ(0) = 0`, `Dφ(0) = 0`, `D²φ(0) = 0` and `disc C ≠ 0` for its cubic
part `C` at `0`. -/
def D4LimitPhase (φ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ 4 φ ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧ (∀ v w, dd φ 0 v w = 0) ∧ disc (cubicCoeffs φ) ≠ 0

/-- `S` is C²-totally bounded on `K`: each member has a C² budget on `K`, and for every `η > 0` a finite subset of `S`
approximates every member of `S` within the C² budget `η` on `K`. -/
def AmpTotallyBounded (K : Set (ℝ × ℝ)) (S : Set (ℝ × ℝ → ℂ)) : Prop :=
  (∀ A ∈ S, ∃ M : ℝ, AmpBound 2 K A M) ∧
    ∀ η : ℝ, 0 < η → ∃ B : Set (ℝ × ℝ → ℂ), B.Finite ∧ B ⊆ S ∧ ∀ A ∈ S, ∃ b ∈ B, AmpBound 2 K (A - b) η

/-- **S4.2U** D4 limit uniform over a C²-totally bounded family of amplitudes. -/
def D4LimitUniformStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, D4LimitPhase φ →
    ∃ δ > 0, ∀ S : Set (ℝ × ℝ → ℂ), AmpTotallyBounded (Metric.closedBall 0 δ) S →
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ A ∈ S,
        ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ) A -
          (d4Constant (cubicCoeffs φ) : ℂ) * A 0‖ < ε

theorem statement_pin_D4LimitUniform : D4LimitUniformStatement = D4LimitUniformStatement := rfl

/-- **S4.2O** D4 limit uniform over bounded linear offsets. -/
def D4LimitOffsetStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, D4LimitPhase φ →
    ∃ δ > 0, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound 2 (Metric.closedBall 0 δ) A M →
      ∀ R ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ y : ℝ × ℝ, ‖y‖ ≤ R →
        ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * φ κ + lin y κ) A -
          (d4Constant (cubicCoeffs φ) : ℂ) * A 0‖ < ε

theorem statement_pin_D4LimitOffset : D4LimitOffsetStatement = D4LimitOffsetStatement := rfl

end OscInt.Statements
