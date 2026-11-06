import OscInt.Statements.StationaryPhase

/-!
# S4.1: uniform D4 (umbilic) estimate (statement only)

Mathematics: `docs/statements.md`, S4.

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean`).
* `cubicCoeffs φ = (a, b, c, d)` with `a = ∂³_{111}φ(0)/6`, `b = ∂³_{112}φ(0)/2`, `c = ∂³_{122}φ(0)/2`,
  `d = ∂³_{222}φ(0)/6` (via `ddd`), so that the cubic part of `φ` at `0` is
  `C(x, y) = a x³ + b x² y + c x y² + d y³`.
* `disc a b c d = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`, the discriminant of the binary cubic.
* The linear term is `lin y κ = y·κ` with `y ∈ ℝ²` arbitrary (no compactness).

Modelling choices.
* No hypothesis `∇φ(0) = 0`: a gradient at `0` is absorbed by the uniformity in `y`.
* The brief's "the cubic part has an isolated critical point" is implied by `disc < 0` (a nonzero critical point
  of a binary cubic is a root by Euler's identity and makes it a repeated root, so `disc = 0`); it is not stated.
* `t ^ (-(2 : ℝ) / 3)` is `Real.rpow` with `t ≥ 1`. Constants: `∃ δ C` after `φ`, before `A, M, y, t`.
-/

namespace OscInt.Statements

/-- Coefficients of the cubic part `(1/6) D³φ(0)[κ, κ, κ] = a x³ + b x²y + c xy² + d y³`. -/
noncomputable def cubicCoeffs (φ : ℝ × ℝ → ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (ddd φ 0 (1, 0) (1, 0) (1, 0) / 6, ddd φ 0 (1, 0) (1, 0) (0, 1) / 2,
    ddd φ 0 (1, 0) (0, 1) (0, 1) / 2, ddd φ 0 (0, 1) (0, 1) (0, 1) / 6)

/-- The discriminant of the binary cubic `a x³ + b x²y + c xy² + d y³`. -/
def disc (q : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  let a := q.1; let b := q.2.1; let c := q.2.2.1; let d := q.2.2.2
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- **S4.1** Uniform D4 estimate: at a point with vanishing Hessian whose cubic part has negative discriminant,
`|∫ e^{i(tφ(κ) + y·κ)} A(κ) dκ| ≤ C M t^{-2/3}` for amplitudes supported near `0`, uniformly in `y ∈ ℝ²`. -/
def D4BoundStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → (∀ v w, dd φ 0 v w = 0) → disc (cubicCoeffs φ) < 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_D4Bound : D4BoundStatement = D4BoundStatement := rfl

theorem sanity_fd_cubes (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) y v = 3 * y.1 ^ 2 * v.1 + 3 * y.2 ^ 2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3)
      ((3 * y.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (3 * y.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 3) using 1
    ext <;> simp
  rw [h.fderiv]; simp

theorem sanity_fd_sq_sq (y w : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2) y w = 2 * a * y.1 * w.1 + 2 * b * y.2 * w.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2)
      ((2 * a * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * b * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul a).add
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2).const_mul b) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp

theorem sanity_dd_cubes (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) y v w = 6 * y.1 * v.1 * w.1 + 6 * y.2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) y v) =
      fun y => (3 * v.1) * y.1 ^ 2 + (3 * v.2) * y.2 ^ 2 := by funext y; rw [sanity_fd_cubes]; ring
  rw [dd, this, sanity_fd_sq_sq]; ring

theorem sanity_ddd_cubes (y u v w : ℝ × ℝ) :
    ddd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) y u v w = 6 * u.1 * v.1 * w.1 + 6 * u.2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) y u v) =
      fun y => (6 * u.1 * v.1) * y.1 + (6 * u.2 * v.2) * y.2 := by funext y; rw [sanity_dd_cubes]; ring
  rw [ddd, this, sanity_fd_lin]

/-- S4.1 hypotheses are satisfiable: `φ = x³ + y³` has vanishing Hessian at `0` and cubic part with
coefficients `(1, 0, 0, 1)`, discriminant `-27`. -/
theorem sanity_D4_hyps :
    ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) ∧
      (∀ v w, dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 v w = 0) ∧
      cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) = (1, 0, 0, 1) ∧
      disc (cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3)) = -27 := by
  have hc : cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) = (1, 0, 0, 1) := by
    simp only [cubicCoeffs, sanity_ddd_cubes]; norm_num
  refine ⟨by fun_prop, fun v w => by rw [sanity_dd_cubes]; simp, hc, ?_⟩
  rw [hc]; simp [disc]

end OscInt.Statements
