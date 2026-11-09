import OscInt.Statements.VanDerCorput
import OscInt.Statements.StationaryPhase

/-!
# Batch A3: the k-th derivative van der Corput bound (S1.k) and the uniform cusp bound (S5.1, S5.1′)
(statements only)

Mathematics: `docs/statements.md`, "Batch A3".

Symbols (in addition to `OscInt/Statements/VanDerCorput.lean` and `OscInt/Statements/StationaryPhase.lean`).
* `DerivChain D k a b`: `D (j + 1)` is the derivative of `D j` on `[a, b]` (`HasDerivOn`) for every `j < k`; only
  `D 0, …, D k` matter, and `D 0` is the phase.
* `IsA3Point Ψ k₀`: there are `v w` with `D²Ψ(k₀)[v, z] = 0` for all `z`, `D²Ψ(k₀)[w, w] ≠ 0`,
  `D³Ψ(k₀)[v, v, v] = 0` and `D²Ψ(k₀)[w, w] · D⁴Ψ(k₀)[v, v, v, v] − 3 (D³Ψ(k₀)[v, v, w])² ≠ 0`
  (derivatives are `iteratedFDeriv` applied to `![…]`).
* `IsStableA3Point Ψ k₀`: the same `v w` also have `D³Ψ(k₀)[v, v, w] ≠ 0`.

Modelling choices.
* S1.k: `k ≥ 2`; the constant `(5 * 2 ^ (k - 1) - 2 : ℝ)` with `k - 1` a natural number; `μ ^ (-(1 : ℝ) / k)` is
  `Real.rpow` with `0 < μ`; everything else as S1.2/S1.3.
* S5.1, S5.1′: at the origin, phase `ContDiff ℝ ∞` (the smooth index, lessons 12), amplitude bound
  `(2, closedBall 0 δ, M)` with the max norm, linear term `lin y κ` with `y ∈ ℝ²` arbitrary, `t ^ (-(3 : ℝ) / 4)` is
  `Real.rpow` with `1 ≤ t`. Constants: `∃ δ C` after `φ`, before `A, M, y, t`.
* `IsA3Point` uses `iteratedFDeriv` (as `IsD4Point` in `Global.lean`); for a C⁴ phase these are the symmetric
  multilinear derivatives. The existential form is equivalent to the universal one (`docs/statements.md`).
-/

namespace OscInt.Statements

open Set MeasureTheory Complex
open scoped ContDiff

/-- `D (j + 1)` is the derivative of `D j` on `[a, b]` for every `j < k`. -/
def DerivChain (D : ℕ → ℝ → ℝ) (k : ℕ) (a b : ℝ) : Prop :=
  ∀ j < k, HasDerivOn (D j) (D (j + 1)) a b

/-- **S1.k** k-th derivative van der Corput bound with amplitude, `k ≥ 2`, constant `5·2^{k−1} − 2`, uniform in a
linear term. -/
def VdCkStatement : Prop :=
  ∀ (k : ℕ) (D : ℕ → ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b μ p : ℝ), 2 ≤ k → a ≤ b → 0 < μ →
    DerivChain D k a b → (∀ x ∈ Ioo a b, μ ≤ |D k x|) → AmplitudeOn ψ ψ' a b →
    ‖oscInt (fun x => D 0 x + p * x) ψ a b‖ ≤
      ((5 : ℝ) * 2 ^ (k - 1) - 2) * μ ^ (-(1 : ℝ) / (k : ℝ)) * ampNorm ψ ψ' a b

theorem statement_pin_VdCk : VdCkStatement = VdCkStatement := rfl

/-- `k₀` is an A3 (cusp) point of `Ψ`: the Hessian has rank one with kernel vector `v`, the third derivative along
`v` vanishes, and the reduced quartic `D²Ψ[w, w]·D⁴Ψ[v⁴] − 3 (D³Ψ[v, v, w])²` is nonzero. -/
def IsA3Point (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) : Prop :=
  ∃ v w : ℝ × ℝ, (∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0) ∧ iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 ∧
    iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, v] = 0 ∧
    iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] * iteratedFDeriv ℝ 4 Ψ k₀ ![v, v, v, v] -
      3 * iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] ^ 2 ≠ 0

/-- `k₀` is a stable A3 point of `Ψ`: an A3 point at which the kernel and transverse directions are coupled,
`D³Ψ(k₀)[v, v, w] ≠ 0` (the gradient map has a Whitney cusp). -/
def IsStableA3Point (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) : Prop :=
  ∃ v w : ℝ × ℝ, (∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0) ∧ iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 ∧
    iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, v] = 0 ∧
    iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] * iteratedFDeriv ℝ 4 Ψ k₀ ![v, v, v, v] -
      3 * iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] ^ 2 ≠ 0 ∧
    iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] ≠ 0

/-- **S5.1** Uniform stable-cusp bound: at a stable A3 point, decay `t^{-3/4}`, uniform over every linear term. -/
def CuspBoundStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → IsStableA3Point φ 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4)

theorem statement_pin_CuspBound : CuspBoundStatement = CuspBoundStatement := rfl

/-- **S5.1′** Uniform cusp bound: at an A3 point, decay `t^{-3/4}`, uniform over every linear term. -/
def CuspBoundGenStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → IsA3Point φ 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4)

theorem statement_pin_CuspBoundGen : CuspBoundGenStatement = CuspBoundGenStatement := rfl

end OscInt.Statements
