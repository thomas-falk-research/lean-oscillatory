import OscInt.Statements.VanDerCorput

/-!
# Batch VC2: the second-derivative van der Corput bound with its sharp constant (statements only)

Mathematics: `docs/statements.md`, "Batch VC2". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

For `f` continuous on `[a, b]` whose derivative `f′` on `(a, b)` increases at rate at least `λ > 0`
(`f′(y) − f′(x) ≥ λ (y − x)`; for instance `f″ ≥ λ`):
* VC2-S `SecondDerivSharpStatement`: `|∫_a^b e^{if}| ≤ A(w)/√λ` for some `w ∈ [0, π]`, where
  `A(w) = 2 ∫_0^{√(2w)} sin(w − u²/2) du` (`vdc2Profile`).
* VC2-A `SecondDerivAttainedStatement`: `A(w) ≤ |∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx|` for every `w ≥ 0`, so no constant
  smaller than `sup_{[0, π]} A` is true in VC2-S (the quadratic phase on a symmetric interval satisfies its hypotheses
  with `λ = 1`).
* VC2-N `Vdc2ProfileBoundStatement`: `A(w) ≤ 7/2` on `[0, π]` (the supremum is van der Corput's constant
  `3.3643175781…`).
* VC2-K `SecondDerivSevenHalvesStatement`: the second-derivative test with amplitude in the shape of S1.k at `k = 2`,
  with the constant `7/2` in place of `8`.

Modelling choices: the hypothesis of VC2-S is on the increments of `f′`, so no second derivative is needed; VC2-K asks
for a second derivative of modulus at least `μ`, as S1.k does; integrals are interval integrals; `A` is defined by a
proper integral of a real function.
-/

namespace OscInt.Statements

open Set

/-- `A(w) = 2 ∫_0^{√(2w)} sin(w − u²/2) du`: the largest real part, over rotations, that the quadratic phase can reach
when its positive arc ends at phase `w`. Its maximum over `[0, π]` is van der Corput's constant. -/
noncomputable def vdc2Profile (w : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..Real.sqrt (2 * w), Real.sin (w - u ^ 2 / 2)

/-- `f′` increases at rate at least `lam` on the open interval `(a, b)`. -/
def DerivIncreasesAtRate (f' : ℝ → ℝ) (a b lam : ℝ) : Prop :=
  ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y → lam * (y - x) ≤ f' y - f' x

/-- **VC2-S** The second-derivative van der Corput bound with its sharp constant: if `f′` increases at rate at least
`λ > 0`, then `|∫_a^b e^{if}| ≤ A(w)/√λ` for some `w ∈ [0, π]`. -/
def SecondDerivSharpStatement : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b lam : ℝ), a ≤ b → 0 < lam → HasDerivOn f f' a b → DerivIncreasesAtRate f' a b lam →
    ∃ w ∈ Icc (0 : ℝ) Real.pi,
      ‖∫ x in a..b, Complex.exp (((f x : ℝ) : ℂ) * Complex.I)‖ ≤ vdc2Profile w / Real.sqrt lam

theorem statement_pin_SecondDerivSharp : SecondDerivSharpStatement = SecondDerivSharpStatement := rfl

/-- **VC2-A** The bound of VC2-S is attained by the quadratic phase: `A(w) ≤ |∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx|`. -/
def SecondDerivAttainedStatement : Prop :=
  ∀ w : ℝ, 0 ≤ w →
    vdc2Profile w ≤
      ‖∫ x in (-Real.sqrt (2 * w))..(Real.sqrt (2 * w)), Complex.exp (((x ^ 2 / 2 : ℝ) : ℂ) * Complex.I)‖

theorem statement_pin_SecondDerivAttained : SecondDerivAttainedStatement = SecondDerivAttainedStatement := rfl

/-- **VC2-N** An explicit bound for the sharp constant: `A(w) ≤ 7/2` for `0 ≤ w ≤ π`. -/
def Vdc2ProfileBoundStatement : Prop :=
  ∀ w ∈ Icc (0 : ℝ) Real.pi, vdc2Profile w ≤ 7 / 2

theorem statement_pin_Vdc2ProfileBound : Vdc2ProfileBoundStatement = Vdc2ProfileBoundStatement := rfl

/-- **VC2-K** The second-derivative test with amplitude and a linear term, constant `7/2`:
`|∫_a^b e^{i(φ(x) + px)} ψ(x) dx| ≤ (7/2) μ^{−1/2} (|ψ(b)| + ∫_a^b |ψ′|)` when `|φ″| ≥ μ > 0` on `(a, b)`. -/
def SecondDerivSevenHalvesStatement : Prop :=
  ∀ (φ φ' φ'' : ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b μ p : ℝ), a ≤ b → 0 < μ →
    HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b → (∀ x ∈ Ioo a b, μ ≤ |φ'' x|) → AmplitudeOn ψ ψ' a b →
    ‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ (7 / 2 : ℝ) * μ ^ (-(1 : ℝ) / 2) * ampNorm ψ ψ' a b

theorem statement_pin_SecondDerivSevenHalves :
    SecondDerivSevenHalvesStatement = SecondDerivSevenHalvesStatement := rfl

end OscInt.Statements
