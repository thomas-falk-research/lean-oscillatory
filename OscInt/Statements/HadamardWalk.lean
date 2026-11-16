import OscInt.Statements.Cusp

/-!
# Batch HW: the Hadamard walk on the line, an explicit `t^{−1/3}` bound (statements only)

Mathematics: `docs/statements.md`, "Batch HW". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

Symbols.
* `hadamardStep ψ`: one step of the Hadamard walk on `ℤ`. A state is `ψ : ℤ → ℂ × ℂ` (first component: the part that
  moves to the left, second: to the right). The coin `H = [[1, 1], [1, −1]] / √2` acts at every site, then the first
  component moves one site to the left and the second one site to the right:
  `(Uψ)(x) = ((ψ₁(x+1) + ψ₂(x+1)) / √2, (ψ₁(x−1) − ψ₂(x−1)) / √2)`.
* `hadamardWalk ψ₀ t`: `t` steps from `ψ₀`. `pointState a b`: the state `(a, b)` at the origin, `0` elsewhere.
* `hadamardDispersion k = arcsin(sin k / √2)`: the dispersion relation `ω(k)`; the step has the eigenvalues
  `e^{−iω(k)}` and `−e^{iω(k)}` at quasi-momentum `k`.
* `hadamardKernel t x = (2π)^{−1} ∫_{−π}^{π} (e^{−itω(k)} − (−1)^t e^{itω(k)}) / √(2 (1 + cos² k)) · e^{−ixk} dk`.

Modelling choices.
* Time is a natural number, the site an integer; powers of `t` are `Real.rpow` of the cast.
* HW-K, HW-D and HW-L assume `1 ≤ t`. At `t = 0` the right sides are `0` in Lean (`0 ^ (−1/3) = 0`): HW-D and HW-L
  would be false there; HW-K would still be true (`K(0, x) = 0`), so in HW-K the hypothesis carries no content.
* HW-L: the initial state has finite support (`Set.Finite` of the set where it is not `(0, 0)`); the sum over the
  support is `∑ᶠ`.
* Constants are explicit numbers; they are those of the route (S1.k with `k = 2, 3`) rounded up, not sharp
  (`docs/statements.md`).
-/

namespace OscInt.Statements

/-- One step of the Hadamard walk on `ℤ`: the coin `[[1, 1], [1, −1]] / √2` at every site, then the first component
moves one site to the left and the second one site to the right. -/
noncomputable def hadamardStep (ψ : ℤ → ℂ × ℂ) (x : ℤ) : ℂ × ℂ :=
  (((ψ (x + 1)).1 + (ψ (x + 1)).2) / ((Real.sqrt 2 : ℝ) : ℂ),
    ((ψ (x - 1)).1 - (ψ (x - 1)).2) / ((Real.sqrt 2 : ℝ) : ℂ))

/-- `t` steps of the Hadamard walk from `ψ₀`. -/
noncomputable def hadamardWalk (ψ₀ : ℤ → ℂ × ℂ) (t : ℕ) : ℤ → ℂ × ℂ :=
  hadamardStep^[t] ψ₀

/-- The state `(a, b)` at the origin and `0` at every other site. -/
def pointState (a b : ℂ) (y : ℤ) : ℂ × ℂ :=
  if y = 0 then (a, b) else (0, 0)

/-- The dispersion relation of the Hadamard walk, `ω(k) = arcsin(sin k / √2)`. -/
noncomputable def hadamardDispersion (k : ℝ) : ℝ :=
  Real.arcsin (Real.sin k / Real.sqrt 2)

/-- The scalar kernel of the Hadamard walk,
`(2π)^{−1} ∫_{−π}^{π} (e^{−itω(k)} − (−1)^t e^{itω(k)}) / √(2 (1 + cos² k)) · e^{−ixk} dk`. -/
noncomputable def hadamardKernel (t : ℕ) (x : ℤ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi,
    (Complex.exp (↑(-((t : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ t * Complex.exp (↑((t : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) *
    Complex.exp (↑(-((x : ℝ) * k)) * Complex.I)

/-- **HW-R** The walk from a point state in terms of the scalar kernel: for every `t ≥ 0`,
`ψ_{t+1}(x) = ((a + b)/√2 · K(t+1, x+1) + a K(t, x), (a − b)/√2 · K(t+1, x−1) + b K(t, x))`. -/
def HadamardKernelStatement : Prop :=
  ∀ (a b : ℂ) (t : ℕ) (x : ℤ),
    hadamardWalk (pointState a b) (t + 1) x =
      ((a + b) / ((Real.sqrt 2 : ℝ) : ℂ) * hadamardKernel (t + 1) (x + 1) + a * hadamardKernel t x,
        (a - b) / ((Real.sqrt 2 : ℝ) : ℂ) * hadamardKernel (t + 1) (x - 1) + b * hadamardKernel t x)

theorem statement_pin_HadamardKernel : HadamardKernelStatement = HadamardKernelStatement := rfl

/-- **HW-K** Explicit bound for the scalar kernel: `|K(t, x)| ≤ 7 t^{−1/2} + 12 t^{−1/3}` for `t ≥ 1` and every
site `x`. -/
def HadamardKernelBoundStatement : Prop :=
  ∀ (t : ℕ) (x : ℤ), 1 ≤ t →
    ‖hadamardKernel t x‖ ≤ 7 * (t : ℝ) ^ (-(1 : ℝ) / 2) + 12 * (t : ℝ) ^ (-(1 : ℝ) / 3)

theorem statement_pin_HadamardKernelBound : HadamardKernelBoundStatement = HadamardKernelBoundStatement := rfl

/-- **HW-D** Decay of the Hadamard walk from a point state: each component of `ψ_t(x)` is at most
`39 (|a| + |b|) t^{−1/3}`, for `t ≥ 1` and every site `x`. -/
def HadamardDecayStatement : Prop :=
  ∀ (a b : ℂ) (t : ℕ) (x : ℤ), 1 ≤ t →
    ‖(hadamardWalk (pointState a b) t x).1‖ ≤ 39 * (‖a‖ + ‖b‖) * (t : ℝ) ^ (-(1 : ℝ) / 3) ∧
    ‖(hadamardWalk (pointState a b) t x).2‖ ≤ 39 * (‖a‖ + ‖b‖) * (t : ℝ) ^ (-(1 : ℝ) / 3)

theorem statement_pin_HadamardDecay : HadamardDecayStatement = HadamardDecayStatement := rfl

/-- **HW-L** The dispersive estimate `ℓ¹ → ℓ^∞` for finitely supported initial states: each component of `ψ_t(x)` is
at most `39 t^{−1/3} ∑_y (|ψ₀(y)₁| + |ψ₀(y)₂|)`, for `t ≥ 1` and every site `x`. -/
def HadamardDispersiveStatement : Prop :=
  ∀ (ψ₀ : ℤ → ℂ × ℂ) (t : ℕ) (x : ℤ), {y : ℤ | ψ₀ y ≠ (0, 0)}.Finite → 1 ≤ t →
    ‖(hadamardWalk ψ₀ t x).1‖ ≤
      39 * (∑ᶠ y : ℤ, (‖(ψ₀ y).1‖ + ‖(ψ₀ y).2‖)) * (t : ℝ) ^ (-(1 : ℝ) / 3) ∧
    ‖(hadamardWalk ψ₀ t x).2‖ ≤
      39 * (∑ᶠ y : ℤ, (‖(ψ₀ y).1‖ + ‖(ψ₀ y).2‖)) * (t : ℝ) ^ (-(1 : ℝ) / 3)

theorem statement_pin_HadamardDispersive : HadamardDispersiveStatement = HadamardDispersiveStatement := rfl

end OscInt.Statements
