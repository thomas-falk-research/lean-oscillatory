/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.TriangularDecay

/-!
# Batch A5U: the decay of the triangular lattice kernel uniformly across an exceptional coupling (statements only)

Mathematics: `docs/statements.md`, "Batch A5U". Written, stamped and blind-reviewed before any Lean proof of this
statement exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1). A proof route on paper is older: an external
research packet reviewed in `review/2026-11-28-postK2-packet-answers.md`.

Symbols as in batch K2 (`OscInt/Statements/TriangularDecay.lean`): `triKernel`, `triExceptional = 1/(2√2)`.
* `crossEnvelope s = 1` for `s ≤ 1` and `s^{−1/4}` for `s > 1`; for `s ≥ 0` this is `min(1, s^{−1/4})` with value `1`
  at `s = 0`.

* A5U `TriCrossoverUpperStatement`: for each exceptional coupling `a₀ = ±1/(2√2)` there are a radius `r > 0` and one
  constant `C` such that `|triKernel α t n| ≤ C t^{−2/3} E(|α − a₀| t^{1/3})` for every `α` with `|α − a₀| ≤ r`, every
  real `t ≥ 1` and every `n ∈ ℤ²`, where `E = crossEnvelope`.

Modelling choices. `C` and `r` are existential and depend on `a₀` only; they are the same for every `α` in the window,
every `t ≥ 1` and every site. Equivalently, for `ε = |α − a₀| > 0`, the bound is `C min(t^{−2/3}, ε^{−1/4} t^{−3/4})`.
Nothing is said about a lower bound uniform in `α`, about couplings near `0`, or about explicit values of `C`, `r`.
-/

namespace OscInt.Statements

/-- The crossover envelope: `1` on `(−∞, 1]` and `s^{−1/4}` for `s > 1`. -/
noncomputable def crossEnvelope (s : ℝ) : ℝ := if s ≤ 1 then 1 else s ^ (-(1 : ℝ) / 4)

/-- **A5U** Upper bound uniform across an exceptional coupling `a₀ = ±1/(2√2)`:
`|triKernel α t n| ≤ C t^{−2/3} E(|α − a₀| t^{1/3})` for `|α − a₀| ≤ r`, real `t ≥ 1` and every site `n`. -/
def TriCrossoverUpperStatement : Prop :=
  ∀ a₀ : ℝ, |a₀| = triExceptional → ∃ r > 0, ∃ C : ℝ, ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → 1 ≤ t →
    ‖triKernel α t n‖ ≤ C * t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3))

theorem statement_pin_TriCrossoverUpper : TriCrossoverUpperStatement = TriCrossoverUpperStatement := rfl

end OscInt.Statements
