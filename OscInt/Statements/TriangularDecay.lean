/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Statements.TriangularAniso
import OscInt.Statements.Global

/-!
# Batch K2: sharp fixed-coupling decay on the anisotropic triangular lattice (statements only)

Mathematics: `docs/statements.md`, "Batch K2". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1). Proofs on paper exist and are older: an external
derivation reviewed in `review/2026-11-27-K2-proof-answers.md` and an external research packet reviewed in
`review/2026-11-28-K2-packet-answers.md`.

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean`, `Global.lean` and `TriangularAniso.lean`).
* `triKernel α t n = ∫_{[−π, π]²} e^{i(t triPhase α k + n·k)} dk`, unnormalised as `latticeKernel` (batch GD):
  `triKernel 0 = latticeKernel`.
* `triRate α = 2/3` if `α = 0` or `|α| = 1/(2√2)`, and `3/4` otherwise.
* `PlateauCutoff b r`: `b` is `C¹`, compactly supported, even, equal to `1` on `[−r, r]`, nonincreasing on
  `[0, ∞)`, and `r > 0`.

Statements.
* K2-L `ReducedOrderBoundStatement`: a local bound of order `m`. If `D²Ψ(k₀)[w, w] ≠ 0` for vectors `v, w` that span
  `ℝ²`, and along a reduced curve the reduced function has a nonzero `m`-th derivative at `0`, then near `k₀`,
  `|∫ e^{i(tΨ + y·κ)} A| ≤ C M t^{−(1/2 + 1/m)}` for every linear term `y`, every `t ≥ 1` and every `C²` amplitude
  supported in a small ball, with constants independent of `A, M, y, t`. Lower-order derivatives are not
  restricted.
* K2-MA `MonomialAsymptoticStatement`: for `m ≥ 2` and `σ = ±1` the improper integral `C = ∫_ℝ e^{iσx^m} dx`
  (symmetric limit) has `Re C ≥ 1/(12m)`, and `|∫ b(x) e^{itσx^m} dx − t^{−1/m} C| ≤ 4/(m t r^{m−1})` for every
  plateau cutoff `b` and every `t > 0`.
* K2-ML `MonomialLowerStatement`: `|∫ b(x) e^{itσx^m} dx| ≥ t^{−1/m}/(24m)` once `t^{1−1/m} ≥ 96 r^{1−m}`.
* K2-F `TorusLocalizationStatement`: for a smooth `χ` with support inside the open box `(−π, π)²` there is `D` such
  that a bound `B` on every lattice coefficient `|∫_{[−π, π]²} e^{i(tΨ + n·k)} dk|` (`n ∈ ℤ²`) of a continuous
  biperiodic phase gives `|∫_{[−π, π]²} χ e^{it(Ψ + p·k)} dk| ≤ D B` for every real `t` and every real `p`.
* K2-U `TriDecayUpperStatement`: for every real `α` there is `C` with `|triKernel α t n| ≤ C t^{−triRate α}` for all
  real `t ≥ 1` and all `n ∈ ℤ²`.
* K2-D `TriDecayLowerStatement`: for every real `α` there are `c > 0` and `T` such that for every real `t ≥ T` some
  `n ∈ ℤ²` has `|triKernel α t n| ≥ c t^{−triRate α}`.

Modelling choices.
* Constants are existential in K2-L, K2-F, K2-U and K2-D (they depend on the phase, the point, the cutoff or `α`) and
  explicit in K2-MA and K2-ML. Nothing is uniform in `α`; no best constant; no fixed lattice site in K2-D.
* Powers are `Real.rpow`. Times are real, not integers.
* The vectors of K2-L span `ℝ²` (`v₁w₂ − v₂w₁ ≠ 0`); no condition on `D²Ψ(k₀)[v, ·]` is made, so the statement also
  covers nondegenerate points (`m = 2`) and folds (`m = 3`).
* K2-F is stated without a supremum: "every lattice coefficient is at most `B`" implies "the localised integral is at
  most `D B`". Integrals over the box are the set integral over `torusBox`.
-/

namespace OscInt.Statements

open Filter Topology
open scoped ContDiff

/-- The kernel `∫_{[−π, π]²} e^{i(t triPhase α k + n·k)} dk` of the anisotropic triangular lattice (unnormalised, as
`latticeKernel`). -/
noncomputable def triKernel (α t : ℝ) (n : ℤ × ℤ) : ℂ :=
  ∫ k in torusBox, Complex.exp (↑(t * triPhase α k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)

/-- The fixed-coupling decay exponent: `2/3` at `α = 0` and `|α| = 1/(2√2)`, `3/4` otherwise. -/
noncomputable def triRate (α : ℝ) : ℝ := if α = 0 ∨ |α| = triExceptional then 2 / 3 else 3 / 4

/-- `b` is a `C¹` even plateau cutoff: compact support, `b = 1` on `[−r, r]`, nonincreasing on `[0, ∞)`, `r > 0`. -/
def PlateauCutoff (b : ℝ → ℝ) (r : ℝ) : Prop :=
  ContDiff ℝ 1 b ∧ HasCompactSupport b ∧ 0 < r ∧ (∀ x, b (-x) = b x) ∧ (∀ x, |x| ≤ r → b x = 1) ∧
    AntitoneOn b (Set.Ici 0)

/-- **K2-L** Local bound of order `m`: a nonzero `m`-th derivative of the reduced function gives decay
`t^{−(1/2 + 1/m)}` near `k₀`, uniformly over every linear term. -/
def ReducedOrderBoundStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ) (m : ℕ), ContDiff ℝ ∞ Ψ → 2 ≤ m →
    v.1 * w.2 - v.2 * w.1 ≠ 0 → iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 → 0 < ε → ReducedCurve Ψ k₀ v w ε h →
      iteratedDeriv m (reducedFn Ψ k₀ v w h) 0 ≠ 0 →
      ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
        AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
          ‖oscInt2 (fun κ => t * Ψ κ + lin y κ) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ)))

theorem statement_pin_ReducedOrderBound : ReducedOrderBoundStatement = ReducedOrderBoundStatement := rfl

/-- **K2-MA** Monomial asymptotics with an explicit remainder: the improper integral `C = ∫_ℝ e^{iσx^m} dx` has
`Re C ≥ 1/(12m)`, and a plateau cutoff integral is `t^{−1/m} C` up to `4/(m t r^{m−1})`. -/
def MonomialAsymptoticStatement : Prop :=
  ∀ (m : ℕ) (σ : ℝ), 2 ≤ m → (σ = 1 ∨ σ = -1) →
    ∃ C : ℂ, 1 / (12 * (m : ℝ)) ≤ C.re ∧
      Tendsto (fun R : ℝ => ∫ x in -R..R, Complex.exp (↑(σ * x ^ m) * Complex.I)) atTop (𝓝 C) ∧
      ∀ (b : ℝ → ℝ) (r t : ℝ), PlateauCutoff b r → 0 < t →
        ‖(∫ x : ℝ, (b x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)) -
            ((t ^ (-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) * C‖ ≤ 4 / ((m : ℝ) * t * r ^ (m - 1))

theorem statement_pin_MonomialAsymptotic : MonomialAsymptoticStatement = MonomialAsymptoticStatement := rfl

/-- **K2-ML** Monomial lower bound: `|∫ b(x) e^{itσx^m} dx| ≥ t^{−1/m}/(24m)` once `t^{1−1/m} ≥ 96 r^{1−m}`. -/
def MonomialLowerStatement : Prop :=
  ∀ (m : ℕ) (σ : ℝ) (b : ℝ → ℝ) (r t : ℝ), 2 ≤ m → (σ = 1 ∨ σ = -1) → PlateauCutoff b r → 0 < t →
    96 * r ^ (1 - (m : ℝ)) ≤ t ^ (1 - 1 / (m : ℝ)) →
      t ^ (-(1 : ℝ) / (m : ℝ)) / (24 * (m : ℝ)) ≤
        ‖∫ x : ℝ, (b x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)‖

theorem statement_pin_MonomialLower : MonomialLowerStatement = MonomialLowerStatement := rfl

/-- **K2-F** Fourier localisation: for a smooth `χ` supported inside `(−π, π)²`, a bound on every lattice coefficient
of `e^{itΨ}` bounds the `χ`-localised integral at every real velocity `p`. -/
def TorusLocalizationStatement : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ χ →
    tsupport χ ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi →
    ∃ D : ℝ, ∀ (Ψ : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) (B : ℝ), Continuous Ψ →
      (∀ k : ℝ × ℝ, Ψ (k.1 + 2 * Real.pi, k.2) = Ψ k) → (∀ k : ℝ × ℝ, Ψ (k.1, k.2 + 2 * Real.pi) = Ψ k) →
      (∀ n : ℤ × ℤ, ‖∫ k in torusBox,
          Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤ B) →
        ‖∫ k in torusBox, χ k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)‖ ≤ D * B

theorem statement_pin_TorusLocalization : TorusLocalizationStatement = TorusLocalizationStatement := rfl

/-- **K2-U** Fixed-coupling upper bound: `|triKernel α t n| ≤ C_α t^{−triRate α}` for all real `t ≥ 1` and all
`n ∈ ℤ²`. -/
def TriDecayUpperStatement : Prop :=
  ∀ α : ℝ, ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel α t n‖ ≤ C * t ^ (-triRate α)

theorem statement_pin_TriDecayUpper : TriDecayUpperStatement = TriDecayUpperStatement := rfl

/-- **K2-D** Fixed-coupling lower bound: for all real `t ≥ T_α` some lattice site has
`|triKernel α t n| ≥ c_α t^{−triRate α}`, `c_α > 0`. -/
def TriDecayLowerStatement : Prop :=
  ∀ α : ℝ, ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-triRate α) ≤ ‖triKernel α t n‖

theorem statement_pin_TriDecayLower : TriDecayLowerStatement = TriDecayLowerStatement := rfl

end OscInt.Statements
