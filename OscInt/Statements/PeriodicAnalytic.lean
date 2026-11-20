import OscInt.Statements.LatticeExplicit

/-!
# Batch PA: periodic functions analytic in a strip (statements only)

Mathematics: `docs/statements.md`, "Batch PA". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

For `v : ℂ → ℂ` holomorphic, `2π`-periodic and bounded by `M` on the open strip `|Im z| < a`:
* PA-C `FourierCoeffStripStatement`: `|∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}` for every integer `k`.
* PA-T `TrapezoidalRuleStatement`: for every `N ≥ 1`, the `N`-point trapezoidal sum `I_N = (2π/N) Σ_{j<N} v(2πj/N)`
  satisfies `|I_N − ∫_0^{2π} v| ≤ 4πM / (e^{aN} − 1)` (Trefethen and Weideman, SIAM Review 56 (2014), Theorem 3.2).
* LC-1 `LatticeKernel1LightConeStatement`: `|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}` for the 1D lattice kernel
  `I(t, n) = ∫_{−π}^{π} e^{i(t cos k + nk)} dk` of batch LE, every real `t`, integer `n` and `η ≥ 0`.

Modelling choices: the function is given on all of `ℂ` and constrained only on the open strip; the integrals are
interval integrals of the restriction to the real axis (`θ : ℝ` coerced to `ℂ`); `k`, `n` are integers and `N` a
positive natural number; `latticeKernel1` (batch LE) is reused unchanged, at the real number `(n : ℝ)`.
-/

namespace OscInt.Statements

/-- The open horizontal strip `{z : |Im z| < a}`. -/
def openStrip (a : ℝ) : Set ℂ := {z : ℂ | |z.im| < a}

/-- `v` is holomorphic on the open strip `|Im z| < a`, `2π`-periodic there and bounded by `M` there. -/
def PeriodicAnalyticOn (v : ℂ → ℂ) (a M : ℝ) : Prop :=
  DifferentiableOn ℂ v (openStrip a) ∧ (∀ z ∈ openStrip a, v (z + ((2 * Real.pi : ℝ) : ℂ)) = v z) ∧
    ∀ z ∈ openStrip a, ‖v z‖ ≤ M

/-- The `N`-point trapezoidal sum `(2π/N) Σ_{j<N} v(2πj/N)` of a `2π`-periodic function (for a periodic function the
trapezoidal and the rectangle rule coincide). -/
noncomputable def trapezoidalSum (v : ℂ → ℂ) (N : ℕ) : ℂ :=
  ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * ∑ j ∈ Finset.range N, v ((2 * Real.pi * (j : ℝ) / (N : ℝ) : ℝ) : ℂ)

/-- **PA-C** Fourier coefficients of a periodic function analytic in a strip decay exponentially:
`|∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}`. -/
def FourierCoeffStripStatement : Prop :=
  ∀ (v : ℂ → ℂ) (a M : ℝ) (k : ℤ), 0 < a → PeriodicAnalyticOn v a M →
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)‖ ≤
      2 * Real.pi * M * Real.exp (-(a * |(k : ℝ)|))

theorem statement_pin_FourierCoeffStrip : FourierCoeffStripStatement = FourierCoeffStripStatement := rfl

/-- **PA-T** The trapezoidal rule converges exponentially for a periodic function analytic in a strip:
`|I_N − ∫_0^{2π} v| ≤ 4πM / (e^{aN} − 1)` for every `N ≥ 1` (Trefethen–Weideman 2014, Theorem 3.2). -/
def TrapezoidalRuleStatement : Prop :=
  ∀ (v : ℂ → ℂ) (a M : ℝ) (N : ℕ), 0 < a → 0 < N → PeriodicAnalyticOn v a M →
    ‖trapezoidalSum v N - ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ)‖ ≤
      4 * Real.pi * M / (Real.exp (a * (N : ℝ)) - 1)

theorem statement_pin_TrapezoidalRule : TrapezoidalRuleStatement = TrapezoidalRuleStatement := rfl

/-- **LC-1** Light-cone bound for the 1D lattice kernel: `|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}` for every real `t`,
integer `n` and `η ≥ 0`. -/
def LatticeKernel1LightConeStatement : Prop :=
  ∀ (t η : ℝ) (n : ℤ), 0 ≤ η →
    ‖latticeKernel1 t (n : ℝ)‖ ≤ 2 * Real.pi * Real.exp (|t| * Real.sinh η - |(n : ℝ)| * η)

theorem statement_pin_LatticeKernel1LightCone :
    LatticeKernel1LightConeStatement = LatticeKernel1LightConeStatement := rfl

end OscInt.Statements

/- Attribution, appended after the freeze; not part of the frozen text (stamps/pins.txt).
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: Apache-2.0 -/
