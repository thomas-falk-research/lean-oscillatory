/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.PeriodicAnalytic

/-! # Blueprint for batch PA (PA-C, PA-T, LC-1): intermediate propositions, definitions only

Route: `docs/proof-PA.md`. Four parts; the assembly `OscInt/Front/PeriodicAnalyticAssembly.lean` proves the three
statements from them. -/

namespace OscInt.Blueprint.PeriodicAnalytic

open OscInt.Statements

/-- **P-shift** The Fourier integral of a periodic-analytic function is unchanged when the contour `[0, 2π]` is moved
to height `b`, `|b| < a` (Cauchy on a rectangle; the vertical sides cancel by periodicity). -/
def ContourShiftFacts : Prop :=
  ∀ (v : ℂ → ℂ) (a M b : ℝ) (k : ℤ), PeriodicAnalyticOn v a M → |b| < a →
    ∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v ((θ : ℂ) + (b : ℂ) * Complex.I) *
        Complex.exp (-((k : ℂ) * ((θ : ℂ) + (b : ℂ) * Complex.I)) * Complex.I)

/-- **P-series** Given the coefficient bound of PA-C for `v`, the Fourier series of the restriction of `v` to the real
axis converges to `v` at every real point. -/
def FourierSeriesFacts : Prop :=
  ∀ (v : ℂ → ℂ) (a M : ℝ), 0 < a → PeriodicAnalyticOn v a M →
    (∀ k : ℤ, ‖∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)‖ ≤
      2 * Real.pi * M * Real.exp (-(a * |(k : ℝ)|))) →
    ∀ x : ℝ, HasSum (fun k : ℤ =>
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I)) *
        Complex.exp (↑((k : ℝ) * x) * Complex.I)) (v (x : ℂ))

/-- **P-alias** Aliasing, as a statement about sequences: if `|c_k| ≤ M e^{−a|k|}` and the series
`Σ_k c_k e^{ik·2πj/N}` has sum `f j` for every `j < N`, then the mean of the `f j` differs from `c_0` by at most
`2M/(e^{aN} − 1)`. -/
def AliasBoundFacts : Prop :=
  ∀ (c : ℤ → ℂ) (f : ℕ → ℂ) (a M : ℝ) (N : ℕ), 0 < a → 0 < N →
    (∀ k : ℤ, ‖c k‖ ≤ M * Real.exp (-(a * |(k : ℝ)|))) →
    (∀ j < N, HasSum (fun k : ℤ =>
      c k * Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I)) (f j)) →
    ‖((N : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range N, f j - c 0‖ ≤ 2 * M / (Real.exp (a * (N : ℝ)) - 1)

/-- **P-lc** The integrand of the 1D lattice kernel: `z ↦ e^{it cos z}` is periodic-analytic on the strip of
half-width `η > 0` with bound `e^{|t| sinh η}`, and the kernel is its Fourier integral of index `−n`. -/
def KernelIntegrandFacts : Prop :=
  (∀ t η : ℝ, 0 < η →
    PeriodicAnalyticOn (fun z : ℂ => Complex.exp ((t : ℂ) * Complex.cos z * Complex.I)) η
      (Real.exp (|t| * Real.sinh η))) ∧
  ∀ (t : ℝ) (n : ℤ), latticeKernel1 t (n : ℝ) =
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((t : ℂ) * Complex.cos (θ : ℂ) * Complex.I) *
      Complex.exp (↑(-(((-n : ℤ) : ℝ) * θ)) * Complex.I)

end OscInt.Blueprint.PeriodicAnalytic
