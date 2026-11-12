/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.LatticeGroup

/-!
# Blueprint for batch LS (LS-E, LS-K, LS-D, LS-D′): the parts of the route (definitions only)

Route: `docs/proof-LS.md`. The operator `iΔ` is bounded on `ℓ²(ℤ^d)`; the solution is `exp(t · iΔ) f`; solutions are
unique (a Lipschitz linear ODE); the coordinates of `exp(t · iΔ) f` are identified with the kernel convolution through
the exponential series, the stencil powers `Lₙ` of `Δ` and their Fourier representation on the box `[−π, π]^d`.
-/

namespace OscInt.Blueprint.LatticeGroup

open OscInt.Statements

/-- The stencil powers of `Δ`: `L₀ = δ₀`, `Lₙ₊₁ = Δ Lₙ` (as functions on `ℤ^d`). -/
def stencil (d : ℕ) : ℕ → (Fin d → ℤ) → ℂ
  | 0 => fun z => if z = 0 then 1 else 0
  | n + 1 => latticeLaplacian d (stencil d n)

/-- **P-op** The Laplacian is a bounded operator on `ℓ²(ℤ^d)` with the coordinate formula and norm at most `4d`. -/
def LapOpFacts : Prop :=
  ∀ d : ℕ, ∃ A : LatticeL2 d →L[ℂ] LatticeL2 d,
    (∀ (g : LatticeL2 d) (x : Fin d → ℤ), A g x = latticeLaplacian d (fun y => g y) x) ∧ ‖A‖ ≤ 4 * d

/-- **P-exp** `t ↦ exp(t · iA) f` is a solution, for any operator `A` with the coordinate formula. -/
def ExpSolutionFacts : Prop :=
  ∀ (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d),
    (∀ (g : LatticeL2 d) (x : Fin d → ℤ), A g x = latticeLaplacian d (fun y => g y) x) →
    ∀ f : LatticeL2 d,
      IsLatticeSchrodingerSolution d f (fun t => NormedSpace.exp (t • (Complex.I • A)) f)

/-- **P-unique** Two solutions with the same datum coincide. -/
def UniqueFacts : Prop :=
  ∀ (d : ℕ) (f : LatticeL2 d) (u v : ℝ → LatticeL2 d),
    IsLatticeSchrodingerSolution d f u → IsLatticeSchrodingerSolution d f v → u = v

/-- **P-stencil** The stencil powers are in `ℓ¹` with `Σ_z |Lₙ(z)| ≤ (4d)ⁿ`, and `Aⁿ` acts as convolution with `Lₙ`. -/
def StencilFacts : Prop :=
  ∀ (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d),
    (∀ (g : LatticeL2 d) (x : Fin d → ℤ), A g x = latticeLaplacian d (fun y => g y) x) →
    ∀ n : ℕ,
      (Summable (fun z => ‖stencil d n z‖) ∧ ∑' z, ‖stencil d n z‖ ≤ (4 * d) ^ n) ∧
      ∀ (f : LatticeL2 d) (x : Fin d → ℤ),
        Summable (fun y => ‖stencil d n (x - y) * f y‖) ∧ (A ^ n) f x = ∑' y, stencil d n (x - y) * f y

/-- **P-fourier** `Lₙ(z) = (2π)^{−d} ∫_{[−π,π]^d} (2 Σ_j cos k_j − 2d)ⁿ e^{i z·k} dk`. -/
def FourierStencilFacts : Prop :=
  ∀ (d n : ℕ) (z : Fin d → ℤ),
    stencil d n z = (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
      ∫ k in hypercubeBox d, ((2 * ∑ j, Real.cos (k j) - 2 * d : ℝ) : ℂ) ^ n *
        Complex.exp (↑(∑ j, (z j : ℝ) * k j) * Complex.I)

/-- **P-series** `G_d(t, z) = Σₙ (it)ⁿ/n! Lₙ(z)`. -/
def KernelSeriesFacts : Prop :=
  ∀ (d : ℕ) (t : ℝ) (z : Fin d → ℤ),
    HasSum (fun n : ℕ => ((Complex.I * t) ^ n / n.factorial) * stencil d n z) (schrodingerKernel d t z)

/-- **P-conv** The coordinates of `exp(t · iA) f` are the kernel convolution, absolutely convergent (from P-stencil and
P-series by exchanging the two sums). -/
def KernelConvFacts : Prop :=
  ∀ (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d),
    (∀ (g : LatticeL2 d) (x : Fin d → ℤ), A g x = latticeLaplacian d (fun y => g y) x) →
    ∀ (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ),
      Summable (fun y => ‖schrodingerKernel d t (x - y) * f y‖) ∧
        NormedSpace.exp (t • (Complex.I • A)) f x = ∑' y, schrodingerKernel d t (x - y) * f y

/-- **P-envelope** For `t ≠ 0`: `min{1, (C*/(2π))^d (2|t|)^{−d/3}} ≤ (1 + τ)^{d/3} (1 + |t|)^{−d/3}`,
`τ = (C*/(2π))³/2`. -/
def EnvelopeFacts : Prop :=
  ∀ (d : ℕ) (t : ℝ), t ≠ 0 →
    min 1 ((8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ d * (2 * |t|) ^ (-(d : ℝ) / 3)) ≤
      (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ ((d : ℝ) / 3) * (1 + |t|) ^ (-(d : ℝ) / 3)

/-- **P-bound** The kernel bound: `|G_d(t, z)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}}` for `t ≠ 0`. -/
def KernelBoundFacts : Prop :=
  ∀ (d : ℕ) (t : ℝ) (z : Fin d → ℤ), t ≠ 0 →
    ‖schrodingerKernel d t z‖ ≤
      min 1 ((8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ d * (2 * |t|) ^ (-(d : ℝ) / 3))

end OscInt.Blueprint.LatticeGroup
