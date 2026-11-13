import OscInt.Statements.LatticeCubeRoot

/-!
# Batch HC: the hypercubic lattice kernel in every dimension (statements only)

Mathematics: `docs/statements.md`, "Batch HC". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`, lessons 23 and 29).

* `hypercubicKernel d t x = ∫_{[−π, π]^d} e^{i(t Σ_j cos k_j + Σ_j x_j k_j)} dk` on `Fin d → ℝ` (product measure).
* TdF `HypercubicKernelFactorStatement`: `K_d(t, x) = ∏_j I(t, x_j)` for every `d`, real `t`, `x ∈ ℤ^d`.
* TdE′ `HypercubicCubeRootStatement`: `|K_d(t, x)| ≤ (8(1 + √7)/3)^d t^{−d/3}` for every `d`, `t > 0`, `x ∈ ℤ^d`.

Modelling choices: `latticeKernel1` (batch LE) is reused unchanged; powers of `t` are `Real.rpow` with the real exponent
`−d/3`; `d = 0` is included (both sides are 1).
-/

namespace OscInt.Statements

/-- The box `[−π, π]^d` in `Fin d → ℝ`. -/
def hypercubeBox (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc (-Real.pi) Real.pi)

/-- The `d`-dimensional hypercubic lattice kernel `K_d(t, x) = ∫_{[−π, π]^d} e^{i(t Σ_j cos k_j + Σ_j x_j k_j)} dk`. -/
noncomputable def hypercubicKernel (d : ℕ) (t : ℝ) (x : Fin d → ℤ) : ℂ :=
  ∫ k in hypercubeBox d,
    Complex.exp (↑(t * ∑ j, Real.cos (k j) + ∑ j, (x j : ℝ) * k j) * Complex.I)

/-- **TdF** The `d`-dimensional hypercubic kernel factorises: `K_d(t, x) = ∏_j I(t, x_j)` for every `d`, every real
`t` and `x ∈ ℤ^d`. -/
def HypercubicKernelFactorStatement : Prop :=
  ∀ (d : ℕ) (t : ℝ) (x : Fin d → ℤ), hypercubicKernel d t x = ∏ j, latticeKernel1 t (x j : ℝ)

theorem statement_pin_HypercubicKernelFactor :
    HypercubicKernelFactorStatement = HypercubicKernelFactorStatement := rfl

/-- **TdE′** Dispersive decay of the free lattice Schrödinger group on `ℤ^d` with an explicit constant:
`|K_d(t, x)| ≤ (8(1 + √7)/3)^d t^{−d/3}` for every `d`, every `t > 0` and `x ∈ ℤ^d`. -/
def HypercubicCubeRootStatement : Prop :=
  ∀ (d : ℕ) (t : ℝ) (x : Fin d → ℤ), 0 < t →
    ‖hypercubicKernel d t x‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ d * t ^ (-(d : ℝ) / 3)

theorem statement_pin_HypercubicCubeRoot : HypercubicCubeRootStatement = HypercubicCubeRootStatement := rfl

end OscInt.Statements
