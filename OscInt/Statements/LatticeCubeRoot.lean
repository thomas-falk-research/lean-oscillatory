import OscInt.Statements.LatticeExplicit

/-!
# Batch LE2: the cube-root bound for the 1D lattice kernel and its 2D corollary (statements only)

Mathematics: `docs/statements.md`, "Batch LE2". Written, stamped and blind-reviewed before any proof of these
statements exists (`CONTRIBUTING.md`, lessons 23 and 29).

* T0E′ `LatticeKernel1CubeRootStatement`: the 1D lattice kernel `I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk` satisfies
  `|I(t, ξ)| ≤ 8(1 + √7)/3 · t^{−1/3}` for every `t > 0` and every real `ξ`.
* T6E′ `LatticeLaplacianCubeRootStatement`: T6's kernel satisfies `|K(t, x)| ≤ (8(1 + √7)/3)² t^{−2/3}` for every
  `t > 0`, uniformly over `x ∈ ℤ²`.

Modelling choices.
* `latticeKernel1` (batch LE) and `latticeKernel` (batch GD) are reused unchanged; this file defines nothing new.
* Powers are `Real.rpow`; both statements assume `0 < t` (at `t = 0`, `0 ^ (−1/3) = 0` in Lean and both bounds would be
  false).
* The constant `8(1 + √7)/3 ≈ 9.722` is written out in each statement; it is within a factor 2 of the best constant
  (`docs/statements.md`, Batch LE2, modelling choice 3).
-/

namespace OscInt.Statements

/-- **T0E′** Cube-root bound for the 1D lattice kernel: `|I(t, ξ)| ≤ 8(1 + √7)/3 · t^{−1/3}` for every `t > 0` and
every real `ξ`. -/
def LatticeKernel1CubeRootStatement : Prop :=
  ∀ t ξ : ℝ, 0 < t →
    ‖latticeKernel1 t ξ‖ ≤ 8 * (1 + Real.sqrt 7) / 3 * t ^ (-(1 : ℝ) / 3)

theorem statement_pin_LatticeKernel1CubeRoot :
    LatticeKernel1CubeRootStatement = LatticeKernel1CubeRootStatement := rfl

/-- **T6E′** Dispersive decay of the 2D lattice Laplacian with the cube-root constant:
`|K(t, x)| ≤ (8(1 + √7)/3)² t^{−2/3}` for every `t > 0`, uniformly over `x ∈ ℤ²`. -/
def LatticeLaplacianCubeRootStatement : Prop :=
  ∀ (t : ℝ) (x : ℤ × ℤ), 0 < t →
    ‖latticeKernel t x‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ 2 * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_LatticeLaplacianCubeRoot :
    LatticeLaplacianCubeRootStatement = LatticeLaplacianCubeRootStatement := rfl

end OscInt.Statements
