import OscInt.Statements.Global

/-!
# Batch LE: explicit constants for the 1D and 2D lattice kernels (statements only)

Mathematics: `docs/statements.md`, "Batch LE". Written, stamped and blind-reviewed before any proof of these statements
exists (`CONTRIBUTING.md`, lessons 23 and 29).

* T0E `LatticeKernel1ExplicitStatement`: the 1D lattice kernel `I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk` satisfies
  `|I(t, ξ)| ≤ 24 · 2^{1/4} t^{−1/2} + 36 · 2^{1/6} t^{−1/3}` for every `t > 0` and every real `ξ`.
* T6F `LatticeKernelFactorStatement`: T6's kernel factorises, `K(t, x) = I(t, x₁) I(t, x₂)` for `x ∈ ℤ²`.
* T6E `LatticeLaplacianExplicitStatement`: `|K(t, x)| ≤ (24 · 2^{1/4} + 36 · 2^{1/6})² t^{−2/3}` for `t ≥ 1`,
  uniformly over `x ∈ ℤ²` (T6 with an explicit constant, about 4754).

Modelling choices.
* `I` is Lean's oriented interval integral over `[−π, π]`; `K` is `latticeKernel` of batch GD, unchanged.
* Powers are `Real.rpow`; T0E assumes `0 < t` (at `t = 0`, `0 ^ (−1/2) = 0` in Lean and the bound would be false).
* The constants are those the frozen S1 constants (8 and 18) give; they are not sharp (`docs/statements.md`).
-/

namespace OscInt.Statements

/-- The 1D lattice kernel `I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk`. For integer `ξ = n` it is `2π iⁿ Jₙ(t)`
(Bessel's integral; not used or stated here). -/
noncomputable def latticeKernel1 (t ξ : ℝ) : ℂ :=
  ∫ k in (-Real.pi)..Real.pi, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)

/-- **T0E** Explicit bound for the 1D lattice kernel: `|I(t, ξ)| ≤ 24 · 2^{1/4} t^{−1/2} + 36 · 2^{1/6} t^{−1/3}`
for every `t > 0` and every real `ξ`. -/
def LatticeKernel1ExplicitStatement : Prop :=
  ∀ t ξ : ℝ, 0 < t →
    ‖latticeKernel1 t ξ‖ ≤
      24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) * t ^ (-(1 : ℝ) / 3)

theorem statement_pin_LatticeKernel1Explicit :
    LatticeKernel1ExplicitStatement = LatticeKernel1ExplicitStatement := rfl

/-- **T6F** The 2D lattice kernel factorises: `K(t, x) = I(t, x₁) I(t, x₂)` for every real `t` and `x ∈ ℤ²`. -/
def LatticeKernelFactorStatement : Prop :=
  ∀ (t : ℝ) (x : ℤ × ℤ), latticeKernel t x = latticeKernel1 t (x.1 : ℝ) * latticeKernel1 t (x.2 : ℝ)

theorem statement_pin_LatticeKernelFactor :
    LatticeKernelFactorStatement = LatticeKernelFactorStatement := rfl

/-- **T6E** Dispersive decay of the 2D lattice Laplacian with an explicit constant:
`|K(t, x)| ≤ (24 · 2^{1/4} + 36 · 2^{1/6})² t^{−2/3}` for `t ≥ 1`, uniformly over `x ∈ ℤ²`. -/
def LatticeLaplacianExplicitStatement : Prop :=
  ∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t →
    ‖latticeKernel t x‖ ≤
      (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_LatticeLaplacianExplicit :
    LatticeLaplacianExplicitStatement = LatticeLaplacianExplicitStatement := rfl

end OscInt.Statements
