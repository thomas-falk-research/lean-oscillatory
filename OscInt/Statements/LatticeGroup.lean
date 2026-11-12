import OscInt.Statements.Hypercubic

/-!
# Batch LS: the free lattice Schrödinger group on ℤ^d (statements only)

Mathematics: `docs/statements.md`, "Batch LS". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`, lessons 23 and 29).

The equation `i u′(t) + Δu(t) = 0` on `ℓ²(ℤ^d)` with the nearest-neighbour Laplacian
`(Δg)(x) = Σ_j (g(x + e_j) + g(x − e_j) − 2g(x))`, stated through its solutions: a curve `u : ℝ → ℓ²(ℤ^d)` that is
differentiable in the `ℓ²` norm at every real time, with derivative `iΔu(t)` coordinate by coordinate.
* LS-E `LatticeSchrodingerExistsStatement`: every `ℓ²` datum has a solution.
* LS-K `LatticeSchrodingerKernelStatement`: every solution is the convolution of its datum with
  `G_d(t, z) = (2π)^{−d} e^{−2idt} K_d(2t, z)` (absolutely convergent), `K_d` the frozen hypercubic kernel of batch HC.
  In particular solutions are unique.
* LS-D `LatticeSchrodingerDispersiveStatement`: for `ℓ¹` data and `t ≠ 0`,
  `|u(t, x)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}} ‖f‖_1`, `C* = 8(1 + √7)/3`.
* LS-D′ `LatticeSchrodingerDecayStatement`: for `ℓ¹` data and every real `t`,
  `|u(t, x)| ≤ (1 + τ)^{d/3} (1 + |t|)^{−d/3} ‖f‖_1`, `τ = (C*/(2π))³/2`.

Modelling choices: `ℓ²(ℤ^d)` is Mathlib's `lp (fun _ : Fin d → ℤ => ℂ) 2`; the Laplacian is written on coordinates, so
no operator is constructed in this file; `d = 0` is included (the lattice is one point, `Δ = 0`). Powers of `t` are
`Real.rpow`; LS-D excludes `t = 0`, where `0^{−d/3}` would be `0` in Lean.
-/

namespace OscInt.Statements

/-- `ℓ²(ℤ^d)` with complex values. -/
noncomputable abbrev LatticeL2 (d : ℕ) := lp (fun _ : Fin d → ℤ => ℂ) 2

/-- The unit vector `e_j` of `ℤ^d`. -/
def latticeUnit (d : ℕ) (j : Fin d) : Fin d → ℤ := Pi.single j 1

/-- The nearest-neighbour discrete Laplacian of `g` at the site `x`: `Σ_j (g(x + e_j) + g(x − e_j) − 2g(x))`. -/
def latticeLaplacian (d : ℕ) (g : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) : ℂ :=
  ∑ j, (g (x + latticeUnit d j) + g (x - latticeUnit d j) - 2 * g x)

/-- `u` solves `i u′ + Δu = 0` in `ℓ²(ℤ^d)` with `u(0) = f`: at every real time `u` is differentiable in the `ℓ²` norm,
and its derivative is `iΔu(t)` at every site. -/
def IsLatticeSchrodingerSolution (d : ℕ) (f : LatticeL2 d) (u : ℝ → LatticeL2 d) : Prop :=
  u 0 = f ∧ ∀ t : ℝ, ∃ w : LatticeL2 d, HasDerivAt u w t ∧
    ∀ x : Fin d → ℤ, w x = Complex.I * latticeLaplacian d (fun y => u t y) x

/-- The Schrödinger kernel `G_d(t, z) = (2π)^{−d} e^{−2idt} K_d(2t, z)`. -/
noncomputable def schrodingerKernel (d : ℕ) (t : ℝ) (z : Fin d → ℤ) : ℂ :=
  (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) * Complex.exp (↑(-(2 * (d : ℝ) * t)) * Complex.I) * hypercubicKernel d (2 * t) z

/-- **LS-E** Every datum `f ∈ ℓ²(ℤ^d)` has a solution of `i u′ + Δu = 0` with `u(0) = f`. -/
def LatticeSchrodingerExistsStatement : Prop :=
  ∀ (d : ℕ) (f : LatticeL2 d), ∃ u : ℝ → LatticeL2 d, IsLatticeSchrodingerSolution d f u

theorem statement_pin_LatticeSchrodingerExists :
    LatticeSchrodingerExistsStatement = LatticeSchrodingerExistsStatement := rfl

/-- **LS-K** Every solution is the kernel convolution of its datum: for every real `t` and site `x`, the series
`Σ_y G_d(t, x − y) f(y)` converges absolutely and equals `u(t, x)`. -/
def LatticeSchrodingerKernelStatement : Prop :=
  ∀ (d : ℕ) (f : LatticeL2 d) (u : ℝ → LatticeL2 d), IsLatticeSchrodingerSolution d f u →
    ∀ (t : ℝ) (x : Fin d → ℤ),
      Summable (fun y : Fin d → ℤ => ‖schrodingerKernel d t (x - y) * f y‖) ∧
        u t x = ∑' y : Fin d → ℤ, schrodingerKernel d t (x - y) * f y

theorem statement_pin_LatticeSchrodingerKernel :
    LatticeSchrodingerKernelStatement = LatticeSchrodingerKernelStatement := rfl

/-- **LS-D** Dispersive estimate with an explicit constant: for a solution with `ℓ¹` datum and `t ≠ 0`,
`|u(t, x)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}} ‖f‖_1`, `C* = 8(1 + √7)/3`. -/
def LatticeSchrodingerDispersiveStatement : Prop :=
  ∀ (d : ℕ) (f : LatticeL2 d) (u : ℝ → LatticeL2 d), IsLatticeSchrodingerSolution d f u →
    Summable (fun y : Fin d → ℤ => ‖f y‖) →
    ∀ (t : ℝ) (x : Fin d → ℤ), t ≠ 0 →
      ‖u t x‖ ≤ min 1 ((8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ d * (2 * |t|) ^ (-(d : ℝ) / 3)) *
        ∑' y : Fin d → ℤ, ‖f y‖

theorem statement_pin_LatticeSchrodingerDispersive :
    LatticeSchrodingerDispersiveStatement = LatticeSchrodingerDispersiveStatement := rfl

/-- **LS-D′** Decay at every time: for a solution with `ℓ¹` datum and every real `t`,
`|u(t, x)| ≤ (1 + τ)^{d/3} (1 + |t|)^{−d/3} ‖f‖_1`, `τ = (C*/(2π))³/2`, `C* = 8(1 + √7)/3`. -/
def LatticeSchrodingerDecayStatement : Prop :=
  ∀ (d : ℕ) (f : LatticeL2 d) (u : ℝ → LatticeL2 d), IsLatticeSchrodingerSolution d f u →
    Summable (fun y : Fin d → ℤ => ‖f y‖) →
    ∀ (t : ℝ) (x : Fin d → ℤ),
      ‖u t x‖ ≤ (1 + (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2) ^ ((d : ℝ) / 3) *
        (1 + |t|) ^ (-(d : ℝ) / 3) * ∑' y : Fin d → ℤ, ‖f y‖

theorem statement_pin_LatticeSchrodingerDecay :
    LatticeSchrodingerDecayStatement = LatticeSchrodingerDecayStatement := rfl

end OscInt.Statements
