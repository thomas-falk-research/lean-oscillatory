import OscInt.Statements.Family

/-!
# Batch GD: global decay from a local classification, the lattice Laplacian, sharpness (statements only)

Mathematics: `docs/statements.md`, "Batch GD". Written, stamped and blind-reviewed before any proof of these statements
exists (`CONTRIBUTING.md`, lessons 23 and 29).

* GD-C `GlobalDecayCritStatement`: a phase smooth on an open `U ⊇ K` (`K` compact) whose critical points for `Ψ + L`,
  `L ∈ K'` compact, are nondegenerate or folds, except at finitely many D4 points (vanishing Hessian, cubic part with
  nonzero discriminant): decay `m^{-2/3}`, uniform over amplitudes supported in `K` and over `L ∈ K'`.
* GD `GlobalDecayStatement`: every point of `K` is nondegenerate, a fold, or one of finitely many D4 points: decay
  `m^{-2/3}` uniformly over **all** linear terms `L` (the form a dispersive estimate needs, `L = x/t`).
* GD-F `GlobalFoldStatement`: every point of `K` is nondegenerate or a fold: `m^{-5/6}` over all `L`.
* GD-N `GlobalNondegStatement`: every point of `K` is nondegenerate: `m^{-1}` over all `L`.
* SH `SharpnessStatement`: a limit `m^σ I(m) → c ≠ 0` gives the lower bound `|I(m)| ≥ (|c|/2) m^{-σ}` eventually and
  excludes every faster rate; for functions on `ℝ` and for sequences.
* T1 `TorusUnfoldStatement`: a smooth weight `η` supported in `closedBall 0 4` (max norm) with
  `∫_{[−π, π]²} g = ∫_{ℝ²} η g` for every continuous `2π`-biperiodic `g`.
* T6 `LatticeLaplacianDecayStatement`: the kernel `∫_{[−π, π]²} e^{i(t(cos k₁ + cos k₂) + x·k)} dk` of the 2D lattice
  Schrödinger group is `O(t^{-2/3})` uniformly over `x ∈ ℤ²`.
* T6L `LatticeLaplacianLimitStatement`: along `x = (n, n)` at time `n`, `(−1)ⁿ n^{2/3} K → Γ(1/3)² · 48^{1/6}/√3`
  (`d4ClosedConstant (−1/48)`), so the rate `t^{-2/3}` is sharp (with SH).

Modelling choices.
* Amplitudes, the integral and linear terms are as in front-end batch 3 (`ContDiff ℝ 2 A`, `tsupport A ⊆ K`, bounds
  on `iteratedFDeriv ℝ j A` for `j ≤ 2`; `L : (ℝ × ℝ) →L[ℝ] ℝ`; the integral written out; max norm on `ℝ × ℝ`).
* Derivatives of a phase smooth only on `U` are Mathlib's `iteratedFDeriv` of the function on `ℝ²` at points of `U`.
* A D4 point is given as in FE-S4.1′L, at the point `k₀` instead of `0`: `D²Ψ(k₀) = 0` and
  `D³Ψ(k₀)[κ, κ, κ] = 6(a x³ + b x²y + c xy² + d y³)` with `(Cubic.mk a b c d).discr ≠ 0` for some coefficients.
* The exceptional set is a `Finset`; its points must lie in `U` (not necessarily in `K`).
* The lattice kernel omits the normalisation `(2π)^{-2}` and the constant `−4t` of the symbol
  `−4 + 2 cos k₁ + 2 cos k₂` of the discrete Laplacian, and uses `t` for `2t`; none changes the rate.
-/

namespace OscInt.Statements

open Filter Topology
open scoped ContDiff

/-- `k₀` is a D4 point of `Ψ`: the Hessian vanishes and the cubic part `D³Ψ(k₀)[κ, κ, κ]/6` is a binary cubic with
nonzero discriminant. -/
def IsD4Point (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) : Prop :=
  iteratedFDeriv ℝ 2 Ψ k₀ = 0 ∧ ∃ a b c d : ℝ,
    (∀ x y : ℝ, iteratedFDeriv ℝ 3 Ψ k₀ ![(x, y), (x, y), (x, y)] =
      6 * (a * x ^ 3 + b * x ^ 2 * y + c * x * y ^ 2 + d * y ^ 3)) ∧
    (Cubic.mk a b c d).discr ≠ 0

/-- Classification at critical points: for `L ∈ K'`, every critical point of `Ψ + L` in `K` outside `D` is
nondegenerate or a fold, and every point of `D` is a D4 point. -/
def ClassifiedCrit (Ψ : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)) (D : Finset (ℝ × ℝ)) : Prop :=
  (∀ L ∈ K', ∀ k ∈ K, k ∉ D → fderiv ℝ Ψ k + L = 0 → FoldOrNondegMatrix Ψ k) ∧ ∀ k₀ ∈ D, IsD4Point Ψ k₀

/-- Pointwise classification: every point of `K` outside `D` is nondegenerate or a fold, every point of `D` is a D4
point. -/
def Classified (Ψ : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (D : Finset (ℝ × ℝ)) : Prop :=
  (∀ k ∈ K, k ∉ D → FoldOrNondegMatrix Ψ k) ∧ ∀ k₀ ∈ D, IsD4Point Ψ k₀

/-- **GD-C** Global decay from the classification at critical points: decay `m^{-2/3}`, uniform over amplitudes
supported in `K` and over `L ∈ K'`. -/
def GlobalDecayCritStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)) (D : Finset (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → (↑D : Set (ℝ × ℝ)) ⊆ U → IsCompact K' → ContDiffOn ℝ 4 Ψ U →
    ClassifiedCrit Ψ K K' D →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3)

theorem statement_pin_GlobalDecayCrit : GlobalDecayCritStatement = GlobalDecayCritStatement := rfl

/-- **GD** Global decay from the pointwise classification: decay `m^{-2/3}`, uniform over amplitudes supported in `K`
and over all linear terms `L`. -/
def GlobalDecayStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (D : Finset (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → (↑D : Set (ℝ × ℝ)) ⊆ U → ContDiffOn ℝ 4 Ψ U → Classified Ψ K D →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3)

theorem statement_pin_GlobalDecay : GlobalDecayStatement = GlobalDecayStatement := rfl

/-- **GD-F** Every point of `K` nondegenerate or a fold: decay `m^{-5/6}` over all linear terms. -/
def GlobalFoldStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 4 Ψ U → (∀ k ∈ K, FoldOrNondegMatrix Ψ k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_GlobalFold : GlobalFoldStatement = GlobalFoldStatement := rfl

/-- **GD-N** Every point of `K` nondegenerate: decay `m^{-1}` over all linear terms. -/
def GlobalNondegStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 4 Ψ U → (∀ k ∈ K, (hessianMatrix Ψ k).det ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M / m

theorem statement_pin_GlobalNondeg : GlobalNondegStatement = GlobalNondegStatement := rfl

/-- **SH** Sharpness: if `m^σ I(m) → c ≠ 0`, then eventually `|I(m)| ≥ (|c|/2) m^{-σ}`, and no bound
`|I(m)| ≤ C m^{-σ'}` with `σ' > σ` holds eventually; for functions on `ℝ` and for sequences. -/
def SharpnessStatement : Prop :=
  (∀ (I : ℝ → ℂ) (σ : ℝ) (c : ℂ), Tendsto (fun m : ℝ => ((m ^ σ : ℝ) : ℂ) * I m) atTop (𝓝 c) → c ≠ 0 →
    (∀ᶠ m : ℝ in atTop, ‖c‖ / 2 * m ^ (-σ) ≤ ‖I m‖) ∧
    ∀ σ' > σ, ¬ ∃ C : ℝ, ∀ᶠ m : ℝ in atTop, ‖I m‖ ≤ C * m ^ (-σ')) ∧
  (∀ (I : ℕ → ℂ) (σ : ℝ) (c : ℂ), Tendsto (fun n : ℕ => (((n : ℝ) ^ σ : ℝ) : ℂ) * I n) atTop (𝓝 c) → c ≠ 0 →
    (∀ᶠ n : ℕ in atTop, ‖c‖ / 2 * (n : ℝ) ^ (-σ) ≤ ‖I n‖) ∧
    ∀ σ' > σ, ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ‖I n‖ ≤ C * (n : ℝ) ^ (-σ'))

theorem statement_pin_Sharpness : SharpnessStatement = SharpnessStatement := rfl

/-- The fundamental box `[−π, π]²` of the torus `(ℝ / 2πℤ)²`. -/
def torusBox : Set (ℝ × ℝ) := Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi

/-- **T1** Unfolding: a smooth weight `η` supported in `closedBall 0 4` (max norm) with
`∫_{[−π, π]²} g = ∫_{ℝ²} η g` for every continuous `g` that is `2π`-periodic in each variable. -/
def TorusUnfoldStatement : Prop :=
  ∃ η : ℝ × ℝ → ℝ, ContDiff ℝ ∞ η ∧ tsupport η ⊆ Metric.closedBall 0 4 ∧
    ∀ g : ℝ × ℝ → ℂ, Continuous g → (∀ k : ℝ × ℝ, g (k.1 + 2 * Real.pi, k.2) = g k) →
      (∀ k : ℝ × ℝ, g (k.1, k.2 + 2 * Real.pi) = g k) →
      ∫ k in torusBox, g k = ∫ k : ℝ × ℝ, (η k : ℂ) * g k

theorem statement_pin_TorusUnfold : TorusUnfoldStatement = TorusUnfoldStatement := rfl

/-- The kernel `K(t, x) = ∫_{[−π, π]²} e^{i(t(cos k₁ + cos k₂) + x·k)} dk` of the 2D lattice Schrödinger group
(up to the factor `(2π)^{-2}`, a time scale and a phase `e^{-4it}`). -/
noncomputable def latticeKernel (t : ℝ) (x : ℤ × ℤ) : ℂ :=
  ∫ k in torusBox,
    Complex.exp (↑(t * (Real.cos k.1 + Real.cos k.2) + ((x.1 : ℝ) * k.1 + (x.2 : ℝ) * k.2)) * Complex.I)

/-- **T6** Dispersive decay of the 2D lattice Laplacian: `|K(t, x)| ≤ C t^{-2/3}` for `t ≥ 1`, uniformly over
`x ∈ ℤ²`. -/
def LatticeLaplacianDecayStatement : Prop :=
  ∃ C : ℝ, ∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t → ‖latticeKernel t x‖ ≤ C * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_LatticeLaplacianDecay :
    LatticeLaplacianDecayStatement = LatticeLaplacianDecayStatement := rfl

/-- **T6L** The leading term on the diagonal: `(−1)ⁿ n^{2/3} K(n, (n, n)) → Γ(1/3)² 48^{1/6}/√3`
(`= d4ClosedConstant (−1/48)`, the D4 constant of the cubic `(κ₁³ + κ₂³)/6` at `(π/2, π/2)`). -/
def LatticeLaplacianLimitStatement : Prop :=
  Tendsto (fun n : ℕ => (((n : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * (-1 : ℂ) ^ n * latticeKernel n ((n : ℤ), (n : ℤ)))
    atTop (𝓝 (d4ClosedConstant (-1 / 48) : ℂ))

theorem statement_pin_LatticeLaplacianLimit :
    LatticeLaplacianLimitStatement = LatticeLaplacianLimitStatement := rfl

end OscInt.Statements
