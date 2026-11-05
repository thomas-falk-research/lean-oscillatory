import OscInt.Statements.StationaryPhase

/-!
# Blueprint for S2, S3: infrastructure parts (definitions only)

Route: `docs/proof-S2S3.md`. These parts are needed by every step of that route and are independent of its
details: family algebra (R1, L2), the affine change of variables (L2), and localisation by partitions of unity (R2).
The analytic parts (L1, L3–L6, N1–N2) are added after the route has been refereed.
Each part is proved as `theorem OscInt.StationaryPhase.<part> : <Prop>` under `OscInt/StationaryPhase/`.
-/

namespace OscInt.Blueprint

open Set MeasureTheory OscInt.Statements
open scoped ContDiff

/-- **F1a** Adding a linear term indexed by a subset `P ⊆ ℝ²` keeps a family of class `Cⁿ`: the family over
`Λ × P` given by `(σ, p) ↦ Ψ σ + p·(·)` is again of class `Cⁿ`. -/
def FamilyAddLinearFacts : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] (n : ℕ) (Ψ : Λ → ℝ × ℝ → ℝ) (P : Set (ℝ × ℝ)),
    FamilyCk n Ψ → FamilyCk n (fun q : Λ × P => fun k => Ψ q.1 k + lin q.2.1 k)

/-- **F1b** Composing every member of a family of class `Cⁿ` with a fixed affine map keeps class `Cⁿ`. -/
def FamilyAffineFacts : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] (n : ℕ) (Ψ : Λ → ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)),
    FamilyCk n Ψ → FamilyCk n (fun σ => fun k => Ψ σ (k₀ + L k))

/-- **F1c** Affine change of variables in `oscInt2`: for a linear automorphism `L` of `ℝ²` and `k₀ ∈ ℝ²`,
`∫ e^{iQ} A = |det L| ∫ e^{iQ(k₀ + L·)} A(k₀ + L·)`. -/
def AffineChangeFacts : Prop :=
  ∀ (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
    oscInt2 Q A = ((|LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| : ℝ) : ℂ) *
      oscInt2 (fun k => Q (k₀ + L k)) (fun k => A (k₀ + L k))

/-- **F1d** Amplitude bounds under an affine change of variables: derivatives of order `j` pick up `‖L‖ʲ`. -/
def AmpBoundAffineFacts : Prop :=
  ∀ (n : ℕ) (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ) (M : ℝ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
    AmpBound n K A M →
      AmpBound n ((fun k => k₀ + L k) ⁻¹' K) (fun k => A (k₀ + L k))
        (max 1 ‖(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ n * M)

/-- **F2a** Smooth partitions of unity subordinate to a finite open cover of a compact set: each `χ i` is smooth,
compactly supported with `tsupport (χ i) ⊆ U i`, takes values in `[0, 1]`, and `∑ χ i = 1` on `K`. -/
def PartitionFacts : Prop :=
  ∀ (r : ℕ) (K : Set (ℝ × ℝ)) (U : Fin r → Set (ℝ × ℝ)),
    IsCompact K → (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
    ∃ χ : Fin r → ℝ × ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧ (∀ i, tsupport (χ i) ⊆ U i) ∧
        (∀ i k, χ i k ∈ Icc (0 : ℝ) 1) ∧ ∀ k ∈ K, ∑ i, χ i k = 1

/-- **F2b** Cutting an amplitude off by a smooth compactly supported function: the product satisfies an amplitude
bound with support in `K ∩ tsupport χ` and a constant depending only on `n` and `χ`. -/
def AmpBoundMulFacts : Prop :=
  ∀ (n : ℕ) (χ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ) (M : ℝ),
      AmpBound n K A M → AmpBound n (K ∩ tsupport χ) (fun k => (χ k : ℂ) * A k) (C * M)

end OscInt.Blueprint
