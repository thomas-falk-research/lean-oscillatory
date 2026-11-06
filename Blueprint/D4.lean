import OscInt.Statements.D4
import Blueprint.StationaryPhase

/-!
# Blueprint for S4.1 (definitions only)

Route: `docs/proof-S4.md`. Each part is proved as `theorem OscInt.D4.<part> : <Prop>` under `OscInt/D4/`; the
assembly `OscInt.D4.d4Bound_of` (in `OscInt/D4/Assembly.lean`) derives `D4BoundStatement` from these parts, the
S2/S3 infrastructure parts (`AffineChangeFacts`, `AmpBoundAffineFacts`, `AmpBoundMulFacts`) and the proved theorems
`OscInt.fold` (S3) and `OscInt.nonStationary` (S2.1).

Symbols.
* `cubicPoly q z = a z₁³ + b z₁²z₂ + c z₁z₂² + d z₂³` for `q = (a, b, c, d)`.
* `normalize φ = φ − φ(0) − Dφ(0)` and `grad0 φ = (∂₁φ(0), ∂₂φ(0))`.
* `rescale φ ε z = φ(εz)/ε³` for `ε ≠ 0` and `cubicPoly (cubicCoeffs φ) z` for `ε = 0`.
* `annulus = {z : 1/2 ≤ ‖z‖ ≤ 2}` (max norm).
* `hessNorm Ψ k = (∂₁₁Ψ)² + (∂₁₂Ψ)² + (∂₂₂Ψ)²` at `k`; `kerVec₁ = (−∂₁₂Ψ, ∂₁₁Ψ)`, `kerVec₂ = (∂₂₂Ψ, −∂₁₂Ψ)`
  (both lie in the kernel of the Hessian when `hessDet Ψ k = 0`);
  `foldGauge Ψ k = (hessDet Ψ k)² + (D³Ψ(k)[kerVec₁³])² + (D³Ψ(k)[kerVec₂³])²`.
  `0 < foldGauge ∧ 0 < hessNorm` is an open condition implying `FoldOrNondeg`.
-/

namespace OscInt.Blueprint

open Set MeasureTheory OscInt.Statements
open scoped ContDiff

/-- The binary cubic `a z₁³ + b z₁²z₂ + c z₁z₂² + d z₂³`. -/
def cubicPoly (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  q.1 * z.1 ^ 3 + q.2.1 * z.1 ^ 2 * z.2 + q.2.2.1 * z.1 * z.2 ^ 2 + q.2.2.2 * z.2 ^ 3

/-- `φ` minus its value and differential at `0`. -/
noncomputable def normalize (φ : ℝ × ℝ → ℝ) (κ : ℝ × ℝ) : ℝ := φ κ - φ 0 - fderiv ℝ φ 0 κ

/-- The gradient of `φ` at `0`. -/
noncomputable def grad0 (φ : ℝ × ℝ → ℝ) : ℝ × ℝ := (fderiv ℝ φ 0 (1, 0), fderiv ℝ φ 0 (0, 1))

/-- The rescaled phases `ε⁻³ φ(ε ·)`, with the cubic part at `ε = 0`. -/
noncomputable def rescale (φ : ℝ × ℝ → ℝ) (ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  if ε = 0 then cubicPoly (cubicCoeffs φ) z else φ (ε • z) / ε ^ 3

/-- The closed annulus `1/2 ≤ ‖z‖ ≤ 2` (max norm). -/
def annulus : Set (ℝ × ℝ) := {z | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

/-- Sum of squares of the Hessian entries. -/
noncomputable def hessNorm (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  dd Ψ k (1, 0) (1, 0) ^ 2 + dd Ψ k (1, 0) (0, 1) ^ 2 + dd Ψ k (0, 1) (0, 1) ^ 2

/-- First candidate kernel vector of the Hessian. -/
noncomputable def kerVec₁ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ × ℝ := (-dd Ψ k (1, 0) (0, 1), dd Ψ k (1, 0) (1, 0))

/-- Second candidate kernel vector of the Hessian. -/
noncomputable def kerVec₂ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ × ℝ := (dd Ψ k (0, 1) (0, 1), -dd Ψ k (1, 0) (0, 1))

/-- Quantitative fold/nondegeneracy gauge. -/
noncomputable def foldGauge (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  hessDet Ψ k ^ 2 + ddd Ψ k (kerVec₁ Ψ k) (kerVec₁ Ψ k) (kerVec₁ Ψ k) ^ 2 +
    ddd Ψ k (kerVec₂ Ψ k) (kerVec₂ Ψ k) (kerVec₂ Ψ k) ^ 2

/-- **D1** Normalisation: subtracting the affine part at `0` keeps `C⁴` and all second and third derivatives,
and moves the gradient into the linear term without changing the modulus of the integral. -/
def NormalizeFacts : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ →
    ContDiff ℝ 4 (normalize φ) ∧ normalize φ 0 = 0 ∧ fderiv ℝ (normalize φ) 0 = 0 ∧
      dd (normalize φ) = dd φ ∧ ddd (normalize φ) = ddd φ ∧
      ∀ (A : ℝ × ℝ → ℂ) (t : ℝ) (y : ℝ × ℝ),
        ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ =
          ‖oscInt2 (fun κ => t * normalize φ κ + lin (y + t • grad0 φ) κ) A‖

/-- **D2** Rescaled family: for a normalised `C⁴` phase with vanishing Hessian at `0`, the phases
`ε⁻³ φ(ε ·)` (`ε ∈ ℝ`, cubic part at `ε = 0`) form a family of class `C⁴` over `ℝ`. -/
def RescaleFamilyFacts : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → φ 0 = 0 → fderiv ℝ φ 0 = 0 → (∀ v w, dd φ 0 v w = 0) →
    FamilyCk 4 (rescale φ)

/-- **D3** Algebra of binary cubics: if `disc q ≠ 0`, then at every `z ≠ 0` the Hessian of the cubic is nonzero
and the fold gauge is positive. -/
def CubicGaugeFacts : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → ∀ z : ℝ × ℝ, z ≠ 0 →
    0 < foldGauge (cubicPoly q) z ∧ 0 < hessNorm (cubicPoly q) z

/-- **D4** The gauge condition implies the fold-or-nondegenerate condition. -/
def GaugeFoldFacts : Prop :=
  ∀ Ψ : ℝ × ℝ → ℝ, ContDiff ℝ 3 Ψ → ∀ k : ℝ × ℝ,
    0 < foldGauge Ψ k → 0 < hessNorm Ψ k → FoldOrNondeg Ψ k

/-- **D5** Openness: for a `C³` family, the gauge condition on a compact set persists near any parameter. -/
def GaugeOpenFacts : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) (σ₀ : Λ) (K : Set (ℝ × ℝ)),
    FamilyCk 3 Ψ → IsCompact K → (∀ k ∈ K, 0 < foldGauge (Ψ σ₀) k ∧ 0 < hessNorm (Ψ σ₀) k) →
      ∀ᶠ σ in nhds σ₀, ∀ k ∈ K, 0 < foldGauge (Ψ σ) k ∧ 0 < hessNorm (Ψ σ) k

/-- **D6** Large linear terms are non-stationary: for a `C¹` family over a compact space and a compact `K` there
is `G` with `|∇(Ψ_σ + p·)| ≥ 1` on `K` whenever `‖p‖ ≥ G`. -/
def GradBoundFacts : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)),
    FamilyCk 1 Ψ → IsCompact K →
      ∃ G : ℝ, ∀ σ, ∀ k ∈ K, ∀ p : ℝ × ℝ, G ≤ ‖p‖ → GradLower (Ψ σ) p k 1

/-- **D7** A smooth cut-off: `χ = 1` on `B̄(0, 1)`, `tsupport χ ⊆ B̄(0, 2)`, values in `[0, 1]`, and
`χ(2z) ≤ χ(z)` (so `χ − χ(2·) ≥ 0`; e.g. a product of two even one-dimensional bumps nonincreasing in `|x|`). -/
def CutoffFacts : Prop :=
  ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧
    (∀ z, ‖z‖ ≤ 1 → χ z = 1) ∧ tsupport χ ⊆ Metric.closedBall 0 2 ∧ ∀ z, χ ((2 : ℝ) • z) ≤ χ z

/-- **D8** Trivial bound: a continuous amplitude bounded by `M` with support in `B̄(0, r)` gives
`|I(Q, A)| ≤ 4 r² M` (the area of the max-norm ball). -/
def TrivialBoundFacts : Prop :=
  ∀ (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M r : ℝ), Continuous A → (∀ k, ‖A k‖ ≤ M) →
    tsupport A ⊆ Metric.closedBall 0 r → ‖oscInt2 Q A‖ ≤ 4 * r ^ 2 * M

/-- **D9** Dyadic sum: for `δ ∈ (0, 1]` and `t ≥ 1` there is `J` with `t ε_j³ ≥ 1` for `j < J`, `t ε_J³ < 1`,
`ε_J² ≤ t^{-2/3}` and `∑_{j<J} ε_j² (t ε_j³)^{-5/6} ≤ 4 t^{-2/3}`, where `ε_j = δ / 2^j`. -/
def DyadicSumFacts : Prop :=
  ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ t →
    ∃ J : ℕ, (∀ j < J, 1 ≤ t * (δ / 2 ^ j) ^ 3) ∧ t * (δ / 2 ^ J) ^ 3 < 1 ∧
      (δ / 2 ^ J) ^ 2 ≤ t ^ (-(2 : ℝ) / 3) ∧
      ∑ j ∈ Finset.range J, (δ / 2 ^ j) ^ 2 * (t * (δ / 2 ^ j) ^ 3) ^ (-(5 : ℝ) / 6) ≤ 4 * t ^ (-(2 : ℝ) / 3)

end OscInt.Blueprint
