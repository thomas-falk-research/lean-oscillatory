/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

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

/-! ## Analytic parts (route: `docs/proof-S2S3.md` with its revision section) -/

/-- Local bound with rate `r` at `(τ₀, k₀)`: on a neighbourhood of `τ₀` and for amplitudes supported in a small
closed ball around `k₀`, `|I(mQ_τ, A)| ≤ C M m^{-r}`. -/
def LocalBound {T : Type} [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T) (k₀ : ℝ × ℝ) (r : ℝ) : Prop :=
  ∃ U ∈ nhds τ₀, ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (τ : T) (m : ℝ),
    τ ∈ U → AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * Q τ k) A‖ ≤ C * M * m ^ (-r)

/-- **R2** Localisation: local bounds at every point of `T × K` give a global bound (`T` compact). -/
def LocalizationFacts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [CompactSpace T] (Q : T → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (r : ℝ),
    IsCompact K → (∀ τ, ∀ k ∈ K, LocalBound Q τ k r) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (τ : T) (m : ℝ), AmpBound 2 K A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * Q τ k) A‖ ≤ C * M * m ^ (-r)

/-- **L1** Non-critical point: rate 1. -/
def LocalNonCritFacts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T) (k₀ : ℝ × ℝ),
    FamilyCk 2 Q → ¬ IsCritical (Q τ₀) 0 k₀ → LocalBound Q τ₀ k₀ 1

/-- Normal form of order `j` at the origin (`docs/proof-S2S3.md` (L2)): `∇Ψ(0) = 0`, `∂²_yΨ(0) ≠ 0`,
`∂_x∂_yΨ(0) = 0`, and for `j = 2` `∂²_xΨ(0) ≠ 0`, for `j = 3` `∂²_xΨ(0) = 0`, `∂³_xΨ(0) ≠ 0`. -/
def NormalPoint (j : ℕ) (Ψ : ℝ × ℝ → ℝ) : Prop :=
  fderiv ℝ Ψ 0 (1, 0) = 0 ∧ fderiv ℝ Ψ 0 (0, 1) = 0 ∧ dd Ψ 0 (0, 1) (0, 1) ≠ 0 ∧ dd Ψ 0 (0, 1) (1, 0) = 0 ∧
    (j = 2 → dd Ψ 0 (1, 0) (1, 0) ≠ 0) ∧
    (j = 3 → dd Ψ 0 (1, 0) (1, 0) = 0 ∧ ddd Ψ 0 (1, 0) (1, 0) (1, 0) ≠ 0)

/-- **L2** Normal form by a linear change of coordinates centred at a critical point. -/
def NormalFormFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ : ℝ × ℝ), ContDiff ℝ 4 Ψ → IsCritical Ψ 0 k₀ →
    (hessDet Ψ k₀ ≠ 0 → ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), NormalPoint 2 (fun k => Ψ (k₀ + L k))) ∧
    (hessDet Ψ k₀ = 0 → FoldOrNondeg Ψ k₀ → ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), NormalPoint 3 (fun k => Ψ (k₀ + L k)))

/-- The quantitative hypotheses of the core estimate (L6) for one phase `Q` and a curve `ys` of critical points
in `y`, on the box `[-a, a] × [-2b, 2b]`, with lower bounds `μ` (for `∂²_y Q`), `ν` (for the `j`-th derivative of
the reduced phase `g(x) = Q(x, ys x)`) and an upper bound `D` on derivatives. -/
def CoreHyps (j : ℕ) (a b μ ν D : ℝ) (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) : Prop :=
  ContDiff ℝ 4 Q ∧ ContDiffOn ℝ 3 ys (Ioo (-2 * a) (2 * a)) ∧
    (∀ x ∈ Icc (-a) a, ys x ∈ Ioo (-b) b ∧ fderiv ℝ Q (x, ys x) (0, 1) = 0) ∧
    (∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-2 * b) (2 * b), μ ≤ |dd Q (x, y) (0, 1) (0, 1)|) ∧
    (∀ i ≤ 4, ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-2 * b) (2 * b), ‖iteratedFDeriv ℝ i Q (x, y)‖ ≤ D) ∧
    (∀ i ≤ 2, ∀ x ∈ Icc (-a) a, |iteratedDeriv i ys x| ≤ D) ∧
    ∀ x ∈ Icc (-a) a, ν ≤ |iteratedDeriv j (fun x => Q (x, ys x)) x|

/-- **L6** Core estimate (single phase, explicit uniformity): for `j ∈ {2, 3}` the constant depends only on
`(a, b, μ, ν, D)`, and `|I(mQ, A)| ≤ C M m^{-(1/2 + 1/j)}` for amplitudes supported in `[-a, a] × [-b, b]`. -/
def CoreEstimateFacts : Prop :=
  ∀ (j : ℕ), j = 2 ∨ j = 3 → ∀ (a b μ ν D : ℝ), 0 < a → 0 < b → 0 < μ → 0 < ν →
    ∃ C : ℝ, ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M m : ℝ),
      CoreHyps j a b μ ν D Q ys → AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ m →
        ‖oscInt2 (fun k => m * Q k) A‖ ≤ C * M * m ^ (-(1 / 2 + 1 / (j : ℝ)))

/-- **L3–L5** From a normal point to the core hypotheses, uniformly near `τ₀` (implicit critical point with a
topological parameter, tube lemma). -/
def NormalizedDataFacts : Prop :=
  ∀ (j : ℕ), j = 2 ∨ j = 3 → ∀ (T : Type) [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T),
    FamilyCk 4 Q → NormalPoint j (Q τ₀) →
    ∃ U ∈ nhds τ₀, ∃ a b μ ν D : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : T → ℝ → ℝ, ∀ τ ∈ U, CoreHyps j a b μ ν D (Q τ) (ys τ)

/-- **L2–L6 assembled** Critical points: rate 1 if the Hessian is nondegenerate, rate 5/6 at a fold point. -/
def LocalCritFacts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T) (k₀ : ℝ × ℝ),
    FamilyCk 4 Q → IsCritical (Q τ₀) 0 k₀ →
    (hessDet (Q τ₀) k₀ ≠ 0 → LocalBound Q τ₀ k₀ 1) ∧
    (FoldOrNondeg (Q τ₀) k₀ → LocalBound Q τ₀ k₀ (5 / 6))

/-- **N2** Non-stationary phase of order `N` for a compact family with `|∇Φ_τ| ≥ c` on `K`. -/
def NonStatCoreFacts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [CompactSpace T] (N : ℕ) (Φ : T → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (c : ℝ),
    FamilyCk (N + 1) Φ → IsCompact K → 0 < c → (∀ τ, ∀ k ∈ K, GradLower (Φ τ) 0 k c) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (τ : T) (m : ℝ), AmpBound N K A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * Φ τ k) A‖ ≤ C * M / m ^ N

/-- **F3** Parametric calculus: products and reciprocals of families of class `Cⁿ` are of class `Cⁿ`. -/
def FamilyCalculusFacts : Prop :=
  ∀ (T : Type) [TopologicalSpace T] (n : ℕ) (f g : T → ℝ × ℝ → ℝ),
    FamilyCk n f → FamilyCk n g →
      FamilyCk n (fun τ k => f τ k * g τ k) ∧ ((∀ τ k, f τ k ≠ 0) → FamilyCk n (fun τ k => (f τ k)⁻¹))

end OscInt.Blueprint
