/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Cusp
import OscInt.Statements.TriangularDecay

/-!
# Blueprint for batch K2: the parts of the route (definitions only)

Route: `docs/proof-K2.md` (with its section 8, the revision after the route referee). Written after the answers to
the blind pre-proof reviews were stamped (`stamps/20261128T023440Z-e368c37563ab`); propositions only. Each part is
proved as `theorem OscInt.K2.<lowerCamel name> : OscInt.Blueprint.K2.<Prop>` (for example
`coreEstimateM : CoreEstimateMFacts`).

Assemblies (the lead's):
* K2-L from P1, P2, P3 and the proved far branch `OscInt.Cusp.transverseNonStat` (`TransverseNonStatFacts`);
* K2-U from K2-L, P5, P6, P7, `ReducedBridge.bridge` and TRI-K/X (the A3 branch through P5, the bridge and K2-L
  with m = 4), and T6E′ at α = 0;
* K2-MA from P10a and P10b; K2-ML from K2-MA;
* K2-F from P13 and P14;
* K2-D from P5, P6, `bridge`, TRI-Q/W, P11, P12, K2-F and K2-ML (P11 and P12 take P9 as a hypothesis).

Parts.
* P1 `CoreEstimateMFacts`: the order-m core estimate with an outer linear term.
* P2 `NormalizedDataMFacts`: from a normal point of order m to `CoreHypsM` uniformly in the transverse velocity.
* P3 `ChartFacts`: the chart `k₀ + u v + s w` turns K2-L's hypotheses into a normal point of order m.
* P5 `ReducedCurveExistsFacts`, P6 `ReducedOrderTwoFacts`: a reduced curve exists; the order-2 identity.
* P7 `TorusPatchFacts`: local bounds at every point give the lattice bound.
* P9 `ParamIntegralSmoothFacts`: parametric integrals over `[0, 1]` preserve smoothness.
* P10a `MonomialPositivityFacts`, P10b `MonomialTailFacts`: K2-MA's two halves.
* P11 `ProductNormalFormFacts`, P12 `SquareNormalFormFacts`: exact product normal forms at a witness.
* P13 `FourierDecayFacts`: summable coefficients of a cutoff times `e^{iδ·k}`, uniformly in δ.
* P14 `TorusExpansionFacts`: the Fourier expansion of `χ e^{iδ·k}` integrated against any continuous g (route
  referee R, finding M2).
-/

namespace OscInt.Blueprint.K2

open Set MeasureTheory OscInt.Statements OscInt.Blueprint
open scoped ContDiff

/-- Order-m core hypotheses: `CoreHyps` with a smooth phase, a smooth critical curve, and the lower bound ν on the
m-th derivative of the reduced phase. -/
def CoreHypsM (m : ℕ) (a b μ ν D : ℝ) (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ Q ∧ ContDiffOn ℝ ∞ ys (Ioo (-2 * a) (2 * a)) ∧
    (∀ x ∈ Icc (-a) a, ys x ∈ Ioo (-b) b ∧ fderiv ℝ Q (x, ys x) (0, 1) = 0) ∧
    (∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-2 * b) (2 * b), μ ≤ |dd Q (x, y) (0, 1) (0, 1)|) ∧
    (∀ i ≤ 4, ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-2 * b) (2 * b), ‖iteratedFDeriv ℝ i Q (x, y)‖ ≤ D) ∧
    ∀ x ∈ Icc (-a) a, ν ≤ |iteratedDeriv m (fun x => Q (x, ys x)) x|

/-- **P1** Order-m core estimate with an outer linear term. -/
def CoreEstimateMFacts : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (a b μ ν D : ℝ), 0 < a → 0 < b → 0 < μ → 0 < ν →
    ∃ C : ℝ, ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M t p : ℝ),
      CoreHypsM m a b μ ν D Q ys → AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (Q k + p * k.1)) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ)))

/-- A normal point of order m at the origin, with a curve of transverse critical points. -/
def NormalPointM (m : ℕ) (F : ℝ × ℝ → ℝ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ fderiv ℝ F 0 (0, 1) = 0 ∧ dd F 0 (0, 1) (0, 1) ≠ 0 ∧ 0 < ε ∧ ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
    (∀ u : ℝ, |u| < ε → fderiv ℝ F (u, h u) (0, 1) = 0) ∧ iteratedDeriv m (fun u => F (u, h u)) 0 ≠ 0

/-- **P2** Normalized data of order m, uniformly over transverse velocities `|q| ≤ q₀`. -/
def NormalizedDataMFacts : Prop :=
  ∀ (m : ℕ) (F : ℝ × ℝ → ℝ) (ε : ℝ) (h : ℝ → ℝ), 2 ≤ m → NormalPointM m F ε h →
    ∃ q₀ > 0, ∃ a b μ ν D : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : ℝ → ℝ → ℝ, ∀ q : ℝ, |q| ≤ q₀ → CoreHypsM m a b μ ν D (fun k => F k + q * k.2) (ys q)

/-- **P3** The chart: K2-L's hypotheses give a normal point of order m for the phase minus its tangent plane in the
coordinates `(u, s) ↦ k₀ + u v + s w`. -/
def ChartFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ) (m : ℕ), ContDiff ℝ ∞ Ψ → 1 ≤ m →
    v.1 * w.2 - v.2 * w.1 ≠ 0 → iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 → 0 < ε → ReducedCurve Ψ k₀ v w ε h →
      iteratedDeriv m (reducedFn Ψ k₀ v w h) 0 ≠ 0 →
      ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), (∀ k, L k = k.1 • v + k.2 • w) ∧
        NormalPointM m (fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k)) ε h

/-- **P5** A reduced curve exists when `D²Ψ(k₀)[w, w] ≠ 0`. -/
def ReducedCurveExistsFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ), ContDiff ℝ ∞ Ψ → iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 →
    ∃ ε > 0, ∃ h : ℝ → ℝ, ReducedCurve Ψ k₀ v w ε h

/-- **P6** Order 2: `g″(0) = D²Ψ[v, v] − D²Ψ[v, w]² / D²Ψ[w, w]` along any reduced curve. -/
def ReducedOrderTwoFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ), ContDiff ℝ ∞ Ψ →
    iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 → 0 < ε → ReducedCurve Ψ k₀ v w ε h →
      iteratedDeriv 2 (reducedFn Ψ k₀ v w h) 0 =
        iteratedFDeriv ℝ 2 Ψ k₀ ![v, v] - iteratedFDeriv ℝ 2 Ψ k₀ ![v, w] ^ 2 / iteratedFDeriv ℝ 2 Ψ k₀ ![w, w]

/-- **P7** Torus patching: local bounds uniform in the linear term at every point of a smooth biperiodic phase give
the bound for every lattice coefficient. -/
def TorusPatchFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (β : ℝ), ContDiff ℝ ∞ Ψ → 0 ≤ β →
    (∀ k : ℝ × ℝ, Ψ (k.1 + 2 * Real.pi, k.2) = Ψ k) → (∀ k : ℝ × ℝ, Ψ (k.1, k.2 + 2 * Real.pi) = Ψ k) →
    (∀ k₀ : ℝ × ℝ, ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
        AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t → ‖oscInt2 (fun κ => t * Ψ κ + lin y κ) A‖ ≤ C * M * t ^ (-β)) →
    ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t →
      ‖∫ k in torusBox, Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤ C * t ^ (-β)

/-- **P9** Parametric integrals over `[0, 1]` preserve smoothness. -/
def ParamIntegralSmoothFacts : Prop :=
  ∀ (n : ℕ∞) (f : (ℝ × ℝ) × ℝ → ℝ), ContDiff ℝ n f → ContDiff ℝ n (fun x : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, f (x, τ))

/-- **P10a** L1: the improper integral exists as a symmetric limit and has real part at least `1/(12m)`. -/
def MonomialPositivityFacts : Prop :=
  ∀ (m : ℕ) (σ : ℝ), 2 ≤ m → (σ = 1 ∨ σ = -1) →
    ∃ C : ℂ, 1 / (12 * (m : ℝ)) ≤ C.re ∧
      Filter.Tendsto (fun R : ℝ => ∫ x in -R..R, Complex.exp (↑(σ * x ^ m) * Complex.I)) Filter.atTop (nhds C)

/-- **P10b** L2: a plateau cutoff integral differs from the symmetric partial integrals' limit by the tail bound. -/
def MonomialTailFacts : Prop :=
  ∀ (m : ℕ) (σ : ℝ) (C : ℂ) (b : ℝ → ℝ) (r t : ℝ), 2 ≤ m → (σ = 1 ∨ σ = -1) →
    Filter.Tendsto (fun R : ℝ => ∫ x in -R..R, Complex.exp (↑(σ * x ^ m) * Complex.I)) Filter.atTop (nhds C) →
    PlateauCutoff b r → 0 < t →
      ‖(∫ x : ℝ, (b x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)) -
          ((t ^ (-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) * C‖ ≤ 4 / ((m : ℝ) * t * r ^ (m - 1))

/-- **P11** Exact product normal form at a point of reduced order exactly m (lower jets zero), for a smooth phase:
for every `δ > 0` there are a smooth cutoff χ supported in `closedBall k₀ δ`, a constant c, signs σ ε, smooth plateau
cutoffs `(b₁, r₁)`, `(b₂, r₂)` and `J > 0` with
`∫ χ e^{it(Ψ − DΨ(k₀)·)} = J⁻¹ e^{itc} (∫ b₁ e^{itσz^m} dz) (∫ b₂ e^{itεw²} dw)` for every real t. -/
def ProductNormalFormFacts : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε₀ : ℝ) (h : ℝ → ℝ) (m : ℕ) (δ : ℝ), ContDiff ℝ ∞ Ψ → 2 ≤ m →
    v.1 * w.2 - v.2 * w.1 ≠ 0 → iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 → 0 < ε₀ → ReducedCurve Ψ k₀ v w ε₀ h →
    (∀ j ∈ Finset.Icc 1 (m - 1), iteratedDeriv j (reducedFn Ψ k₀ v w h) 0 = 0) →
    iteratedDeriv m (reducedFn Ψ k₀ v w h) 0 ≠ 0 → 0 < δ →
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Metric.closedBall k₀ δ ∧
      ∃ (c σ ε J r₁ r₂ : ℝ) (b₁ b₂ : ℝ → ℝ), (σ = 1 ∨ σ = -1) ∧ (ε = 1 ∨ ε = -1) ∧ 0 < J ∧
        PlateauCutoff b₁ r₁ ∧ PlateauCutoff b₂ r₂ ∧ ContDiff ℝ ∞ b₁ ∧ ContDiff ℝ ∞ b₂ ∧
        ∀ t : ℝ, ∫ k, (χ k : ℂ) * Complex.exp (↑(t * (Ψ k - fderiv ℝ Ψ k₀ k)) * Complex.I) =
          (J⁻¹ : ℂ) * Complex.exp (↑(t * c) * Complex.I) *
            (∫ z : ℝ, (b₁ z : ℂ) * Complex.exp (↑(t * σ * z ^ m) * Complex.I)) *
            (∫ y : ℝ, (b₂ y : ℂ) * Complex.exp (↑(t * ε * y ^ 2) * Complex.I))

/-- **P12** The square case: at `(π/2, π/2)`, for every `δ > 0`, a smooth cutoff makes the localised integral of
`triPhase 0` an exact product of two cubic monomial integrals. -/
def SquareNormalFormFacts : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Metric.closedBall (Real.pi / 2, Real.pi / 2) δ ∧
      ∃ (c r : ℝ) (b : ℝ → ℝ), PlateauCutoff b r ∧ ContDiff ℝ ∞ b ∧
        ∀ t : ℝ, ∫ k, (χ k : ℂ) * Complex.exp (↑(t * (triPhase 0 k + k.1 + k.2)) * Complex.I) =
          Complex.exp (↑(t * c) * Complex.I) * (∫ z : ℝ, (b z : ℂ) * Complex.exp (↑(t * z ^ 3) * Complex.I)) ^ 2

/-- **P13** Fourier decay: a smooth χ supported inside `(−π, π)²`, times `e^{iδ·k}`, has coefficients
`c_j(δ) = ∫_{[−π,π]²} χ e^{iδ·k} e^{−ij·k}` with `Σ_j |c_j(δ)|` bounded uniformly for `δ ∈ [0, 1]²`. -/
def FourierDecayFacts : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ χ → tsupport χ ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi →
    ∃ S : ℝ, ∀ δ : ℝ × ℝ, δ ∈ Set.Icc (0 : ℝ × ℝ) 1 →
      Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖) ∧
        ∑' j : ℤ × ℤ, ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖ ≤ S

/-- **P14** Torus expansion: for a smooth χ supported inside `(−π, π)²` whose coefficients `c_j(δ)` are summable,
`∫_{box} χ e^{iδ·k} g = Σ_j (4π²)⁻¹ c_j(δ) ∫_{box} e^{ij·k} g` for every continuous g. -/
def TorusExpansionFacts : Prop :=
  ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ χ → tsupport χ ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi →
    ∀ δ : ℝ × ℝ,
      Summable (fun j : ℤ × ℤ => ‖∫ k in torusBox, χ k *
          Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)‖) →
      ∀ g : ℝ × ℝ → ℂ, Continuous g →
        HasSum (fun j : ℤ × ℤ => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) *
            (∫ k in torusBox, χ k * Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I)) *
            ∫ k in torusBox, Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k)
          (∫ k in torusBox, χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) * g k)

end OscInt.Blueprint.K2
