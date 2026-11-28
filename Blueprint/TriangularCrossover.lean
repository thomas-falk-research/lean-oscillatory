/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Statements.TriangularCrossover

/-!
# Blueprint for batch A5U: the parts of the route (definitions only)

Route: `docs/proof-A5U.md` (sections 1–5); the analytic content is the external packet's X1–X5 (its crossover work
package, `review/2026-11-28-postK2-packet-answers.md`) with the fixed chart of the route.
Propositions only. Each part is proved as `theorem OscInt.A5UAux.<lowerCamel name> : OscInt.Blueprint.A5U.<Prop>`.
A conditional part `X → Y → Z` is proved with `X`, `Y` as hypotheses; where a later part needs the conclusion of a
conditional part, that conclusion has its own name `…Bound` (so the later part does not need the earlier part's
hypotheses).

Notation. `a* = 1/(2√2)`, `a₀ = ±a*`, `θ₀ = arccos(−2a₀)` (`a5Theta`), `k* = (θ₀, −θ₀)` (`a5Centre`),
`L(u, s) = u (1, 1) + s (1, −1)` (`a5L`), `F_α = triPhase α (k* + L ·) − triPhase α k* − DtriPhase α (k*) (L ·)`
(`a5F`), `Q_{α,q} = F_α + q s` (`a5Q`), `g_{α,q}(u) = Q_{α,q}(u, ys u)` (`a5Red`), `ε = |α − a₀|`,
`W = t^{−2/3} crossEnvelope(ε t^{1/3})` (`crossWeight`).

Parts (generic = no lattice; they can be proved first).
* A1 `LevelCrossingFacts` (generic): Rolle count, `D n ≠ 0` on `(a, b)` ⇒ `D 0 = c` at most `n` times on `[a, b]`.
* A2 `AmpNormRestrictFacts` (generic): the amplitude hypothesis and `ampNorm` restrict to subintervals.
* A3 `PiecewiseVdCFacts` (generic, from A1, A2): piecewise van der Corput with three thresholds, 19 pieces.
* A4 `CoreEstimateMultiFacts` (generic, from A3's bound): the core estimate of `coreEstimateM` with A3 in place of
  one order.
* A5 `EvenJetTaylorFacts` (generic): Taylor bounds of `g″, g‴, g⁗` for an even function with `|g⁽⁸⁾| ≤ L`.
* A6 `JetSeparationFacts` (generic algebra): the packet's X2 contradiction.
* A7 `CrossEnvelopeFacts` (generic algebra): the three envelope inequalities.
* A8 `A5FixedChartFacts`: closed form of `F_α` in the fixed chart.
* A9 `A5BaseDataFacts` (from A8): `CoreHypsM 6` data at `a₀` uniformly in the tilt, evenness, jet bounds.
* A10 `PerturbLongitudinalFacts` (generic): adding `e (cos 2u − 1)` keeps `CoreHypsM`.
* A11 `A5TiltJetFacts` (from A8): `g″(0) = 4(α* − α)`, `g⁗(0) = 24α* − 3/α* − 4g″(0)` (the route's sketch
  went via TRI-Q at `α*`; the proof computes the jets directly).
* A12a `A5CoreWindowFacts` (from A4's bound, A5, A6, A7, A8, A9's bound, A10, A11's bound): the window estimate in
  the chart, near tilt.
* A12 `A5WindowLocalFacts` (from A8, A12a's bound): the local bound at `k*` uniform in `α` (chart + far tilt).
* A13 `LocalTransferFacts` (generic): a local bound moves along `κ ↦ σκ + c` when the phase is invariant.
* B1 `ReducedOrderBoundParamFacts` (generic): K2-L uniformly over a parameter near `α₀`.
* B2 `ComplementLocalFacts` (from B1): `t^{−3/4}` near every non-A5 point of `triPhase a₀`, uniformly in `α`.
* B3 `TorusPatchParamFacts` (generic): family torus patch with a weight `W α t`.

Assembly (the lead's): `OscInt.A5UAux.triCrossoverUpper_of` in `TriangularCrossoverAssembly.lean`.
-/

namespace OscInt.Blueprint.A5U

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2
open scoped ContDiff

/-! ## Definitions -/

/-- `θ₀ = arccos(−2a₀)`. -/
noncomputable def a5Theta (a₀ : ℝ) : ℝ := Real.arccos (-2 * a₀)

/-- The A5 point `k* = (θ₀, −θ₀)` of `triPhase a₀` (for `|a₀| = a*`). -/
noncomputable def a5Centre (a₀ : ℝ) : ℝ × ℝ := (a5Theta a₀, -a5Theta a₀)

/-- The fixed chart `L(u, s) = u (1, 1) + s (1, −1)`. -/
def a5L (k : ℝ × ℝ) : ℝ × ℝ := k.1 • ((1 : ℝ), (1 : ℝ)) + k.2 • ((1 : ℝ), (-1 : ℝ))

/-- `F_α(u, s)`: `triPhase α` in the chart at `k*` (of `a₀`) with its tangent plane at `k*` removed. -/
noncomputable def a5F (a₀ α : ℝ) (k : ℝ × ℝ) : ℝ :=
  triPhase α (a5Centre a₀ + a5L k) - triPhase α (a5Centre a₀) - fderiv ℝ (triPhase α) (a5Centre a₀) (a5L k)

/-- `Q_{α,q}(u, s) = F_α(u, s) + q s`: the chart phase with transverse tilt `q`. -/
noncomputable def a5Q (a₀ α q : ℝ) (k : ℝ × ℝ) : ℝ := a5F a₀ α k + q * k.2

/-- The reduced function `g(u) = Q_{α,q}(u, ys u)` along a curve `ys`. -/
noncomputable def a5Red (a₀ α q : ℝ) (ys : ℝ → ℝ) (x : ℝ) : ℝ := a5Q a₀ α q (x, ys x)

/-- The moving coupling `α* = −cos(θ₀ + y)/2`: `k* + y (1, −1)` is TRI-Q's point `(θ_{α*}, −θ_{α*})`. -/
noncomputable def a5Moving (a₀ y : ℝ) : ℝ := -Real.cos (a5Theta a₀ + y) / 2

/-- The target weight `t^{−2/3} E(|α − a₀| t^{1/3})`. -/
noncomputable def crossWeight (a₀ α t : ℝ) : ℝ :=
  t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3))

/-! ## Stage A, generic parts -/

/-- **A1** (route §4, Rolle) Level crossings: if `D 0, …, D n` is a derivative chain on `[a, b]`, `n ≥ 1`, and
`D n ≠ 0` on `(a, b)`, then `D 0` takes any value `c` at most `n` times on `[a, b]`. -/
def LevelCrossingFacts : Prop :=
  ∀ (D : ℕ → ℝ → ℝ) (n : ℕ) (a b c : ℝ) (S : Finset ℝ), 1 ≤ n → DerivChain D n a b →
    (∀ x ∈ Ioo a b, D n x ≠ 0) → (∀ x ∈ S, x ∈ Icc a b ∧ D 0 x = c) → S.card ≤ n

/-- **A2** (route §4, X4 addendum) Restriction of the amplitude: on `[l, r] ⊆ [a, b]` the amplitude hypothesis
holds and `ampNorm` on `[l, r]` is at most `ampNorm` on `[a, b]` (endpoint value by the fundamental theorem). -/
def AmpNormRestrictFacts : Prop :=
  ∀ (ψ ψ' : ℝ → ℂ) (a b l r : ℝ), a ≤ l → l ≤ r → r ≤ b → AmplitudeOn ψ ψ' a b →
    AmplitudeOn ψ ψ' l r ∧ ampNorm ψ ψ' l r ≤ ampNorm ψ ψ' a b

/-- The conclusion of A3: piecewise van der Corput. If `D 6 ≠ 0` on `(a, b)` and at every point of `(a, b)` one of
`|D 2| > l₂`, `|D 3| > l₃`, `|D 4| > l₄` holds, the integral is at most
`19 (8 l₂^{−1/2} + 18 l₃^{−1/3} + 38 l₄^{−1/4}) ampNorm`, uniformly in the linear term. -/
def PiecewiseVdCBound : Prop :=
  ∀ (D : ℕ → ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b p l₂ l₃ l₄ : ℝ), a ≤ b → 0 < l₂ → 0 < l₃ → 0 < l₄ →
    DerivChain D 6 a b → (∀ x ∈ Ioo a b, D 6 x ≠ 0) →
    (∀ x ∈ Ioo a b, l₂ < |D 2 x| ∨ l₃ < |D 3 x| ∨ l₄ < |D 4 x|) → AmplitudeOn ψ ψ' a b →
    ‖oscInt (fun x => D 0 x + p * x) ψ a b‖ ≤
      19 * (8 * l₂ ^ (-(1 : ℝ) / 2) + 18 * l₃ ^ (-(1 : ℝ) / 3) + 38 * l₄ ^ (-(1 : ℝ) / 4)) * ampNorm ψ ψ' a b

/-- **A3** (route §4, packet X3) Piecewise van der Corput, from A1 and A2: the levels `D j = ±l_j` (`j = 2, 3, 4`)
cut `[a, b]` at most `2(4 + 3 + 2) = 18` times (A1 with `n = 6 − j`); on each of the at most 19 pieces one
alternative holds throughout (intermediate values), and `OscInt.API.vdCk` of that order applies with the restricted
amplitude (A2). -/
def PiecewiseVdCFacts : Prop := LevelCrossingFacts → AmpNormRestrictFacts → PiecewiseVdCBound

/-- The conclusion of A4: the order-6 core data of `CoreHypsM` together with the pointwise three-threshold
alternative for the reduced function give `P M t^{−1/2} (8 (t l₂)^{−1/2} + 18 (t l₃)^{−1/3} + 38 (t l₄)^{−1/4})`,
with `P` depending only on `(a, b, μ, D)` (not on `ν`, the thresholds, the linear term or the amplitude). -/
def CoreEstimateMultiBound : Prop :=
  ∀ (a b μ D : ℝ), 0 < a → 0 < b → 0 < μ →
    ∃ P : ℝ, ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M t p ν l₂ l₃ l₄ : ℝ),
      0 < ν → 0 < l₂ → 0 < l₃ → 0 < l₄ → CoreHypsM 6 a b μ ν D Q ys →
      (∀ x ∈ Ioo (-a) a, l₂ < |iteratedDeriv 2 (fun x => Q (x, ys x)) x| ∨
        l₃ < |iteratedDeriv 3 (fun x => Q (x, ys x)) x| ∨ l₄ < |iteratedDeriv 4 (fun x => Q (x, ys x)) x|) →
      AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (Q k + p * k.1)) A‖ ≤
          P * M * t ^ (-(1 : ℝ) / 2) *
            (8 * (t * l₂) ^ (-(1 : ℝ) / 2) + 18 * (t * l₃) ^ (-(1 : ℝ) / 3) + 38 * (t * l₄) ^ (-(1 : ℝ) / 4))

/-- **A4** (route §4, packet X4) The multi-order core estimate, from A3's bound: a clone of
`OscInt.K2.coreEstimateM` (`phase_facts`, `amplitude_facts`, `oscInt2_eq_outer_linear`, the chain `t g^{(j)}`) with
`PiecewiseVdCBound` (thresholds `t l_j`) in place of `vdCk`; `P = 19 · 8 (1 + 4b)(1 + 2a(1 + 24 β(D, μ)⁶))/√μ`. -/
def CoreEstimateMultiFacts : Prop := PiecewiseVdCBound → CoreEstimateMultiBound

/-- **A5** (route §3) Even-jet Taylor bounds: for `g` smooth and even on `(−a, a)` with `|g⁽⁸⁾| ≤ L` there, the odd
jets at `0` vanish and `|g″ − (A + B u²/2 + D u⁴/24)| ≤ L u⁶`, `|g‴ − (B u + D u³/6)| ≤ L |u|⁵`,
`|g⁗ − (B + D u²/2)| ≤ L u⁴` with `A, B, D = g″(0), g⁗(0), g⁽⁶⁾(0)`. -/
def EvenJetTaylorFacts : Prop :=
  ∀ (g : ℝ → ℝ) (a L : ℝ), 0 < a → ContDiffOn ℝ ∞ g (Ioo (-a) a) → (∀ x ∈ Ioo (-a) a, g (-x) = g x) →
    (∀ x ∈ Ioo (-a) a, |iteratedDeriv 8 g x| ≤ L) →
    ∀ u ∈ Ioo (-a) a,
      |iteratedDeriv 2 g u -
          (iteratedDeriv 2 g 0 + iteratedDeriv 4 g 0 * u ^ 2 / 2 + iteratedDeriv 6 g 0 * u ^ 4 / 24)| ≤ L * u ^ 6 ∧
      |iteratedDeriv 3 g u - (iteratedDeriv 4 g 0 * u + iteratedDeriv 6 g 0 * u ^ 3 / 6)| ≤ L * |u| ^ 5 ∧
      |iteratedDeriv 4 g u - (iteratedDeriv 4 g 0 + iteratedDeriv 6 g 0 * u ^ 2 / 2)| ≤ L * u ^ 4

/-- **A6** (route §3, packet X2) Jet separation, as algebra: with `ρ = max(√ε, |A|^{1/4}, |u|)` the scaled Taylor
forms of A5 cannot all be smaller than `η ρ^{6−j}`. Here `η` depends on `(c_B, K, d_min, d_max)` only, and `δ` on
`L` in addition. In the window `c_B = 24`, `K = 10` (A11). -/
def JetSeparationFacts : Prop :=
  ∀ cB K dmin dmax : ℝ, 0 < cB → 0 ≤ K → 0 < dmin → dmin ≤ dmax →
    ∃ η > 0, ∀ L : ℝ, 0 ≤ L → ∃ δ > 0, δ ≤ 1 ∧
      ∀ ε A B D u g₂ g₃ g₄ : ℝ, 0 < ε → ε ≤ δ ^ 2 → |A| ≤ δ ^ 4 → |u| ≤ δ → dmin ≤ |D| → |D| ≤ dmax →
        cB * ε - K * |A| ≤ |B| →
        |g₂ - (A + B * u ^ 2 / 2 + D * u ^ 4 / 24)| ≤ L * u ^ 6 →
        |g₃ - (B * u + D * u ^ 3 / 6)| ≤ L * |u| ^ 5 →
        |g₄ - (B + D * u ^ 2 / 2)| ≤ L * u ^ 4 →
          η * ε ^ 2 < |g₂| ∨ η * (ε * √ε) < |g₃| ∨ η * ε < |g₄|

/-- **A7** (route §4) Envelope algebra: (i) `t^{−3/4} ≤ W` for `ε ≤ 1` (the complement); (ii) `E = 1` when
`t ε³ ≤ 1` (the order-6 branch); (iii) for `t ε³ ≥ 1` the three van der Corput terms of A4 with thresholds
`l₂ = η ε²`, `l₃ = η ε^{3/2}`, `l₄ = η ε`, times `t^{−1/2}`, are at most `C(η) W`. -/
def CrossEnvelopeFacts : Prop :=
  (∀ ε t : ℝ, 0 ≤ ε → ε ≤ 1 → 1 ≤ t →
      t ^ (-(3 : ℝ) / 4) ≤ t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3))) ∧
    (∀ ε t : ℝ, 0 ≤ ε → 0 < t → t * ε ^ 3 ≤ 1 → crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) = 1) ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ ε t : ℝ, 0 < ε → 1 ≤ t → 1 ≤ t * ε ^ 3 →
      t ^ (-(1 : ℝ) / 2) * (8 * (t * (η * ε ^ 2)) ^ (-(1 : ℝ) / 2) +
          18 * (t * (η * (ε * √ε))) ^ (-(1 : ℝ) / 3) + 38 * (t * (η * ε)) ^ (-(1 : ℝ) / 4)) ≤
        C * (t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)))

/-- **A10** (route §5, A10) Longitudinal perturbation: adding `e (cos 2u − 1)` (independent of `s`) to the phase
changes the reduced derivatives of order `j ≥ 1` by at most `2^j |e|` and keeps `CoreHypsM` with `D + 16|e|` and
any `ν'` that bounds the new m-th reduced derivative. -/
def PerturbLongitudinalFacts : Prop :=
  ∀ (m : ℕ) (a b μ ν D e : ℝ) (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ), CoreHypsM m a b μ ν D Q ys →
    (∀ j : ℕ, 1 ≤ j → ∀ x ∈ Ioo (-2 * a) (2 * a),
      |iteratedDeriv j (fun x => Q (x, ys x) + e * (Real.cos (2 * x) - 1)) x -
          iteratedDeriv j (fun x => Q (x, ys x)) x| ≤ 2 ^ j * |e|) ∧
    ∀ ν' : ℝ, (∀ x ∈ Icc (-a) a, ν' ≤ |iteratedDeriv m (fun x => Q (x, ys x) + e * (Real.cos (2 * x) - 1)) x|) →
      CoreHypsM m a b μ ν' (D + 16 * |e|) (fun k => Q k + e * (Real.cos (2 * k.1) - 1)) ys

/-- **A13** (route §5) Transfer of a local bound along `κ ↦ σ κ + c`, `σ = ±1`, when the phase is
invariant: a bound `B M` for amplitudes on `closedBall k₀ δ`, uniform in the linear term, holds on
`closedBall (σ k₀ + c) δ`. Used with `φ = t triPhase α`, `c ∈ 2πℤ²`, for `−k*` and the translates. -/
def LocalTransferFacts : Prop :=
  ∀ (φ : ℝ × ℝ → ℝ) (k₀ c : ℝ × ℝ) (σ δ B : ℝ), (σ = 1 ∨ σ = -1) → (∀ κ, φ (σ • κ + c) = φ κ) →
    (∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M →
      ‖oscInt2 (fun κ => φ κ + lin y κ) A‖ ≤ B * M) →
    ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ), AmpBound 2 (Metric.closedBall (σ • k₀ + c) δ) A M →
      ‖oscInt2 (fun κ => φ κ + lin y κ) A‖ ≤ B * M

/-! ## Stage A, the window at the A5 point -/

/-- **A8** (route §1) The fixed chart: for every `a₀, α`,
`F_α(u, s) = 2 cos(θ₀ + s) cos u − 2 cos θ₀ + α (cos 2u − 1) + 2 s sin θ₀`. In particular `F_α = F_{a₀} +
(α − a₀)(cos 2u − 1)`, `F_α` is even in `u`, and `∂_s F_α` does not depend on `α`. -/
def A5FixedChartFacts : Prop :=
  ∀ (a₀ α : ℝ) (k : ℝ × ℝ),
    a5F a₀ α k = 2 * Real.cos (a5Theta a₀ + k.2) * Real.cos k.1 - 2 * Real.cos (a5Theta a₀) +
      α * (Real.cos (2 * k.1) - 1) + 2 * k.2 * Real.sin (a5Theta a₀)

/-- The conclusion of A9: base data at `a₀`, uniformly in the tilt `|q| ≤ q₀`. One curve family `ys q` with
`CoreHypsM 6` for `Q_{a₀,q}`, `ys q` even on `[−a, a]`, `μ |ys q 0| ≤ |q|`, and `|g⁽⁶⁾|, |g⁽⁸⁾| ≤ L` on
`[−a, a]` for `g = g_{a₀,q}`. -/
def A5BaseDataBound : Prop :=
  ∀ a₀ : ℝ, |a₀| = triExceptional →
    ∃ q₀ > 0, ∃ a b μ ν D L : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : ℝ → ℝ → ℝ, ∀ q : ℝ, |q| ≤ q₀ →
        CoreHypsM 6 a b μ ν D (a5Q a₀ a₀ q) (ys q) ∧ (∀ x ∈ Icc (-a) a, ys q (-x) = ys q x) ∧
          μ * |ys q 0| ≤ |q| ∧
          ∀ x ∈ Icc (-a) a, |iteratedDeriv 6 (a5Red a₀ a₀ q (ys q)) x| ≤ L ∧
            |iteratedDeriv 8 (a5Red a₀ a₀ q (ys q)) x| ≤ L

/-- **A9** (route §1 and §5, packet X1/X4) Base data at `a₀`, from A8: K2's P3 (`chart`), P5, P2
(`normalizedDataM`) and TRI-W give `CoreHypsM 6`; the jet bounds uniform in `q` come from the explicit reduced
derivatives (`NormalizedDataMAux.iteratedDeriv_reduced_eq`, `contDiffOn_Gop`) on a compact set; evenness from the
uniqueness of the transverse critical point (`|∂²_s Q| ≥ μ`) and the evenness of `F_{a₀}` in `u` (A8); the bound on
`ys q 0` from the mean value theorem in `s` at `u = 0`. -/
def A5BaseDataFacts : Prop := A5FixedChartFacts → A5BaseDataBound

/-- The conclusion of A11: along a transverse critical curve `ys` of `Q_{a₀,q}` near `u = 0` with `|ys 0| < π/4`,
for `α* = a5Moving a₀ (ys 0)` and every coupling `α`: `α* a₀ > 0`, `|α* − a₀| ≤ |ys 0|/2`,
`g″(0) = 4(α* − α)`, `g⁗(0) = 24α* − 3/α* − 4 g″(0)` and `|g⁗(0)| ≥ 24|α − a₀| − 10|g″(0)|`, `g = g_{α,q}`. -/
def A5TiltJetBound : Prop :=
  ∀ a₀ : ℝ, |a₀| = triExceptional → ∀ (q a : ℝ) (ys : ℝ → ℝ), 0 < a → ContDiffOn ℝ ∞ ys (Ioo (-2 * a) (2 * a)) →
    (∀ x ∈ Icc (-a) a, fderiv ℝ (a5Q a₀ a₀ q) (x, ys x) (0, 1) = 0) → |ys 0| < Real.pi / 4 →
    0 < a5Moving a₀ (ys 0) * a₀ ∧ |a5Moving a₀ (ys 0) - a₀| ≤ |ys 0| / 2 ∧
      ∀ α : ℝ, iteratedDeriv 2 (a5Red a₀ α q ys) 0 = 4 * (a5Moving a₀ (ys 0) - α) ∧
        iteratedDeriv 4 (a5Red a₀ α q ys) 0 =
          24 * a5Moving a₀ (ys 0) - 3 / a5Moving a₀ (ys 0) - 4 * iteratedDeriv 2 (a5Red a₀ α q ys) 0 ∧
        24 * |α - a₀| - 10 * |iteratedDeriv 2 (a5Red a₀ α q ys) 0| ≤ |iteratedDeriv 4 (a5Red a₀ α q ys) 0|

/-- **A11** (route §2, packet X1) Tilt jets via TRI-Q, from A8: `k* + y (1, −1)` with `y = ys 0` is the point
`(θ_{α*}, −θ_{α*})` of `triPhase α*`; `ys − y` (cut off away from `0`) is a reduced curve there, `g_{α,q}` is its
reduced function plus `(a₀ − α*) cos 2u + (α − a₀)(cos 2u − 1)` up to a constant; K2's P6 (kernel ⇒ `r″(0) = 0`),
`ReducedBridge.bridge` and `OscInt.API.triQuartic` (`r⁗(0) = 12(8α*² − 1)/(4α*)`) give the jets; the inequality is
`|24α* − 3/α*| ≥ 24|α* − a₀|` (`a₀² = 1/8`, `α* a₀ > 0`) and `|α* − α| = |g″(0)|/4`. -/
def A5TiltJetFacts : Prop := A5FixedChartFacts → A5TiltJetBound

/-- The conclusion of A12a: the window estimate in the chart for near tilts, uniformly in `|α − a₀| ≤ r`,
`|q| ≤ q₀`, the longitudinal velocity `p`, `t ≥ 1` and the amplitude. -/
def A5CoreWindowBound : Prop :=
  ∀ a₀ : ℝ, |a₀| = triExceptional →
    ∃ q₀ > 0, ∃ a > 0, ∃ b > 0, ∃ r > 0, ∃ C : ℝ, ∀ α q : ℝ, |α - a₀| ≤ r → |q| ≤ q₀ →
      ∀ (A : ℝ × ℝ → ℂ) (M t p : ℝ), AmpBound 2 (Icc (-a) a ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) A‖ ≤ C * M * crossWeight a₀ α t

/-- **A12a** (route §3–4, packet X2–X4) The core window, from A4's bound, A5, A6, A7, A8, A9's bound, A10 and A11's
bound. Data of A9; `Q_{α,q} = Q_{a₀,q} + (α − a₀)(cos 2u − 1)` (A8) keeps `CoreHypsM 6` with `ν/2` (A10, `r ≤ ν/128`);
`η` from A6 with `c_B = 24`, `K = 10`, `d_min = ν/2`, `d_max = L + 64`, then `δ` with `L + 256`; shrink `a`, `r`,
`q₀` so that `|u| ≤ δ`, `ε ≤ δ²`, `|g″(0)| ≤ 2|q|/μ + 4ε ≤ δ⁴` (A11) and `|ys q 0| < π/4`. If `ε = 0` or
`t ε³ ≤ 1`: `OscInt.K2.coreEstimateM` of order 6 and A7(ii). Otherwise A5 + A6 pointwise, A4 with
`l_j = η ε^{(6−j)/2}`, and A7(iii). -/
def A5CoreWindowFacts : Prop :=
  CoreEstimateMultiBound → EvenJetTaylorFacts → JetSeparationFacts → CrossEnvelopeFacts → A5FixedChartFacts →
    A5BaseDataBound → PerturbLongitudinalFacts → A5TiltJetBound → A5CoreWindowBound

/-- The conclusion of A12: the local bound at `k*`, uniform in `|α − a₀| ≤ r`, the linear term, `t ≥ 1` and the
amplitude. -/
def A5WindowLocalBound : Prop :=
  ∀ a₀ : ℝ, |a₀| = triExceptional → ∃ δ > 0, ∃ r > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ r →
    ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall (a5Centre a₀) δ) A M → 1 ≤ t →
      ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * crossWeight a₀ α t

/-- **A12** (route §4–5, packet X4) The window local bound at `k*`, from A8 and A12a's bound: a clone of
`OscInt.K2.reducedOrderBound_of` with the fixed chart `κ = k* + L k` (`LocalAux.phase_eq_at`, `affineChange`,
`ampBoundAffine`); near tilts `|q| ≤ q₀` by A12a; far tilts by `OscInt.Cusp.transverseNonStat` with a box on which
`|∂_s F_α| ≤ q₀/2` (independent of `α` by A8) and `|∂²_s F_α| ≤ 2`, and `t^{−1} ≤ W` (`ε ≤ 1`). -/
def A5WindowLocalFacts : Prop := A5FixedChartFacts → A5CoreWindowBound → A5WindowLocalBound

/-! ## Stage B, the rest of the torus -/

/-- **B1** (route §5, packet X5) K2-L uniformly in a parameter: for a jointly smooth family `Ψ α` and the
hypotheses of K2-L for `Ψ α₀` at `k₀`, the local bound of order `m` holds with one `δ`, `C` for all
`|α − α₀| ≤ ρ`. (Parametric `ImplicitAux.exists_coreHyps` / P2 over `(α, q)`; the far branch is uniform since
`∂_s` of the chart phase vanishes at `0` for every `α`.) -/
def ReducedOrderBoundParamFacts : Prop :=
  ∀ (Ψ : ℝ → ℝ × ℝ → ℝ) (α₀ : ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ) (m : ℕ),
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ p.1 p.2) → 2 ≤ m → v.1 * w.2 - v.2 * w.1 ≠ 0 →
    iteratedFDeriv ℝ 2 (Ψ α₀) k₀ ![w, w] ≠ 0 → 0 < ε → ReducedCurve (Ψ α₀) k₀ v w ε h →
    iteratedDeriv m (reducedFn (Ψ α₀) k₀ v w h) 0 ≠ 0 →
    ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - α₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * Ψ α κ + lin y κ) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ)))

/-- The conclusion of B2: near every point that is not an A5 point of `triPhase a₀`, `a₀ ≠ 0`, decay `t^{−3/4}`
uniformly in `|α − a₀| ≤ ρ`. -/
def ComplementLocalBound : Prop :=
  ∀ a₀ : ℝ, a₀ ≠ 0 → ∀ k₀ : ℝ × ℝ, ¬ IsA5Point (triPhase a₀) k₀ →
    ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4)

/-- **B2** (route §5, packet X5) The complement, from B1: TRI-K at `a₀` (`OscInt.API.triClassification`) gives a
nondegenerate point, a fold or an A3 point, with orders 2, 3, 4 exactly as in `OscInt.K2.TriDecayUpperAux.local_tri`
(P5, P6, `ReducedBridge.bridge`); B1 for the family `(α, k) ↦ triPhase α k`; `1/2 + 1/m ≥ 3/4`. -/
def ComplementLocalFacts : Prop := ReducedOrderBoundParamFacts → ComplementLocalBound

/-- **B3** (route §5, packet X5) Family torus patch: local bounds `C M W α t` at every point, uniform in
`|α − α₀| ≤ ρ` (ρ depending on the point), give the lattice bound `C W α t` for `|α − α₀| ≤ r`. (The proof of
`OscInt.K2.torusPatch` with one finite subcover, `r = min ρ_i`, and the same partition for every `α`.) -/
def TorusPatchParamFacts : Prop :=
  ∀ (Ψ : ℝ → ℝ × ℝ → ℝ) (W : ℝ → ℝ → ℝ) (α₀ : ℝ), (∀ α, Continuous (Ψ α)) →
    (∀ (α : ℝ) (k : ℝ × ℝ), Ψ α (k.1 + 2 * Real.pi, k.2) = Ψ α k) →
    (∀ (α : ℝ) (k : ℝ × ℝ), Ψ α (k.1, k.2 + 2 * Real.pi) = Ψ α k) →
    (∀ k₀ : ℝ × ℝ, ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - α₀| ≤ ρ →
      ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * Ψ α κ + lin y κ) A‖ ≤ C * M * W α t) →
    ∃ r > 0, ∃ C : ℝ, ∀ α : ℝ, |α - α₀| ≤ r → ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t →
      ‖∫ k in torusBox, Complex.exp (↑(t * Ψ α k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤
        C * W α t

end OscInt.Blueprint.A5U
