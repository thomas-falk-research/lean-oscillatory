# Briefs for the S2/S3 analytic agents (wave 1)

## Common rules
As in `review/prompts/S2S3-briefs-infra.md` (which refers to `review/prompts/S1-briefs.md`). Read first:
`docs/proof-S2S3.md` including its final "Revision after the route referee" section (it overrides the text above
it), `OscInt/Statements/StationaryPhase.lean`, `Blueprint/StationaryPhase.lean`. Your file lives under
`OscInt/StationaryPhase/`; helpers are public in `namespace OscInt.StationaryPhase.<Part>Aux`. Use `ContDiff ℝ ∞`
or a numeral for smoothness, never `ContDiff ℝ ⊤` (that is analytic in this Mathlib; the guard rejects it).
Available proved results you may import and use:
- S1, one-dimensional van der Corput with amplitude: `OscInt.vanDerCorput_one/_two/_three` (types
  `OscInt.Statements.VdC{1,2,3}Statement`, in `OscInt/VanDerCorput/Final.lean`), and the parts in
  `OscInt/VanDerCorput/` (e.g. `OscInt.VanDerCorput.amplitudeTransfer`, `vdc2Plain`).
- Infrastructure (`OscInt/StationaryPhase/Family.lean`, `Change.lean`, `Partition.lean`): `familyAddLinear`,
  `familyAffine`, `ampBoundAffine`, `affineChange`, `ampBoundMul`, `partition` and their `Aux` lemmas.
Long proofs are expected (hundreds of lines). Split into many lemmas ≤ ~60 lines each. If an interface is false,
stop and report with a counterexample (rule 3): two blueprint errors have already been caught this way.

## Task H1: `OscInt/StationaryPhase/Core.lean`
`theorem OscInt.StationaryPhase.coreEstimate : OscInt.Blueprint.CoreEstimateFacts`.
Route: (L5) and (L6) of `docs/proof-S2S3.md`, revision items 4 and 5. Outline in Lean terms:
1. From `CoreHyps`: `∂²_yQ` has constant sign on the box (IVT/connectedness from `μ ≤ |…|` and continuity).
   Define `h(x, y) = ∫₀¹ ∂²_yQ(x, ys x + s(y − ys x)) ds` and `K(x, y) = ∫₀¹ ∂_y∂_xQ(x, ys x + s(y − ys x)) ds`;
   prove `∂_yQ(x, y) = (y − ys x) h(x, y)` and `∂_xQ(x, y) − ∂_xQ(x, ys x) = (y − ys x) K(x, y)` (FTC along the
   segment), `|h| ≥ μ`, and bounds on `h, K` and their first two `y`-derivatives in terms of `D` (differentiation
   under the integral sign in `s`, or an explicit formula; only `y`-regularity in `y` is needed).
2. Fubini on the rectangle: `oscInt2 (m Q) A = ∫ x in -a..a, ∫ y in -2b..2b, …` (`MeasureTheory.integral_prod`,
   `intervalIntegral`, support of `A`).
3. (L6a) the `(y − ys)E` term by one integration by parts in `y` per `x` (1D `intervalIntegral.integral_mul_deriv_eq_deriv_mul`).
4. (L6b) `J(x) = ∫ y in -2b..2b, e^{im(Q(x,y) − g(x))} θ(y)`: `|J| ≤ C m^{-1/2}` and `|J'| ≤ C m^{-1/2}` by
   `vanDerCorput_two` in `y`; `J` differentiable in `x` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
5. `vanDerCorput_two` (j = 2) or `vanDerCorput_three` (j = 3) in `x` with phase `m g` and amplitude `b J`.
6. Combine: `C M (m^{-1} + m^{-1/2-1/j}) ≤ C' M m^{-(1/2+1/j)}` for `m ≥ 1`.
θ: a fixed smooth cutoff with `θ = 1` on `[-b, b]`, `tsupport θ ⊆ (-2b, 2b)` (e.g. from `ContDiffBump` on ℝ).
This is the largest part. Prove j = 2 and j = 3 with one shared development (only step 5 differs).

## Task H2: `OscInt/StationaryPhase/Implicit.lean`
`theorem OscInt.StationaryPhase.normalizedData : OscInt.Blueprint.NormalizedDataFacts`.
Route: (L3), (L4) with revision items 1 and 3 (tube lemma; contraction constants). Outline:
1. Tube lemma for the jointly continuous `(τ, k) ↦ iteratedFDeriv ℝ i (Q τ) k` on compact boxes (Mathlib:
   `IsCompact.eventually_forall_of_forall_eventually` or `generalized_tube_lemma`).
2. Implicit critical point by the contraction `y ↦ y − ∂_yQ_τ(x, y)/q₀` on `[-b, b]` with constant 1/2, for
   `(τ, x) ∈ U × [-2a, 2a]` (`ContractingWith.fixedPoint` on the complete metric space `Icc (-b) b`;
   continuity in `(τ, x)` from `ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le`/`fixedPoint_lipschitz_in_map`).
   Define `ys τ x` as this fixed point (any value outside).
3. Differentiability in `x` at fixed τ: classical IFT at each point (`ImplicitFunctionData`,
   `implicitFunctionOfBivariate`, or directly: `HasStrictFDerivAt` + uniqueness), derivative
   `−∂_x∂_yQ/∂²_yQ` at `(x, ys x)`; bootstrap to `C³` on `(-2a, 2a)` (the right side is `C²` in `(x, y)` and
   `ys` is `C¹`, …).
4. Bounds: `D` from sups (tube lemma) of `‖iteratedFDeriv ℝ i (Q τ)‖` on the box and of the explicit formulas
   for `ys′, ys″`; `ν` from continuity of `g_τ^{(j)}(x)` at `(τ₀, 0)` (value `∂²_xQ(0)` for j = 2,
   `∂³_xQ(0)` for j = 3, using `ys′(τ₀, 0) = 0` from `∂_x∂_yQ(0) = 0`); shrink `a` last.
Note `NormalPoint` gives `ys τ₀ 0 = 0` by uniqueness. Joint continuity of `(τ, x) ↦ ys′, ys″, ys‴` follows from
the formulas and joint continuity of the derivatives of `Q`.

## Task H3: `OscInt/StationaryPhase/NonStat.lean`
`theorem OscInt.StationaryPhase.familyCalculus : OscInt.Blueprint.FamilyCalculusFacts` and
`theorem OscInt.StationaryPhase.nonStatCore : OscInt.Blueprint.NonStatCoreFacts`.
Route: (N2) with revision item 6 (c/2 on a neighbourhood `K₁`, Euclidean square). Outline for F3: induction on `n`
using `iteratedFDeriv_succ_eq_comp_right`/`fderiv` of products (`ContDiff.mul`, `norm_iteratedFDeriv_mul_le`
style formulas: `iteratedFDeriv_mul` if present, else `iteratedFDeriv_succ_apply_left` and `fderiv_mul`), and
`D(1/f) = −Df/f²`. Outline for N2: replace `|∇Φ|²` by `G̃ = |∇Φ|² + (1 − χ)·c²/4` with χ a smooth cutoff equal to 1
near `K` and supported in `K₁` (so `G̃ > 0` everywhere and `= |∇Φ|²` near K), `w = ∇Φ/G̃`, the identity
`e^{imΦ} A = (1/(im)) Σ_j ∂_j(e^{imΦ}) w_j A` on `K`, integrate by parts in each coordinate direction
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), induct on `N` with the amplitude `A ↦ i·div(wA)`,
bounds by compactness of `T × K₁` (F3 gives joint continuity of the derivatives of `w`).

## Task H4: `OscInt/StationaryPhase/Local.lean`
`theorem OscInt.StationaryPhase.normalForm : OscInt.Blueprint.NormalFormFacts` and
`theorem OscInt.StationaryPhase.localNonCrit : OscInt.Blueprint.LocalNonCritFacts`.
Route: (L2) with revision item 2, and (L1) with revision item 1. For L2: `dd (Ψ ∘ (k₀ + L·)) 0 v w = dd Ψ k₀ (L v) (L w)`
and the same for `ddd` (chain rule for `C²`/`C³`), symmetry `dd Ψ k v w = dd Ψ k w v` for `C²`
(`second_derivative_symmetric_of_eventually` / `ContDiffAt.isSymmSndFDerivAt`); choose `w` with
`H(w, w) ≠ 0` (polarisation), `v ≠ 0` with `H(v, w) = 0`, `L = (v, w)` as columns (`LinearEquiv` from a basis or
`ContinuousLinearEquiv.ofEq`/`Matrix.toLin` with nonzero determinant). For L1: pick a coordinate direction `e`
with `∂_eQ_{τ₀}(k₀) ≠ 0`, tube lemma on `closedBall k₀ (2δ)`, one integration by parts in direction `e`
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` with `v = e`).
