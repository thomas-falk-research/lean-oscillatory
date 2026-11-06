# Briefs for the S2/S3 infrastructure agents

## Common rules

Same as `review/prompts/S1-briefs.md` ("Common rules for every proof agent"), with these changes: the statements
file is `OscInt/Statements/StationaryPhase.lean`, the blueprint is `Blueprint/StationaryPhase.lean`, your file is
under `OscInt/StationaryPhase/`, helpers go in `namespace OscInt.StationaryPhase.<Part>Aux` or are `private`
(but note: the axiom audit enumerates only non-private theorems and checks the count against the guard; `private`
theorems are allowed but each one makes the guard count exceed the audit count, so prefer a public name inside
your `Aux` namespace). Upstream-readiness matters for these lemmas: write them as general Mathlib-style lemmas
(state the general fact first, then specialise to the blueprint Prop), with docstrings. Read
`review/prompts/S1-briefs.md` for the common rules first.

Why each proposition is true (checked by the lead):
- F1a: for j = 0 the value, for j = 1 the derivative `DΨ_σ(k) + p·`, for j ≥ 2 `DʲΨ_σ(k)` (the linear term has zero
  higher derivatives); each is jointly continuous in ((σ, p), k).
- F1b: `Dʲ(Ψ_σ ∘ (k₀ + L·))(k) = DʲΨ_σ(k₀ + L k) ∘ (L, …, L)` (`ContinuousLinearMap.iteratedFDeriv_comp_right`),
  continuous in (σ, k) as a composition with a continuous map on multilinear maps.
- F1c: Lebesgue measure on ℝ² is an additive Haar measure; `∫ f(L x) dx = |det L|⁻¹ ∫ f` and translation invariance.
- F1d: `ContinuousLinearMap.norm_iteratedFDeriv_comp_right`; `M ≥ 0` follows from the `j = 0` bound.
- F2a: finite smooth partitions of unity on a finite-dimensional normed space subordinate to an open cover; shrink
  each `U i` to a bounded open set first so supports are compact.
- F2b: Leibniz bound `norm_iteratedFDeriv_mul_le` (or the `smul` version) with the finitely many sups of
  `‖Dᵃχ‖` (continuous with compact support, hence bounded).

## Task G1: `OscInt/StationaryPhase/Family.lean`
Prove `theorem OscInt.StationaryPhase.familyAddLinear : OscInt.Blueprint.FamilyAddLinearFacts`,
`theorem OscInt.StationaryPhase.familyAffine : OscInt.Blueprint.FamilyAffineFacts`,
`theorem OscInt.StationaryPhase.ampBoundAffine : OscInt.Blueprint.AmpBoundAffineFacts`.
Mathlib: `ContDiff.add`, `contDiff_const`, `ContinuousLinearMap.iteratedFDeriv_comp_right`,
`ContinuousLinearMap.norm_iteratedFDeriv_comp_right`, `iteratedFDeriv_add_apply`, `iteratedFDeriv_const_of_ne`,
`ContinuousLinearMap.iteratedFDeriv_comp_left`. For F1a the cleanest route may be to prove
`iteratedFDeriv ℝ j (fun k => Ψ k + lin p k) = iteratedFDeriv ℝ j Ψ + iteratedFDeriv ℝ j (lin p)` and compute the
iterated derivatives of a continuous linear map (zero for j ≥ 2).

## Task G2: `OscInt/StationaryPhase/Change.lean`
Prove `theorem OscInt.StationaryPhase.affineChange : OscInt.Blueprint.AffineChangeFacts` and
`theorem OscInt.StationaryPhase.ampBoundMul : OscInt.Blueprint.AmpBoundMulFacts`.
Mathlib: `MeasureTheory.Measure.integral_comp_add_left` / `integral_add_left_eq_self`,
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`, `MeasureTheory.Measure.integral_comp_linearMap`
or the `LinearEquiv` variants (search: `grep -rn "integral_comp.*inear" .lake/packages/mathlib/Mathlib`),
`norm_iteratedFDeriv_mul_le`, `HasCompactSupport.iteratedFDeriv`, `Continuous.bounded_above_of_compact_support`,
`tsupport_mul_subset_left/right`. Check the names with `#check` before relying on them.

## Task G3: `OscInt/StationaryPhase/Partition.lean`
Prove `theorem OscInt.StationaryPhase.partition : OscInt.Blueprint.PartitionFacts`.
Mathlib: `SmoothPartitionOfUnity.exists_isSubordinate` (manifold version; ℝ × ℝ is a manifold over itself with
`𝓘(ℝ, ℝ × ℝ)`; `contMDiff_iff_contDiff`), or `exists_contDiff_support_eq_eq_one_iff` / `ContDiffBump` with a
finite subcover and normalisation. Shrink `U i` to `U i ∩ ball 0 R` (R large, K ⊆ ball 0 (R − 1)) to get
compact supports. If `r = 0` then `K = ∅` and the statement is trivial.
