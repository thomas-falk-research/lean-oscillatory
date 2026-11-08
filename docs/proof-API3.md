# Proof route: front-end batch 3 (API3)

Statements: `OscInt/Statements/Family.lean`, stamped `stamps/20261108T002603Z-9d03130c8f3a` (RFC 3161 ×3 at
2026-11-08T00:26:05Z). Disclosure (lessons 29): this route was drafted in the lead's scratch while the two blind
pre-proof reviews ran (after the stamp); it contains no Lean proof code. No Lean proof of an API3 statement was
written before both reviews were committed and stamped.

All parts live in `OscInt/Front/` (lessons 30: no module except the root has submodules), namespace
`OscInt.API` for final theorems and `OscInt.API.FamilyAux` for helpers.

## R1 S2.2F, S3c (lead): re-assembly of proved parts
The proofs of S2.2 and S3 (`OscInt/StationaryPhase/Assembly.lean`, `stationaryPhase_of`, `fold_of`) localise over the
compact parameter space `T = Λ × K'` (`compactSpace_prod_subtype`), with `Q (σ, p) = Ψ σ + lin p` (`FamilyCk 4` by
`familyAddLinear`). At `(τ, k)`, `k ∈ K`: if `k` is not critical for `Q τ`, `localNonCrit` gives a local bound of rate
1 (hence 5/6, `LocalBound.of_one`); if it is critical, `localCrit_of normalForm normalizedData coreEstimate` gives
rate 1 when `hessDet (Q τ) k ≠ 0` and rate 5/6 when `FoldOrNondeg (Q τ) k`. The hypothesis is used only at critical
points; `isCritical_add_lin`, `hessDet_add_lin`, `foldOrNondeg_add_lin` move between `Q τ` with `p = 0` and `Ψ σ` with
`p`. S2.2F: copy `stationaryPhase_of` with `Λ` in place of `Unit`. S3c: `fold_of` with the hypothesis applied under
`hcr`. Rate bookkeeping as in the originals (`Real.rpow_neg_one`; `-(5:ℝ)/6 = -(5/6)`).

## P1 C10 (agent): joint smoothness gives `FamilyCk`
For `σ ∈ S`, `Ψ σ = (uncurry Ψ) ∘ (fun k => (σ, k))`, and `fun k => (σ, k) = (σ, 0) + inr k` with
`inr = ContinuousLinearMap.inr ℝ E (ℝ × ℝ)`. Hence (`iteratedFDeriv_comp_add_left`,
`ContinuousLinearMap.iteratedFDeriv_comp_right`) `iteratedFDeriv ℝ j (Ψ σ) k =
(iteratedFDeriv ℝ j (uncurry Ψ) (σ, k)).compContinuousLinearMap (fun _ => inr)` for `j ≤ n`. The right side is
continuous in `(σ, k)`: `ContDiff.continuous_iteratedFDeriv` composed with the continuous linear map
`ContinuousMultilinearMap.compContinuousLinearMapL` (or `compContinuousLinearMapContinuousMultilinear`; `#check` at
the pin). `ContDiff ℝ n (Ψ σ)`: `contDiff.comp` with the affine map.

## P2 cut-off (agent)
(a) `exists_cutoff`: for `K` compact ⊆ `U` open in `ℝ × ℝ` there are `χ` with `ContDiff ℝ ∞ χ`, `tsupport χ ⊆ U`, and an
open `W ⊇ K` with `χ = 1` on `W`. Route: `IsCompact.exists_cthickening_subset_open` gives `δ > 0` with
`cthickening δ K ⊆ U`; `exists_contDiff_support_eq_eq_one_iff` (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean`,
`#check`ed) with `s = thickening (δ/2) K` (open), `t = cthickening (δ/4) K` (closed); `W = thickening (δ/4) K`;
`tsupport χ = closure s ⊆ cthickening (δ/2) K ⊆ U` (the closure lemma is not `closure_thickening_subset_cthickening` at the pin; find and `#check` the namespaced name, e.g. under `Metric.`).
(b) `familyCk_cutoff`: `IsOpen V`, `IsOpen U`, `S ⊆ V`, `ContDiffOn ℝ n (uncurry Ψ) (V ×ˢ U)`, `χ` as in (a) ⇒
`FamilyCk n (fun σ : S => fun k => χ k * Ψ σ k)`. At `(σ, k)` with `k ∈ U`: `(σ', k') ↦ χ k' * Ψ σ' k'` is `ContDiffAt`
at `(σ, k)` (open product), and the P1 identity holds on a neighbourhood (a local version of P1, via
`ContDiffAt.iteratedFDeriv` / restricting to a ball). At `k ∉ U`: `k ∉ tsupport χ`, so the function vanishes on a
product neighbourhood `univ ×ˢ (tsupport χ)ᶜ`, and every `iteratedFDeriv` vanishes there.
(c) `eq_near`: for `k ∈ K`, `(fun k => χ k * Ψ σ k) =ᶠ[𝓝 k] Ψ σ`; then `fderiv`, `hessianMatrix`, `iteratedFDeriv ℝ 3`
agree at `k` (`Filter.EventuallyEq.fderiv_eq`, `Filter.EventuallyEq.iteratedFDeriv`), and the integrands agree on
`tsupport A ⊆ K` (outside, `A = 0`).

## P3 bridges (lead or agent)
- FE-S2.1L: `S` as a compact space; `nonStationary` (S2.1) for the family of P2(b) with `c/√2`; gradient via
  `gradLower_iff` (C8 iii) and P2(c); integrals via `integral_eq_oscInt2` and P2(c).
- FE-S2.2L, FE-S3L: R1 for the family of P2(b) with `K'` replaced by `vecOf '' K'` (compact, `continuous_vecOf`);
  critical points via `isCritical_iff` and P2(c); `hessDet_eq_det` (C3) and `foldOrNondeg_iff` (C7) at `k ∈ K` need
  `ContDiffAt` of the cut-off phase, from P2(b).
- FE-S4.1′L: `exists_cutoff` with `K = {0}`; `W` contains a ball `B(0, r)`; `d4BoundFE` for `χ φ`; its derivative
  hypotheses at `0` by P2(c); `δ' = min δ (r/2)`.
- FE-S2.1l, FE-S2.2l, FE-S3l: the L forms with `E = ℝ`, `S = {0}`, `V = univ`, `Ψ _ = φ`
  (`ContDiffOn` of `φ ∘ Prod.snd` on `univ ×ˢ U`).

## Numerical check of interfaces
None needed: every step is a re-assembly or a germ argument with no new estimate.
