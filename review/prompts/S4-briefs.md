# Briefs for the S4.1 proof agents

## Common rules
As in `review/prompts/S1-briefs.md` (hard rules 1–7; replace `Blueprint.VanDerCorput` by `Blueprint.D4`), with:
- Read first: `docs/proof-S4.md`, `Blueprint/D4.lean`, `OscInt/Statements/StationaryPhase.lean`,
  `OscInt/Statements/D4.lean`. Your file lives under `OscInt/D4/`; helpers in `namespace OscInt.D4.<Part>Aux` or
  `private`. The guard (`make guard`, allowed) also forbids `open Lean`, `Lean.`-qualified names, `attribute`,
  `run_tac` and `set_option` except `set_option maxHeartbeats N in`. Write `ContDiff ℝ ∞` (with
  `open scoped ContDiff`) or a numeral, never `ContDiff ℝ ⊤` (analytic in this Mathlib).
- Proved results you may import: `OscInt/StationaryPhase/*.lean` (e.g. `Family.lean`: `iteratedFDeriv_comp_affine`,
  `continuous_iteratedFDeriv_comp_affine`, `iteratedFDeriv_lin`; `Assembly.lean`: `dd_add_lin`, `ddd_add_lin`,
  `familyCk_of_le`; `Implicit.lean`, `NonStat.lean` contain tube-lemma and `dd`/`iteratedFDeriv` conversions; grep
  before writing your own).
- Four agents share 4 CPUs and 15 GB: at most ONE Lean process each, always `nice -n 10`.
- If a part is false as stated, STOP and report a counterexample (rule 3). Do not weaken it.

## Task P: `OscInt/D4/Rescale.lean` — `theorem OscInt.D4.rescaleFamily : OscInt.Blueprint.RescaleFamilyFacts`
Route: `docs/proof-S4.md` Step 2. Suggested: for `ε ≠ 0`, `iteratedFDeriv ℝ j (rescale φ ε) z =
ε^{j-3} • (iteratedFDeriv ℝ j φ (ε • z)).compContinuousLinearMap (fun _ => ε⁻¹ ... )` — more simply
`iteratedFDeriv ℝ j (fun z => φ (ε • z)) z = ε^j • (iteratedFDeriv ℝ j φ (ε • z))` (as multilinear maps, by
`iteratedFDeriv_comp_affine`/`ContinuousLinearMap.iteratedFDeriv_comp_right`). Joint continuity away from `ε = 0` is
then composition. At `ε = 0`: Taylor with integral remainder for `iteratedFDeriv ℝ j φ` along the segment
`[0, εz]` (`taylor_mean_remainder`-style results are 1D; a clean route is to apply the 1D integral form
`intervalIntegral.integral_eq_sub_of_hasDerivAt` to `s ↦ iteratedFDeriv ℝ j φ (s • w)` repeatedly, or to prove
`‖iteratedFDeriv ℝ j φ w − P_j(w)‖ ≤ C ‖w‖^{4-j} · ω(‖w‖)`-type bounds on a ball). You also need
`iteratedFDeriv ℝ j (cubicPoly (cubicCoeffs φ)) z` in terms of `D³φ(0)` (symmetry of the third derivative:
`ContDiffAt.isSymmSndFDerivAt`, `second_derivative_symmetric`). This is the largest part; split it.

## Task Q: `OscInt/D4/Gauge.lean` — `theorem OscInt.D4.cubicGauge : OscInt.Blueprint.CubicGaugeFacts` and
`theorem OscInt.D4.gaugeFold : OscInt.Blueprint.GaugeFoldFacts`
Route: Step 3. For D3 compute `dd`/`ddd` of `cubicPoly q` explicitly (as in the sanity lemmas of
`OscInt/Statements/D4.lean`), reduce to a polynomial statement in `(a, b, c, d, z₁, z₂)` and prove it, e.g. by
polynomial certificates (`linear_combination` showing `disc q * z₁^N` and `disc q * z₂^N` lie in the ideal of the
vanishing conditions) or by the case analysis in the route. For D4: `dd Ψ k` is bilinear and symmetric for `C²`
(`ContDiffAt.isSymmSndFDerivAt`), `ddd Ψ k` is trilinear for `C³`.

## Task R: `OscInt/D4/Open.lean` — `theorem OscInt.D4.gaugeOpen : OscInt.Blueprint.GaugeOpenFacts` and
`theorem OscInt.D4.gradBound : OscInt.Blueprint.GradBoundFacts`
Route: Step 3 (D5) and Step 4 (D6). Express `dd Ψ k v w` and `ddd Ψ k u v w` through `iteratedFDeriv ℝ 2/3 Ψ k`
applied to vectors (`iteratedFDeriv_two_apply`, `iteratedFDeriv_succ_apply_left`, or the conversions already in
`OscInt/StationaryPhase/`), so `FamilyCk 3` gives joint continuity; then the tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`). D6: `‖fderiv ℝ (Ψ σ) k‖ = ‖iteratedFDeriv ℝ 1 (Ψ σ) k‖`
(`norm_iteratedFDeriv_one`) is bounded on the compact `Λ × K`; with the max norm, the coordinate `i` with
`|p_i| = ‖p‖` gives `(∂_iΨ + p_i)² ≥ 1` when `‖p‖ ≥ sup + 1`.

## Task S: `OscInt/D4/Basic.lean` — `normalizeFacts : NormalizeFacts`, `cutoff : CutoffFacts`,
`trivialBound : TrivialBoundFacts`, `dyadicSum : DyadicSumFacts` (all `theorem OscInt.D4.<name>`)
D1: `ddd_add_lin`/`dd_add_lin` in `OscInt/StationaryPhase/Assembly.lean` handle adding a linear term; a constant does
not change `fderiv`; the integrand identity is pointwise, the factor `exp(i t φ(0))` has norm 1. D7: product
`g(z₁) g(z₂)` of a one-dimensional `ContDiffBump` (`ℝ` is an inner product space, so the bump is
`smoothTransition`-radial and nonincreasing in `|x|`), or any construction meeting all five conjuncts. D8:
`norm_integral_le_of_norm_le` with the bound `M · indicator (closedBall 0 r)`; `volume (closedBall 0 r)` for the max
norm on `ℝ × ℝ` is `(2r)²` (`closedBall_prod_same`, `Measure.prod_prod`, `Real.volume_Icc`); handle `r < 0`.
D9: `J := Nat.find` of `∃ j, t (δ/2^j)³ < 1`; the sum is geometric in `2^{-1/2}` after factoring
`t^{-5/6} ε_{J-1}^{-1/2}`; `1/(1 − 2^{-1/2}) < 4`.
