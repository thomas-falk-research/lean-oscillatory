# Cookbook

Copy-paste starting points. Each recipe points at a file that `make quick` (or the consumer CI job) compiles, so the
code there cannot rot silently; copy from it. Which theorem fits which phase: `docs/which-theorem.md`.

| Task | Compiled example | Theorem(s) |
|---|---|---|
| A phase given by a polynomial formula: derivative data by `ring` identities, then a front end | `examples/consumer/ConsumerFormula.lean` | `nonStationaryFE`, `stationaryPhaseFE`, `foldFE`, `d4BoundFE`; helpers `OscInt.API.Poly.*` |
| A phase smooth only on an open set (arccos-type dispersion relation; a phase with a kink outside the support) | `examples/consumer/ConsumerLocal.lean` | `nonStationaryLocal`, `stationaryPhaseOn`, `foldOn` |
| Non-vacuity: critical points exist, planted hypotheses are false | `examples/consumer/ConsumerLocalChecks.lean` | — |
| Amplitude bounds `M` from `ContDiff` + compact support | `OscInt/Front/Core.lean` (the F2 bridge uses it) | `ampBoundOfContDiff` (F1) |
| The D4 leading term with its closed-form constant | `examples/consumer/Consumer.lean`, `OscInt/Front/Sanity.lean` | `d4LimitClosedForm` (F2) |
| Every front end applied to an explicit phase (non-vacuity) | `OscInt/Front/Examples.lean` | FE-S2.1, FE-S2.2, FE-S4.1′, C8 |
| Hessian matrices and the fold condition of explicit phases (`hessianMatrix`, `FoldOrNondegMatrix`) | `OscInt/Front/ConvertSanity.lean`, `OscInt/Front/GlobalSanity.lean` | C1–C7 |
| A D4 point (`IsD4Point`) of an explicit cubic | `OscInt/Front/GlobalSanity.lean` (`ell_isD4`) | C1, C2, C5 |
| Periodic integrals over `[−π, π]²` | `OscInt/Front/GlobalSanity.lean` (`latticeKernel_zero_zero`, `torusUnfold_moments`) | T1 |
| The 2D lattice Laplacian, `t^{-2/3}` and sharpness | `examples/consumer/ConsumerLattice.lean` | T6, T6L, SH |
| Every batch-GD theorem applied to concrete data | `examples/consumer/ConsumerGlobalChecks.lean` | GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L |
| The 1D lattice kernel with the cube-root constant: transition probabilities on a cosine-band lattice | `examples/consumer/ConsumerPhotonLattice.lean` | T0E′ (`latticeKernel1CubeRoot`) |
| The d-dimensional hypercubic kernel, factorised and bounded | `OscInt/Front/HypercubicSanity.lean` | TdF, TdE′ |
| Checking `IsA3Point` / `IsStableA3Point` for an explicit quartic phase; S1.k at k = 2, 3 | `OscInt/Front/CuspSanity.lean` | S1.k, S5.1, S5.1′ |
| A 1D phase with a third-derivative lower bound (whistler waves at an inflection) | `examples/consumer/ConsumerWhistler.lean` | S1.3 (`vanDerCorput_three`) |
| A phase with nondegenerate Hessian everywhere (cold-plasma waves); free streaming | `examples/consumer/ConsumerColdPlasma.lean`, `examples/consumer/ConsumerPhaseMixing.lean` | GD-N, FE-S2.1 |

Recurring steps, in the order they come up:
1. **Smoothness.** `fun_prop` closes `ContDiff ℝ n` for polynomial and trigonometric formulas; for `ContDiffOn` on an
   open set use `Real.contDiffOn_arccos.comp` (and friends) as in `ConsumerLocal.lean`.
2. **Derivatives.** Compute `fderiv` with an explicit `HasFDerivAt` (`hasFDerivAt_fst`, `.pow`, `.const_mul`, `.add`)
   and `HasFDerivAt.fderiv`; then `dd`/`ddd` (nested `fderiv`) and convert with `iteratedFDeriv_two_eq_dd`,
   `iteratedFDeriv_three_diag` (`OscInt/Front/ConvertSanity.lean`), or C1/C2 directly.
3. **Hessian matrix.** `ext i j; fin_cases i <;> fin_cases j <;> simp [hessianMatrix, …, coordVec]`, then
   `Matrix.det_fin_two`.
4. **Amplitude bound.** `ampBoundOfContDiff` gives `M`; keep the same `K` as in the statement.
5. **Linear terms.** A vector `x` is the functional `x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ`.
