<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

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
| The D4 limit along a bounded offset that changes with `t` (rounding to lattice sites), with the closed-form constant, and the lower bound it gives | `examples/consumer/ConsumerD4Uniform.lean` | S4.2O (`d4LimitOffset`), S4.4, SH |
| **[v0.7.0]** Normalised Fourier coefficients of a function analytic in a strip; a stopping rule for the trapezoidal rule; the lattice light cone at `η = 1` | `examples/consumer/ConsumerPeriodicAnalytic.lean` | PA-C (`fourierCoeffStrip`), PA-T (`trapezoidalRule`), LC-1 (`latticeKernel1LightCone`) |
| **[v0.7.0]** An exponential sum with a linear phase `αn`, `λ ≤ α ≤ 1 − λ`, bounded uniformly in the number of terms | `examples/consumer/ConsumerKusminLandau.lean` | KL-D (`kusminLandau`), KL-C (`kusminLandauTwoOverPi`) |
| **[v0.7.0]** A ring of `N` sites and an open chain of `M` sites against the infinite line (finite-size bounds at `η = 1`); the chain of two sites in closed form | `examples/consumer/ConsumerFiniteRing.lean` | FR-P (`ringFiniteSize`), FC-P (`chainFiniteSize`), FC-U (`chainUnique`) |
| **[v0.7.0]** A 1D phase whose derivative increases at rate at least `λ`: the bound `(7/2)/√λ`; partial integrals of the Fresnel phase `e^{iλx²/2}` | `examples/consumer/ConsumerSecondDerivSharp.lean` | VC2-S (`secondDerivSharp`), VC2-N (`vdc2ProfileBound`) |
| **[v0.7.0]** The Hadamard walk from a normalised point state: a bound for each amplitude and for the probability at a site | `examples/consumer/ConsumerHadamardWalk.lean` | HW-D (`hadamardDecay`) |

Rows marked **[v0.7.0]** use theorems of batches PA, KL, FR, VC2 and HW, which are new in release v0.7.0.

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
