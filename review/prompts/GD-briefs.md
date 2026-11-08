# Proof-agent briefs: batch GD (launched only after the pre-proof review stamp)

## Common rules (every agent)
1. Work only in your own file (named below). Do not edit any other file in the repository. Never edit
   `OscInt/Statements/*` or `Blueprint/*`.
2. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`, `macro`, `elab`, `syntax`,
   `notation`, `run_cmd`, `run_tac`, `#eval`, `open Lean`, `Lean.`-qualified names, `attribute`, `private`, or
   `set_option` other than `set_option maxHeartbeats N in` (N ≤ 800000). Write `∞` with `open scoped ContDiff` for
   C^∞ (`⊤` is analytic, lessons 12). Keep declarations under ~60 lines; helpers in a namespace ending in `Aux`.
3. If you find that your proposition is false or unprovable as stated, STOP and report a counterexample or the exact
   obstacle. Never weaken the proposition.
4. Iterate with `cd /home/user/lean-oscillatory && export PATH=$HOME/.elan/bin:$PATH && nice -n 10 lake env lean
   -DautoImplicit=false <your file>`; one Lean process at a time; never `lake build` of the whole library or `make`.
5. Your final theorem must have exactly the stated type (`theorem name : Blueprint.GD.XFacts := …`). Report: file,
   theorem names, the compile command and its clean output, and `#print axioms` of the final theorem (only `propext`,
   `Classical.choice`, `Quot.sound`) from a scratch file under `/tmp/<agent>/`.
6. Mathlib names below were `#check`ed at the pin (`docs/replay/2026-11-08-GD-names.txt`); `#check` anything else
   before relying on it (lessons 1, 19).

## GD-P1 — `OscInt/Front/GlobalLocal.lean`: `d4PieceFacts`, `bumpFacts`, `mulBoundFacts`, `largeLFacts`
Imports: `OscInt.Front.Local` (gives `OscInt.API.d4BoundLocal : D4BoundLocalStatement`, `OscInt.API.nonStationaryOn`),
`Blueprint.Global`.
- `theorem d4PieceFacts : OscInt.Blueprint.GD.D4PieceFacts`. Route `docs/proof-GD.md` R1. φ := fun κ => Ψ (k₀ + κ),
  U₀ := (fun κ => k₀ + κ) ⁻¹' U (open by continuity, `0 ∈ U₀`). `ContDiffOn ℝ 4 φ U₀`: `hΨ.comp (contDiffOn_const.add
  contDiffOn_id)` with `Set.MapsTo`. Derivatives: `iteratedFDeriv_comp_add_left n k₀ 0` gives
  `iteratedFDeriv ℝ n φ 0 = iteratedFDeriv ℝ n Ψ (k₀ + 0)`. Apply `d4BoundLocal φ U₀ a b c d …` (a, b, c, d from
  `IsD4Point`) to get δ, C. Given A supported in `closedBall k₀ δ`, B := fun κ => A (k₀ + κ): `ContDiff`, support
  `⊆ closedBall 0 δ` (`dist (k₀ + κ) k₀ = ‖κ‖`), same derivative bounds (`iteratedFDeriv_comp_add_left`). Integral:
  `MeasureTheory.integral_add_left_eq_self (μ := volume) (fun k => F k) k₀` rewrites
  `∫ k, F k = ∫ κ, F (k₀ + κ)`; then `m * (Ψ (k₀+κ) + L (k₀+κ)) = m * φ κ + (m • L) κ + m * L k₀`, pull out the
  unimodular factor `Complex.exp (↑(m * L k₀) * I)` (`Complex.norm_exp_ofReal_mul_I`), and apply the D4 bound with
  `t = m`, linear term `m • L`.
- `theorem bumpFacts : …BumpFacts`. `ContDiffBump` with `rIn = ρ/2`, `rOut = ρ` at `k₀`: `ContDiffBump.contDiff`,
  `ContDiffBump.tsupport_eq` (= closedBall), `ContDiffBump.one_of_mem_closedBall`, `nonneg`, `le_one`; derivative
  bound: a `C^∞` function with compact support has bounded `iteratedFDeriv` (`ContDiff.continuous_iteratedFDeriv` +
  `HasCompactSupport.iteratedFDeriv` + `Continuous.bounded_above_of_compact_support`, check names); take the max over
  `j ≤ 2` (a finite `Finset.sup'` or sum).
- `theorem mulBoundFacts : …MulBoundFacts`. `norm_iteratedFDeriv_mul_le` with `f = fun k => (χ k : ℂ)` (`ContDiff` via
  `Complex.ofRealCLM.contDiff.comp`), `‖iteratedFDeriv ℝ i (ofReal ∘ χ) k‖ ≤ ‖iteratedFDeriv ℝ i χ k‖`
  (`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` with `‖ofRealCLM‖ ≤ 1`, check name); C := 4·max B 0 (binomial
  sum over `i ≤ j ≤ 2` is at most 4 terms with coefficients ≤ 2).
- `theorem largeLFacts : …LargeLFacts`. `ContDiffOn.continuousOn_fderiv_of_isOpen` (order 2 ≥ 1) gives
  `ContinuousOn (fderiv ℝ Ψ) U`; `IsCompact.exists_bound_of_continuousOn` on `K` gives `B` with `‖fderiv ℝ Ψ k‖ ≤ B`;
  R := B + 1; `‖DΨ + L‖ ≥ ‖L‖ − ‖DΨ‖` (`norm_sub_norm_le` / `norm_add_le`).

## GD-P2 — `OscInt/Front/Torus.lean`: `unfoldWeight`, `unfoldFacts`
- `noncomputable def unfoldStep (s : ℝ) : ℝ := Real.smoothTransition (s + 1 / 2)`;
  `noncomputable def unfoldWeight₁ (s : ℝ) : ℝ := unfoldStep (s + Real.pi) - unfoldStep (s - Real.pi)`;
  `noncomputable def unfoldWeight (k : ℝ × ℝ) : ℝ := unfoldWeight₁ k.1 * unfoldWeight₁ k.2`.
- `theorem unfoldFacts : OscInt.Blueprint.GD.UnfoldFacts unfoldWeight`. Route R6: the 1D identity
  `∫ s in (-π)..π, g s = ∫ s, (unfoldWeight₁ s : ℂ) * g s` for continuous 2π-periodic `g` via `G s = g s * step(s+π)`,
  `g s * w₁ s = G s - G (s - 2π)`, `intervalIntegral.integral_comp_sub_right`, `Function.Periodic.intervalIntegral_add_eq`,
  support of `w₁` in `[−π − 1/2, π + 1/2]` (so `∫ = ∫ in −4..4`, `MeasureTheory.integral_eq_integral_of_support_subset`
  or `intervalIntegral.integral_of_le` + support), then 2D by `MeasureTheory.integral_prod` (integrable: continuous with
  compact support, `Continuous.integrable_of_hasCompactSupport`) and `MeasureTheory.setIntegral_prod` on
  `torusBox = Icc ×ˢ Icc` with `Measure.volume_eq_prod`; `Icc` vs `Ioc`: `MeasureTheory.integral_Icc_eq_integral_Ioc`.
  `unfoldWeight (π/2, π/2) = 1`: `smoothTransition (3π/2 + 1/2) = 1`, `smoothTransition (−π/2 + 1/2) = 0`
  (`one_of_one_le`, `zero_of_nonpos`, `Real.pi_gt_three`). Support: outside `[−π−1/2, π+1/2]` both steps are equal
  (both 0 or both 1).

## GD-P3 — `OscInt/Front/LatticeSymbol.lean`: `latticeSymbolFacts`, `diagPhaseFacts`
- `theorem latticeSymbolFacts : OscInt.Blueprint.GD.LatticeSymbolFacts`. Route R7. Derivatives of
  ω = cos k₁ + cos k₂ by explicit `HasFDerivAt` (pattern: `OscInt/Front/ConvertSanity.lean`, `sanity_fd_cubes` in
  `OscInt/Statements/D4.lean`), `dd ω y v w = −cos y₁ v₁ w₁ − cos y₂ v₂ w₂`, `ddd ω y u v w = sin y₁ u₁v₁w₁ +
  sin y₂ u₂v₂w₂`, then `iteratedFDeriv_two_eq_dd`, `iteratedFDeriv_three_diag` (`OscInt.API.ConvertSanity`) for the
  Hessian matrix `!![-cos y₁, 0; 0, -cos y₂]` and the cubic. Cases on `cos y₁ = 0`, `cos y₂ = 0` for `y ∈ closedBall 0 4`
  (max norm: `|y₁| ≤ 4`, `|y₂| ≤ 4`): `Real.cos_eq_zero_iff` and `π > 3.14`, `π < 3.15` (`Real.pi_gt_d2`,
  `Real.pi_lt_d2`, check names) force `y_i = ±π/2`. Fold branch: kernel of `diag(0, c)` (`c ≠ 0`) is the span of
  `(1, 0)` (see `sanity_FoldCondSpan` and `foldOrNondegMatrix_fold` in `ConvertSanity` for the pattern); third
  derivative `sin y₁ = ±1 ≠ 0`. D4 points: `iteratedFDeriv ℝ 2 ω y = 0` by `ContinuousMultilinearMap.ext` on
  `Fin 2 → ℝ × ℝ` (write each vector in the basis, or use `dd` and C1 with linearity), cubic coefficients
  `(sin y₁/6, 0, 0, sin y₂/6)`, `discr = −27 (sin y₁ sin y₂)²/1296 ≠ 0`.
- `theorem diagPhaseFacts : OscInt.Blueprint.GD.DiagPhaseFacts`: the same derivative computations for
  `φ = −sin κ₁ − sin κ₂ + κ₁ + κ₂`; `Real.cos_pi_div_two_add` (check name; else `Real.cos_add` with `cos (π/2) = 0`,
  `sin (π/2) = 1`); `cubicCoeffs φ = (1/6, 0, 0, 1/6)`; `disc` by `norm_num [disc]`.
