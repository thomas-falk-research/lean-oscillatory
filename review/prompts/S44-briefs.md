# Briefs for the S4.4 proof agents

## Common rules
As in `review/prompts/S1-briefs.md` (hard rules 1–7; replace `Blueprint.VanDerCorput` by `Blueprint.D4ClosedForm`
and `OscInt.VanDerCorput.<PartName>Aux` by `OscInt.D4.<PartName>Aux`), with:
- Read first: `docs/proof-S44.md` including its final "Revision after the route referee" section (it overrides the
  text above it), `Blueprint/D4ClosedForm.lean`, `OscInt/Statements/D4Limit.lean` (definitions of `cubicForm`,
  `cosMoment`, `cosMomentPartial`, `angularMoment`, `d4Constant`), `OscInt/Statements/D4.lean` (`disc`),
  `OscInt/D4/CubicComp.lean` (E4: `cubicForm_cubicComp`, `disc_cubicComp`). Your file lives under `OscInt/D4/`.
- The guard (`make guard` is allowed) forbids `open Lean`, `Lean.`-qualified names, `attribute`, `run_tac`,
  `set_option` except `set_option maxHeartbeats N in`, and `ContDiff ℝ ⊤`.
- S4.4 is about Gamma, so `GammaFree.lean` does not apply to your part. Your part must not import or depend on
  another S4.4 part's file: where your Prop takes another part's Prop as a hypothesis, use the hypothesis.
- Reuse is encouraged: `OscInt.d4ConstantPos : D4ConstantPosStatement` (`OscInt/D4/ConstantPosFinal.lean`: the
  improper integral converges; for `disc q ≠ 0` the angular integrand is interval integrable on `[0, 2π]`),
  `OscInt.D4.circleNondeg` (`OscInt/D4/Angular.lean`: zeros of `θ ↦ C(cos θ, sin θ)` are simple when `disc ≠ 0`),
  `OscInt.D4.PolarAux.cubicForm_neg`, `OscInt.D4.PolarAux.cubicForm_polar` (`OscInt/D4/Polar.lean`),
  `OscInt.D4.singularPower` (`OscInt/D4/SingularPower.lean`).
- Four agents share 4 CPUs and 15 GB: at most ONE Lean process each, always `nice -n 10`. A cold first run takes
  minutes (Mathlib loads from disk); that is not a hang.
- If a part is false as stated, STOP and report a counterexample (rule 3). Do not weaken it.

## Task M: `OscInt/D4/CosMomentValue.lean` —
`theorem OscInt.D4.cosMomentValue (hB : OscInt.Blueprint.BetaIoiFacts) : OscInt.Blueprint.CosMomentValueFacts`
Route E1 (steps 1–5). Mathlib: `Real.integral_rpow_mul_exp_neg_mul_Ioi` (route revision 3),
`MeasureTheory.integral_integral_swap` / `MeasureTheory.integrable_prod_iff` (Fubini on `Ioc 0 R ×ˢ Ioi 0`; the
absolute iterated integral is finite), `intervalIntegral.integral_eq_sub_of_hasDerivAt` (the antiderivative
e^{−su}(sin u − s cos u)/(1 + s²)), `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` (R → ∞ along
`atTop`), `MeasureTheory.integral_comp_rpow_Ioi_of_pos` (t = s²), `Real.Gamma_one`, `Filter.Tendsto.limUnder_eq`.
`integrableOn_Ioi_rpow_of_lt` and `intervalIntegral.intervalIntegrable_rpow'` for the dominating functions.

## Task N: `OscInt/D4/Chart.lean` — `theorem OscInt.D4.angularLine : OscInt.Blueprint.AngularLineFacts`
Route E2. Mathlib: `Function.Periodic.intervalIntegral_add_eq`, `intervalIntegral.integral_add_adjacent_intervals`,
`Real.range_arctan`, `Real.arctan_injective`, `Real.hasDerivAt_arctan`,
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (with `s = univ`, `f = Real.arctan`), `Real.cos_arctan`,
`Real.sin_arctan`, `intervalIntegral.integral_of_le`, `MeasureTheory.integral_Ioc_eq_integral_Ioo`,
`Real.rpow_natCast`, `Real.mul_rpow`, `Real.sqrt_eq_rpow`.

## Task O: `OscInt/D4/Covariance.lean` — `theorem OscInt.D4.covariance : OscInt.Blueprint.CovarianceFacts`
Route E3. Mathlib: `integral_comp_polarCoord_symm`, `polarCoord_target`, `MeasureTheory.lintegral_prod` /
`MeasureTheory.setLIntegral_prod` (Tonelli; working in `lintegral` avoids integrability side conditions until the
end), `integral_rpow_mul_exp_neg_mul_rpow` or a direct antiderivative for ∫₀^∞ r e^{−a r²} dr = 1/(2a),
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` with `MeasureTheory.integral_map` (or the `lintegral`
analogue), `LinearMap.det_toLin'` / `Matrix.det_fin_two` for `det2`, `Function.Periodic.intervalIntegral_add_eq`
(J over (−π, π) = over (0, 2π)). Null zero set: route E3 step 1.

## Task T: `OscInt/D4/NormalForm.lean` — `theorem OscInt.D4.normalForm : OscInt.Blueprint.CubicNormalFormFacts`
Route E5 (steps 1–4). Mathlib: `intermediate_value_Icc` / `intermediate_value_Icc'`, `Real.sin_sq_add_cos_sq`,
`Real.rpow_natCast`, `Real.rpow_inv_natCast_pow` (cube roots of positive reals; handle the sign by hand), `ring`,
`linear_combination`, `field_simp`. Prove a composition lemma
`cubicComp (cubicComp q g) h = cubicComp q (mul g h)` with an explicit `mul` and `det2 (mul g h) = det2 g * det2 h`
(both by `ring` after `simp only [cubicComp, cubicForm, lin2]`), in your file's `Aux` namespace.

## Task K (second wave): `OscInt/D4/Beta.lean` — `theorem OscInt.D4.betaIoi : OscInt.Blueprint.BetaIoiFacts`,
`theorem OscInt.D4.betaUnit : OscInt.Blueprint.BetaUnitFacts`; and `OscInt/D4/LineMoments.lean` —
`theorem OscInt.D4.lineMomentValues (hB : OscInt.Blueprint.BetaIoiFacts) (hU : OscInt.Blueprint.BetaUnitFacts) :
OscInt.Blueprint.LineMomentValuesFacts`
Route E6a–c. Mathlib: `Real.integral_rpow_mul_exp_neg_mul_Ioi` (route revision 3),
`MeasureTheory.lintegral_lintegral_swap`, `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`;
`Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Complex.betaIntegral`, `Complex.Gamma_ofReal`, `Complex.ofReal_cpow`,
`intervalIntegral.integral_ofReal`; `MeasureTheory.integral_comp_rpow_Ioi_of_pos`, `integral_comp_neg_Ioi`,
`MeasureTheory.setIntegral_union`, `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`, `MeasureTheory.Integrable.of_integral_ne_zero`, `Real.Gamma_one_half_eq`.

Every Mathlib name in this file was `#check`ed at Mathlib 56a0058 on 2026-11-06 (lesson 1).
