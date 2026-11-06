# Briefs for the S4.2 proof agents

## Common rules
As in `review/prompts/S43-briefs.md` (which refers to `review/prompts/S1-briefs.md`), without the Gamma-free rule
(S4.2 may use any Mathlib), with: read first `docs/proof-S42.md` including its final revision section (it overrides
the text above it), `Blueprint/D4LimitS42.lean`, `Blueprint/D4Limit.lean`, `OscInt/Statements/D4Limit.lean`,
`review/2026-11-06-S42-proof-route.md` (§3 has the referee's sketch and Mathlib names). Proved results you may import:
`OscInt.D4.circleNondeg`, `OscInt.D4.angularPos` (`OscInt/D4/Angular.lean`), `OscInt.D4.singularPower`
(`OscInt/D4/SingularPower.lean`), `OscInt.D4.d4ConstantPos_of` (`OscInt/D4/ConstantPos.lean`), the S4.1 parts in
`OscInt/D4/`. Several agents share 4 CPUs and 15 GB: one Lean process each, `nice -n 10`. If a part is false as
stated, STOP and report a counterexample.

## Task X: `OscInt/D4/Tail.lean` — `OscInt.D4.innerLimit : OscInt.Blueprint.InnerLimitFacts` (E2) and
`OscInt.D4.dyadicTail : OscInt.Blueprint.DyadicTailFacts` (E3)
E2: `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` along `𝓝 0` (first countable), bound
sup‖B‖·sup{‖A(s•w)‖ : |s| ≤ 1, w ∈ tsupport B}·1_{tsupport B}, then `integral_mul_const`. E3: `Nat.find` for the
least N with δ ≤ 2^N ρ (or N = 0), each term = 2^{−(j+1)/2} R^{−1/2} t^{−2/3}, geometric sum ≤ 1/(√2 − 1) < 3.

## Task Y: `OscInt/D4/Radial.lean` — `OscInt.D4.radialIdentity : OscInt.Blueprint.RadialIdentityFacts` (E1a)
Route revision: ψ r = −∫_r^K ψ′ (FTC), Fubini on the triangle 0 ≤ r ≤ ρ ≤ K (or integrate by parts in r against
F(r) = ∫₀^r cos(λs³) s ds, which is simpler: ∫₀^K cos(λr³)ψ r dr = [Fψ]₀^K − ∫₀^K F ψ′ = −∫₁^K F ψ′, using ψ(K) = 0,
F(0) = 0, ψ′ = 0 on (0, 1)), and F(ρ) = (1/3) λ^{−2/3} cosMomentPartial(λρ³) by the substitution u = λ r³
(`intervalIntegral.integral_comp_mul_deriv'''` or a direct HasDerivAt/FTC argument on (0, ρ)).

## Task Z: `OscInt/D4/Polar.lean` — `OscInt.D4.polarReduction : OscInt.Blueprint.PolarReductionFacts` (E1b)
Evenness: w ↦ −w (`integral_neg_eq_self`), C(−w) = −C(w), so the integral equals its conjugate and is the integral
of cos(C(w)) χ(R⁻¹w) (real); `integral_comp_polarCoord_symm` (target `Ioi 0 ×ˢ Ioo (-π) π`), Fubini with θ outer
(`setIntegral_prod`, `integral_prod_symm`), truncation of r at 2K₀R (‖rω‖ ≥ r/√2 ≥ K₀R ⇒ χ(R⁻¹ rω) = 0), and
cubicForm q (r cos θ, r sin θ) = r³ · circleCubic q θ.

## Task Q2: `OscInt/D4/PolarLimit.lean` — `OscInt.D4.circleZerosNull : OscInt.Blueprint.CircleZerosNullFacts` (E1c)
and `OscInt.D4.cubicCutoffLimit_of : OscInt.Blueprint.CubicCutoffLimitCombineFacts` (E1d)
E1c: from `circleNondeg`, zeros are isolated (`HasDerivAt.eventually_ne` or `deriv ≠ 0` ⇒ locally injective), so
finitely many in each compact interval, so the zero set is countable, hence null (`Set.Countable.measure_zero`).
E1d (assume E1a–E1c as hypotheses): route revision text; uniform bound |λ^{2/3}∫ …| ≤ (1/3) (K − 1) sup|ψ′| sup|P|
with P = cosMomentPartial bounded on [0, ∞) (continuous, convergent); after r = Rρ the inner integral at angle θ is
(1/3)|g(θ)|^{−2/3}·[λ^{2/3}… with λ = R³|g(θ)|] → (1/3)|g(θ)|^{−2/3} cosMoment for g(θ) ≠ 0; dominated convergence in θ
(bound const·|g|^{−2/3}, integrable by the hypothesis of E1 after the periodic shift), limit
(1/3) cosMoment ∫_{−π}^{π}|g|^{−2/3} = d4Constant q (shift by 2π-periodicity, `Function.Periodic.intervalIntegral_add_eq`).
Note ψ_θ(ρ) = χ(ρ ω(θ)) is `1` on [0, 1] because ‖ρω‖ ≤ ρ (max norm) and χ = 1 on B̄(0, 1); its ρ-derivative is
bounded by sup‖fderiv χ‖ uniformly in θ; it vanishes for ρ ≥ 2K₀ for any K₀ with χ = 0 outside B̄(0, K₀).
