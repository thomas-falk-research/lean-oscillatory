# S4.4 route referee report (verbatim)

Prompt: `review/prompts/S44-proof-route.md`. Fresh-context agent, 2026-11-06, on repository commit 828309a and the
four scratch files with the hashes in its first line (committed afterwards, with the fixes recorded in
`docs/proof-S44.md`, "Revision after the route referee"). Recorded by the lead without edits below the line.

---

sha256: 91e131b9a9eb22059bb2fc230e4f419479c6fa186db1d1079213ab21e68243fa proof-S44.md; 7cbb4299244bbfa7ba2bfac665dcfea3d0658d60f00bf8036af70ecf80135767 Blueprint_D4ClosedForm.lean; fa88ece5948eada7a28434d8ee21a22a78e9fe70a01fea1bbb0f15e78ef2cc3d ClosedForm.lean; 808b43ebff9a86fa8643147d50f3cf9721b4545fa803dcede6772ca4e8be2cd4 GammaSixth.lean

# Referee report: S4.4 proof route and blueprint (repo commit 828309a, Mathlib 56a00585)

Nothing in the repo was modified. My test files are in /tmp/claude-0/-home-user-lean-oscillatory/448ffe38-12ad-59da-9f96-48c131dcaeee/scratchpad/s44rev/ (`Names.lean`, `Combined.lean`, `T1.lean`, `T2.lean`). I ran one Lean process at a time, each under `nice -n 10`.

## What I checked in Lean
- **Assembly against the whole repo.** `T2.lean` is `import OscInt`, `import Blueprint`, then the blueprint, `GammaSixth` and `ClosedForm` with `NormalFormFacts` renamed. It elaborates, and `#print axioms OscInt.D4.d4ConstantClosedForm_of` gives `[propext, Classical.choice, Quot.sound]`. So the assembly holds against the full development once the name clash below is fixed. Apart from `NormalFormFacts`, no blueprint or `OscInt.D4` name clashes.
- **Existing results the route relies on.** `OscInt.d4ConstantPos`, `OscInt.D4.circleZerosNull` and `OscInt.D4.gammaSixth` use only the three standard axioms.
- **Algebra facts, all checked by `ring`, `field_simp` or `norm_num` in `Combined.lean`:**
  - `cubicComp (cubicComp q g) h = cubicComp q (g·h)` with `det2` multiplicative.
  - `cubicComp (1,0,-1,0) (1,1,1,-1) = (0,4,4,0)`.
  - The shear step `cubicComp (a,b,c,0) (1,0,-(b/(2c)),1) = (a - b²/(4c), 0, c, 0)`.
  - The rotation's y³ coefficient is `cubicForm q (cos θ₀, sin θ₀)`.
  - `disc (a,b,c,0) = c²(b² − 4ac)`.
  - `lineCubic (1,0,1,0) = 1 + u²` and `lineCubic (0,1,1,0) = u + u²`.
- **`cubicComp` coefficient order.** By hand: with f = Ax³+Bx²y+Cxy²+Dy³, (f(1,1)−f(1,−1))/2 − f(0,1) = B and (f(1,1)+f(1,−1))/2 − f(1,0) = C. That is the `cubicForm` order. E4a `cubicForm_cubicComp` confirms it by `ring`.

## Findings

**BLOCKER 1. Name clash.** `Blueprint_D4ClosedForm.lean` declares `def NormalFormFacts : Prop` in `namespace OscInt.Blueprint`. `OscInt.Blueprint.NormalFormFacts` already exists in `Blueprint/StationaryPhase.lean:87` (the L2 normal form).
- Lean output: "`OscInt.Blueprint.NormalFormFacts` has already been declared".
- `import OscInt.D4.ConstantPosFinal` alone already brings that name in (`T1.lean`). The E2 route needs exactly that import, for `OscInt.d4ConstantPos`.
- So the new blueprint cannot sit in a file that imports `d4ConstantPos`. Adding `import Blueprint.D4ClosedForm` to the root `Blueprint.lean` (a default target, which imports `Blueprint.StationaryPhase`) breaks the library build.
- The lead's check did not catch it because the blueprint was elaborated against `OscInt.Statements.D4Limit` only.
- Fix: rename it, e.g. `CubicNormalFormFacts`, in the blueprint, in `ClosedForm.lean` (the `h5 : NormalFormFacts` binder) and in `proof-S44.md`. I tested the renamed version against `import OscInt` + `import Blueprint`.

**MAJOR.** None.

**MINOR 1. Wrong names in the route.**
- `OscInt.D4.cubicForm_neg` and `OscInt.D4.cubicForm_polar` (route, E2 step 1 and E3 step 1) do not exist. The real names are `OscInt.D4.PolarAux.cubicForm_neg` and `OscInt.D4.PolarAux.cubicForm_polar`. The second has the form `cubicForm q (r * cos θ, r * sin θ) = r ^ 3 * circleCubic q θ`.
- `integral_cpow_mul_exp_neg_mul_Ioi` is `Complex.integral_cpow_mul_exp_neg_mul_Ioi`. Its rate really is real (`0 < r`), so the route's "Change from the hand-off route" note is correct.

**MINOR 2. E3 step 1, polar angle range.** `integral_comp_polarCoord_symm` and `lintegral_comp_polarCoord_symm` integrate over `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`, not (0, 2π). The route needs one more periodicity step (`Function.Periodic.intervalIntegral_add_eq` with T = 2π) to reach `angularMoment`. It does not say so.

**MINOR 3. E3 null set.** The route sketches two arguments that the zero set of θ ↦ C(cos θ, sin θ) is null. Neither is needed: `OscInt.D4.circleZerosNull : CircleZerosNullFacts` (`∀ q, disc q ≠ 0 → volume {θ | circleCubic q θ = 0} = 0`, where `circleCubic q θ = cubicForm q (cos θ, sin θ)`) is already proved and axiom-clean. The route should cite it.

**MINOR 4. Better Mathlib lemmas.**
- E1 step 1 and E6a: `Real.integral_rpow_mul_exp_neg_mul_Ioi : 0 < a → 0 < r → ∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a` gives the Gamma representation in one step. Use it instead of `Real.Gamma_eq_integral` + `integral_comp_mul_left_Ioi`; both of those do exist.
- E3: the radial integral ∫₀^∞ r e^{−a r²} dr = 1/(2a) is `integral_rpow_mul_exp_neg_mul_rpow` (p = 2, q = 1, `MeasureTheory/Integral/Gamma.lean:44`).
- E3: `Complex.integral_exp_neg_mul_rpow` in the same file does a polar-coordinates Gamma computation and is a ready template.

**MINOR 5. E3 step 2 needs a determinant computation the route does not spell out.** `map_linearMap_addHaar_eq_smul_addHaar` takes `LinearMap.det f`. To get `det2 g`, write `lin2 g` as `Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![g₁, g₂; g₃, g₄]` (`Matrix.toLin_finTwoProd_apply`). Then use `LinearMap.det_toLin` and `Matrix.det_fin_two_of`. The add-Haar instance on ℝ × ℝ is `Measure.prod.instIsAddHaarMeasure`. After that, `integral_map` and `integral_smul_measure` (or the lintegral versions).

**NIT 1. E2 step 1.** `Function.Periodic.intervalIntegral_add_eq` needs no integrability. `intervalIntegral.integral_add_adjacent_intervals` does: get it from `(OscInt.d4ConstantPos.2.2 q hq).1` via `IntervalIntegrable.mono_set`.

**NIT 2. E6c integrability.** "a Bochner integral that is nonzero" works:
- Set integrals: `MeasureTheory.Integrable.of_integral_ne_zero`.
- The interval integral over (−1, 0): `intervalIntegral.intervalIntegrable_of_integral_ne_zero`. It lives in namespace `intervalIntegral`; the bare name does not exist.
- The substitution lemmas `integral_comp_neg_Ioi`, `integral_comp_rpow_Ioi_of_pos` (p = 2) and `integral_image_eq_integral_abs_deriv_smul` need no integrability. So apply `of_integral_ne_zero` to each original piece after computing it.
- Splitting ℝ: `intervalIntegral.integral_Iic_add_Ioi`, or `setIntegral_union` with `Set.Iic_union_Ioi`.
- `integral_comp_neg_Ioi` is in the root namespace; `MeasureTheory.integral_comp_neg_Ioi` does not exist.

**NIT 3. E5 step 1.** The sign of g(0) = a is unknown, so the zero needs `intermediate_value_Icc` or `intermediate_value_Icc'` by cases (or the `uIcc` form). α must be built as `SignType.sign a₂ * |a₂| ^ (-1/3)`, as the route says, and not as `a₂ ^ (-1/3)` (`Real.rpow` of a negative base is not the real cube root).

## Per-part verdict (is the Lean Prop true; is the route correct and complete)

**E1 `CosMomentValueFacts` (`cosMoment = Γ(2/3)/2`).**
- TRUE. ∫₀^∞ cos u · u^{s−1} du = Γ(s)cos(πs/2) at s = 2/3. `limUnder` is correct once Tendsto is shown (`Filter.Tendsto.limUnder_eq`, T2, `atTop` NeBot). `u^(-1/3)` at u = 0 is a null point. The orientation 0..R is positive for R > 0, which holds eventually.
- Route correct and complete:
  - The antiderivative e^{−su}(sin u − s cos u)/(1+s²) differentiates to cos u · e^{−su}, so the formula for h_R is right.
  - The bound (2s+1)/(1+s²) ≤ 3 on (0,1] and ≤ 3/s on [1,∞) holds.
  - The pointwise limit is s^{1/3}/(1+s²).
  - The substitution t = s² gives ½ t^{−1/3}(1+t)^{−1}, which is E6a with a = 2/3, b = 1/3.
- Lemmas: `tendsto_integral_filter_of_dominated_convergence`, `integral_integral_swap` (integrability by `integrable_prod_iff` on the absolute integrand), `intervalIntegral.integral_of_le`, `integral_comp_rpow_Ioi_of_pos`, `Real.integral_rpow_mul_exp_neg_mul_Ioi`.

**E2 `AngularLineFacts`.**
- TRUE. For disc ≠ 0, p = C(1,·) has simple real roots (exponent 2/3 < 1) and degree ≥ 2: if d = 0 then disc = c²(b²−4ac) forces c ≠ 0. So |p|^{−2/3} is integrable on ℝ and the Bochner value is the genuine one.
- Route correct and complete. At zeros of p both sides are `0 ^ (-2/3) = 0` (`Real.zero_rpow`). The factor (1+u²) cancels via `Real.mul_rpow`. The endpoints ±π/2 are null (`integral_Ioc_eq_integral_Ioo`).
- Lemmas: `integral_image_eq_integral_abs_deriv_smul` (unconditional), `Real.range_arctan`, `Real.arctan_injective`, `Real.hasDerivAt_arctan`, `Real.cos_arctan`, `Real.sin_arctan`. Names as in MINOR 1 and NIT 1.

**E3 `CovarianceFacts`.**
- TRUE. For disc q ≠ 0, E4b gives disc(cubicComp q g) = det⁶ · disc q ≠ 0. G(C) = ∫ exp(−|C|^{2/3}) is finite and equals J/2: inner integral ∫₀^∞ r e^{−r²a} = 1/(2a) with a = |g(θ)|^{2/3} > 0 a.e., since (r³|g|)^{2/3} = r²|g|^{2/3} for r > 0. G(C∘L) = G(C)/|det L|.
- Route correct. It is incomplete only as noted in MINOR 2 (angle range), MINOR 3 (null set) and MINOR 5 (determinant). It should work with lintegrals, then `ofReal_integral_eq_lintegral_ofReal` to return to `angularMoment`.

**E5 normal forms.**
- TRUE. disc < 0 means one real root (x³ + y³ gives −27): GL₂(ℝ)-equivalent to x(x²+y²). disc > 0 means three distinct real roots: equivalent to xy(x+y).
- Route correct and complete. Every algebraic step was checked in Lean (see above). The step-3 sign rule (a₂c₁ > 0 iff disc < 0) holds, and so does the step-4 composition with the scaling 4^{−1/3} > 0.

**E6a `BetaIoiFacts`.**
- TRUE: the beta integral of the second kind. Integrable for a, b > 0.
- Route correct: Tonelli, then y^{a+b−1}e^{−y}·Γ(a)y^{−a} integrates to Γ(a)Γ(b). Use `Real.integral_rpow_mul_exp_neg_mul_Ioi` and `lintegral_lintegral_swap` (or `integral_integral_swap`), and divide by Γ(a+b) > 0.

**E6b `BetaUnitFacts`.**
- TRUE. The orientation 0..1 is positive. At x = 0, `0 ^ (a-1)` is 0 (or 1 when a = 1), a null point.
- Route correct. `Complex.betaIntegral u v` is definitionally `∫ x in 0..1, ↑x ^ (u - 1) * (1 - ↑x) ^ (v - 1)`. Then `Complex.Gamma_mul_Gamma_eq_betaIntegral` (re > 0), `Complex.ofReal_cpow` (needs `0 ≤ x` and `0 ≤ 1 − x` on [0,1], with an a.e. or `uIcc` congruence), `intervalIntegral.integral_ofReal`, `Complex.Gamma_ofReal`, and Γ(a+b) ≠ 0.

**E6c `LineMomentValuesFacts`.**
- TRUE. ∫(1+u²)^{−2/3} = B(1/2, 1/6) = √π Γ(1/6)/Γ(2/3) (`Real.Gamma_one_half_eq`). ∫|u+u²|^{−2/3} = 3B(1/3, 1/3) = 3Γ(1/3)²/Γ(2/3).
- Route correct: the piece maps u ↦ −1−u and u ↦ −u preserve |u(1+u)|. Complete with NIT 2.

**E7 `gammaSixth`.** Proved and axiom-clean (re-elaborated in `T2.lean`).

## Verdict
Fix BLOCKER 1 first (rename `NormalFormFacts` in all three places), then the parts can go to proof agents as they stand. Every Prop E1, E2, E3, E5, E6a, E6b, E6c is true as stated, the routes are mathematically correct, and the assembly suffices. Before dispatch, also correct the route's lemma names (MINOR 1) and add the notes in MINOR 2 to 5 for the E3 agent.
