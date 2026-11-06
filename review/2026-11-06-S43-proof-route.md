<!-- Route referee for S4.3 (fresh-context agent, prompt review/prompts/S43-proof-route.md), commit a348412. Verbatim final report. -->

`a3484126e77d64008c0b79de285eca22ce06044d`

# S4.3 proof route and blueprint review (commit a348412)

I read these files at a348412: `docs/statements.md` (S4), `OscInt/Statements/D4Limit.lean`, `docs/proof-S43.md`, `Blueprint/D4Limit.lean`, `OscInt/D4/ConstantPos.lean` and `GammaFree.lean`, plus the Mathlib sources under `/home/user/lean-oscillatory/.lake/packages/mathlib/Mathlib`. I did not compile anything and wrote nothing in the repository.

**Verdict: yes. C1–C5 can go to proof agents as they stand.** All five are true as stated in Lean. The route's argument is correct for each one. Each can be proved with Mathlib lemmas whose proofs do not go through Gamma, Beta or Mellin. I found no BLOCKER and no MAJOR.

## Truth of each part as stated in Lean

**C1 (`CosIBPFacts`): TRUE.**
- `R > 0`, so only `u ∈ [0, R]` occurs. The negative-base branch of `rpow` never arises.
- At `u = 0`, `0 ^ (-(1:ℝ)/3) = 0` and `0 ^ (-(4:ℝ)/3) = 0` (`Real.zero_rpow`). This affects a null set only.
- Parsing: `(1 / 3) * ∫ u in (0 : ℝ)..R, …` is `(1/3) * (∫ …)`, and `-(4 : ℝ) / 3` is `-4/3`.
- Both integrands are integrable on (0, R): `|sin u| ≤ |u|` (`Real.abs_sin_le_abs`) gives `|sin u · u^{-4/3}| ≤ u^{-1/3}`.
- With `f u = sin u * u^(-1/3)`, Lean's value `f 0 = 0` equals the right limit, since `|f u| ≤ u^{2/3}`. So `f` is continuous on `Icc 0 R` and the identity holds exactly.

**C2 (`SinMomentFacts`): TRUE.**
- The integrand is integrable on `Ioi 0`: bounded by `u^{-1/3}` on (0, 1] and by `u^{-4/3}` on [1, ∞).
- The integral is positive by the hump pairing. Each `b_k = ∫_{2kπ}^{2kπ+π} sin u (u^{-4/3} − (u+π)^{-4/3}) du` has an integrand that is positive and continuous on the open interval, so `b_k > 0`. For `k = 0` the integrand is integrable near 0 because each term is.
- `R → ∞` along `atTop`, so values for `R < 0` (negative-base `rpow`) do not matter.

**C3 (`CircleNondegFacts`): TRUE.**
- `circleCubic q` is a polynomial in cos and sin, hence differentiable everywhere. So `deriv` is the real derivative, not a junk value.
- If `g(θ) = g′(θ) = 0`, then `∇C(ω)·ω⊥ = 0` and, by Euler, `∇C(ω)·ω = 3C(ω) = 0`. Hence `∇C(ω) = 0` at `ω ≠ 0`, which forces `disc q = 0`.
- `q = 0` is excluded because `disc 0 = 0`.

**C4 (`SingularPowerFacts`): TRUE.**
- With `ContDiff ℝ 1 g`, `deriv g x` is the real two-sided derivative, including at `a` and `b`.
- The zeros in `[a, b]` are isolated, so finitely many by compactness. Near a zero `x₀`, `|g x| ≥ c|x − x₀|`, and `α < 1` makes the bound integrable. Away from zeros `|g|` is bounded below.
- Edge cases: `α = 0` gives `|g x|^0 = 1` everywhere (`0^0 = 1`), which is integrable. `a = b` is trivial.
- Measurability follows from continuity of `g` and measurability of `rpow` in its first argument.
- The hypothesis `a ≤ b` fixes the orientation. Using `IntervalIntegrable` rather than `IntegrableOn` causes no gap: `uIoc a b = Ioc a b`.

**C5 (`AngularPosFacts`): TRUE.**
- The integrand is `≥ 0` everywhere (`Real.rpow_nonneg`). It equals 0 exactly where `g = 0` (`0^(-2/3) = 0`) and is `> 0` elsewhere.
- `disc q ≠ 0` implies `q ≠ 0`, and then `g` is nonzero at one of θ = π/4, π/2, 3π/4, π, all inside `(0, 2π)`. If C vanished at all four, then d = 0, a = 0 and b ± c = 0, so q = 0.
- By continuity the support contains an open interval, so `intervalIntegral.integral_pos_iff_support_of_nonneg_ae` applies.
- `angularMoment` is written with `cubicForm` and C5 with `circleCubic`; these are definitionally equal, and the assembly already checks this.

**Assembly.** `d4ConstantPos_of` is already checked by Lean. Its use of `Tendsto.limUnder_eq`, `tendsto_rpow_neg_atTop` and `positivity` is sound.

## Is the route an "alternating-series argument"?

**Yes, in substance.** After the integration by parts, the hump integrals `a_k = ∫_{kπ}^{(k+1)π} sin u · u^{-4/3} du` alternate in sign. Their size decreases, because `u^{-4/3}` decreases and `sin(u+π) = −sin u`. Grouping consecutive pairs (`b_k = a_{2k} + a_{2k+1} > 0`) is the standard Leibniz alternating-series argument. It is applied to `S`, and `cosMoment = S/3` then proves the brief's `∫₀^∞ cos u · u^{-1/3} du > 0`.

Integration by parts is not a Mellin or Gamma identity. The route is also stronger than the direct cosine-hump version: it needs no numerical bound for `a₀ + a₁ > 0`.

It does differ from the method text in statements.md; see the first MINOR below.

## Gamma-freeness and the Mathlib lemmas a prover will likely need

These are the lemmas I expect a prover to use. I read the proofs of each one marked "(proof read)": each is elementary (fundamental theorem of calculus, rpow derivatives, `integrableOn_deriv_of_nonneg`), and none uses a Gamma, Beta or Mellin constant.

- `intervalIntegral.intervalIntegrable_rpow'` (proof read)
- `intervalIntegral.integrableOn_Ioo_rpow_iff` (proof read)
- `integrableOn_Ioi_rpow_of_lt` (proof read; via `integrableOn_add_rpow_Ioi_of_lt`)
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`
- `Real.hasDerivAt_rpow_const`
- `intervalIntegral.intervalIntegral_pos_of_pos_on`, `intervalIntegral.integral_pos_iff_support_of_nonneg_ae`
- `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`
- `intervalIntegral.sum_integral_adjacent_intervals`, `intervalIntegral.integral_comp_add_right`
- `Real.abs_sin_le_abs`, `Real.sin_le`, `Real.abs_sin_le_one`

Imports alone are irrelevant here: `GammaFree.lean` follows used constants, not imports. A text search for `Gamma|Beta|mellin|Mellin` found no hits in:
- `MeasureTheory/Function/Jacobian*.lean`, `MeasureTheory/Covering/*`, `MeasureTheory/Integral/IntervalIntegral/*`, `IntegralEqImproper.lean`
- `Analysis/SpecialFunctions/{Integrability/*, ImproperIntegrals.lean, Pow/*, Integrals/Basic.lean}`, `MeasureTheory/Measure/Haar/*`

The only hit among the files searched was `MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`. Nothing on this route should need it.

## Findings

**MINOR 1 (method text drift).** The stamped S4.3 text in `docs/statements.md` names a different decomposition:

> "by the alternating-series argument of the brief: on [π/2 + (k−1)π, π/2 + kπ] the integrals alternate in sign with decreasing modulus and ∫₀^{π/2} + ∫_{π/2}^{3π/2} > 0"

The route instead pairs the humps of the sine moment after integration by parts (`docs/proof-S43.md` C2; `Blueprint/D4Limit.lean` `SinMomentFacts` docstring). The Lean statement is unaffected, and the brief's requirement and the `GammaFree.lean` check are both met. Still, the change should be recorded as a dated clarification or decision, so that a referee checking against statements.md does not see the method as substituted. The `D4Limit.lean` module doc says "(the brief's alternating-series argument …)", which is fine.

**MINOR 2 (C1: which Lean lemma to use).** proof-S43.md says "Integration by parts on [ε, R] … then ε → 0⁺". A prover should not use `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. It needs `HasDerivAt` on all of `uIcc 0 R`, which fails at 0 because `u^(-1/3)` is not differentiable there.

The simpler route is `integral_eq_sub_of_hasDerivAt_of_le` with:
- `f u = Real.sin u * u ^ (-(1:ℝ)/3)`;
- `ContinuousOn f (Icc 0 R)`, which holds since Lean's `f 0 = 0` matches the limit;
- `HasDerivAt` only on `Ioo 0 R`.

Then split the result with `integral_sub`. Alternatively, `integral_eq_sub_of_hasDerivAt_of_tendsto` takes the limit at 0⁺ directly. No ε-limit of integrals is needed.

**MINOR 3 (C4: Lean sketch).** `integrableOn_image_iff_integrableOn_abs_deriv_smul` gives integrability of `x ↦ |g' x| • |g x|^(-α)` on the piece. To get back to `|g x|^(-α)`, the prover still needs the domination `|g x|^(-α) ≤ c⁻¹ · |g' x| · |g x|^(-α)` from `|g'| ≥ c` (`Integrable.mono'`). That step is not in the sketch. Two further points:
- Mathlib states the base lemma for `x ^ r` (`intervalIntegrable_rpow'`), not for `|x| ^ r`; the absolute-value version takes a small extra step.
- The change-of-variables route pulls in the n-dimensional Jacobian and Besicovitch machinery. The text search found no forbidden names there, but the transitive constant closure is unchecked.

Bounding directly by `c^{-α} |x − x₀|^{-α}` near each zero avoids that machinery and is likely shorter.

**MINOR 4 (C3: unchecked dependency).** proof-S43.md relies on "the algebraic lemma `OscInt.D4.GaugeAux.disc_eq_zero` with z = v = ω". The brief forbade reading other proof files, so I did not check that its hypotheses take this form. If they do not, the needed fact (`∇C(ω) = 0`, `ω ≠ 0` ⇒ `disc q = 0`) can be proved directly with `linear_combination`, using the resultant identity Res(C_x, C_y) ∝ Disc. It is a finite algebraic fact either way.

**NIT 1.** proof-S43.md C3 does more than needed: `∇C(ω) = 0` at `ω ≠ 0` already forces Disc = 0, and the Hessian step is only needed to fit `disc_eq_zero`'s interface.

**NIT 2.** The forbidden-name rule in `GammaFree.lean` is a case-sensitive substring match on name components: `(s.splitOn p).length > 1` for `"Gamma"`, `"Beta"`, and so on. In principle it could reject a harmless constant such as `Lean.Expr.headBeta` if a proof term ever embedded meta code. This is unlikely with `ring`, `norm_num`, `positivity` or `fun_prop` terms, and the baseline and assembly already pass. If such a failure ever appears, check whether it is a false positive before restructuring the proof.

No orientation issue appears anywhere: every interval has `a ≤ b` (`0 < R`, `0 ≤ 2π`, the explicit `a ≤ b` in C4).

**Verdict: C1–C5 can go to proof agents as they stand.** Record MINOR 1 as a clarification, and pass MINOR 2 and MINOR 3 to the provers as guidance.