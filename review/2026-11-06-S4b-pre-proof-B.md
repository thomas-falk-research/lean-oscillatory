<!-- Blind pre-proof review of S4.1', S4.2, S4.3, S4.4, referee B (fresh-context agent, prompt review/prompts/S4b-pre-proof.md), commit ad8e7fd. Verbatim final report. -->

`git rev-parse HEAD` = `ad8e7fd18e2c2bbbb8e06008664e0825234f0950`

# Referee B: blind pre-proof review of S4.1′, S4.2, S4.3, S4.4

## Summary

All four statements are **TRUE** and **FAITHFUL** to `docs/statements.md`. Against the brief, they are FAITHFUL-STRONGER: the hypothesis is widened to `disc ≠ 0`, and S4.3 proves `> 0` where the brief asks for `≠ 0`. Together, S4.2 and S4.4 give the brief's limit with the brief's constant.

- No BLOCKER and no MAJOR findings.
- Two MINOR findings: the "Gamma-free proof" rule exists only as a process rule, and the brief's statement only exists as the pair S4.2 + S4.4.

## What I did

- Read the allowed files.
- Ran `numerics/target/release/d4const`. Result: PASS throughout. I also read its source.
- Compiled one scratch file, `/tmp/refereeB/check.lean`, with `nice -n 10 lake env lean`. It did four things:
  - Collected every constant reachable from the statements, both through definitions only and through theorem proofs as well.
  - Checked the axioms of the sanity lemmas: `propext`, `Classical.choice`, `Quot.sound` only.
  - Printed the elaborated S4.4. Every `1/3`, `2/3`, `1/6` is ℝ-valued and every power is `Real.rpow`.
  - Recomputed `disc` for (1,0,−3,0) = 108, (0,1,0,1) = −4 and (1,0,0,1) = −27.

## Verdicts

| Statement | vs `docs/statements.md` | vs the brief | True? |
|---|---|---|---|
| `D4BoundNeStatement` (S4.1′) | FAITHFUL | FAITHFUL-STRONGER (`disc ≠ 0` ⊇ `disc < 0`) | TRUE |
| `D4LimitStatement` (S4.2) | FAITHFUL | FAITHFUL-STRONGER (`disc ≠ 0`); the constant matches the brief's through S4.4 | TRUE |
| `D4ConstantPosStatement` (S4.3) | FAITHFUL | FAITHFUL-STRONGER (convergence and `> 0` instead of `≠ 0`); the proof-method rule is not encoded (MINOR 1) | TRUE |
| `D4ConstantClosedFormStatement` (S4.4) | FAITHFUL | FAITHFUL; for `Disc < 0` it is exactly the brief's formula | TRUE |

### Why each is true

**S4.1′.** This is the classical uniform t^{−2/3} bound for D4±, uniform in linear terms.

- The S3 hypothesis holds on annuli for the rescaled cubic:
  - For Disc > 0, the Hessian determinant of C is a negative definite quadratic, for example −36|w|² for x³ − 3xy², so it is nondegenerate off 0.
  - For Disc < 0 there are rank-one lines, and the third derivative along the kernel is nonzero, for example ∂₁₁₁(x³ + y³) = 6 on x = 0.
- Both conditions are open, so they survive for ε small.

**S4.2.** Substitute z = t^{−1/3}w.

- On |w| ≤ R the integrand converges to e^{iC(w)}A(0), using φ(0) = 0, ∇φ(0) = 0, D²φ(0) = 0 and φ ∈ C⁴.
- For |w| ≥ R, take dyadic annuli at scale ε. S2.1 with N = 2 applies: the amplitude is C², and ε^{−2}∇φ(εw) → ∇C(w) with |∇C| ≥ c on the annulus because Disc ≠ 0. Each annulus contributes ≲ ε²(tε³)^{−2}. After multiplying by t^{2/3}, the tail is ≲ R^{−4}, uniformly in t.
- The limit is therefore A(0)·∫e^{iC}, taken with dyadic cut-offs, and that equals I·J/3 by the polar computation. Only the cubic part matters.
- δ depends only on φ. It is chosen so that 0 is the only critical point in B̄(0, δ), and so that the amplitude may touch ∂B̄(0, δ).

## The constant

**Polar derivation (checked).** Write C(rθ) = r³C(θ) and u = t|C(θ)|r³. Then r dr = (1/3)(t|C(θ)|)^{−2/3}u^{−1/3}du, so

∫₀^∞ e^{itr³C(θ)} r dr = (1/3)t^{−2/3}|C(θ)|^{−2/3}(I + i·sgn C(θ)·S).

- C(θ+π) = −C(θ), so ∫ sgn C·|C|^{−2/3} dθ = 0 and the sine part cancels.
- This gives c_C = I·J/3, which is `cosMoment * angularMoment q / 3`. The factor 1/3 and the exponents −1/3 and −2/3 are right.

**Closed forms (checked by hand, independently of the probe).**

- I = Γ(2/3)cos(π/3) = Γ(2/3)/2.
- For x³ + y³: J = 2∫_ℝ|1+t³|^{−2/3}dt = 2B(1/3,1/3) = 2Γ(1/3)²/Γ(2/3).
  - Each of the three pieces (0,∞), (−1,0) and (−∞,−1) equals B(1/3,1/3)/3.
  - So c = Γ(1/3)²/3, and the brief's formula gives the same value: √3·27^{1/6} = 3.
- For x³ − 3xy²: on the circle C = cos 3θ, and J = ∫|sin θ|^{−2/3} = 2√π Γ(1/6)/Γ(2/3).
  - So c = √π Γ(1/6)/3 = Γ(1/3)²/108^{1/6}, using Γ(1/6) = 2^{−1/3}(3/π)^{1/2}Γ(1/3)². I checked that identity numerically (5.5663).
  - Disc = 108 > 0, and the statement correctly has no √3 in this case.
- Covariance: Disc(λC∘L) = λ⁴ det(L)⁶ Disc(C), and c scales by |λ|^{−2/3}|det L|^{−1}. Both closed forms scale the same way, and GL₂ acts transitively on each sign class. So the two normal forms prove S4.4 in general.
- The probe agrees to about 7e-15 on eight cubics.
- The `disc` normalisation is the standard one. With it, Disc < 0 means one real line (D4⁺) and the √3 belongs to that case. This matches the brief.

**Junk values: none reachable.**

- `cosMomentPartial R` integrates an integrable function (u^{−1/3} near 0, exponent > −1). Its value at u = 0 is `0 ^ (-1/3) = 0`, on a null set. Negative bases only arise for R < 0, which `atTop` ignores.
- `limUnder` equals the real limit because the limit exists, and S4.3 asserts that it exists.
- `angularMoment` is 0, a junk value, only when the integrand is not integrable, that is a repeated real factor or C ≡ 0. Both have `disc = 0`, which every statement excludes. With simple roots the singularities are |θ−θ₀|^{−2/3}, which is integrable, and the zeros of |C| are a finite set.
- So no statement is trivially true or false.

**S4.3 is Gamma-free as a statement (mechanically checked).**

| Closure of | Following | Constants reached | Names containing `Gamma`, `mellin` or `Beta` |
|---|---|---|---|
| `D4ConstantPosStatement` | definitions only | 4,677 | 0 |
| `D4ConstantPosStatement` | definitions and theorem proofs | 33,082 | 0 |
| `D4LimitStatement` | definitions only | 5,370 | 0 |
| `D4LimitStatement` | definitions and theorem proofs | 33,620 | 0 |
| `d4Constant` | definitions only | 4,654 | 0 |
| `d4Constant` | definitions and theorem proofs | 33,074 | 0 |

## Conventions and vacuity

- `t ^ ((2:ℝ)/3)` is only used as t → ∞.
- The real-to-complex coercions `((t ^ _ : ℝ) : ℂ)` and `(d4Constant _ : ℂ) * A 0` are correct.
- `fderiv ℝ φ 0 = 0` together with `φ 0 = 0` is needed for the limit to be true. Without them there is a phase e^{itφ(0)} or a non-stationary point at 0.
- The quantifier order `∃ δ > 0, ∀ A M` is right: δ depends on φ only.
- `∀ M` with `AmpBound` acts only as a regularity and support condition, and every C² compactly supported A has some M.
- `oscInt2` is integrable under `AmpBound`.
- The hypotheses are satisfiable for both signs (`sanity_D4Limit_hyps`, `sanity_D4Limit_hyps_elliptic`). Since c_C > 0, the conclusion is non-trivial whenever A(0) ≠ 0.

## Question 4: is the encoding faithful?

Yes, on both counts.

- **Defining c_C by I·J/3.** With the closed form as the definition, the brief's "c_C ≠ 0 by alternating series, without Gamma" would be empty. S4.4 then links the definition to the brief's constant.
- **Widening to `disc ≠ 0`.** For a binary cubic, `disc ≠ 0` is exactly "isolated critical point at 0". The brief's "negative discriminant" is still covered by S4.1 and by the `disc < 0` clause of S4.4.

## Findings

**MINOR 1 (S4.3: the proof-method rule is not encoded).** The brief requires that "the proof must not use [Gamma/Mellin] (checked mechanically once proved)". Nothing in `def D4ConstantPosStatement : Prop := …` enforces this. A proof that runs through S4.4 and `Real.Gamma_pos_of_pos` would satisfy the Lean statement.

- Fix the check now: a forbidden-name list (at least `Real.Gamma`, `Complex.Gamma`, `Complex.betaIntegral`, `mellin`, `Real.GammaIntegral`) and the scope of the check (transitive through proofs).
- The transitive baseline of the statement is already clean (0 of 33,082 constants), so a transitive check of the proof is meaningful.
- Decide in advance what happens if a generic Mathlib lemma pulls in Gamma transitively.

**MINOR 2 (the brief's S4 is only the pair S4.2 ∧ S4.4).** `D4LimitStatement` states the limit with `d4Constant`, not with `Γ(1/3)²/(√3|Disc|^{1/6})`. Any claim that "the brief's limit is machine-checked" must cite both S4.2 and S4.4 (and S4.3 for ≠ 0). I suggest saying this in the status map.

**NIT 3 (numerics coverage).** `limit2d` only tests homogeneous cubic phases and the even amplitude `bump ⊗ bump`.

- The Richardson step assumes a t^{−2/3} correction. That is right for even A. For a general A, the linear Taylor term gives a t^{−1/3} correction.
- No probe uses φ with quartic terms. My scaling argument above covers both cases, but the validation does not.

**NIT 4 (S4.3 proof risk, not a statement defect).** The required inequality a₀ + a₁ > 0 has a margin of 0.0901 on a₀ ≈ 1.471, about 6%. a₀ and a₁ are integrals over intervals of different lengths, so the shift-by-π monotonicity does not give it. The proof will need explicit, certified bounds on both integrals. The modulus decrease for k ≥ 1 does follow from the shift argument.

**NIT 5.** `d4Constant` is 0 when `disc = 0`, a junk value of the non-integrable `angularMoment`. It is unreachable under every hypothesis. A docstring note would stop a later reader from citing `d4Constant` for degenerate cubics.

**NIT 6.** S4.2 is only a limit, with no rate and no uniformity in A or in a linear term. This is consistent with the brief; it is already noted under "Modelling choices".

I wrote nothing in the repository; the scratch file is `/tmp/refereeB/check.lean`.