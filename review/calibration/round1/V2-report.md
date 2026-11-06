<!-- Calibration round 1, referee for V2; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V2

# Statement review: V2 (calibration round 1)

**Scope.** I read only `V2/Statements.lean`, `V2/statements.md` and Mathlib sources. I compiled a scratch copy, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V2/Check.lean` (the file plus `#print` checks), with Mathlib only.
- It compiles without errors.
- `sanity_hypotheses_satisfiable` depends only on `[propext, Classical.choice, Quot.sound]`.
- Mathlib has no `HasDerivOn`, so the local definition shadows nothing.
- The pretty-printed `VdC3Statement` reads `18 * μ ^ (-1 / 3) * ampNorm ψ ψ' a b`. The exponent is a real number, and `example : (-(1 : ℝ) / 3) = -(1/3)` checks.
- `HasDerivAt ψ (ψ' x) x` takes its derivative over ℝ (`HasDerivAt Real … Complex`), as intended.

## Checks that apply to all three statements

**Definitions.**
- `HasDerivOn f f' a b := ContinuousOn f (Icc a b) ∧ ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x` matches "has derivative on [a, b]" in the md: continuous on the closed interval, differentiable at every point of the open interval, and the values f′(a), f′(b) are unused.
- `AmplitudeOn` is that same definition for a complex ψ, plus `IntervalIntegrable ψ' volume a b`. This matches the md's amplitude hypothesis.
- `oscInt φ ψ a b = ∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * ψ x` is I(φ, ψ; a, b).
- `ampNorm ψ ψ' a b = ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖` is A(ψ; a, b).

**Lean conventions do not collapse anything.**
- *Oriented integral:* every statement assumes `a ≤ b`, so `∫ x in a..b` is the integral over `Ioc a b`, i.e. over [a, b].
- *Integrability of `oscInt`'s integrand:* φ and ψ are continuous on `Icc a b`, so the integrand is continuous there and integrable. The "non-integrable gives 0" trap cannot occur.
- *Integrability of `‖ψ'‖`:* it is integrable because `IntervalIntegrable ψ'` is assumed. Without that hypothesis the integral would be 0 and the bound false, as the header says.
- *Endpoint value `ψ b`:* it is meaningful because ψ is continuous on the closed interval.
- *Division, `Real.sqrt`, `rpow`:* `3 / ν`, `8 / √μ` and `μ ^ (-(1:ℝ)/3)` appear only under `0 < ν` or `0 < μ`, so no zero-division, square-root or rpow convention is triggered.
- *Parsing:* `3 / ν * ampNorm …` parses as (3/ν)·A, and `8 / √μ * ampNorm …` as (8/√μ)·A.

**Mathematical soundness of the hypotheses.** ψ is continuous on [a, b], differentiable at *every* point of (a, b), and has an integrable derivative. Mathlib's FTC (`integral_eq_sub_of_hasDerivAt_of_le`) then applies. So the integration by parts ∫ e^{iφ}ψ = F(b)ψ(b) − ∫ F ψ′, with F(x) = ∫_a^x e^{iφ}, is valid. A Cantor-type amplitude is excluded because differentiability is required everywhere, not almost everywhere. The hypotheses carry over to every subinterval [a, x], so the plain bound applies to F(x). The theorems are therefore true with the stated constants, which follow Stein's c₁ = 3, c₂ = 8 = 2·3 + 2, c₃ = 18 = 2·8 + 2.

**Vacuity.**
- The hypotheses can be met together, and not only degenerately: `sanity_hypotheses_satisfiable` shows φ = x³/6 + x²/2 + x on [0, 1] with ψ = 1 satisfies every hypothesis set.
- The case a = b is harmless: the interval (a, b) is empty, the integral is 0, and 0 ≤ the right-hand side.
- The conclusions are non-trivial in general: the left side can be of size b − a, while the right side is fixed.
- Quantifier order: all variables are universally quantified up front, and every constant is a numeral. There is no ∃ and no dependence of a constant on the data.

## VdC1Statement

**Verdict: FAITHFUL.**
- The hypotheses match S1.1 one for one: `a ≤ b`, `0 < ν`, `HasDerivOn φ φ' a b`, `HasDerivOn φ' φ'' a b`, `(MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b))`, `(∀ x ∈ Ioo a b, ν ≤ |φ' x|)` and `AmplitudeOn ψ ψ' a b`.
- The conclusion `‖oscInt φ ψ a b‖ ≤ 3 / ν * ampNorm ψ ψ' a b` matches, and there is no linear term, as in the md.
- Relative to Stein this theorem is weaker, because it requires φ′ to be differentiable. The md declares this choice and its post-stamp clarification states the consequence.

**Vacuity:** none found.

**Findings.**
- NIT: `φ''` in `HasDerivOn φ' φ'' a b` appears nowhere else in the statement. It acts only as an existential witness that φ′ is differentiable on (a, b) and continuous on [a, b]. This is fine and matches the md.

## VdC2Statement

**Verdict: FAITHFUL.**
- The hypotheses match S1.2: the derivative chain to φ″, `(∀ x ∈ Ioo a b, μ ≤ |φ'' x|)`, and the amplitude hypothesis.
- `p` is universally quantified, the hypotheses concern φ alone, and the conclusion is `‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ 8 / √μ * ampNorm ψ ψ' a b`.
- No monotonicity hypothesis is needed. A derivative has the intermediate-value (Darboux) property, so φ″ has constant sign on (a, b) and φ′ is monotone; the md has no such hypothesis either.
- The linear term is harmless: φ_p satisfies the same hypotheses with φ_p′ = φ′ + p and φ_p″ = φ″.

**Vacuity:** none found.

**Findings.** None beyond the shared NIT below.

## VdC3Statement

**Verdict: FAITHFUL.**
- The hypotheses match S1.3, which is S1.2 plus `HasDerivOn φ'' φ''' a b`, with `(∀ x ∈ Ioo a b, μ ≤ |φ''' x|)` replacing the bound on φ″. No bound on φ″ is kept, as "in place of" requires.
- The conclusion `18 * μ ^ (-(1 : ℝ) / 3) * ampNorm ψ ψ' a b` matches 18 μ^{−1/3}·A.
- `-(1 : ℝ) / 3` is (−1)/3, the real number −1/3. It is not natural-number or integer division, and it is not `-(1/3)` evaluated in ℕ.

**Vacuity:** none found.

**Findings.**
- NIT: `φ''` does double duty: it is the derivative of φ′ and must also be continuous on [a, b] and differentiable on (a, b). This is intended, and the md lists it among the modelling choices.

## Shared minor findings

- NIT: the header says "Mathematics: `docs/statements.md`, S1", but the review copy is `statements.md`. This affects only the documentation reference.
- NIT: `theorem statement_pin_VdCk : VdCkStatement = VdCkStatement := rfl` is a tautology and checks nothing about content. It is harmless; presumably it exists to pin the names.

## Summary

| Statement | Verdict | BLOCKER | MAJOR | MINOR | NIT |
|---|---|---|---|---|---|
| VdC1Statement | FAITHFUL | 0 | 0 | 0 | 1 |
| VdC2Statement | FAITHFUL | 0 | 0 | 0 | 0 (shared only) |
| VdC3Statement | FAITHFUL | 0 | 0 | 0 | 1 |

I found no planted error. Hypotheses, constants (3, 8, 18), exponents (ν^{−1}, μ^{−1/2}, μ^{−1/3}), the amplitude norm, the integral's orientation, open versus closed intervals, the placement of the linear term and the quantifier order all agree with S1 of `statements.md`.