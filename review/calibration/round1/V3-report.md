<!-- Calibration round 1, referee for V3; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V3

# Statement review, calibration round 1 (V3)

I read only `Statements.lean` and `statements.md` in my directory. `Statements.lean` compiles cleanly. I also compiled one scratch file, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V3/Check.lean`, with `pp.parens`. It confirms how Lean parses the three bounds:
- `(3 / ν) * (…)`
- `(8 / √μ) * (ampNorm …)`
- `(18 * (μ ^ ((-1) / 3))) * (ampNorm …)`, with `-(1:ℝ)/3 = -1/3`.

## Shared definitions (all three statements)

These match the "Common notation" paragraph of S1:
- `HasDerivOn f f' a b := ContinuousOn f (Icc a b) ∧ ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x`
- `AmplitudeOn`: continuity on `Icc`, `HasDerivAt` on `Ioo`, and `IntervalIntegrable ψ' volume a b`
- `oscInt φ ψ a b = ∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * ψ x`
- `ampNorm ψ ψ' a b = ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖`

Vacuity checks on the definitions:
- **Integrands are integrable**, so Lean's "integral of a non-integrable function is 0" convention is never used. `ψ` and `exp(iφ)` are continuous on `Icc a b`, so `oscInt` and `∫‖ψ‖` are genuine integrals. `ψ'` is assumed interval-integrable, so `∫‖ψ'‖` is genuine too.
- **Orientation:** `a ≤ b` is assumed everywhere, so the oriented integral is the ordinary one.
- **Degenerate case `a = b`:** the hypotheses on `Ioo a b` are vacuous and the conclusion reads `0 ≤ c·‖ψ b‖`, which is true. It is harmless.
- **Endpoint values:** the values of `ψ'` at the endpoints sit on a null set and play no role. `‖ψ b‖` is the value at the endpoint, as the mathematics intends.
- **No hidden conventions reached:** `ν` and `μ` are strictly positive, so `x/0`, `√` of a negative number and `rpow` of a non-positive base never occur.
- **Satisfiable:** `sanity_hypotheses_satisfiable` exhibits non-degenerate data meeting all three hypothesis sets.
- **Quantifier order:** every variable is universally quantified up front and the constants are numerals. This matches the spec.

---

## VdC1Statement

**Verdict: UNFAITHFUL.** Logically it is a strictly weaker conclusion than S1.1, but the weakening is undocumented and the result is not the stated theorem.

The spec (S1.1) says |I(φ, ψ; a, b)| ≤ (3/ν) · A(ψ; a, b). The Lean conclusion is:

```lean
‖oscInt φ ψ a b‖ ≤ 3 / ν * (ampNorm ψ ψ' a b + ∫ x in a..b, ‖ψ x‖)
```

**Findings**

- **BLOCKER.** `3 / ν * (ampNorm ψ ψ' a b + ∫ x in a..b, ‖ψ x‖)` adds the term `(3/ν)·∫_a^b |ψ|`, which neither `statements.md` nor the Lean header mentions. (The header describes `ampNorm` alone as the amplitude norm.)
  - **It is strictly weaker than S1.1.** Since `∫‖ψ‖ ≥ 0`, the spec implies the Lean statement, but not the other way round.
  - **It is trivially true whenever `ν ≤ 3`,** with no use of monotonicity or of the lower bound on `|φ′|`:
    - `‖oscInt‖ ≤ ∫‖exp(iφ)ψ‖ = ∫‖ψ‖`, because the norm of an integral is at most the integral of the norm and `‖exp(iθ)‖ = 1`;
    - and `∫‖ψ‖ ≤ (3/ν)∫‖ψ‖ ≤ RHS`.
  - **It has the wrong scaling.** `∫|ψ|` carries a length while `|ψ(b)| + ∫|ψ′|` does not, so the bound no longer scales like van der Corput. Dilating `[a, b]` by `L` multiplies `(3/ν)∫|ψ|` by `L²` while `|I|` grows only like `L`, so the extra term makes the bound useless on long intervals.
  - **Fix:** the conclusion should be `‖oscInt φ ψ a b‖ ≤ 3 / ν * ampNorm ψ ψ' a b`.
- **MINOR.** `(MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b))` matches the spec's "nondecreasing or nonincreasing on (a, b)". Combined with `HasDerivOn φ' φ'' a b`, monotonicity extends to `[a, b]` by continuity, so nothing is lost. I note it only to confirm it was checked.
- **NIT.** `φ''` is used only through `HasDerivOn φ' φ'' a b`. This matches the documented modelling choice that S1.1 assumes φ′ differentiable on (a, b), which is weaker than Stein, and it is disclosed in both files.

---

## VdC2Statement

**Verdict: FAITHFUL.**

The Lean conclusion is:

```lean
‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ 8 / √μ * ampNorm ψ ψ' a b
```

It parses as `(8/√μ) * ampNorm`, which is exactly (8/√μ)·A(ψ; a, b) with φ_p(x) = φ(x) + p x.

The hypotheses also match S1.2:
- `HasDerivOn φ φ' a b`
- `HasDerivOn φ' φ'' a b`
- `∀ x ∈ Ioo a b, μ ≤ |φ'' x|`
- `AmplitudeOn ψ ψ' a b`
- `0 < μ`, `a ≤ b`, and `p` quantified universally

They constrain only φ, as the spec intends. They are jointly satisfiable, and `√μ > 0` under `0 < μ`.

**Findings**

- **NIT.** In `↑(φ x + p * x)` the coercion is applied to the real sum, which is the intended real phase. No issue.
- **NIT.** `|φ''| ≥ μ` on `(a, b)`, together with φ″ being a derivative (Darboux), forces constant sign, as in the standard proof. Nothing is missing.

---

## VdC3Statement

**Verdict: FAITHFUL.**

The Lean conclusion is:

```lean
‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ 18 * μ ^ (-(1 : ℝ) / 3) * ampNorm ψ ψ' a b
```

It parses as `(18 * μ^(-1/3)) * ampNorm`. This is `Real.rpow` with exponent −1/3, and the base `μ > 0`, so it is genuinely μ^{−1/3}.

The hypotheses are:
- `HasDerivOn φ φ' a b`
- `HasDerivOn φ' φ'' a b`
- `HasDerivOn φ'' φ''' a b`
- `∀ x ∈ Ioo a b, μ ≤ |φ''' x|`
- the amplitude hypothesis and the linear term `p`

This matches "As S1.2 with additionally φ″ having derivative φ‴ … in place of the bound on φ″". The bound on φ″ is correctly dropped.

**Findings**

- **NIT.** `-(1 : ℝ) / 3` is `(-1)/3`, not `-(1/3)`. The two are equal, so there is no issue. (Checked by `norm_num` in the scratch file.)

---

## Summary

| Statement | Verdict | Worst finding |
|---|---|---|
| VdC1Statement | UNFAITHFUL (weaker than spec; undocumented) | BLOCKER: the term `+ ∫ x in a..b, ‖ψ x‖` is not in S1.1; it makes the statement trivially true for ν ≤ 3 and gives it the wrong scaling |
| VdC2Statement | FAITHFUL | NIT only |
| VdC3Statement | FAITHFUL | NIT only |
