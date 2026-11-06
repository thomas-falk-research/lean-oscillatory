<!-- Calibration round 1, referee for V1; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V1

# Statement review, calibration round 1: directory V1

I read only `V1/Statements.lean`, `V1/statements.md` and Mathlib. `Statements.lean` compiles cleanly as given. Scratch files: `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V1/Disproof.lean` (Lean) plus a short inline Python numerical check.

## Main finding (affects all three statements)

**BLOCKER: `ampNorm` takes the norm of the integral, not the integral of the norm.**

```lean
noncomputable def ampNorm (ψ ψ' : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ‖ψ b‖ + ‖∫ x in a..b, ψ' x‖
```

statements.md defines A(ψ; a, b) = |ψ(b)| + ∫_a^b |ψ′(x)| dx. The file header (`ampNorm ψ ψ' a b = ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖`) and the docstring (`|ψ(b)| + ∫_a^b |ψ'(x)| dx`) say the same, but the definition does not.

- Under `AmplitudeOn`, the fundamental theorem of calculus (ψ continuous on [a, b], derivative on (a, b), ψ′ integrable) turns this into ‖ψ b‖ + ‖ψ b − ψ a‖. That quantity can be 0 while the oscillatory integral is not.
- **Counterexample:** [a, b] = [0, π], ψ = sin, ψ′ = cos. Then ampNorm = |sin π| + |sin π − sin 0| = 0, so every conclusion would require `oscInt … = 0`.
- **VdC1 is false, machine-checked.** In Disproof.lean, `theorem not_VdC1 : ¬ VdC1Statement` compiles with no `sorry` and no errors. It uses φ = id, φ′ = 1, φ″ = 0, ν = 1, ψ = sin. The imaginary part of `oscInt` is ∫₀^π sin² = π/2 ≠ 0.
- **VdC2 and VdC3 are false, not machine-checked.**
  - Analytic argument: with the same ψ and ampNorm = 0, the conclusion forces ∫₀^π e^{i(φ(x)+px)} sin x dx = 0 for every p ∈ ℝ. That says the Fourier transform of the nonzero L¹ function 1_[0,π] e^{iφ} sin is identically zero, which injectivity of the Fourier transform rules out. Any admissible φ works: φ = x²/2 with μ = 1 for VdC2, φ = x³/6 with μ = 1 for VdC3. (Strictly, for VdC3 φ‴ ≡ 1 only gives |φ‴| ≥ μ for μ ≤ 1; μ = 1 qualifies.)
  - Numerical check at p = 0 (midpoint rule): VdC2 gives I ≈ 0.332 + 1.035i, VdC3 gives I ≈ 0.918 + 0.870i. Both are nonzero, so a single p = 0 instance already refutes each.
- **The sanity theorems cannot catch this.** `sanity_amplitude_one` uses ψ′ ≡ 0, where ‖∫ψ′‖ = ∫‖ψ′‖ = 0.
- **Fix:** `‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖`.

## VdC1Statement

**Verdict: UNFAITHFUL.** It is strictly stronger than statements.md S1.1 and false (proved in Lean above).

Everything apart from `ampNorm` matches S1.1:
- quantifiers and order: φ, φ′, φ″, ψ, ψ′, a, b, ν are all universal and the constant is a numeral;
- `a ≤ b` and `0 < ν`;
- `HasDerivOn φ φ' a b` and `HasDerivOn φ' φ'' a b`;
- `(MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b))`;
- `(∀ x ∈ Ioo a b, ν ≤ |φ' x|)`;
- `AmplitudeOn`, which includes `IntervalIntegrable ψ' volume a b`;
- the constant `3 / ν`.

Vacuity hunt:
- The hypotheses can hold together; the sanity theorem and my counterexample both satisfy them.
- `3 / ν` only appears under `0 < ν`, so Lean's division by zero is never reached.
- `oscInt` uses the oriented integral under `a ≤ b`, which is the Lebesgue integral over [a, b], as intended.
- The integrand is continuous on [a, b], so it is integrable and the integral-of-non-integrable convention is never reached.
- The conclusion is not trivially true; it is false because of the BLOCKER.

Findings:
- **BLOCKER:** `‖∫ x in a..b, ψ' x‖` in `ampNorm` (see above).
- **NIT:** `HasDerivOn φ' φ'' a b` makes φ′ continuous on the closed interval [a, b]. statements.md states this as a deliberate modelling choice, so it is consistent.

## VdC2Statement

**Verdict: UNFAITHFUL.** It is stronger than S1.2 and false (analytic argument plus numerics above).

Everything apart from `ampNorm` matches S1.2:
- p is universally quantified up front;
- the phase is `fun x => φ x + p * x`;
- the lower bound is `(∀ x ∈ Ioo a b, μ ≤ |φ'' x|)` on φ alone;
- the constant is `8 / √μ`, which only appears under `0 < μ`, so `Real.sqrt` and division conventions are never reached.

Findings:
- **BLOCKER:** the same `ampNorm` defect.
- No other issues.

## VdC3Statement

**Verdict: UNFAITHFUL.** It is stronger than S1.3 and false.

Everything apart from `ampNorm` matches S1.3:
- the additional `HasDerivOn φ'' φ''' a b`;
- `(∀ x ∈ Ioo a b, μ ≤ |φ''' x|)`, which replaces the φ″ bound as S1.3 says;
- the constant is `18 * μ ^ (-(1 : ℝ) / 3)`. This parses as `μ ^ ((-1)/3)` = μ^{−1/3} via `Real.rpow`, and μ > 0, so the rpow conventions are not an issue.

Findings:
- **BLOCKER:** the same `ampNorm` defect.
- **NIT:** `-(1 : ℝ) / 3` is correct but reads ambiguously. `(-(1/3) : ℝ)` would be clearer.

## Summary

| Statement | Verdict | Blocking issue |
|---|---|---|
| VdC1Statement | UNFAITHFUL (false; disproved in Lean) | `ampNorm` uses `‖∫ ψ'‖` |
| VdC2Statement | UNFAITHFUL (false; analytic argument plus numerics) | same |
| VdC3Statement | UNFAITHFUL (false; analytic argument plus numerics) | same |

Fix `ampNorm` to `‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖`. After that change all three statements match S1 as far as I can see. I found no vacuity, convention collapse or quantifier problem elsewhere.