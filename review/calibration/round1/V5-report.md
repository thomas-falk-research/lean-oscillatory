<!-- Calibration round 1, referee for V5; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V5

# Statement review of V5 (calibration round 1)

I read only `Statements.lean` and `statements.md` in my directory. I compiled one scratch copy, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V5/Check.lean`, with nice -n 10. The file compiles, and the sanity theorems use only `propext`, `Classical.choice` and `Quot.sound`. In the same scratch file I checked that `μ ^ (-(1 : ℝ) / 3)` parses as μ^(−1/3): `8 ^ (-(1:ℝ)/3) = 1/2` is provable.

## Shared definitions
- `HasDerivOn f f' a b := ContinuousOn f (Icc a b) ∧ ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x` matches "f has derivative f′ on [a, b]" exactly.
- `AmplitudeOn` matches the amplitude hypothesis: continuous on `Icc`, `HasDerivAt` on `Ioo`, `IntervalIntegrable ψ' volume a b`. Together with continuity on `Icc`, these are exactly the hypotheses of Mathlib's FTC (`integral_eq_sub_of_hasDerivAt_of_le`), so ψ(x) − ψ(a) = ∫ψ′ holds. `∫ ‖ψ' x‖` is a genuine integral, not Lean's default value of 0.
- `oscInt`: under `a ≤ b`, ψ is continuous on `Icc` and φ is continuous on `Icc`, so the integrand is continuous there and therefore integrable. There is no collapse to the default value, and the orientation is correct.
- `ampNorm ψ ψ' a b = ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖` matches A(ψ; a, b).
- Degenerate case a = b: `Ioo a b` is empty, so the lower-bound hypotheses hold vacuously. The left side is 0, so the bound is trivially true and not harmful.

## VdC1Statement
**Verdict: FAITHFUL.**
- The hypotheses `a ≤ b → 0 < ν → HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b → (MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b)) → (∀ x ∈ Ioo a b, ν ≤ |φ' x|) → AmplitudeOn ψ ψ' a b` match S1.1 term for term.
- The conclusion `‖oscInt φ ψ a b‖ ≤ 3 / ν * ampNorm ψ ψ' a b` is (3/ν)·A.
- Vacuity: `3 / ν` only appears under `0 < ν`. The hypotheses can all hold at once (the sanity theorem shows this). The quantifiers are all universal, with no constant chosen existentially. Nothing collapses.
- Findings: none beyond the NIT below.

## VdC2Statement
**Verdict: FAITHFUL.**
- The hypotheses match S1.2: `HasDerivOn φ φ' a b`, `HasDerivOn φ' φ'' a b`, `∀ x ∈ Ioo a b, μ ≤ |φ'' x|` and `AmplitudeOn`.
- `p` is universally quantified, and the phase is `fun x => φ x + p * x`, which is φ_p.
- The conclusion `8 / √μ * ampNorm ψ ψ' a b` is (8/√μ)·A. `√μ` is only reached with `0 < μ`.
- Continuity of φ″ is not assumed. That is harmless: φ″ is a genuine derivative on (a, b), so by Darboux's theorem `μ ≤ |φ'' x|` forces a constant sign. This matches the stamped text.
- Findings: none beyond the NIT below.

## VdC3Statement
**Verdict: UNFAITHFUL** (much stronger than S1.3, and false).

**BLOCKER.** The lower-bound hypothesis reads
`(∃ x ∈ Ioo a b, μ ≤ |φ''' x|) →`
S1.3 says "|φ‴(x)| ≥ μ on (a, b)", which means for all x, i.e. `∀ x ∈ Ioo a b, μ ≤ |φ''' x|`. With `∃`, the hypothesis only requires φ‴ to be large at one point, and the statement is false.

Counterexample: μ = 1, p = 0, ψ ≡ 1, ψ′ ≡ 0, so A = 1. On [0, b] with b > 2, take φ(x) = x⁴/(6b). Then φ‴(x) = 4x/b ≥ 1 at x = 3b/4, so the `∃` hypothesis holds. All the `HasDerivOn` hypotheses hold because φ is a polynomial. Substituting x = b^{1/4} t gives

∫₀ᵇ e^{i x⁴/(6b)} dx = b^{1/4} ∫₀^{b^{3/4}} e^{i t⁴/6} dt ~ b^{1/4} · 6^{1/4} Γ(5/4) e^{iπ/8} → ∞,

which exceeds 18 · 1^{−1/3} · 1 = 18 for large b. So `VdC3Statement` is provably `False` and cannot be proved as written.

Fix: replace `∃` with `∀`, i.e. `(∀ x ∈ Ioo a b, μ ≤ |φ''' x|) →`.

The other parts of VdC3Statement are faithful:
- the hypothesis `HasDerivOn φ'' φ''' a b`;
- the linear term `fun x => φ x + p * x`;
- the constant `18 * μ ^ (-(1 : ℝ) / 3)`, which is 18·μ^{−1/3} with `Real.rpow` under `0 < μ`.

## Other findings
- **MINOR.** `sanity_hypotheses_satisfiable` checks `(∀ x ∈ Ioo (0 : ℝ) 1, 1 ≤ |φ''' x|)`, which is the `∀` form, not the `∃` hypothesis that `VdC3Statement` actually uses. The sanity check therefore does not test the stated hypothesis, and it gives false comfort that the S1.3 hypotheses are the intended ones. It should restate each hypothesis exactly as it appears in the statement.
- **NIT.** The `statement_pin_* : VdCkStatement = VdCkStatement := rfl` theorems carry no content; they only show that the definitions elaborate.
- **NIT.** The header's "Lower bounds are on the open interval (a, b)" does not say "for all x". Saying so would have made the S1.3 mismatch visible to a reader.

## Summary
| Statement | Verdict | Worst finding |
|---|---|---|
| VdC1Statement | FAITHFUL | none |
| VdC2Statement | FAITHFUL | none |
| VdC3Statement | UNFAITHFUL (false as stated) | BLOCKER: `∃ x ∈ Ioo a b, μ ≤ \|φ''' x\|` should be `∀` |