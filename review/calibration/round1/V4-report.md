<!-- Calibration round 1, referee for V4; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V4

# Statement review: V4 (`Statements.lean` vs `statements.md` S1)

## Headline
**BLOCKER, affects all three statements.** `AmplitudeOn` does not include the integrability hypothesis on ψ′ that `statements.md` and the Lean file's own header both say it includes:

```lean
def AmplitudeOn (ψ ψ' : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn ψ (Icc a b) ∧ (∀ x ∈ Ioo a b, HasDerivAt ψ (ψ' x) x)
```

`statements.md` says: "ψ has derivative ψ′ on [a, b] … **and ψ′ is Lebesgue integrable on [a, b]**". The header of `Statements.lean` says that `AmplitudeOn` includes "`IntervalIntegrable ψ' volume a b`", and that "`IntervalIntegrable ψ'` is required: without it `∫ ‖ψ'‖` would be `0` by Lean's convention and the bound false." The docstring of the definition ("`ψ'` integrable") claims the same thing. The conjunct is missing from the definition body. The header itself predicts the result: all three statements are false.

**Counterexample (all three statements).** Take [a, b] = [0, 1] and g(x) = x² sin(1/x²) with g(0) = 0. g is differentiable everywhere on ℝ, and g′ is not Lebesgue integrable on [0, 1]. Put ψ(x) = g(x) − x·g(1) and ψ′ = its derivative.
- ψ is continuous with derivative ψ′ everywhere, so `AmplitudeOn ψ ψ' 0 1` holds.
- ψ(1) = 0.
- ψ′ is not integrable, so `fun x => ‖ψ' x‖` is not `IntervalIntegrable`. Then `intervalIntegral.integral_undef` gives `∫ x in 0..1, ‖ψ' x‖ = 0`. I checked this step in a scratch compile.
- Therefore `ampNorm ψ ψ' 0 1 = 0`, and every conclusion reduces to `‖oscInt …‖ ≤ 0`.

The oscillatory integral is not zero for a suitable choice of the remaining data:
- **VdC1:** take φ(x) = νx, φ′ ≡ ν, φ″ ≡ 0, so φ′ is monotone and |φ′| ≥ ν. Then oscInt = ∫₀¹ e^{iνx} ψ(x) dx. This is the Fourier transform of a compactly supported L¹ function, so it is real-analytic in ν. It is not identically zero because ψ ≢ 0, so it is nonzero for some ν > 0.
- **VdC2:** take φ = μx²/2. For **VdC3:** take φ = μx³/6. In both, p ↦ ∫₀¹ e^{i(φ(x)+px)} ψ(x) dx is the Fourier transform of the nonzero L¹ function e^{iφ}ψ·1_[0,1]. It is therefore not identically zero, so some p gives a nonzero value.

Each `VdCkStatement` is refutable, so none can be proved. If one were "proved" anyway, that would point to an inconsistency elsewhere.

**Fix:** change the body to
`ContinuousOn ψ (Icc a b) ∧ (∀ x ∈ Ioo a b, HasDerivAt ψ (ψ' x) x) ∧ IntervalIntegrable ψ' volume a b`.

The sanity theorems did not catch this. `sanity_amplitude_one` only shows that the hypotheses can be satisfied; it never tests whether the bound holds. After the fix, `sanity_amplitude_one` will need a third component, for example `intervalIntegrable_const`.

## VdC1Statement
1. **Verdict: UNFAITHFUL**, because of the BLOCKER above. Apart from `AmplitudeOn`, it matches S1.1:
   - φ has derivative φ′ on [a, b], and φ′ has derivative φ″ on [a, b];
   - `MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b)`;
   - `∀ x ∈ Ioo a b, ν ≤ |φ' x|`;
   - no linear term;
   - `3 / ν * ampNorm ψ ψ' a b`.
2. **Vacuity hunt.**
   - `a ≤ b` together with the oriented integral gives the Lebesgue integral over [a, b]. When a = b both sides are 0, which is fine.
   - `3 / ν` is safe under `0 < ν`.
   - The hypotheses can be satisfied (see the sanity theorem).
   - Quantifiers: all variables are universal and the constant is a numeral. Fine.
3. **Findings.**
   - BLOCKER: `AmplitudeOn` is missing `IntervalIntegrable ψ' volume a b`; the statement is false (see above).
   - NIT: the docstring of `AmplitudeOn` says "`ψ'` integrable", but the body does not contain it. Docstring and body disagree.

## VdC2Statement
1. **Verdict: UNFAITHFUL**, because of the same BLOCKER. Otherwise it matches S1.2:
   - `HasDerivOn φ φ' a b → HasDerivOn φ' φ'' a b`;
   - `∀ x ∈ Ioo a b, μ ≤ |φ'' x|`;
   - p is universally quantified, and the conclusion is about `oscInt (fun x => φ x + p * x) ψ a b`;
   - the hypotheses are on φ alone, as `statements.md` says;
   - `8 / √μ`, with `0 < μ`, so `Real.sqrt` and division by zero are never reached.
2. **Vacuity hunt.** The quantifier order (p universal, constant fixed) gives the uniform statement. Nothing else collapses.
3. **Findings.**
   - BLOCKER: `AmplitudeOn ψ ψ' a b` lacks integrability, so `ampNorm` can be `0` while `‖oscInt (fun x => φ x + p * x) ψ a b‖ > 0`.

## VdC3Statement
1. **Verdict: UNFAITHFUL**, because of the same BLOCKER. Otherwise it matches S1.3:
   - `HasDerivOn φ'' φ''' a b`;
   - `∀ x ∈ Ioo a b, μ ≤ |φ''' x|`, with no hypothesis on φ″ beyond continuity and differentiability;
   - `18 * μ ^ (-(1 : ℝ) / 3)`, where `-(1:ℝ)/3 = -1/3` and `Real.rpow` with positive base is the true μ^{−1/3}.
2. **Vacuity hunt.** Same as VdC2: nothing else collapses, and the quantifier order is right.
3. **Findings.**
   - BLOCKER: the same missing `IntervalIntegrable ψ' volume a b` in `AmplitudeOn`.

## Other checks (no further findings)
- `oscInt` = `∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * ψ x` is e^{iφ}ψ, and it is integrable because ψ is continuous on [a, b].
- `ampNorm` = `‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖` matches A(ψ; a, b), once ψ′ is assumed integrable.
- `HasDerivOn` matches "continuous on [a, b], derivative on (a, b)".
- Constants 3, 8, 18 match c_k.

## Scratch file
The one compile check is `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V4/Check.lean`. It confirms that `∫ x in a..b, ‖ψ' x‖ = 0` when the integrand is not `IntervalIntegrable`, via `intervalIntegral.integral_undef`.