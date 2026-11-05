<!-- Calibration round 1, referee for V6; verbatim final report extracted from the agent's hand-back call. Prompt: review/prompts/calibration-r1.md (sha256 6bb8e1b9…). -->

V6

# Statement review, calibration round 1: copy V6

**Files read:** `Statements.lean` and `statements.md` in my directory, the calibration prompt, and one Mathlib source (`Mathlib/Analysis/Real/Sqrt.lean:116`, `prefix:max "√" => Real.sqrt`). I read nothing else under the repository.

**Compilation:** I compiled a scratch copy, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib1/V6/Check.lean` (the statements file plus `#print` with `pp.parens` and two `example`s), with `nice -n 10 lake env lean`. It compiles with no errors, sanity theorems included. The fully parenthesised prints confirm three parses:
- `((3 / ν) * (ampNorm ψ ψ' a b))`
- `((8 / √μ) * (ampNorm ψ ψ' a b))`, where `√` is max precedence, so it does not swallow the product
- `((18 * (μ ^ ((-1) / 3))) * (ampNorm ψ ψ' a b))`, which is real `rpow` with exponent −1/3. Checked: `μ ^ (-(1 : ℝ) / 3) = Real.rpow μ (-1/3)`.

## Definitions shared by all three statements
- `HasDerivOn f f' a b := ContinuousOn f (Icc a b) ∧ ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x`. This matches "has derivative on [a, b]" in statements.md exactly. The endpoint values of `f'` are unconstrained, as the md says.
- `AmplitudeOn ψ ψ' a b := ContinuousOn ψ (Icc a b) ∧ (∀ x ∈ Ioo a b, HasDerivAt ψ (ψ' x) x) ∧ IntervalIntegrable ψ' volume a b`. This matches the md. It is also exactly the set of hypotheses for Mathlib's FTC (`integral_eq_sub_of_hasDerivAt_of_le`), so the integration by parts behind the amplitude form is available. A derivative that exists everywhere on (a, b) rules out Cantor-type failures.
- `oscInt φ ψ a b = ∫ x in a..b, Complex.exp (↑(φ x) * Complex.I) * ψ x` is e^{iφ}ψ. The integrand is continuous on [a, b] (φ and ψ are continuous there), so it is integrable and no "non-integrable means 0" collapse can happen. The integral is oriented, but `a ≤ b` is assumed everywhere, so that is harmless.
- `ampNorm ψ ψ' a b = ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖`. This is A(ψ; a, b). `ψ'` is interval-integrable, so `‖ψ'‖` is too and the integral is the genuine one, not the junk value 0. `ψ b` is meaningful because ψ is continuous on `Icc`.

## VdC1Statement (S1.1)
**1. Verdict: FAITHFUL.**
- The quantifier list `∀ (φ φ' φ'' : ℝ → ℝ) (ψ ψ' : ℝ → ℂ) (a b ν : ℝ)` is all universal, with no existential constant.
- The hypotheses `a ≤ b`, `0 < ν`, `HasDerivOn φ φ' a b`, `HasDerivOn φ' φ'' a b`, `MonotoneOn φ' (Ioo a b) ∨ AntitoneOn φ' (Ioo a b)`, `∀ x ∈ Ioo a b, ν ≤ |φ' x|` and `AmplitudeOn ψ ψ' a b` each correspond one-to-one to S1.1.
- The conclusion `‖oscInt φ ψ a b‖ ≤ 3 / ν * ampNorm ψ ψ' a b` is (3/ν)·A.
- There is no linear term, as the md says.
- Relative to Stein the theorem is weaker, because φ′ is required to be differentiable on (a, b) and continuous on [a, b]. The md states and explains this choice, so the verdict against the md is FAITHFUL.

**2. Vacuity hunt: nothing found.**
- The hypotheses can be met together: `sanity_hypotheses_satisfiable` exhibits data on [0, 1] with ν = 1, and it compiles.
- `3 / ν` only occurs under `0 < ν`.
- The conclusion is not trivially true. With φ = νx and ψ = 1 the left side is |∫₀^b e^{iνx}dx|, which can reach 2/ν, against a right side of 3/ν. So the inequality has real content.
- The conclusion is not false either. Integrating by parts against 1/φ′ gives 2/ν from the boundary terms plus 1/ν from the variation of 1/φ′. That variation is bounded because 1/φ′ is monotone. The amplitude version then follows by the Stein corollary argument on the subintervals [a, x].
- When a = b both sides reduce to trivially valid values (0 ≤ (3/ν)|ψ(b)|).

**3. Findings**
- **NIT:** `HasDerivOn φ' φ'' a b` is used in S1.1 only for the existence of φ″ and the continuity of φ′ on `Icc`. It makes the theorem weaker than Stein's. This is documented in both the md and the header, so it is not a fidelity defect.

## VdC2Statement (S1.2)
**1. Verdict: FAITHFUL.**
- The hypotheses `HasDerivOn φ φ' a b`, `HasDerivOn φ' φ'' a b`, `∀ x ∈ Ioo a b, μ ≤ |φ'' x|`, `AmplitudeOn ψ ψ' a b`, `0 < μ` and `a ≤ b` match the md.
- `p` is universally quantified, and the hypotheses concern φ alone. The conclusion is `‖oscInt (fun x => φ x + p * x) ψ a b‖ ≤ 8 / √μ * ampNorm ψ ψ' a b`, which is |I(φ_p, ψ)| ≤ (8/√μ)·A.

**2. Vacuity hunt: nothing found.**
- `√μ` occurs only under `0 < μ`, so `√μ > 0` and the Lean conventions for √ of a negative number and division by zero are never reached.
- The data in the sanity theorem (φ″ = x + 1 ≥ 1 on (0, 1)) satisfies the hypotheses.
- By Darboux, φ″ has a constant sign, so φ′ + p is strictly monotone and the S1.1 reduction applies. The constant 8 = 2·3 + 2 is Stein's c₂.
- The conclusion is neither trivially true nor trivially false.

**3. Findings:** none.

## VdC3Statement (S1.3)
**1. Verdict: FAITHFUL.**
- The md says "as S1.2, plus φ″ has derivative φ‴ on [a, b], with |φ‴| ≥ μ in place of the bound on φ″". The Lean matches: `HasDerivOn φ'' φ''' a b`, `∀ x ∈ Ioo a b, μ ≤ |φ''' x|`, and no lower bound on φ″.
- The conclusion `18 * μ ^ (-(1 : ℝ) / 3) * ampNorm ψ ψ' a b` parses as 18·μ^{−1/3}·A, with real `rpow` and exponent (−1)/3, which is the intended value. 18 = 2·8 + 2 is Stein's c₃.

**2. Vacuity hunt: nothing found.**
- `rpow` with a positive base (`0 < μ`) is the genuine power, not a junk value.
- The sanity data (φ‴ ≡ 1) satisfies the hypotheses.
- The bound is neither trivially true nor trivially false.

**3. Findings:** none.

## Further checks
- **NIT:** the header says `Mathematics: docs/statements.md`, but the review copy sits beside the Lean file, not under `docs/`. This is cosmetic.
- **NIT:** the `statement_pin_*` theorems (`VdC1Statement = VdC1Statement := rfl`) are tautologies with no logical content. They are harmless; presumably they exist for later pinning.

## Overall
| Statement | Verdict | Findings |
|---|---|---|
| VdC1Statement | FAITHFUL | 1 NIT |
| VdC2Statement | FAITHFUL | none |
| VdC3Statement | FAITHFUL | none |

There are no BLOCKER, MAJOR or MINOR findings. Two NITs about the file as a whole are listed under "Further checks". I checked the constants, the parsing and precedence, the Lean conventions (division by zero, √, rpow, junk integrals, orientation), the quantifier order and whether the hypotheses can be satisfied, and found no defect.