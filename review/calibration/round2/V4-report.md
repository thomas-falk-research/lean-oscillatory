<!-- Calibration round 2, referee for V4 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V4

# Statement review: calibration round 2, copy V4

I read only `V4/Statements.lean` and `V4/statements.md`, plus Mathlib sources. I compiled one scratch file, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib2/V4/Scratch1.lean`, which is a copy of `Statements.lean` with a `#print` added. It elaborates with no errors.

## Shared definitions (checked once, used by all four statements)

- **`lin`** is p·k. Correct.
- **`oscInt2 Q A = ∫ k, exp (↑(Q k) * I) * A k`** is I(Q, A). Under `AmpBound`, A is continuous and `tsupport A ⊆ K` with K compact. So the integrand is integrable, and Lean's value 0 for non-integrable integrands is never reached.
- **`dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w`** is ∂_w∂_vΨ(k).
- **`ddd Ψ k u v w`** is ∂_w∂_v∂_uΨ(k).
- **`hessDet`** uses `dd Ψ k (1,0) (0,1)`, which is ∂₂∂₁Ψ. This matches the md. Every statement assumes the phase is at least C⁴, so these nested `fderiv`s are genuine derivatives and never the junk value 0.
- **`IsCritical` and `GradLower`** match the md. `GradLower` is stated with squares, which is equivalent to the md's form because `0 < c` is a hypothesis.
- **`FoldOrNondeg`** has three parts:
  - `hessDet ≠ 0`; or
  - `∃ v w, dd Ψ k v w ≠ 0` (the Hessian is nonzero); and
  - every nonzero kernel vector v has `ddd Ψ k v v v ≠ 0`.

  This matches the md's "rank one, third derivative along the kernel nonzero".
- **`AmpBound n K A M`** says `ContDiff ℝ n A`, `tsupport A ⊆ K`, and `‖iteratedFDeriv ℝ j A k‖ ≤ M` for all j ≤ n. This matches the md. It forces M ≥ 0. The operator norm is taken with respect to the max norm, which the md acknowledges and which changes constants only.
- **`FamilyCk`** asks for each Ψ_σ to be Cⁿ and for `iteratedFDeriv` to be jointly continuous for j ≤ n. This matches the md.
- **Exponents.** `C * M / m ^ N` parses as (C·M)/m^N with a natural power. `m ^ (-(5:ℝ)/6)` and `t ^ (-(2:ℝ)/3)` are `Real.rpow` with base ≥ 1, so the rpow conventions cause no problem.

## NonStationaryStatement (S2.1)

**Verdict: FAITHFUL.**

- **Regularity.** `FamilyCk (N + 1)` for the phases and `AmpBound N K A M` for the amplitude, as in the md.
- **Gradient condition.** `∀ k ∈ K, GradLower (Ψ σ) p k c` with `0 < c`, imposed on K, as in the md.
- **Linear term.** p ranges over all of ℝ² with no compactness, as the md says.
- **Quantifier order.** `∃ C` comes after Λ, N, Ψ, K and c, and before A, M, σ, p and m.

Vacuity hunt: the hypotheses can all be met, as the file's own sanity theorems show. N = 0 gives the trivial bound C·M, which is consistent with "every N ∈ ℕ".

Findings:
- NIT: `∀ (Λ : Type)` limits the family to universe 0. This is harmless.

## StationaryPhaseStatement (S2.2)

**Verdict: FAITHFUL.**

- **Nondegeneracy hypothesis.** `(∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0)` is exactly the md's condition.
- **Rest of the statement.** The phase is C⁴, the amplitude satisfies `AmpBound 2 K A M`, p is in K', m ≥ 1, the bound is `C * M / m`, and `∃ C` comes after Ψ, K and K'.
- **Vacuity hunt.** Nothing found. The saddle example in the sanity theorems even has an actual critical point.

## FoldStatement (S3)

**Verdict: UNFAITHFUL.** As written, the statement is false.

- **BLOCKER.** The hypothesis is `(∀ σ, ∀ k ∈ K', FoldOrNondeg (Ψ σ) k)`. It quantifies over K', the set of linear coefficients p. The md requires the condition "for every σ and every k ∈ K", the support set. Both the md ("Conditions are imposed at every point of K") and the Lean header's intent say K. As written, nothing is assumed about the phase on the support of the amplitude.

  Counterexample (one-point family Λ = Unit, data chosen by me):
  - K = `closedBall 0 1` and K' = {(3, 3)}, both compact.
  - Ψ(k) = k₁⁴ + k₂⁴ − 3k₁ − 3k₂, a polynomial, so `FamilyCk 4` holds.
  - The Hessian of Ψ at (3, 3) is diag(108, 108), so `hessDet ≠ 0` there and the hypothesis holds.
  - For p = (3, 3) ∈ K', the phase is m(k₁⁴ + k₂⁴). It has a degenerate critical point at 0 ∈ K.
  - For a bump A with A(0) ≠ 0, the integral behaves like c·A(0)·m^{−1/2}. This is not O(m^{−5/6}).

  An elementary version needs no asymptotics. Take Ψ = −3k₁ − 3k₂ + χ(k)·((k₁−3)² + (k₂−3)²), where χ is smooth, equal to 1 near (3, 3) and 0 on `closedBall 0 2`. Then the phase is identically 0 on K, so the integral equals ∫A ≠ 0 for every m. But the bound C·M·m^{−5/6} tends to 0.

  The fix is to replace `∀ k ∈ K'` with `∀ k ∈ K`.
- MAJOR: `sanity_Fold_hyps` uses the same set, `closedBall 0 1`, for both K and K'. That is why the sanity check did not catch the swap. The sanity theorems should use distinct sets for K and K'.
- Everything else matches the md: `FamilyCk 4`, `AmpBound 2 K`, p ∈ K', the exponent m^{−5/6}, and the quantifier order.
- NIT: `Λ : Type`, as in S2.1.

## D4BoundStatement (S4.1)

**Verdict: FAITHFUL.**

- **Hypotheses.** φ is C⁴, and `∀ v w, dd φ 0 v w = 0` is D²φ(0) = 0.
- **Cubic coefficients.** `cubicCoeffs` gives a = ∂₁₁₁φ(0)/6, b = `ddd φ 0 e₁ e₁ e₂`/2 = ∂₂∂₁∂₁φ(0)/2 (that is, ∂₁₁₂), c = ∂₁₂₂φ(0)/2 and d = ∂₂₂₂φ(0)/6. These are the coefficients of (1/6)D³φ(0)[κ³].
- **Discriminant.** `disc` is the standard discriminant of a binary cubic and matches the md. The condition `disc < 0` matches the md, and the sanity example x³ + y³ gives −27.
- **Conclusion.** The phase is `t * φ κ + lin y κ` with y ∈ ℝ² arbitrary, the amplitude satisfies `AmpBound 2 (closedBall 0 δ)` (the max-norm ball, as the md states), the bound is `C * M * t ^ (-(2:ℝ)/3)` for t ≥ 1, and `∃ δ > 0, ∃ C` comes after φ and before A, M, y and t.
- **Vacuity hunt.** Nothing found.

Findings:
- MINOR: the header still refers to `OscInt/Statements/StationaryPhase.lean` and `docs/statements.md`, but this review copy is a single file. This affects documentation only.

## Summary

| Statement | Verdict | Worst finding |
|---|---|---|
| `NonStationaryStatement` | FAITHFUL | NIT |
| `StationaryPhaseStatement` | FAITHFUL | none |
| `FoldStatement` | UNFAITHFUL | BLOCKER: `∀ k ∈ K'` should be `∀ k ∈ K`; the statement is false as written |
| `D4BoundStatement` | FAITHFUL | MINOR (header references) |
