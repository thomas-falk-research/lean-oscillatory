<!-- Calibration round 2, referee for V6 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V6

# Statement review, calibration round 2: V6

**Files read:** only `V6/Statements.lean` and `V6/statements.md` (plus Mathlib for definitions). I compiled one scratch file, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib2/V6/scratch/Check.lean`. It is the statement file plus checks, and it builds with no errors. The checks confirm three things:
- `m ^ (N - 1)` uses natural-number subtraction and a natural power.
- `m ^ ((0:ℕ) - 1) = 1`.
- `-(5 : ℝ) / 6 = -5/6`.

## Shared definitions (checked once, used by all four statements)
- `lin`, `oscInt2` (`exp (Q k * I) * A k`, Bochner integral on `ℝ × ℝ`): match `p·k` and `I(Q, A)`.
- `dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w` is ∂_w∂_vΨ, and `ddd Ψ k u v w` is ∂_w∂_v∂_uΨ: correct. `hessDet` = ∂₁₁·∂₂₂ − (∂₂∂₁)²: correct. Every use is on a C⁴ phase, so the nested `fderiv`s are the true derivatives and nothing collapses to `fderiv = 0`.
- `IsCritical`: correct.
- `GradLower` (`c² ≤ (∂₁Ψ+p₁)² + (∂₂Ψ+p₂)²`): this is the Euclidean condition |∇Ψ + p| ≥ c, correct when c > 0.
- `AmpBound n K A M` (`ContDiff ℝ n A`, `tsupport A ⊆ K`, `‖iteratedFDeriv ℝ j A k‖ ≤ M` for all j ≤ n and all k): matches "amplitude bound (n, K, M)". The integrand is continuous with compact support, so it is integrable and the Bochner integral never falls back to Lean's value 0. If M < 0 the hypothesis is false, which is harmless.
- `FamilyCk n Ψ` (each `Ψ σ` is Cⁿ, and `(σ,k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` is jointly continuous for j ≤ n): matches "of class Cⁿ".
- `FoldOrNondeg`: `hessDet ≠ 0 ∨ ((∃ v w, dd Ψ k v w ≠ 0) ∧ ∀ v ≠ 0, (∀ w, dd Ψ k v w = 0) → ddd Ψ k v v v ≠ 0)`. This says "Hessian nonzero, and the third derivative is nonzero along every nonzero kernel vector", which matches S3.
- `cubicCoeffs`: a = ∂₁₁₁/6, b = `ddd φ 0 e₁ e₁ e₂`/2 = ∂³₁₁₂/2, c = ∂³₁₂₂/2, d = ∂³₂₂₂/6. This agrees with (1/6)D³φ(0)[(x,y)³] = (1/6)(φ₁₁₁x³ + 3φ₁₁₂x²y + 3φ₁₂₂xy² + φ₂₂₂y³). Correct.
- `disc` = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd: same as statements.md (the standard discriminant of a binary cubic).

## NonStationaryStatement (S2.1)
**Verdict: FAITHFUL-WEAKER.** The decay exponent is one power short, so as written this does not state S2.1.

- **BLOCKER.** `‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m ^ (N - 1)`. statements.md requires `C M m^{−N}`. Here `N - 1` is natural-number subtraction, so the bound is m^{−(N−1)} for N ≥ 1 and m⁰ for N = 0. Since m ≥ 1, this is strictly weaker than S2.1 by a factor of m for every N ≥ 1. The decay rate is the whole content of the statement, so the gap matters. The fix is `/ m ^ N`.
- **MINOR.** The file disagrees with itself. The header says "`m ^ N` is a natural power" and the docstring says "decay `m^{-N}`", but the code has `m ^ (N - 1)`.
- Vacuity hunt, all clean:
  - The hypotheses can be met together (the file's own sanity theorem, and Ψ = k₁ with p = 0, c = 1).
  - `∃ C` comes after Λ, N, Ψ, K, c and before A, M, σ, p, m, as specified.
  - p is unrestricted, as statements.md intends.
  - The gradient condition is required on all of K, as statements.md intends.
  - For N = 0 the conclusion `‖I‖ ≤ C M` is true and not vacuous.
- **NIT.** `Λ : Type` fixes universe 0. Harmless.

## StationaryPhaseStatement (S2.2)
**Verdict: FAITHFUL.**
- `ContDiff ℝ 4 Ψ`, compact `K` and `K'`, and `∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0` all match S2.2.
- `∃ C` comes before A, M, p, m, and the conclusion `C * M / m` with `1 ≤ m` is m^{−1}, as in S2.2.
- The hypotheses are satisfiable: the saddle has a genuine critical point at p = 0, k = 0, so the nondegeneracy hypothesis is not vacuous.
- Nothing collapses under Lean conventions.
- No findings.

## FoldStatement (S3)
**Verdict: FAITHFUL.**
- `FamilyCk 4`, compact K and K′, and `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k` match S3.
- The conclusion `C * M * m ^ (-(5 : ℝ) / 6)` is `Real.rpow` with base m ≥ 1 > 0 and exponent −5/6 (checked), so there is no `rpow` corner case.
- The quantifier order is correct.
- The hypotheses are satisfiable: the fold k₁³ + k₂² uses the rank-one branch at 0.
- **NIT.** `FoldOrNondeg` requires the condition at every k ∈ K, not just at critical points. statements.md asks for exactly this, so it is not a discrepancy.

## D4BoundStatement (S4.1)
**Verdict: FAITHFUL.**
- `ContDiff ℝ 4 φ`, `∀ v w, dd φ 0 v w = 0` (that is, D²φ(0) = 0), `disc (cubicCoeffs φ) < 0`, then `∃ δ > 0, ∃ C`, then for all A, M, y, t: `AmpBound 2 (closedBall 0 δ) A M`, `1 ≤ t`, and `‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)`. This matches S4.1, including that y is unrestricted and the ball is the max-norm ball.
- The sanity example x³ + y³ gives disc = −27 < 0, so the hypotheses can be met.
- Leaving out ∇φ(0) = 0 and the isolated-critical-point condition is disclosed in statements.md and justified there.
- No findings.

## Summary
| Statement | Verdict | Findings |
|---|---|---|
| NonStationaryStatement | FAITHFUL-WEAKER | BLOCKER: `m ^ (N - 1)` should be `m ^ N`; MINOR: header and docstring say `m^{-N}`; NIT: universe |
| StationaryPhaseStatement | FAITHFUL | none |
| FoldStatement | FAITHFUL | NIT only |
| D4BoundStatement | FAITHFUL | none |