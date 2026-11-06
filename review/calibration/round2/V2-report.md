<!-- Calibration round 2, referee for V2 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V2

# Statement review: calibration round 2, directory V2

I read only `V2/Statements.lean` and `V2/statements.md`, plus Mathlib definitions. `Statements.lean` compiles cleanly with `lake env lean` and gives no errors or warnings. I also compiled one scratch file, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib2/V2/Scratch.lean` (a copy of the statements plus one `example`). It compiles cleanly and checks the hypotheses of the S2.2 counterexample below.

## Shared definitions (checked once, used by all four statements)
- `lin p k = p.1 * k.1 + p.2 * k.2`: this is p·k. Correct.
- `oscInt2 Q A = ∫ k, exp (↑(Q k) * I) * A k`: this is I(Q, A), a Bochner integral over the product Lebesgue measure on ℝ×ℝ. Under `AmpBound` the integrand is continuous with compact support (`tsupport A ⊆ K`, K compact), so it is integrable and Lean's value 0 for non-integrable integrands never applies. Correct.
- `dd Ψ k v w = fderiv ℝ (fun y => fderiv ℝ Ψ y v) k w` is ∂_w∂_vΨ(k). `ddd Ψ k u v w` is ∂_w∂_v∂_uΨ(k). Every use is on a C⁴ phase, so the nested `fderiv`s are the true derivatives and none fall back to Lean's value 0 for a non-differentiable function. Correct.
- `hessDet` is ∂₁₁Ψ·∂₂₂Ψ − (∂₂∂₁Ψ)², matching H(Ψ, k). `IsCritical` is ∂ᵢΨ + pᵢ = 0. Both correct.
- `GradLower` is `c ^ 2 ≤ (∂₁Ψ+p₁)^2 + (∂₂Ψ+p₂)^2`, i.e. the Euclidean |∇Ψ + p| ≥ c, which is right since c > 0. Correct.
- `FoldOrNondeg` is `hessDet ≠ 0 ∨ ((∃ v w, dd Ψ k v w ≠ 0) ∧ ∀ v ≠ 0, (∀ w, dd Ψ k v w = 0) → ddd Ψ k v v v ≠ 0)`. This is "nondegenerate, or Hessian nonzero (so rank one) with third derivative nonzero along every kernel vector". `dd` is symmetric for C² phases, so putting the kernel vector in the first slot does not matter. Correct.
- `AmpBound n K A M` is `ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M`. This matches statements.md. M ≥ 0 follows (take j = 0), and no `iSup` is involved. The operator norms are taken with the max norm on ℝ×ℝ, which changes constants only, as declared. Correct.
- `FamilyCk n Ψ` requires each `Ψ σ` to be Cⁿ and `(σ,k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` to be continuous for j ≤ n. This matches statements.md. NIT: `Λ : Type` is universe 0 only, which is harmless.
- `cubicCoeffs`: a = ∂₁₁₁φ(0)/6, b = `ddd φ 0 e₁ e₁ e₂ / 2` = ∂₂∂₁∂₁φ(0)/2 = ∂₁₁₂φ(0)/2, c = ∂₁₂₂φ(0)/2, d = ∂₂₂₂φ(0)/6. These match statements.md and the expansion of (1/6)D³φ(0)[κ³]. `disc` is the standard binary-cubic discriminant b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd. Correct.

## NonStationaryStatement (S2.1)
**Verdict: FAITHFUL.**
- Quantifier order is Λ, N, Ψ, K, c, then `∃ C`, then A, M, σ, p, m, as statements.md requires. The hypotheses are C^{N+1} family, compact K, c > 0, `AmpBound N K A M`, the gradient bound on all of K, and `1 ≤ m`. The conclusion `C * M / m ^ N` uses a natural power with m ≥ 1, so it equals C M m^{−N}.
- p ranges over all of ℝ² rather than a compact set, as the md asks. The result is still true: under integration by parts, |∇(Ψ+p)| ≥ c on K, and the derivatives of ∇φ/|∇φ|² stay bounded uniformly for large p.
- Vacuity hunt found nothing. The hypotheses can all hold together (the file's sanity theorem uses Ψ = k₁, c = 1). For N = 0 the claim is a correct trivial bound.

## StationaryPhaseStatement (S2.2)
**Verdict: UNFAITHFUL.**

**BLOCKER** concerning `(∃ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0)`.
- statements.md requires the nondegeneracy for every p ∈ K′ ("whenever k ∈ K is a critical point of Ψ + p·(·) for some p ∈ K′"), i.e. `∀ p ∈ K'`. The Lean text only requires it for one p ∈ K′.
- This hypothesis holds for every C⁴ Ψ as soon as K′ contains one p with |p| > sup_K |∇Ψ|. Such a p gives no critical points, so the implication holds vacuously. The conclusion is then claimed for all p ∈ K′, including degenerate ones, so the statement is **false**.
- Counterexample: Ψ = k₁³ + k₂², K = closedBall 0 1, K′ = {0, (1,0)}.
  - With p = (1,0), ∂₁(Ψ + p·) = 3k₁² + 1 ≠ 0, so the hypothesis holds.
  - With p = 0, the point 0 is critical with `hessDet = 0`. I checked these hypotheses in Lean in the scratch file.
  - At p = 0, take A = a(k₁)b(k₂) with bumps a(0) = b(0) = 1. Then I = (∫e^{imx³}a)(∫e^{imy²}b) ~ c₁c₂ m^{−1/3−1/2}, with c₁ = 2Γ(4/3)cos(π/6) ≠ 0. So |I| ≍ m^{−5/6}, which is not ≤ C M m^{−1}.
- The file's sanity theorem `sanity_StationaryPhase_hyps` proves the ∀-form (`∀ p ∈ Metric.closedBall ..., ∀ k ∈ ..., IsCritical ... → hessDet ... ≠ 0`), not the statement's ∃-form. It therefore does not test the hypothesis actually used and hides the mismatch.
- Fix: replace `∃ p ∈ K'` with `∀ p ∈ K'`.

Everything else in S2.2 is faithful: C⁴ phase, `AmpBound 2` (a declared deviation), `∃ C` after Ψ, K, K′, and `C * M / m` with m ≥ 1.

## FoldStatement (S3)
**Verdict: FAITHFUL.**
- Quantifier order is Λ, Ψ, K, K′, then `∃ C`, then A, M, σ, p, m. The hypotheses are `FamilyCk 4`, compact K and K′, `FoldOrNondeg (Ψ σ) k` for all σ and all k ∈ K, `AmpBound 2`, `p ∈ K'` and `1 ≤ m`.
- `m ^ (-(5 : ℝ) / 6)` parses as `Real.rpow m (-5/6)`. With m ≥ 1 that is m^{−5/6}, so the `Real.rpow` conventions for 0 or negative bases do not come into play.
- The condition depends only on the Hessian and third derivative of Ψ_σ, not on p, so imposing it at every point of K matches the md. The hypotheses can all hold together (the sanity theorem uses k₁³ + k₂², which uses the rank-one branch at 0).
- MINOR: the hypothesis has no explicit `hessDet Ψ k = 0` in the rank-one branch. This is harmless: when `hessDet ≠ 0` the left disjunct already holds, and the right disjunct is then automatically consistent because the kernel is trivial.

## D4BoundStatement (S4.1)
**Verdict: FAITHFUL.**
- The hypotheses are `ContDiff ℝ 4 φ`, `∀ v w, dd φ 0 v w = 0` (D²φ(0) = 0) and `disc (cubicCoeffs φ) < 0`. Then `∃ δ > 0, ∃ C`, then A, M, y, t with `AmpBound 2 (closedBall 0 δ) A M` and `1 ≤ t`. The conclusion is `≤ C * M * t ^ (-(2:ℝ)/3)`.
- The phase `t * φ κ + lin y κ` has y ∈ ℝ² unrestricted, matching the md. The ball is the max-norm ball, as declared. The hypotheses can all hold together (x³ + y³ has disc −27).
- NIT: there is no ∇φ(0) = 0 hypothesis and no explicit "isolated critical point" hypothesis. Both omissions are declared and justified in the md, and the second follows from disc ≠ 0.
- NIT: the header line `Symbols (in addition to OscInt/Statements/StationaryPhase.lean)` refers to a file not in this copy; the symbols are actually defined earlier in the same file.

## Summary
| Statement | Verdict | Findings |
|---|---|---|
| NonStationaryStatement | FAITHFUL | none |
| StationaryPhaseStatement | UNFAITHFUL | BLOCKER: `∃ p ∈ K'` should be `∀ p ∈ K'`; the statement as written is false |
| FoldStatement | FAITHFUL | MINOR: rank-one branch has no explicit `hessDet = 0` (harmless) |
| D4BoundStatement | FAITHFUL | NITs only |

Shared definitions: all correct. The only cross-cutting NIT is `Λ : Type` (universe 0).