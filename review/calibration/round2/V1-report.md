<!-- Calibration round 2, referee for V1 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V1

# Statement review, calibration round 2: V1

I read only `V1/Statements.lean` and `V1/statements.md`. I compiled a scratch copy once with `nice -n 10 lake env lean` and then deleted it. The file compiles with no errors and no `sorry`. The sanity lemmas `sanity_D4_hyps`, `sanity_Fold_hyps` and `sanity_ampBound_exists` depend only on `propext`, `Classical.choice` and `Quot.sound`. I also checked that `-(5 : ℝ) / 6 = -5/6` and `-(2 : ℝ) / 3 = -2/3`.

## Shared definitions (all checked against statements.md)
- **`lin`, `oscInt2`:** `oscInt2` is `∫ k, exp(↑(Q k) * I) * A k` with the volume (product Lebesgue) measure, which is I(Q, A). It is correct.
- **`dd`, `ddd`:** these are nested `fderiv` directional derivatives, ∂_w∂_vΨ and ∂_w∂_v∂_uΨ. They are well defined for C⁴ phases, so the `fderiv`-of-non-differentiable collapse never applies.
- **`hessDet`:** it is `dd(e₁,e₁)·dd(e₂,e₂) − dd(e₁,e₂)²`, which matches H = ∂₁∂₁Ψ·∂₂∂₂Ψ − (∂₂∂₁Ψ)².
- **`IsCritical`:** matches.
- **`GradLower`:** it is `c² ≤ (∂₁Ψ+p₁)² + (∂₂Ψ+p₂)²`. With `0 < c` this is the same as |∇Ψ+p| ≥ c in the Euclidean norm.
- **`FoldOrNondeg`:** it is "H ≠ 0, or (∃ v w, dd ≠ 0) and every nonzero v with `∀ w, dd Ψ k v w = 0` has `ddd Ψ k v v v ≠ 0`". This matches the md: the Hessian is symmetric for C⁴ phases, so the left kernel is the kernel. The right-hand branch does not require H = 0, but when H ≠ 0 the left branch holds anyway, so nothing changes.
- **`AmpBound`:** it is `ContDiff ℝ n A`, `tsupport A ⊆ K` and `‖iteratedFDeriv ℝ j A k‖ ≤ M` for j ≤ n and all k, which matches the md. M ≥ 0 is forced, since a norm is ≤ M. There is no `iSup`. With K compact, A is continuous with compact support, so the Bochner integral never falls back to Lean's value 0 for non-integrable functions. The norm on ℝ×ℝ is the max norm, which changes constants only, as the md says.
- **`FamilyCk`:** each Ψ σ is Cⁿ, and `(σ,k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` is jointly continuous for j ≤ n. This matches the md.
- **`cubicCoeffs`:** a = ∂³₁₁₁/6, b = ∂³₁₁₂/2, c = ∂³₁₂₂/2, d = ∂³₂₂₂/6. This is correct: (1/6)D³φ(0)[κ³] = (φ₁₁₁x³ + 3φ₁₁₂x²y + 3φ₁₂₂xy² + φ₂₂₂y³)/6. The order of the arguments to `ddd` does not matter by symmetry.
- **`disc`:** it is b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd, the standard discriminant of a binary cubic. The tuple is unpacked in the same order (a, b, c, d) that `cubicCoeffs` builds it.

## NonStationaryStatement: FAITHFUL
- Quantifiers: Λ, N, Ψ, K, c, then `∃ C`, then A, M, σ, p, m. This matches S2.1.
- Hypotheses: `FamilyCk (N + 1) Ψ`, `IsCompact K`, `0 < c`, `AmpBound N K A M`, `∀ k ∈ K, GradLower (Ψ σ) p k c` and `1 ≤ m`.
- Conclusion: `‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m ^ N`. Here `m ^ N` is a natural-number power and m ≥ 1, so the division is safe.
- Vacuity: none. The hypotheses are jointly satisfiable (`sanity_NonStationary_hyps` together with `sanity_ampBound_exists`). The conclusion is not trivial for N ≥ 1. The statement is true by N integrations by parts, uniformly in unbounded p, because derivatives of ∇Q/|∇Q|² involve only derivatives of Ψ and powers of 1/|∇Q| ≤ 1/c.
- **NIT:** `(Λ : Type)` restricts Λ to universe 0. This is enough for the stated use (the parameter interval ε ∈ [0, ε₀] in S4), and the same applies to `FoldStatement`.

## StationaryPhaseStatement: FAITHFUL
- Hypotheses: `ContDiff ℝ 4 Ψ`, K and K′ compact, and `∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0`.
- Quantifiers: `∃ C` comes before A, M, p, m.
- Conclusion: `AmpBound 2 K A M → p ∈ K' → 1 ≤ m → ‖…‖ ≤ C * M / m`. This matches S2.2.
- Vacuity: none. The hypotheses are satisfiable, and a critical point actually exists in the saddle example (`sanity_StationaryPhase_hyps`). The bound m^{-1} is the correct 2-D nondegenerate rate.
- I found no defects.

## FoldStatement: FAITHFUL
- Hypotheses: `FamilyCk 4 Ψ`, K and K′ compact, and `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k`.
- Quantifiers: `∃ C` comes before A, M, σ, p, m.
- Conclusion: `AmpBound 2 K A M → p ∈ K' → 1 ≤ m → ‖…‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)`. This is `Real.rpow` with m ≥ 1, so it has no edge cases. This matches S3.
- Vacuity: none. `sanity_Fold_hyps` uses x³ + y², where the fold branch is really exercised at 0. The exponent 5/6 = 1/3 + 1/2 is the correct uniform Airy × Gaussian rate. Linear terms do not change the Hessian, so imposing the condition pointwise without reference to p is right. The fold-or-nondegenerate condition is open in (σ, k), so compactness gives uniformity.
- I found no defects.

## D4BoundStatement: FAITHFUL
- Hypotheses: `ContDiff ℝ 4 φ`, `∀ v w, dd φ 0 v w = 0` (that is, D²φ(0) = 0) and `disc (cubicCoeffs φ) < 0`.
- Quantifiers: `∃ δ > 0, ∃ C`, then A, M, y, t.
- Conclusion: `AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t → ‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)`. `Metric.closedBall` is the max-norm ball, as the md says, and y ranges over all of ℝ². This matches S4.1.
- Vacuity: none. For x³ + y³ the sanity lemma gives coefficients (1, 0, 0, 1) and discriminant −27, so the hypotheses can be met.
- **NIT (scope, consistent with the md):** `disc … < 0` covers only the hyperbolic umbilic D4⁺, whose cubic has one real linear factor, as in x³ + y³. The elliptic umbilic D4⁻ (disc > 0) is not covered, even though the section title says "D4 (umbilic)" without a sign. S4.1 in the md explicitly says Disc C < 0, so this is faithful, but the owner should know.
- **NIT:** the header cross-references (`docs/statements.md`, `OscInt/Statements/StationaryPhase.lean`) point to files that are not present in this review copy. This is cosmetic.

## Summary
| Statement | Verdict | Findings |
|---|---|---|
| NonStationaryStatement | FAITHFUL | 1 NIT (`Λ : Type` universe) |
| StationaryPhaseStatement | FAITHFUL | none |
| FoldStatement | FAITHFUL | 1 NIT (same universe note) |
| D4BoundStatement | FAITHFUL | 2 NITs (`disc … < 0` covers D4⁺ only, matching the md; stale header paths) |

There are no BLOCKER, MAJOR or MINOR findings. I found no vacuous hypotheses, no definitions that collapse under Lean conventions (division, `Real.rpow`, `fderiv`, Bochner integral, max norm), and no quantifier-order errors.