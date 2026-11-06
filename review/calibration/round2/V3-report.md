<!-- Calibration round 2, referee for V3 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V3

# Statement review, calibration round 2: directory V3

Files read: `V3/Statements.lean` and `V3/statements.md`. I compiled one scratch copy (`Statements.lean` plus `#print` and `#print axioms` lines, run with `nice -n 10`, then deleted it). The file compiles with no errors. The sanity theorems use only `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`). With `pp.numericTypes`, the elaborated statements read as intended: `m ^ N` is a natural power, `m ^ (-5 / 6 : ℝ)` and `t ^ (-2 / 3 : ℝ)` are rpow, and `ContDiff ℝ (4 : WithTop ℕ∞)`.

## Shared definitions (checked against statements.md)
- `lin p k = p.1 * k.1 + p.2 * k.2` is p·k. Correct.
- `oscInt2 Q A = ∫ k, Complex.exp (↑(Q k) * Complex.I) * A k` is ∫e^{iQ}A. Correct. Under `AmpBound n K A M` with K compact, A is continuous (ContDiff n, n ≥ 0) with compact support, so the integrand is integrable and Lean's value 0 for non-integrable integrands is never reached.
- `dd Ψ k v w = fderiv ℝ (fun y => fderiv ℝ Ψ y v) k w` is ∂_w∂_vΨ(k), and `ddd` is ∂_w∂_v∂_u. Both are nested `fderiv`s and are used only for C⁴ phases, so the junk value 0 never occurs and they are symmetric.
- `hessDet Ψ k = dd Ψ k (1, 0) (1, 0) * dd Ψ k (0, 1) (0, 1) - dd Ψ k (1, 0) (0, 1) ^ 2` is ∂₁∂₁·∂₂∂₂ − (∂₂∂₁)². Matches the md.
- `IsCritical` is ∂₁Ψ + p₁ = ∂₂Ψ + p₂ = 0. Correct.
- `GradLower`: `c ^ 2 ≤ (∂₁Ψ + p₁)^2 + (∂₂Ψ + p₂)^2`. Every statement assumes `0 < c`, so this is equivalent to the Euclidean bound |∇Ψ + p| ≥ c. It does not use the max norm.
- `FoldOrNondeg`: `hessDet ≠ 0 ∨ ((∃ v w, dd Ψ k v w ≠ 0) ∧ ∀ v ≠ 0, (∀ w, dd Ψ k v w = 0) → ddd Ψ k v v v ≠ 0)`. This matches the md: Hessian nonzero and ∂_v³ ≠ 0 on every nonzero kernel vector. The kernel is taken in the first slot, which is harmless because dd is symmetric for C² functions. When `hessDet ≠ 0` the second disjunct is vacuous, which is consistent. ∂_v³Ψ ≠ 0 along the kernel is the right A2 (fold, not cusp) condition, because y*'(0) = 0 in adapted coordinates.
- `AmpBound n K A M`: `ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M`. Matches "amplitude bound (n, K, M)", with `≤ n` and not `< n`. M ≥ 0 is forced, because norms are nonnegative.
- `FamilyCk n Ψ`: each Ψ σ is Cⁿ, and `(σ, k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` is jointly continuous for j ≤ n. Matches the md.
- `cubicCoeffs` / `disc`: a = ∂₁₁₁/6, b = ∂₁₁₂/2 (`ddd φ 0 (1,0) (1,0) (0,1)` is ∂₂∂₁∂₁), c = ∂₁₂₂/2, d = ∂₂₂₂/6. These are the correct Taylor coefficients of (1/6)D³φ(0)[κ³]. The discriminant b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd is the standard one, and the tuple projections (q.1, q.2.1, q.2.2.1, q.2.2.2) give (a, b, c, d) in that order. Check: x³ + y³ gives (1, 0, 0, 1) and disc −27.

## NonStationaryStatement (S2.1)
1. **Verdict: FAITHFUL.**
   - Λ is compact; then N, the family Ψ with `FamilyCk (N + 1)`, compact K and `0 < c`; then `∃ C`; then ∀ A M σ p m.
   - The hypotheses are `AmpBound N K A M`, `∀ k ∈ K, GradLower (Ψ σ) p k c` and `1 ≤ m`, with p unbounded as in the md.
   - The conclusion `≤ C * M / m ^ N` is C M m^{−N}.
   - C may depend on c, which the md allows.
   - The statement is mathematically true: N integrations by parts give coefficients bounded uniformly in p because |∇Φ| ≥ c.
2. **Vacuity hunt: nothing found.**
   - `sanity_NonStationary_hyps` (Ψ = k₁, c = 1, p = 0) together with `sanity_ampBound_exists` shows the hypotheses can be met with a nonzero amplitude.
   - For N = 0 the conclusion becomes |∫A| ≤ C M, which is true and not degenerate.
   - `m ^ N` is a natural-number power with m ≥ 1, so there is no division by zero.
3. **Findings:**
   - NIT: `∀ (Λ : Type)` only quantifies over families indexed in universe 0. This is harmless for the intended use (S4 uses ε ∈ [0, ε₀]).

## StationaryPhaseStatement (S2.2)
1. **Verdict: FAITHFUL.**
   - The hypotheses are `ContDiff ℝ 4 Ψ`, compact K and K′, and `∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0`.
   - `∃ C` comes before A, M, p, m.
   - The amplitude hypothesis is `AmpBound 2 K A M` and the conclusion is `≤ C * M / m`.
   - This matches the md exactly, including the stated single-phase form (no family).
2. **Vacuity hunt: nothing found.**
   - `sanity_StationaryPhase_hyps` uses the saddle k₁² − k₂² and shows that a critical point really occurs, so the nondegeneracy hypothesis is not vacuously satisfied.
   - `/ m` with m ≥ 1 is safe.
   - The statement is true: by compactness of the critical set in K × K′, nondegenerate critical points are isolated uniformly, and the gradient is bounded below elsewhere.
3. **Findings:** none.

## FoldStatement (S3)
1. **Verdict: FAITHFUL.**
   - Λ is compact and the family has `FamilyCk 4`. K and K′ are compact.
   - The hypothesis `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k` is imposed at every point of K, as the md says.
   - `∃ C` comes before A, M, σ, p, m.
   - The amplitude hypothesis is `AmpBound 2 K A M` and the conclusion is `≤ C * M * m ^ (-(5 : ℝ) / 6)`, i.e. the exponent −5/6 (−1/3 from the fold direction, −1/2 from the nondegenerate one).
   - The pointwise condition is open, so by compactness of Λ × K it is uniform, which makes the uniform claim plausible.
2. **Vacuity hunt: nothing found.**
   - `sanity_Fold_hyps` (k₁³ + k₂², one-point family) satisfies the hypotheses and uses the rank-one branch at 0, where `hessDet = 0`. So the fold branch really is used.
   - rpow is applied with base m ≥ 1 > 0.
   - "Hessian nonzero" (`∃ v w, dd Ψ k v w ≠ 0`) rules out rank 0, as intended.
3. **Findings:** NIT: `Λ : Type` universe restriction, as in S2.1.

## D4BoundStatement (S4.1)
1. **Verdict: FAITHFUL** to statements.md.
   - The hypotheses are `ContDiff ℝ 4 φ`, `∀ v w, dd φ 0 v w = 0` (D²φ(0) = 0) and `disc (cubicCoeffs φ) < 0`.
   - Then `∃ δ > 0, ∃ C`, then ∀ A M y t.
   - The amplitude hypothesis is `AmpBound 2 (Metric.closedBall 0 δ) A M`, where the ball is the max-norm ball as the md says. With `1 ≤ t` the conclusion is `‖oscInt2 (fun κ => t * φ κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)`.
   - The linear term is unscaled and y ∈ ℝ² is arbitrary, as in the md.
   - There is no ∇φ(0) = 0 hypothesis, as the md states.
2. **Vacuity hunt: nothing found.**
   - `sanity_D4_hyps` (x³ + y³) meets every hypothesis, with cubicCoeffs = (1, 0, 0, 1) and disc = −27.
   - The `∃ δ` cannot trivialise the conclusion, because the bound must hold for all t ≥ 1 with δ > 0 fixed.
   - rpow is applied with base t ≥ 1.
3. **Findings:**
   - MINOR, about scope rather than fidelity: `disc (cubicCoeffs φ) < 0` covers only the case of one real root (D4⁺, e.g. x³ + y³). The three-real-root case (Disc > 0, D4⁻, e.g. x³ − 3xy²) has the same t^{−2/3} decay and is excluded. The md states `Disc C < 0` too, so Lean matches the md. The md's own reasoning (an isolated critical point holds because a repeated root forces Disc = 0) only needs `Disc ≠ 0`. The owner should confirm that the brief intends only one sign.
   - NIT: the S4 doc header says "Symbols (in addition to `OscInt/Statements/StationaryPhase.lean`)". That path is stale here, because the definitions are in this same file.

## Summary
No BLOCKER or MAJOR findings. All four statements are FAITHFUL to statements.md, and every shared definition checks out against the md and against how Mathlib defines `fderiv`, `iteratedFDeriv`, `tsupport`, `ContDiff`, rpow and the max norm on `ℝ × ℝ`. The only open point is the MINOR `disc … < 0` scope question in S4.1; the remaining two items are NITs (the universe restriction and a stale header reference).