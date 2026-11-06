<!-- Calibration round 2, referee for V5 (fresh-context agent, prompt review/prompts/calibration-r2.md). Verbatim final report. -->

V5

# Statement review, calibration round 2: directory V5

I read only `V5/Statements.lean`, `V5/statements.md` and Mathlib. I compiled one scratch file, `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/calib2/V5/Check.lean`. It is a copy of the definitions plus a counterexample, and it compiles with no errors and no `sorry`.

## Shared definitions, checked against S2/S3/S4 notation
- `lin`, `oscInt2` (`exp (Q k * I) * A k`, Bochner integral over `ℝ × ℝ`): correct.
- `dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w` is ∂_w∂_vΨ(k), and `ddd Ψ k u v w` is ∂_w∂_v∂_uΨ(k): correct.
- `hessDet = dd e₁e₁ · dd e₂e₂ − (dd e₁e₂)²`: correct.
- `IsCritical`: correct. `GradLower` (stated with squares, `c > 0`): matches |∇Ψ_σ + p| ≥ c with the Euclidean norm.
- `AmpBound n K A M`: `ContDiff ℝ n A`, `tsupport A ⊆ K`, `‖iteratedFDeriv ℝ j A k‖ ≤ M` for all k and j ≤ n. Correct. M ≥ 0 is forced by j = 0, and the integrand is continuous with compact support, so the integral is never a junk 0.
- `FamilyCk`: each Ψ σ is Cⁿ, and `(σ,k) ↦ iteratedFDeriv j` is jointly continuous for j ≤ n. Correct.
- `FoldOrNondeg`: correct. If `hessDet = 0` and the Hessian form is nonzero, it has rank one, and "for every v ≠ 0 with dd(v,·) = 0, ddd v v v ≠ 0" is the kernel condition.
- `disc`: same formula as the md.
- **`cubicCoeffs`: wrong, see the BLOCKER under D4BoundStatement.**

## NonStationaryStatement (S2.1)
**Verdict: FAITHFUL.**
- Quantifiers are in the md's order: Λ, N, Ψ, K, c, then `∃ C`, then A, M, σ, p, m.
- Regularity matches: `FamilyCk (N + 1)` for the phase, `AmpBound N K` for the amplitude.
- The gradient condition is required on all of K, and p is unrestricted, as the md says.
- The bound is `C * M / m ^ N` with `1 ≤ m`, so there is no division by zero.

Vacuity hunt: nothing found. The sanity theorems cover the hypotheses (one-point family, Ψ = k₁, c = 1). For N = 0 the conclusion is non-trivial but true (`‖I‖ ≤ M·vol K`).

Findings:
- NIT: `(Λ : Type)` restricts Λ to universe 0. This is harmless.

## StationaryPhaseStatement (S2.2)
**Verdict: FAITHFUL.**
- `ContDiff ℝ 4 Ψ`, compact K and K′, and the condition `∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0` all match the md.
- `∃ C` comes before A, M, p, m.
- The bound `C * M / m` uses `AmpBound 2`. The md declares C² amplitudes as a deliberate choice.

Vacuity hunt: nothing found. The hypotheses are satisfiable with a real critical point (the saddle k₁² − k₂², `sanity_StationaryPhase_hyps`). `hessDet` is built from nested `fderiv`s of a C⁴ function, so it is the genuine Hessian determinant.

Findings:
- MINOR (truth, not fidelity): `AmpBound 2 K A M` with only a C⁴ phase is the md's own PLAUSIBLE choice. The Morse-lemma route costs derivatives, so whether C² amplitudes are enough here needs to be checked when the proof is reviewed.

## FoldStatement (S3)
**Verdict: FAITHFUL.**
- Compact family with `FamilyCk 4`, compact K and K′.
- `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k` is imposed independently of p, as the md says.
- `∃ C` comes before A, M, σ, p, m.
- The bound is `C * M * m ^ (-(5 : ℝ) / 6)` (`Real.rpow`, base ≥ 1, exponent −5/6 as intended).

Vacuity hunt: nothing found. `ddd` is the `fderiv` of a C² function, so it is meaningful. `sanity_Fold_hyps` shows the rank-one branch is really used (k₁³ + k₂², with hessDet = 0 at 0).

## D4BoundStatement (S4.1)
**Verdict: UNFAITHFUL. As written, the statement is false.**

- **BLOCKER.** The third component of `cubicCoeffs` is wrong:
  ```lean
  ddd φ 0 (0, 1) (1, 0) (1, 0) / 2
  ```
  This is ∂_{e₁}∂_{e₁}∂_{e₂}φ(0)/2 = ∂³₁₁₂φ(0)/2, which is the same as `b`. The md requires c = ∂³₁₂₂φ(0)/2, i.e. `ddd φ 0 (1, 0) (0, 1) (0, 1) / 2` (or any order of the indices with two `(0, 1)`). The header's comment ("`c = ∂³_{122}φ(0)/2` (via `ddd`)") disagrees with the code.
  - **Proved counterexample** (in `Check.lean`, theorem `counter`). Take φ = x³ + x²y.
    - φ is C⁴ and `dd φ 0 v w = 0` for all v, w.
    - Lean gives `cubicCoeffs φ = (1, 1, 1, 0)` and `disc = 1 − 4 = −3 < 0`.
    - The true coefficient is ∂³₁₂₂φ(0) = 0, so the true cubic is x²(x + y). It has a repeated linear factor, and its true discriminant is 0. This is not a D4 point.
  - **Why the conclusion fails (paper argument).** Substitute u = x + y (linear, determinant 1), so the phase becomes x²u.
    - Take A = a(x)·b(x + y), with a and b bumps whose supports are small enough for `tsupport A ⊆ closedBall 0 δ`. Take a(0) ≠ 0, b ≥ 0, b ≠ 0, b supported in u > 0, and y = 0.
    - Then I(t) = ∫ a(x) b̂(t x²) dx, and t^{1/2} I(t) → a(0) ∫ b̂(s²) ds = a(0) √π e^{iπ/4} ∫ b(u) u^{−1/2} du ≠ 0.
    - So |I(t)| ≥ c′ t^{−1/2} for large t, which is incompatible with `C * M * t ^ (-(2 : ℝ) / 3)` for every δ > 0 and every C. `D4BoundStatement` is therefore refutable.
  - The intended statement (correct `c`) would be much weaker in the sense of covering fewer phases; the frozen one asserts a false bound for degenerate cubics that slip through.
  - Fix: replace that entry with `ddd φ 0 (1, 0) (0, 1) (0, 1) / 2`.
- **MINOR (process).** `sanity_D4_hyps` uses φ = x³ + y³. Its mixed coefficients b and c are both 0, so it cannot detect the swapped index. A sanity check should use a cubic with every coefficient nonzero, or one with a repeated factor whose `disc` must come out 0.

Everything else in D4BoundStatement matches the md: `ContDiff ℝ 4 φ`; `∀ v w, dd φ 0 v w = 0` (D²φ(0) = 0); no ∇φ(0) hypothesis (declared); `∃ δ > 0, ∃ C` after φ and before A, M, y, t; y ∈ ℝ² unrestricted; phase `t * φ κ + lin y κ` (linear term not scaled by t, as in the md); the ball is the max-norm `closedBall 0 δ` (declared); `Real.rpow` with t ≥ 1.

- NIT (md, not the Lean): Disc C < 0 covers only the hyperbolic umbilic (one real linear factor, e.g. x³ + y³ with disc −27). The elliptic umbilic (Disc > 0, e.g. x³ − 3xy²) has the same t^{−2/3} decay but is excluded. The Lean matches the md, so this is a weakening only relative to any brief that means "D4" in general.

## Summary
| Statement | Verdict | Findings |
|---|---|---|
| NonStationaryStatement | FAITHFUL | NIT (`Λ : Type`) |
| StationaryPhaseStatement | FAITHFUL | MINOR (C² amplitude sufficiency is the md's PLAUSIBLE choice) |
| FoldStatement | FAITHFUL | none |
| D4BoundStatement | UNFAITHFUL, false as stated | BLOCKER (`cubicCoeffs` c-entry `ddd φ 0 (0, 1) (1, 0) (1, 0) / 2` is ∂₁₁₂/2, not ∂₁₂₂/2; counterexample x³ + x²y compiled in `Check.lean`); MINOR (sanity check blind to it); NIT (Disc < 0 covers one D4 type only) |