e42dcd3effb9a0d2e13e0635692b6c3f78d8153d

# Referee B: blind pre-proof review of API3 (`OscInt/Statements/Family.lean`)

I did not prove any of the ten statements, in the repository or in scratch. I wrote nothing in the repository. Scratch was limited to `/tmp/referee-B/`:
- `Check.lean` ran `#print` with `pp.numericTypes` and `pp.coercions` on `NonStationaryLocalStatement`, `NonStationaryOnStatement`, `FamilyCkOfUncurryStatement` and `FamilyCk`.
- `num.py` ran one numerical rate check (numpy).

I read `docs/statements.md` (S2/S3, S4, batches 2 and 3), the five `Statements` files, lessons 11, 12, 17 and 24, `OscInt/StationaryPhase/Assembly.lean`, `Final.lean`, and `Blueprint/StationaryPhase.lean`.

## 1. Verdicts

| Statement | Lean constant | Verdict | True? |
|---|---|---|---|
| S2.2F | `StationaryPhaseFamilyStatement` | FAITHFUL | TRUE |
| S3c | `FoldCritStatement` | FAITHFUL | TRUE |
| C10 | `FamilyCkOfUncurryStatement` | FAITHFUL | TRUE |
| FE-S2.1L | `NonStationaryLocalStatement` | FAITHFUL | TRUE |
| FE-S2.2L | `StationaryPhaseLocalStatement` | FAITHFUL | TRUE |
| FE-S3L | `FoldLocalStatement` | FAITHFUL | TRUE |
| FE-S4.1′L | `D4BoundLocalStatement` | FAITHFUL | TRUE |
| FE-S2.1l | `NonStationaryOnStatement` | FAITHFUL | TRUE |
| FE-S2.2l | `StationaryPhaseOnStatement` | FAITHFUL | TRUE |
| FE-S3l | `FoldOnStatement` | FAITHFUL | TRUE |

I found no counterexample.

Points checked:
- **Order of quantifiers.** Every `∃ C` (and `∃ δ > 0, ∃ C` in FE-S4.1′L) comes after all the data: family or `Ψ`, `S`, `V`, `K`, `U`, `K'`, `c`, `N`, `a, b, c, d`. It comes before `A`, `M`, `σ`, `p`/`L`, `m`/`t`. Depending on `V` and `U` is harmless.
- **Smoothness indices.** `#print` shows `ContDiffOn ℝ (↑N + (1 : WithTop ℕ∞)) …`, `ContDiff ℝ (↑N) A`, `ContDiff ℝ (↑n) (Function.uncurry Ψ)`, and `FamilyCk n` unfolds to `ContDiff ℝ (↑n)`. All are finite, so there is no `⊤`/ω problem (lessons 12).
- **Germ-locality.**
  - `fderiv`, `hessianMatrix` (`iteratedFDeriv ℝ 2`) and `iteratedFDeriv ℝ 3 φ 0` are used only at points of an open set where the function is Cⁿ. There they depend only on the germ (`Filter.EventuallyEq.fderiv_eq` / `.iteratedFDeriv`), so arbitrary or discontinuous values outside `U` do not matter.
  - The integrand `exp(i m(Ψ_σ + L))·A` is continuous with compact support even when `Ψ` is wild off `U`. Off `tsupport A` it vanishes on a neighbourhood; on `tsupport A ⊆ K ⊆ U` it is continuous. So the Bochner integral is never the junk 0.
- **Fold condition only at critical points (S3c, FE-S3L, FE-S3l).** This is enough for m^{-5/6}. `fold_of` in `Assembly.lean` already uses `hfold` only in the branch `IsCritical (Q q) 0 k`, with `Q (σ,p) = Ψ σ + lin p`, which is the same as `IsCritical (Ψ σ) p k`. Non-critical points are handled by `LocalNonCritFacts` (rate 1).
  - The classical argument (compactness of the critical set in Λ × K′ × K, and openness of the fold condition in (σ, k) for a C⁴ family) agrees.
  - A degenerate critical point just outside K is harmless: it only fixes a positive gradient bound on K.
- **Rate check.** For Ψ = x³ + y³, p = (0, −3) (fold critical points at (0, ±1); 0 ∈ K is degenerate but not critical) with a product bump amplitude:
  - m^{5/6}|I| stays in 0.08–0.29 for m = 10…10⁴;
  - m|I| = 0.40, 0.17, 0.37, 1.34, so m^{-5/6} is the right rate and m^{-1} would be false.
- **Norms and spaces.**
  - `‖fderiv ℝ (Ψ σ) k + L‖` is the dual norm of the max norm, |∂₁| + |∂₂|. C8 (iii) converts it to `GradLower` with c/√2.
  - The map `L ↦ (L e₀, L e₁)` is continuous linear, so the image of a compact K′ is compact. `lin p k = L k`, and `fderiv + L = 0` is the same as `IsCritical`.
  - In C10, `fun σ : S => Ψ σ` uses the subspace topology. `Function.uncurry Ψ : E × (ℝ×ℝ) → ℝ` and `V ×ˢ U : Set (E × (ℝ×ℝ))` match.
- **Strength.** S3c's hypothesis is implied by S3's, so S3c is stronger than S3 and implies it. With `U = univ` (and `S = {σ₀}`, `V = univ`), each local form becomes its batch-2 sibling exactly; FE-S3l becomes strictly stronger than FE-S3. None of the ten weakens the uniformity of its sibling.

## 2. Derivability

| Statement | Follows from |
|---|---|
| S2.2F | Not from frozen S2.2 + S2.1 + S3: S2.2 is one phase, and S3 gives only m^{-5/6} at nondegenerate points. It does follow from the proved internal parts (`familyAddLinear`, `localization`, `localNonCrit`, `localCrit_of …`), by copying `stationaryPhase_of` with `Unit` replaced by `Λ`. |
| S3c | Copy of `fold_of`, plus `isCritical_add_lin` to turn `IsCritical (Q q) 0 k` into `IsCritical (Ψ σ) p k`. |
| C10 | Mathlib calculus: the partial `iteratedFDeriv` in k is `iteratedFDeriv` of the uncurried map composed with `(0, ·)`. |
| FE-S2.1L | Frozen S2.1 + C8 (iii) + cut-off |
| FE-S2.2L | S2.2F + C3 + cut-off |
| FE-S3L | S3c + C7 + cut-off |
| FE-S4.1′L | FE-S4.1′ + cut-off, with δ' = min(δ, r), where χ = 1 on B̄(0, r) |
| FE-S2.1l, FE-S2.2l, FE-S3l | The L forms with E = ℝ, S = {0}, V = univ (or batch-2 FE-S2.2 directly for FE-S2.2l) |

The cut-off step: let χ ∈ C_c^∞ have `tsupport χ ⊆ U` and χ = 1 near K, and set Ψ̃(σ, k) = χ(k)Ψ(σ, k).
- **Does it give `FamilyCk` on S?** `ContDiffOn` on `V ×ˢ U` alone does not, because `FamilyCk` needs `ContDiff` on all of ℝ² for each member. The cut-off does:
  - (σ, k) ∈ V × U: Ψ̃ is Cⁿ there.
  - k ∉ tsupport χ: Ψ̃ ≡ 0 nearby, an open set.
  - These two regions cover V × ℝ², so the partial k-derivatives are jointly continuous on S × ℝ² ⊆ V × ℝ².
- **Points outside U.** Joint continuity there is not a problem, since Ψ̃ vanishes near them.
- **Hypotheses and integrals.** These transfer by germ-locality on the open set where χ = 1, and because A = 0 off K.
- **Infinite-dimensional E.** Not a problem.
- **Non-Hausdorff Λ.** Not a problem: `localization` takes any compact T.

Nothing stronger than this argument gives has been slipped in, and nothing a user needs is lost, apart from the gaps in §3.

## 3. Vacuity and usefulness

None of the hypotheses is unsatisfiable or trivially strong. The degenerate cases (S = ∅, K = ∅ which forces A = 0, K′ = ∅) are trivially true, harmlessly, as for the siblings.

Example phases:
- **Arccos dispersion relation**, arccos(a cos x + b cos y) with a, b > 0, a + b < 1.
  - It is `ContDiff` on ℝ² through `Real.contDiffAt_arccos` at every point, so the batch-2 forms already apply.
  - As a family in (a, b) it is smooth only where |a| + |b| < 1. FE-S2.2L and FE-S3L handle that through `V`, but C10 does not apply (MINOR 5).
- **Hemisphere** √(1 − x² − y²): use the local forms with U = {k | k.1² + k.2² < 1}.
  - Not `Metric.ball 0 1`, which is the max-norm square and contains points where 1 − x² − y² < 0.
  - The max-norm ball B̄(0, 1/2) is the square [−½, ½]², which lies inside the disc.
  - The Hessian is definite everywhere on the disc, so FE-S2.2l applies with any K′.
- **Family σ₁k₁² + σ₂k₂²** with σ in a compact set away from the axes: hessDet = 4σ₁σ₂ ≠ 0, so S2.2F and FE-S2.2L apply.

## 4. Sanity theorems

- **Lessons 11 is violated (MAJOR 1).** No sanity theorem mentions any of the ten statement constants or a shared hypothesis `def`; each restates the hypothesis inline. None of the following plants in the statements would be detected:
  - `IsCritical (Ψ σ) 0 k`, `IsCritical (Ψ σ) (-p) k`, or `-L`;
  - dropping `p ∈ K'` or `L ∈ K'` from the hypothesis;
  - `V ×ˢ U` replaced by `S ×ˢ K`. This typechecks and makes the hypothesis a `ContDiffOn` on a non-open set, under which the global `fderiv` used in the hypotheses can be junk. A literal `U ×ˢ V` swap would not typecheck for general `E`.
  - `K ⊆ U` reversed;
  - a changed exponent.
- **S2.2F witness.** It is a two-member `Bool` family; for finite Λ, S2.2F is just the maximum of two S2.2 constants. Its only critical witness is at p = 0, k = 0, which is blind to a `p`→`0` or `k`→`0` plant. Its bite member 3y² is degenerate everywhere, so it does not separate "at critical points" from "everywhere".
- **S3c bite.** It separates the hypotheses of S3c and S3, and with K′ = {(−3, −3)} it would catch a `p`→`0` plant if bundled. But every critical point in it is nondegenerate, so the conclusion already follows from frozen S2.2. It is also sign-symmetric, so it is blind to a `-p` plant (the `-p` hypothesis is vacuously true there).
- **C10 and local-smoothness theorems.** They show only that the hypotheses are satisfiable; that is acceptable.

Derivative-level checks to add after the proofs, through the bridges:
- `hessianMatrix` of a quadratic with generic, distinct, nonzero coefficients including a mixed term (to pin the indices);
- `FoldOrNondegMatrix` for x³ + y³ at (0, 1);
- the hemisphere Hessian at a non-central point;
- the arccos family on V = {|a| + |b| < 1};
- FE-S4.1′L for a generic cubic (1, 2, 3, 5) multiplied by a function smooth only near 0, checking that `iteratedFDeriv ℝ 2/3 φ 0` agrees with the cut-off phase;
- a bite showing each local form applies where `ContDiff` on ℝ² fails, through the actual statement constant.

## 5. Findings

**MAJOR 1. The sanity theorems test restatements, not the statements (lessons 11).**
- Affected theorems: `sanity_StationaryPhaseFamily_hyps`, `sanity_FoldCrit_bite`, `sanity_FamilyCkOfUncurry_hyps`, `sanity_local_bite`.
- Example: the hypothesis line `(∀ σ, ∀ p ∈ K', ∀ k ∈ K, IsCritical (Ψ σ) p k → FoldOrNondeg (Ψ σ) k)` in `FoldCritStatement` is restated by hand in `sanity_FoldCrit_bite`. The same holds for `(∀ σ ∈ S, ∀ L ∈ K', ∀ k ∈ K, fderiv ℝ (Ψ σ) k + L = 0 → FoldOrNondegMatrix (Ψ σ) k)`, `ContDiffOn ℝ 4 (Function.uncurry Ψ) (V ×ˢ U)`, and the others.
- Fix: bundle each hypothesis as a named `def` used by both the statement and the sanity theorem.

**MINOR 2. S2.2F's route needs the internal parts.** The docs line "(S2.2 with the family uniformity that S2.1 and S3 already have)" is right about the content. S2.2F is not derivable from the frozen S2.2/S3 (rate 5/6 only); it needs `localCrit_of …` (family-uniform), which is proved. The docs should say so, so that "derivable from frozen statements" is not claimed.

**MINOR 3. The S3c bite does not show new content.**
- Its conclusion (x³ + y³, K′ = {(−3, −3)}) is already given by S2.2.
- Proposed replacement: x³ + y³ with K = B̄(0, 2) and K′ = {(0, −3)}.
  - The critical points (0, ±1) are folds: Hessian diag(0, ±6), kernel e₁, D³[e₁³] = 6.
  - 0 ∈ K is degenerate but not critical.
  - Neither S2.2 nor S3 applies; the numerical rate check above confirms m^{-5/6} is sharp.
- To pin the sign of p, add a bite such as x⁴ + 4x + y² with K′ = {(4, 0)}:
  - the hypothesis holds (critical point at x = −∛2, nondegenerate);
  - the `-p` version fails (critical point at x = 0, Hessian diag(0, 2), third derivative 24x = 0).

**MINOR 4. The S2.2F witness is too weak.** The `Bool` family is finite and the critical witness is at (p, k) = (0, 0). Use an infinite parameter (e.g. σ ∈ [1, 2], σx² − y²) and a critical pair with p ≠ 0 and k ≠ 0 (e.g. p = (−2, 0), k = (1, 0) for x² − y²).

**MINOR 5. C10 covers only globally smooth families.** `ContDiff ℝ n (Function.uncurry Ψ) → ∀ S : Set E, FamilyCk n …` requires smoothness on all of E × ℝ². It does not cover families smooth only for σ in an open set, such as the arccos family. A variant with `ContDiffOn` on `V ×ˢ univ`, `S ⊆ V`, `V` open would be more useful. There is also no Mathlib-idiom form for families that are only continuous in σ, or a local-smoothness form for a general compact Λ. Both gaps are documented choices, not defects.

**NIT 6. Hemisphere consumer example.** `U` must be the Euclidean disc set, not `Metric.ball 0 1`, which is the max-norm square. The example should say so.

**NIT 7. Docstring wording.** The sanity docstring "so S3 does not apply" is accurate, but should add "S2.2 does" for this data.

Relevant paths: `/home/user/lean-oscillatory/OscInt/Statements/Family.lean`, `/home/user/lean-oscillatory/docs/statements.md`, `/home/user/lean-oscillatory/OscInt/StationaryPhase/Assembly.lean`, `/home/user/lean-oscillatory/Blueprint/StationaryPhase.lean`, `/tmp/referee-B/Check.lean`, `/tmp/referee-B/num.py`.