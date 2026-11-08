e42dcd3effb9a0d2e13e0635692b6c3f78d8153d

# Referee A: blind pre-proof review of front-end batch 3 (API3)

**Scope.** I read `docs/statements.md` (S2/S3, S4, batch 2, and all of batch 3) and `OscInt/Statements/{Family,StationaryPhase,D4,D4Limit,FrontEnd,Convert}.lean`. I also read `docs/lessons.md` entries 11, 12, 17 and 24, `OscInt/StationaryPhase/Assembly.lean`, `Blueprint/StationaryPhase.lean` and some Mathlib sources.

**What I ran.** Everything went under `/tmp/referee-A/`; the repository is unmodified.
- `Check1.lean` elaborated the definitions:
  - `#print` shows the regularity indices are `↑N + (1 : WithTop ℕ∞)` and `↑n`. Both are finite, so there is no `⊤` and no analyticity (lessons 12).
  - Swapping `V ×ˢ U` for `U ×ˢ V` does not type-check: `Set ((ℝ × ℝ) × E)` is not `Set (E × ℝ × ℝ)`.
  - `(1,1) ∈ closedBall (0 : ℝ × ℝ) 1` holds, which confirms the max norm.
- `fold_num.py` checked numerically the uniform Airy factor of a fold: sup over p ∈ [−1,1] of |∫e^{im(x³+px)}a| times m^{1/3} is 0.78, 0.84, 0.81, 0.67 for m = 10…10⁴. Times m^{1/2} it grows (1.1 → 3.1). This is consistent with the m^{−5/6} rate.

I did not prove any statement under review, not even in scratch.

## 1. Verdicts (faithfulness to `docs/statements.md` and truth)

| Constant | Verdict | True? |
|---|---|---|
| S2.2F `StationaryPhaseFamilyStatement` | FAITHFUL | TRUE |
| S3c `FoldCritStatement` | FAITHFUL (stronger than S3, as intended) | TRUE |
| C10 `FamilyCkOfUncurryStatement` | FAITHFUL | TRUE |
| FE-S2.1L `NonStationaryLocalStatement` | FAITHFUL | TRUE |
| FE-S2.2L `StationaryPhaseLocalStatement` | FAITHFUL | TRUE |
| FE-S3L `FoldLocalStatement` | FAITHFUL | TRUE |
| FE-S4.1′L `D4BoundLocalStatement` | FAITHFUL | TRUE |
| FE-S2.1l `NonStationaryOnStatement` | FAITHFUL | TRUE |
| FE-S2.2l `StationaryPhaseOnStatement` | FAITHFUL | TRUE |
| FE-S3l `FoldOnStatement` | FAITHFUL | TRUE |

I found no counterexample to any of the ten.

**Quantifiers.** In every statement `∃ C` (and `∃ δ > 0, ∃ C` in FE-S4.1′L) comes after the data: family or `Ψ`, `S, V, K, U`, and `K'` or `c`/`N`. It comes before `A, M, σ, p/L, m/t`, as the docs require. The membership conditions `σ ∈ S` and `L ∈ K'` sit inside, after `∃ C`.

**S3c / FE-S3L / FE-S3l: is the fold condition at critical points only enough for m^{−5/6}?** Yes. The argument has four parts:
- **Non-critical points.** At a non-critical (σ, p, k), the gradient stays away from 0 on a small ball, uniformly for nearby (σ′, p′). This gives a local rate of m^{−1}.
- **Critical points.** At a critical point the fold condition gives a local rate of m^{−5/6}, uniformly in nearby (σ′, p′). This is `LocalCritFacts`, already proved for S3.
- **Compactness.** Localisation over the compact set Λ × K′ × K gives the global bound.
- **No degenerate point can escape the hypothesis.** Suppose degenerate critical points k*(σ_n, p_n) (rank 0, or rank one with a vanishing cubic along the kernel) accumulated at a point of K. By joint continuity (`FamilyCk 4`), compactness of K′ and closedness of the degenerate condition, the limit would be a degenerate critical point in K with p ∈ K′. That is excluded.

The internal assembly `fold_of` already uses `hfold` only under `IsCritical (Q q) 0 k`, so S3c is a re-assembly of the existing parts over Λ × K′. The same holds for S2.2F with the `hessDet` branch (`stationaryPhase_of` with Λ × K′ instead of Unit × K′). A linear term changes neither the Hessian nor the third derivative (`foldOrNondeg_add_lin`, `hessDet_add_lin`).

**Local smoothness and derivatives.** At `k ∈ U` (open), `fderiv`, `iteratedFDeriv`, and therefore `hessianMatrix` and `iteratedFDeriv ℝ 2 φ 0`, depend only on the germ of the function. Values outside `U` are irrelevant. Every hypothesis evaluates derivatives only at `k ∈ K ⊆ U` with `σ ∈ S ⊆ V`, or at `0 ∈ U`. So none of them can be satisfied by junk values such as `fderiv = 0` at a non-differentiable point.

**The integral.** The integrand `exp(i m(Ψ_σ k + L k)) · A k` is literally equal, at every point, to the integrand for the cut-off phase χΨ_σ. Where `A k ≠ 0` we have `k ∈ K` and χ = 1; elsewhere both sides are 0. So a non-measurable phase outside U causes no Bochner-integral problem.

**C10.** Ψ_σ = (uncurry Ψ) ∘ (k ↦ (σ, k)), which is affine, so each Ψ_σ is Cⁿ. D^jΨ_σ(k) = D^j(uncurry Ψ)(σ, k) ∘ (inr, …, inr), which is jointly continuous for j ≤ n (n finite). Restricting to S with the subspace topology preserves continuity. Completeness of E is not needed. TRUE.

**Max norm.** ‖L‖ for L on ℝ × ℝ is |L e₀| + |L e₁|, and B̄(0, δ) is a square. Both match batch 2 and the docs.

## 2. Derivability

All seven new FE-L/l and C-forms follow from frozen, proved statements plus S2.2F and S3c. S2.2F and S3c themselves follow from the existing internal parts (`FamilyAddLinearFacts`, `LocalizationFacts`, `LocalNonCritFacts`, `LocalCritFacts`) by re-assembly over Λ × K′. None follows from the frozen single-phase S2.2, or from S3 (which needs the fold condition everywhere), alone.

**FE-S2.1L.** Take a smooth χ equal to 1 on a neighbourhood of K, with compact `tsupport χ ⊆ U`, and set Φ_σ = χ·Ψ_σ for σ ∈ S.
- Each Φ_σ is globally C^{N+1}.
- On S × U, D^jΦ_σ(k) is a Leibniz sum of D^iχ and k-partial derivatives of uncurry Ψ. These are continuous on V × U because `ContDiffOn` on an open set makes `iteratedFDerivWithin = iteratedFDeriv` continuous.
- On S × (tsupport χ)ᶜ the derivative is identically 0.
- These two open sets cover ℝ², so `FamilyCk (N+1)` holds on Λ = S (`CompactSpace S` from `IsCompact S`).
- On K, `fderiv Φ_σ = fderiv Ψ_σ`. The bound c ≤ ‖·‖ in the max-norm dual gives `GradLower` with c/√2 (C8 (iii)).
- L = lin(L e₀, L e₁), and S2.1 is uniform over all p.

**FE-S2.2L / FE-S3L.** Use the same cut-off.
- `hessianMatrix` and `iteratedFDeriv 3` of Φ_σ equal those of Ψ_σ on K (`Filter.EventuallyEq.iteratedFDeriv`).
- C3 and C7 convert them to `hessDet` and `FoldOrNondeg`.
- The image of K′ under L ↦ (L e₀, L e₁) is compact, since that map is continuous linear.
- Critical points correspond exactly: `fderiv Ψ_σ k + L = 0` holds iff `IsCritical Ψ_σ (L e₀, L e₁) k`.
- Then apply S2.2F or S3c with Λ = S.

**FE-S4.1′L.** Cut off near 0 with χ = 1 on B̄(0, r) ⊆ U. Derivatives at 0 are unchanged. Apply FE-S4.1′, which is proved, and take δ = min(δ₀, r).

**FE-S2.1l/2.2l/3l.** Take E = ℝ, S = {0}, V = univ, with the family constant in σ. With U = univ these recover FE-S2.1, FE-S2.2 and a strengthening of FE-S3. No uniformity is weaker than in the batch-2 sibling.

**Where the argument needs care.** Nothing fails, but three points need attention:
- `ContDiffOn` on V ×ˢ U with S ⊆ V does **not** give `FamilyCk` on S directly, because `FamilyCk` asks for global `ContDiff` of each Ψ_σ. The cut-off is required, and C10 is not the tool here because it needs global `ContDiff` on E × ℝ².
- Joint continuity at points k ∉ U holds only because Φ vanishes on the open set (tsupport χ)ᶜ.
- The compactness of K′'s image is immediate.

Nothing stronger than the cut-off argument gives has been slipped into a conclusion, and nothing a user needs has been lost.

## 3. Vacuity and usefulness

**Degenerate data.** If S, Λ or K′ is empty, the conclusion holds vacuously because there is no σ, or no p/L. If K is empty, A = 0 and C = 0 works, since M ≥ ‖D⁰A‖ ≥ 0. For N = 0, FE-S2.1L is the trivial bound M·vol(K). In each case the triviality is confined to that degenerate instance, which is harmless.

**Arccos example, Ψ = arccos(a cos x + b cos y) with a, b > 0, a + b < 1.**
- Mathlib has `Real.contDiffOn_arccos : ContDiffOn ℝ n arccos {-1, 1}ᶜ` and `contDiffAt_arccos`.
- The argument stays in [−(a+b), a+b] ⊂ (−1, 1), so `ContDiffAt` holds everywhere. That gives `ContDiff` (batch 2 would already do) or `ContDiffOn` on any U.
- As a family in σ = (a, b), take V = {|a| + |b| < 1} (open) and U = univ. This is dischargeable.
- C10 does not apply here, because the family is not smooth on all of ℝ² × ℝ².

**Hemisphere example, √(1 − x² − y²).**
- Take U = {x² + y² < 1}. It is open by continuity, and `Real.contDiffAt_sqrt` gives `ContDiffOn` on it.
- K = `closedBall 0 (1/2)` is the max-norm square [−½, ½]², whose corners are at distance ≈ 0.707 < 1, so K ⊆ U.
- The Hessian is negative definite on the disc, so FE-S2.2l applies.
- Pitfall: `Metric.ball 0 1` is the open square, not the disc (see NIT N1).

**Quadratic family σ₁k₁² + σ₂k₂², with σ in a compact set away from the axes.** It is polynomial, so jointly smooth (V = univ, U = univ). det H = 4σ₁σ₂ ≠ 0. This is usable through FE-S2.2L with E = ℝ × ℝ, or through C10 and S2.2F.

**Hypotheses that are trivially strong or unsatisfiable.** None are unsatisfiable. The joint C^{N+1} / C⁴ smoothness in σ is more than the mathematics needs (see MINOR m3).

## 4. Sanity theorems

**What they show.** Generic witnesses: a two-member Bool family with distinct K ≠ K′ and a critical point present, and the S3c bite x³ + y³ with K = B̄(0, 2), K′ = {(−3, −3)}. I checked the bite by hand: the critical points are (±1, ±1), all in K, with hessDet = 36xy ≠ 0. At 0 the Hessian vanishes, so S3 would not apply. The C10 hypothesis is satisfiable, and the |k₁| local bite is correct.

**What they miss.**
1. **They restate the hypotheses inline instead of using shared definitions (lessons 11).** No sanity theorem mentions a statement constant or a hypothesis `def` shared with it. A plant that swaps `IsCritical (Ψ σ) p k` for `IsCritical (Ψ σ) 0 k`, or `fderiv ℝ (Ψ σ) k + L = 0` for `… - L = 0`, would therefore go undetected. So would `∀ σ ∈ S` changed to `∀ σ ∈ V` in the hypothesis, `S ⊆ V` changed to `V ⊆ S`, or `Set.univ ×ˢ U` in place of `V ×ˢ U`. The `V ×ˢ U` ↔ `U ×ˢ V` swap is caught by the elaborator; I verified it is a type error.
2. **The S2.2F witness is not specific to critical points (lessons 17).** Its quadratics have constant Hessian determinant, so the hypothesis holds everywhere and the witness cannot tell "critical points only" from "everywhere". Its critical-point witness uses p = 0, which cannot tell `p` from `0`. Its bite (0·x² + 3y²) is degenerate everywhere, so it fails both forms.
3. **The forms in Mathlib's idiom have no sanity check at the level of their hypotheses.** FE-S2.1L/2.2L/3L/4.1′L and the l-forms have nothing beyond the |k₁| smoothness bite. In particular nothing checks `hessianMatrix` or `fderiv … + L = 0` on a phase that is singular outside U, with S ⊊ V and K ⊊ U.

**Derivative-level checks to add after the proofs:**
- (a) The arccos phase, with `hessianMatrix` computed at a critical point, through FE-S2.2l.
- (b) The hemisphere on U = the Euclidean disc with K = B̄(0, ½), with a non-symmetric K′ = {L₀} (L₀ e₀ ≠ L₀ e₁, both nonzero) to pin the sign of `+ L` and the e₀/e₁ order.
- (c) The bite x³ + y³ with K′ = {(−3, −3)} at the level of `FoldOrNondegMatrix` and FE-S3l. This is the case where the critical-only hypothesis holds and the everywhere hypothesis fails.
- (d) For S2.2F, a family whose Hessian degenerates only at non-critical points of K (e.g. x³ + y² + 2x with K′ near 0 and 0 ∈ K). This separates S2.2F from an "everywhere" plant, and p from 0.
- (e) FE-S4.1′L on a phase smooth only near 0 with generic coefficients (1, 2, 3, 5), e.g. (x³ + 2x²y + 3xy² + 5y³)/(1 − x) on {x < 1}.
- (f) A family with E = ℝ², S compact, V ⊋ S, and Ψ singular outside V (e.g. the arccos family in (a, b)).

## 5. Findings

**BLOCKER:** none.

**MAJOR**

- **M1 (lessons 11 and 17): the sanity theorems test copies of the hypotheses, not the statements.** Every sanity theorem in `Family.lean` restates its hypothesis in its own words. For example, `sanity_StationaryPhaseFamily_hyps` contains
  `(∀ σ, ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 2, ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1, IsCritical (… σ) p k → hessDet (… σ) k ≠ 0)`
  and `sanity_FoldCrit_bite` contains
  `∀ p ∈ ({(-3, -3)} : Set (ℝ × ℝ)), ∀ k ∈ …, IsCritical … p k → FoldOrNondeg … k`.
  They do not share a named hypothesis `def` with `StationaryPhaseFamilyStatement` / `FoldCritStatement`, and the statements are not instantiated. So a plant in any statement body (e.g. `IsCritical (Ψ σ) 0 k`, `fderiv ℝ (Ψ σ) k - L = 0`, `∀ σ ∈ V`, `V ⊆ S`) leaves every sanity theorem green. Lessons 11 says to bundle hypotheses as named defs used by both the statement and its sanity theorem. The statement constants are pinned, so this cannot be fixed in this batch. It should be recorded, and the post-proof derivative checks should go through the statement constants or their bridges.

**MINOR**

- **m1 (lessons 17): the S2.2F witness and bite do not test the critical-only feature.**
  - The witness family `sanityQuadFamily (fun σ => if σ then 1 else 2) (fun σ => if σ then -1 else 3)` has constant hessDet (−4 and 24), so its hypothesis would also hold with "at every k ∈ K".
  - The critical-point witness `IsCritical (…) false) 0 0` uses p = 0.
  - The bite `(fun σ => if σ then 1 else 0)` is degenerate everywhere.

  Together they separate neither critical-only from everywhere, nor p from 0 (see check (d) above).
- **m2: there is no sanity theorem for the hypotheses of FE-S2.1L / FE-S2.2L / FE-S3L / FE-S4.1′L / FE-S2.1l / FE-S2.2l / FE-S3l.** The only one, `sanity_local_bite`, concerns the smoothness predicate. The roles S ≠ V, K ≠ U, and the critical condition `fderiv ℝ (Ψ σ) k + L = 0` are not exercised before the proofs.
- **m3: the joint smoothness hypotheses ask for more regularity in σ than the mathematics needs.** The hypotheses are `ContDiffOn ℝ (N + 1) (Function.uncurry Ψ) (V ×ˢ U)` and `ContDiffOn ℝ 4 (Function.uncurry Ψ) (V ×ˢ U)`, i.e. C^{N+1} or C⁴ jointly in σ. The proofs need only k-smoothness with k-derivatives jointly continuous in (σ, k) on S × U. The rescaled family that S4 itself uses, ε⁻³φ(εz) on ε ∈ [0, ε₀], is `FamilyCk 4` but in general not C⁴ in (ε, z) on an open V ∋ 0, so it is out of reach of the FE-L forms. The docs flag joint smoothness as a modelling choice. Still, there is no local analogue of C10 ("C^n in k on U, k-derivatives jointly continuous on V × U ⇒ `FamilyCk` of the cut-off family"), which leaves a gap for users with families that are only continuous in σ. Candidate for the next batch.
- **m4: C10 is not used by its siblings in this batch, and `docs/statements.md` (C10 and the modelling choices) does not say so.** `FamilyCkOfUncurryStatement` requires `ContDiff ℝ n (Function.uncurry Ψ)` on all of E × ℝ². It therefore does not serve the local forms (which need the cut-off) or examples with singularities, such as the arccos family in (a, b). It is correct and useful only for globally smooth families.

**NIT**

- **N1: `Metric.closedBall 0 δ` and `Metric.ball` on `ℝ × ℝ` are max-norm squares.** For the hemisphere, choosing K = `closedBall 0 (3/4)` silently leaves the disc (the corner is at ≈ 1.06). This is worth a sentence in the user-facing docs and example.
- **N2: the docstring of `sanity_local_bite` overstates the gap.** It says "so the local statements apply to phases that front-end batch 2 (`ContDiff` on `ℝ²`) does not". After a hand-made cut-off, batch 2 covers these phases too. The gain is in what the user has to prove, not in mathematical reach.
- **N3: the FE-S3L docstring says "matrix fold-or-nondegenerate condition" without naming the form.** The form is the span form (`FoldCondSpan`); C7 shows it is equivalent to the rank form only under C³ near k, which holds here.
- **N4: E is restricted to universe 0.** The binder is `(E : Type)` in C10 and the FE-L statements, and `Λ : Type` is likewise restricted. This matches the frozen statements and is harmless for ℝⁿ.

**Summary.** All ten statements are FAITHFUL to `docs/statements.md` and TRUE. They follow from the proved parts by localisation over Λ × K′ (S2.2F, S3c) and by a cut-off equal to 1 near K and supported in U (the local forms), with no step that fails. The weakness is in the sanity layer (M1, m1, m2), not in the statements.