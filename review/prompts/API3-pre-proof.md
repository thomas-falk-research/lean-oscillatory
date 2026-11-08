# Blind statement review: front-end batch 3 (S2.2F, S3c, C10; FE-S2.1L, FE-S2.2L, FE-S3L, FE-S4.1′L; FE-S2.1l, FE-S2.2l, FE-S3l)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No Lean proof of these ten statements exists in the repository or in the lead's scratch. **Do not prove the
statements under review, not even in your own scratch: numerical checks, counterexample searches and Lean checks of
small facts about definitions (e.g. evaluating a definition on concrete data) only** (lessons 24). Disclosure: the
repository contains, since session 2, the internal assembly `OscInt/StationaryPhase/Assembly.lean` (`fold_of`,
`stationaryPhase_of`) and the blueprint interfaces `Blueprint/StationaryPhase.lean`; you may read them, as they bear
on how the new statements relate to existing code, but judge the statements on their own.

Read: `docs/statements.md` (section "Front end, batch 3" in full; S2/S3, S4 and "Front end, batch 2" for shared
notation and for the frozen statements this batch is meant to follow from), `OscInt/Statements/Family.lean` (the
batch), `OscInt/Statements/StationaryPhase.lean`, `D4.lean`, `D4Limit.lean`, `FrontEnd.lean`, `Convert.lean` (shared
definitions and the frozen statements), `docs/lessons.md` (entries 11, 12, 17, 24), and Mathlib sources under
`.lake/packages/mathlib`. You may compile scratch files under `/tmp/<your name>/` with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root (`export PATH=$HOME/.elan/bin:$PATH`;
one Lean process at a time) and run numerical checks (Python, standard library or numpy if present). Write nothing in
the repository.

For each statement constant in `Family.lean`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL. Is it TRUE? If
   you believe it false, give a concrete counterexample (exact data) and check it numerically or in Lean. Pay
   attention to: the placement of `∃ C` (and `∃ δ`) relative to the family parameter, `A`, `M`, `L`/`p`, `m`/`t`;
   that S3c and the FE-S3 forms ask for the fold condition only at critical points of `Ψ_σ + p·` (resp. `+ L`) with
   `p ∈ K'` (resp. `L ∈ K'`), and whether that is enough for the m^{-5/6} bound; `ContDiffOn` on `V ×ˢ U` with `V`, `U`
   open, and the meaning of `fderiv`, `hessianMatrix` (an `iteratedFDeriv`) and `iteratedFDeriv ℝ 2 φ 0` for a
   function that is smooth only on an open set and arbitrary (possibly discontinuous) elsewhere; `Function.uncurry`
   and the subspace topology on `S` in C10; `ContDiff ℝ n` with `n : ℕ` cast to `WithTop ℕ∞` (lessons 12: `⊤` would
   mean analytic); the max norm on `ℝ × ℝ` (operator norm of a functional is |L e₀| + |L e₁|).
2. Derivability: is each statement implied by the frozen, proved statements (S2.1 `NonStationaryStatement`, S2.2
   `StationaryPhaseStatement`, S3 `FoldStatement`, S4.1′ `D4BoundNeStatement`, batch 2 C1–C9 and the FE forms), or by
   the existing internal parts, as the docs suggest (families: localisation over `Λ × K'`; local smoothness: multiply
   the phase by a smooth cut-off equal to 1 near `K` and supported in `U`)? Name any step where this argument fails
   (e.g. joint continuity in `(σ, k)` of derivatives of the cut-off phase at points outside `U`, compactness of the
   image of `K'` under `L ↦ (L e₀, L e₁)`, or whether `ContDiffOn` on `V ×ˢ U` with `S ⊆ V` gives `FamilyCk` on `S`).
   Is anything stronger than what that argument gives slipped in, or anything a user needs lost?
3. Vacuity and usefulness: can a user discharge each hypothesis for an explicit phase, e.g. the arccos-type
   dispersion relation Ψ(x, y) = arccos(a cos x + b cos y) with a, b > 0, a + b < 1 (smooth on ℝ², but provably so in
   Mathlib only through `ContDiffOn` of `arccos` on `(−1, 1)`), the hemisphere phase √(1 − x² − y²) on the open unit
   disc with an amplitude supported in B̄(0, 1/2), or a family Ψ_σ(k) = σ₁k₁² + σ₂k₂² with σ in a compact set away
   from the axes? Are any hypotheses unsatisfiable or trivially strong? Are the conclusions trivially true for some
   degenerate data (e.g. `S` empty, `K` empty, `K'` empty)? Does any statement accidentally make the uniformity
   weaker than its global sibling in batch 2?
4. The sanity theorems in `Family.lean`: do they test what they claim (lessons 11 and 17)? What would they miss (for
   example a plant swapping `IsCritical (Ψ σ) p k` for `IsCritical (Ψ σ) 0 k`, or `V ×ˢ U` for `U ×ˢ V`)? Which
   derivative-level non-vacuity checks should be added after the proofs?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
