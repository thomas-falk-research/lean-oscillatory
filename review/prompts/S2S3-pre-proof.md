# Blind pre-proof statement review: S2, S3 (two-dimensional oscillatory integrals)

You are a fresh referee with no access to any proof (none exists yet). Judge whether the Lean statements say what
the mathematics says, and whether they are true and non-vacuous. Two referees review independently; do not try to
find or read the other's report.

Read only:
- `docs/statements.md`, sections "S2, S3" (the intended mathematics; the S1 section is context only);
- `OscInt/Statements/StationaryPhase.lean` (statements, helper definitions, sanity theorems);
- Mathlib sources under `.lake/packages/mathlib/Mathlib/` to check what a definition means (`fderiv`,
  `iteratedFDeriv`, `ContDiff`, `tsupport`, `IsCompact`, `CompactSpace`, Bochner `integral`, `Real.rpow`, the norm
  on `ℝ × ℝ`).
Do not read other repository files. You may use your knowledge of the classical results (Hörmander, *The Analysis of
Linear Partial Differential Operators I*, §7.7; Stein, *Harmonic Analysis*, VIII; Duistermaat, *Oscillatory
integrals, Lagrange immersions and unfolding of singularities*, 1974; Arnold–Gusein-Zade–Varchenko).

You may compile scratch files under `/tmp/<your name>/` with
`cd /home/user/lean-oscillatory && nice -n 10 lake env lean /tmp/<your name>/<file>.lean`
(`export PATH=$HOME/.elan/bin:$PATH`; one process at a time; `import OscInt.Statements.StationaryPhase` works).
Write nothing in the repository.

For each of `NonStationaryStatement`, `StationaryPhaseStatement`, `FoldStatement`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL; and against
   the classical results: is the statement TRUE? (If you believe it is false, give a counterexample.)
2. Vacuity hunt: hypotheses that cannot be met together or only trivially; definitions that collapse under Lean
   conventions (Bochner integral of a non-integrable function is 0, `fderiv` of a non-differentiable function is 0,
   `rpow`, division); quantifier order of `C` (could `C` depend on `A`, `M`, `σ`, `p` or `m`?); universe or
   instance issues with `Λ : Type` and `[CompactSpace Λ]`; whether `dd`, `ddd`, `hessDet`, `FoldOrNondeg` mean the
   second/third derivatives and the rank-one-with-cubic-along-kernel condition.
3. Ill-conditioned regimes: Hessian eigenvalue → 0 across the family or across K; critical points on or near the
   boundary of K; |p| → ∞ (S2.1); amplitude support touching ∂K; m near 1; families where the fold condition holds
   pointwise but degenerates in the limit. Is the claimed uniformity true?
4. The amplitude regularity C² in S2.2 and S3 (stronger than the project brief's C⁴): is the m^{-1} and m^{-5/6}
   decay with constants depending on derivatives of A of order ≤ 2 plausible or known? Give your reasoning.
5. Every finding labelled BLOCKER / MAJOR / MINOR / NIT, quoting the exact Lean text.

Report in Markdown. First line: `git rev-parse HEAD`. Second line: `cat build/commit/commitments.txt` if present.
