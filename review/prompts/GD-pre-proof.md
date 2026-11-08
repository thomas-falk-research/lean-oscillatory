# Blind statement review: batch GD (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No Lean proof of these eight statements exists in the repository or in the lead's scratch. **Do not prove the
statements under review, not even in your own scratch: numerical checks, counterexample searches and Lean checks of
small facts about definitions (e.g. evaluating a definition on concrete data) only** (lessons 24).

Read: `docs/statements.md` (section "Batch GD" in full; "Front end, batch 3", "Front end, batch 2", S2/S3, S4 for
shared notation and the frozen statements this batch is meant to follow from), `OscInt/Statements/Global.lean` (the
batch), `OscInt/Statements/Family.lean`, `Convert.lean`, `FrontEnd.lean`, `D4Limit.lean`, `StationaryPhase.lean`
(shared definitions and frozen statements), `OscInt/Front/GlobalSanity.lean` (sanity theorems through the constants)
with `docs/replay/2026-11-08-GD-sanity-plants.txt` (planted controls), `docs/prereg/2026-11-08-P1-classify.md` with
`numerics/results-classify-2026-11-08.txt` (the numeric pre-registration that informed the batch; tooling, not
evidence), `docs/lessons.md` (entries 11, 12, 17, 24, 33), and Mathlib sources under `.lake/packages/mathlib`. You may
compile scratch files under `/tmp/<your name>/` with `nice -n 10 lake env lean -DautoImplicit=false FILE` from the
repository root (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time) and run numerical checks (Python,
standard library). Write nothing in the repository.

For each statement constant in `Global.lean`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL (say against
   what: the docs, and separately the classical result where one exists). Is it TRUE? If you believe it false, give a
   concrete counterexample (exact data) and check it numerically. Pay attention to: the placement of `∃ C` relative to
   `A`, `M`, `L`, `m`, `t`, `x`; GD-C's and GD's use of a finite exceptional set `D` (a `Finset`, `↑D ⊆ U`, not
   necessarily `⊆ K`) and whether the D4 points' neighbourhoods can be handled with a bound uniform over **all** linear
   terms (FE-S4.1′L is uniform over all `L`) while the rest uses compactness of `K′` (GD-C) or no compactness at all
   (GD, GD-F, GD-N: is the bound over all `L` true, e.g. for large `‖L‖`?); `IsD4Point` (the existential cubic
   coefficients and the factor 6; compare FE-S4.1′L); `FoldOrNondegMatrix` at every point of `K \ D` (GD) versus at
   critical points only (GD-C), and whether critical points near a D4 point that are cusps (A₃) would make the
   hypothesis false rather than the conclusion; SH's two parts (real variable and sequences) and the meaning of
   `m ^ σ` for `m ≤ 0`; T1's weight (`ContDiff ℝ ∞` with `open scoped ContDiff`, lessons 12; support in the max-norm
   ball of radius 4; continuity and 2π-periodicity of `g`; the box `Set.Icc (−π) π ×ˢ Set.Icc (−π) π` and Lebesgue
   measure on `ℝ × ℝ`); T6's kernel (the sign and scale of `x·k` with `x : ℤ × ℤ` cast to ℝ, uniformity over `x`,
   `t ≥ 1`); T6L's normalisation `(−1)ⁿ n^{2/3}`, the casts, and the constant `d4ClosedConstant (−1/48)`.
2. Derivability: is each statement implied by the frozen, proved statements (FE-S4.1′L `D4BoundLocalStatement`, FE-S3l
   `FoldOnStatement`, FE-S2.2l `StationaryPhaseOnStatement`, FE-S2.1l `NonStationaryOnStatement`, F1, F2 / S4.2–S4.4)
   plus a partition of unity, translation invariance of Lebesgue measure and Leibniz bounds, as the docs suggest? Name
   any step where the argument fails. Is anything stronger than what that argument gives slipped in, or anything a
   user needs lost?
3. Vacuity and usefulness: can a user discharge each hypothesis for an explicit phase (cos k₁ + cos k₂ on a box, which
   has nondegenerate points, fold lines and four D4 points; arccos(a cos x + b cos y) for fixed |a| + |b| < 1)? Are
   any hypotheses unsatisfiable or trivially strong? Are the conclusions trivially true for degenerate data (`K`
   empty, `D` empty)? Does T6 with T1 and GD say what a dispersive estimate for the 2D lattice Schrödinger group needs?
4. The sanity theorems and planted controls: do they test the frozen text (lessons 33)? What would they miss? Which
   plants that weaken a hypothesis or strengthen a conclusion matter most here?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
