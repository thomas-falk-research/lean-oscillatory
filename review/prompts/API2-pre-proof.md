# Blind statement review: front-end batch 2 (conversions C1–C9, C7′; front ends FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No proof of these fourteen statements exists anywhere (repository or scratch): this batch restores the
statement-first order. Disclosure: the repository already contains, since session 2 and for another purpose,
internal lemmas `OscInt.StationaryPhase.ImplicitAux.dd_eq_iteratedFDeriv` and `ddd_eq_iteratedFDeriv`
(`OscInt/StationaryPhase/Implicit.lean`, for globally `C^N` functions, with the arguments in reverse order); you may
read them, as they bear on how the new statements relate to existing code, but judge the statements on their own.

Read: `docs/statements.md` (section "Front end, batch 2" in full; S2/S3 and S4 for shared notation and for the frozen
statements the front ends are meant to follow from), `OscInt/Statements/Convert.lean` (the batch),
`OscInt/Statements/StationaryPhase.lean`, `D4.lean`, `D4Limit.lean`, `FrontEnd.lean` (shared definitions), and
Mathlib sources under `.lake/packages/mathlib`. You may compile scratch files under `/tmp/<your name>/` with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root (`export PATH=$HOME/.elan/bin:$PATH`; one
process at a time) and run numerical checks (Python, standard library or numpy if present). Write nothing in the
repository.

For each statement constant in `Convert.lean`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL. Is it TRUE?
   If you believe it false, give a concrete counterexample (exact data), and check it numerically or in Lean.
   Pay attention to: argument order of `iteratedFDeriv` versus `dd`/`ddd` (`dd Ψ k v w = ∂_w∂_vΨ(k)`); the use of
   `ContDiffAt` (neighbourhood) versus `ContDiff`; `Matrix.toLin'` and which side the kernel is on; `Matrix.rank`;
   the orientation `D₂ k (coordVec i) (coordVec j)` in C7′ and whether its iff needs symmetry of `D₂ k` that the
   hypotheses do not give; `𝓝[≠] 0` in C6 and the case q = 0; norms (`ℝ × ℝ` carries the max norm, so the operator
   norm of a functional is |L e₀| + |L e₁|; `EuclideanSpace ℝ (Fin 2)` carries the 2-norm) and the √2 in C8.
2. Front ends: is each implied by the frozen statement it fronts (S2.1 `NonStationaryStatement`, S2.2
   `StationaryPhaseStatement`, S3 `FoldStatement`, S4.1′ `D4BoundNeStatement`) together with the conversions C1–C9, as
   the docs claim? Check the quantifier order (where `∃ C` and `∃ δ` sit relative to `A`, `M`, `L`, `m`, `t`), the
   integrand (`m * (Ψ k + L k)` versus `oscInt2 (fun k => m * (Ψ k + lin p k))`), the passage from a compact set of
   functionals `K'` to a compact set of vectors, the gradient bound `c ≤ ‖fderiv ℝ Ψ k + L‖`, and in FE-S4.1′ the
   identification of `a b c d` with `cubicCoeffs φ` and of `(Cubic.mk a b c d).discr` with `disc`. Is anything stronger
   than the frozen statements slipped in, or anything a user needs lost?
3. Vacuity and usefulness: can a user discharge each hypothesis for an explicit phase (for example the fold x³ + y² on
   the unit ball, or φ(x, y) = x³ − 3xy² + x⁴ for FE-S4.1′)? Are any hypotheses unsatisfiable or trivially strong
   (e.g. C7′ asks for `HasFDerivAt` at every point)? Are the conclusions trivially true for some degenerate data?
4. The sanity theorems in `Convert.lean`: do they test what they claim (lessons 11 and 17 in `docs/lessons.md`)? What
   would they miss? Which derivative-level non-vacuity checks should be added after the proofs?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
