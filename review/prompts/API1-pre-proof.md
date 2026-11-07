# Blind statement review: front-end batch 1 (F1 amplitude bounds, F2 D4 limit with closed-form constant)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether they are true, and
whether they are non-vacuous. Two referees review independently; do not look for the other's report. No proof is in
the repository; the lead drafted bridge proofs in a private scratch directory before this review (disclosed in
`docs/statements.md`), which you must not look for or read: judge the statements on their own.

Read only: `docs/statements.md` (sections "Front end, batch 1" and S4 in full; S2/S3 for shared notation),
`OscInt/Statements/FrontEnd.lean`, `OscInt/Statements/D4Limit.lean`, `OscInt/Statements/D4.lean`,
`OscInt/Statements/StationaryPhase.lean` (shared definitions), and Mathlib sources. You may compile scratch files
under `/tmp/<your name>/` with `nice -n 10 lake env lean …` from the repository root (`export PATH=$HOME/.elan/bin:$PATH`;
one process at a time). Write nothing in the repository.

For each of `AmpBoundOfContDiffStatement` (F1) and `D4LimitClosedFormStatement` (F2):
1. Verdict against `docs/statements.md` (FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL). Is it TRUE?
   If false, give a counterexample. For F2 also: does it say the brief's S4 ("t^{2/3} ∫ e^{itφ} A → c_C A(0) with
   c_C = Γ(1/3)²/(√3|Disc C|^{1/6})" for negative discriminant), and is the elliptic branch Γ(1/3)²/Disc^{1/6} right?
   Check `d4ClosedConstant` against a cubic you choose with all coefficients nonzero (by hand or numerically).
2. Is F2 implied by the frozen S4.2 (`D4LimitStatement`), S4.4 (`D4ConstantClosedFormStatement`) and F1, as the
   docs claim, and is it strictly a front end (nothing stronger slipped in: the order of `∃ δ` and `∀ A`, the
   integral written out versus `oscInt2`, the coercions, `tsupport` versus support, the max-norm ball)?
3. Vacuity and conventions: `d4ClosedConstant` at D = 0 and its `if`; `Real.rpow` of `|D|` and of `D`; whether F1
   is trivially true or false for some n (n = 0; `iteratedFDeriv` of order above n; K empty).
4. The sanity theorems in `FrontEnd.lean`: do they test what they claim (lessons 11, 17)? What would they miss?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line: `git rev-parse HEAD`. Return the
   report as your final message.
