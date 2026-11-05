# Blind pre-proof statement review: S1 (van der Corput)

You are a fresh referee with no access to any proof. Judge whether the Lean statements say what the mathematics says.

Read only:
- `docs/statements.md`, section S1 (the intended mathematics);
- `OscInt/Statements/VanDerCorput.lean` (the Lean statements, their helper definitions and sanity theorems);
- Mathlib sources under `.lake/packages/mathlib/Mathlib/` to check what a Mathlib definition means
  (e.g. `intervalIntegral`, `HasDerivAt`, `MonotoneOn`, `IntervalIntegrable`, `Real.rpow`, `Real.sqrt`).
Do not read anything else in the repository, and do not look up any proof of the van der Corput lemma
(in particular not roos-j/lean-oscillatory or Mathlib PR #39406). You may use your own knowledge of the classical
statement (Stein, Harmonic Analysis, VIII §1.2).

You may run `lake env lean <file>` on scratch files under `/tmp` to test claims (for example, that a hypothesis set is
satisfiable or that a definition unfolds as you think). Write no files in the repository.

For each of `VdC1Statement`, `VdC2Statement`, `VdC3Statement` give:
1. Verdict: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL relative to `docs/statements.md`, and
   separately relative to the classical statement, with reasons.
2. Vacuity hunt: hypotheses that cannot be met together; definitions that collapse (Lean conventions for division by
   zero, `Real.sqrt` of negatives, `rpow`, integrals of non-integrable functions, oriented integrals); conclusions that
   are trivially true; quantifier order; whether the linear term p is really arbitrary.
3. Ill-conditioned regimes: μ or ν → 0, a = b, unbounded derivatives at the endpoints, amplitudes whose derivative is
   integrable but unbounded. Does the statement still say something true and meaningful there?
4. Every finding labelled BLOCKER / MAJOR / MINOR / NIT, with the exact Lean text it concerns.

Report in Markdown. First line: the commit hash you read (`git rev-parse HEAD`). Second line: the output of
`cat build/commit/commitments.txt` if present, else "commitments not available".
