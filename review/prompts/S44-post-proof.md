# Post-proof fidelity review: S4.4

You are a fresh referee. Decide whether the proved Lean theorem establishes the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` (S4 in full, including the clarifications at the end), `docs/decisions/2026-11-06-S4.md`,
`OscInt/Statements/D4Limit.lean` (and `D4.lean`, `StationaryPhase.lean` for shared definitions),
`OscInt/D4/ClosedFormFinal.lean`, `StatementTypes.lean`, `comparator-S44.json`, `stamps/pins.txt`,
`stamps/20261106T081634Z-e2d7771c358e/manifest.txt`, `review/2026-11-06-S4b-pre-proof-{A,B}.md` and
`review/2026-11-06-S4b-pre-proof-answers.md`, the replay record named in `docs/STATUS.md` for S4.4, and Mathlib
sources as needed. You may read `docs/proof-S44.md`, `Blueprint/D4ClosedForm.lean` and the proof files under
`OscInt/D4/` only to check that nothing in them can change the meaning of the statement; say what you looked at. Do
not edit repository files, git state or `build/`.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD` and `git status --short` (the tree must be clean).
2. `lake env lean StatementTypes.lean`
3. `cat build/commit/commitments.txt`, comparing the `D4ConstantClosedFormStatement` line with the pinned stamp
   manifest (say on which commit the file was computed, per the replay record).
4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4ConstantClosedForm |AUDIT-TOTAL'`

Decide, against `docs/statements.md` S4.4 and against the brief's constant Γ(1/3)²/(√3|Disc C|^{1/6}): does
`OscInt.d4ConstantClosedForm : D4ConstantClosedFormStatement` say I = Γ(2/3)/2 for the improper integral, and the
two closed forms of c_C with the right sign convention for `disc`, the right power of |Disc| and no junk-value
escape (`limUnder`, a non-integrable `angularMoment`, `Real.rpow` of a negative base)? Check one closed form against
a cubic you choose with all coefficients nonzero, by hand or numerically, and say what you used. Verdict FAITHFUL /
FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL, scope (`full` or `part`), and the commitment hash the verdict is
pinned to. Say whether S4.2 ∧ S4.4 now gives the brief's S4 limit with its closed-form constant. Findings as
BLOCKER / MAJOR / MINOR / NIT. Return the report as your final message.
