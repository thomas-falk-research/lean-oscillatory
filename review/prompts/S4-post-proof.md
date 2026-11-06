# Post-proof fidelity review: S4.1

You are a fresh referee. Decide whether the proved Lean theorems establish the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` (S4, including the clarification at the end), `OscInt/Statements/D4.lean` (and `OscInt/Statements/StationaryPhase.lean` for shared definitions),
`OscInt/D4/Final.lean`, `OscInt/D4/Sanity.lean`, `StatementTypes.lean`, `comparator-S4.json`, `stamps/pins.txt`,
`stamps/20261106T033706Z-63564a8d78cd/manifest.txt`, `review/2026-11-06-S4-pre-proof-A.md` and `-B.md`, and Mathlib
sources as needed. You may read the proof files under `OscInt/D4/` only to check that nothing in them can
change the meaning of the statements; say what you looked at. Do not edit repository files.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD`
2. `lake env lean StatementTypes.lean`
3. `cat build/commit/commitments.txt` (computed by the lead's `make verify-all` on this commit; if absent, say so),
   and compare the S4.1 line with the `commitment` lines of the pinned stamp manifest.
4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4Bound |AUDIT-TOTAL'`

For `OscInt.d4Bound`: verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md` and against the classical results, scope (`full` or
`part`), and the commitment hash the verdict is pinned to. Findings as BLOCKER / MAJOR / MINOR / NIT.
