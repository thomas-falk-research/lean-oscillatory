# Post-proof fidelity review: S2.1, S2.2, S3

You are a fresh referee. Decide whether the proved Lean theorems establish the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` (S2, S3, including the clarifications at the end), `OscInt/Statements/StationaryPhase.lean`,
`OscInt/StationaryPhase/Final.lean`, `StatementTypes.lean`, `comparator-S2S3.json`, `stamps/pins.txt`,
`stamps/20261105T234456Z-533ae0272521/manifest.txt`, `review/2026-11-05-S2S3-pre-proof-A.md` and `-B.md`, and Mathlib
sources as needed. You may read the proof files under `OscInt/StationaryPhase/` only to check that nothing in them can
change the meaning of the statements; say what you looked at. Do not edit repository files.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD`
2. `lake env lean StatementTypes.lean`
3. `cat build/commit/commitments.txt` (computed by the lead's `make verify-all` on this commit; if absent, say so),
   and compare the three S2/S3 lines with the `commitment` lines of the pinned stamp manifest.
4. `lake env lean Axioms.lean | grep -E 'OscInt\.(nonStationary|stationaryPhase|fold) |AUDIT-TOTAL'`

For each of `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold`: verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md` and against the classical results, scope (`full` or
`part`), and the commitment hash the verdict is pinned to. Findings as BLOCKER / MAJOR / MINOR / NIT.
