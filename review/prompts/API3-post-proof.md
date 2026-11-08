# Post-proof fidelity review: front-end batch 3 (S2.2F, S3c, C10; FE-S2.1L, FE-S2.2L, FE-S3L, FE-S4.1′L; FE-S2.1l, FE-S2.2l, FE-S3l)

You are a fresh referee. Decide whether the ten proved Lean theorems establish the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` ("Front end, batch 3" in full including its clarification; S2/S3, S4 and batch 2 for
shared notation), `OscInt/Statements/Family.lean`, `review/2026-11-08-API3-pre-proof-{A,B}.md` and
`review/2026-11-08-API3-pre-proof-answers.md`, the proofs `OscInt/Front/Family.lean` (S2.2F, S3c),
`OscInt/Front/FamilyC10.lean` (C10), `OscInt/Front/Cutoff.lean` (cut-off), `OscInt/Front/Local.lean` (the seven
bridges), `StatementTypes.lean`, `comparator-API3.json`, `stamps/pins.txt`,
`stamps/20261108T002603Z-9d03130c8f3a/manifest.txt`, `OscInt/Front/FamilySanity.lean` and
`docs/replay/2026-11-08-API3-sanity-plants.txt` (non-vacuity), the replay record named in `docs/STATUS.md` for this
batch, and Mathlib sources as needed. You may read `docs/proof-API3.md` and `OscInt/StationaryPhase/*.lean` to check
that nothing there can change the meaning of a statement; say what you looked at. Do not edit repository files, git
state or `build/`; scratch only under `/tmp/<your name>/`; do not run `make` targets.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD` and `git status --short` (the tree must be clean).
2. `lake env lean StatementTypes.lean | grep -E 'API\.(stationaryPhaseFamily|foldCrit|familyCk_of_uncurry|nonStationaryLocal|stationaryPhaseLocal|foldLocal|d4BoundLocal|nonStationaryOn|stationaryPhaseOn|foldOn) '`
3. `lake env lean Axioms.lean | grep -E 'OscInt\.API\.(stationaryPhaseFamily|foldCrit|familyCk_of_uncurry|nonStationaryLocal|stationaryPhaseLocal|foldLocal|d4BoundLocal|nonStationaryOn|stationaryPhaseOn|foldOn) |AUDIT-TOTAL'`

For each of the ten theorems: verdict FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL against
`docs/statements.md`, scope (`full` or `part`). Say which frozen or proved results each proof goes through (S2.1
`OscInt.nonStationary`, the internal parts of S2.2/S3, FE-S4.1′ `OscInt.API.d4BoundFE`, C3, C7, C8) and whether
anything else could change its meaning. Do the sanity theorems in `FamilySanity.lean` now witness non-vacuity of
the hypotheses for genuinely new cases (critical-points-only fold; infinite family; phase not C¹ on ℝ²)? Which
post-proof derivative-level checks from the pre-proof reports remain open? Findings as BLOCKER / MAJOR / MINOR / NIT.
First line: `git rev-parse HEAD`. Return the report as your final message.
