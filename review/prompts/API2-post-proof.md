# Post-proof fidelity review: front-end batch 2 (C1–C9, C7′, FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′)

You are a fresh referee. Decide whether the fourteen proved Lean theorems establish the intended mathematics. Two
referees review independently; do not look for the other's report.

Read: `docs/statements.md` ("Front end, batch 2" in full including its clarification; S2/S3 and S4 for shared
notation), `OscInt/Statements/Convert.lean`, `review/2026-11-07-API2-pre-proof-{A,B}.md` and
`review/2026-11-07-API2-pre-proof-answers.md`, `OscInt/API/Convert.lean` (the lead's assembly: C7 and the four front
ends), `StatementTypes.lean`, `comparator-API2.json`, `stamps/pins.txt`, `stamps/20261107T101640Z-4acb308f54f4/manifest.txt`,
`OscInt/API/ConvertSanity.lean` and `examples/consumer/ConsumerFormula.lean` (non-vacuity), and Mathlib sources as
needed. You may read `docs/proof-API2.md` and the part files `OscInt/API/Convert{Deriv,Disc,Fold,Norm}.lean` and
`OscInt/API/Poly.lean` only to check that nothing in them can change the meaning of a statement; say what you looked
at. Do not edit repository files, git state or `build/`. The replay record for this commit is being produced while
you work (`make verify-all`); do not run `make` targets.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD` and `git status --short` (the tree must be clean).
2. `lake env lean StatementTypes.lean | grep -E 'API\.(dd_|ddd_|hessDet|cubicCoeffs_eq|disc_|foldOrNondeg|gradLower|ampBound_conv|nonStationaryFE|stationaryPhaseFE|foldFE|d4BoundFE)'`
3. `lake env lean Axioms.lean | grep -E 'OscInt\.API\.(dd_iteratedFDeriv|ddd_iteratedFDeriv|hessDet_eq_det|cubicCoeffs_eq|disc_eq_cubic_discr|disc_ne_zero_iff_isolated|foldOrNondeg_iff|foldOrNondeg_of_hasFDeriv|gradLower_iff|ampBound_conv|nonStationaryFE|stationaryPhaseFE|foldFE|d4BoundFE) |AUDIT-TOTAL'`
4. `cd examples/consumer && lake env lean ConsumerFormula.lean` after `lake build` there if needed (may take minutes;
   if it is too slow, say so and read the file instead).

For each of the fourteen theorems: verdict FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL against
`docs/statements.md`, scope (`full` or `part`). For the four front ends, say whether the proof goes through the frozen
statement it fronts (`OscInt.nonStationary`, `stationaryPhase`, `fold`, `d4BoundNe`) and nothing else that could
change its meaning. Does `examples/consumer/ConsumerFormula.lean` meet the acceptance criterion "S3 and S4.1′
applied to a phase given only by an explicit formula, with no `dd`, `ddd`, `AmpBound` or `cubicCoeffs` in the user's
hypotheses"? Findings as BLOCKER / MAJOR / MINOR / NIT. First line: `git rev-parse HEAD`. Return the report as your
final message.
