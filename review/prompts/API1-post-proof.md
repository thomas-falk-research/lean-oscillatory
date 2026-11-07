# Post-proof fidelity review: front-end batch 1 (F1, F2)

You are a fresh referee. Decide whether the proved Lean theorems establish the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` ("Front end, batch 1" and S4), `OscInt/Statements/FrontEnd.lean` (and `D4Limit.lean`,
`D4.lean`, `StationaryPhase.lean` for shared definitions), `OscInt/API.lean`, `OscInt/API/Sanity.lean`,
`StatementTypes.lean`, `comparator-API1.json`, `stamps/pins.txt`, `stamps/20261107T012459Z-2d5356432156/manifest.txt`,
`review/2026-11-07-API1-pre-proof-{A,B}.md`, the replay record named in `docs/STATUS.md` for F1 and F2, and Mathlib
sources as needed. Do not edit repository files, git state or `build/`.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD` and `git status --short` (the tree must be clean).
2. `lake env lean StatementTypes.lean`
3. `cat build/commit/commitments.txt`, comparing the `AmpBoundOfContDiffStatement` and `D4LimitClosedFormStatement`
   lines with the pinned stamp manifest (say on which commit the file was computed, per the replay record).
4. `lake env lean Axioms.lean | grep -E 'OscInt\.API\.(ampBoundOfContDiff|d4LimitClosedForm) |AUDIT-TOTAL'`

For each of `OscInt.API.ampBoundOfContDiff` and `OscInt.API.d4LimitClosedForm`: verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md` (and, for F2, against the brief's S4 as quoted there),
scope (`full` or `part`), and the commitment hash the verdict is pinned to. Also judge `OscInt/API/Sanity.lean`:
do its theorems answer the statement referees' MINORs (an elliptic instance of F2's hypotheses, an independent value
of the elliptic constant, bite), and do they test what they claim? And `OscInt/API.lean`'s docstring: does it claim
anything the files do not support? Findings as BLOCKER / MAJOR / MINOR / NIT. Return the report as your final message.
