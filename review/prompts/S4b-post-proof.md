# Post-proof fidelity review: S4.1′, S4.2, S4.3

You are a fresh referee. Decide whether the proved Lean theorems establish the intended mathematics. Two referees
review independently; do not look for the other's report.

Read: `docs/statements.md` (S4 in full, including the clarifications at the end), `docs/decisions/2026-11-06-S4.md`,
`OscInt/Statements/D4Limit.lean` (and `D4.lean`, `StationaryPhase.lean` for shared definitions),
`OscInt/D4/Final.lean`, `OscInt/D4/ConstantPosFinal.lean`, `OscInt/D4/LimitFinal.lean`, `OscInt/D4/LimitSanity.lean`,
`StatementTypes.lean`, `GammaFree.lean`, `comparator-S41w.json`, `comparator-S42.json`, `comparator-S43.json`,
`stamps/pins.txt`, `stamps/20261106T081634Z-e2d7771c358e/manifest.txt`, `review/2026-11-06-S4b-pre-proof-{A,B}.md`
and the answers file, the replay record named in `docs/STATUS.md` for these statements, and Mathlib sources as
needed. You may read the proof files under `OscInt/D4/` only to check that nothing in them can change the meaning of
the statements; say what you looked at. Do not edit repository files.

Run and report verbatim (repository root; `export PATH=$HOME/.elan/bin:$PATH`; one process at a time, `nice -n 10`):
1. `git rev-parse HEAD`
2. `lake env lean StatementTypes.lean`
3. `cat build/commit/commitments.txt`, comparing the D4BoundNe, D4Limit and D4ConstantPos lines with the pinned
   stamp manifest (say on which commit the file was computed, per the replay record).
4. `lake env lean Axioms.lean | grep -E 'OscInt\.(d4BoundNe|d4Limit|d4ConstantPos) |AUDIT-TOTAL'`
5. `lake env lean GammaFree.lean` (the S4.3 proof-method check; read its header and controls and say whether it
   really follows proofs).

For each of `OscInt.d4BoundNe`, `OscInt.d4Limit`, `OscInt.d4ConstantPos`: verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md` and against the brief as quoted in the decision record,
scope (`full` or `part`), and the commitment hash the verdict is pinned to. State plainly what remains unproved for
the brief's S4 (S4.4). Findings as BLOCKER / MAJOR / MINOR / NIT.
