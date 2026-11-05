# Post-proof fidelity review: S1 (van der Corput)

You are a fresh referee. Decide whether the proved Lean theorems establish the intended mathematics.

Read: `docs/statements.md` (S1), `OscInt/Statements/VanDerCorput.lean`, `OscInt/VanDerCorput/Final.lean`,
`StatementTypes.lean`, `comparator.json`, `stamps/20261105T203058Z-7516eb518dce/manifest.txt`,
`review/2026-11-05-S1-pre-proof.md`, and Mathlib sources as needed. You may read the proof files under
`OscInt/VanDerCorput/` only to check that nothing in them changes the meaning of the statements (they cannot, if the
checks below pass, but say what you looked at). Do not edit repository files.

Run and report verbatim (from the repository root, `export PATH=$HOME/.elan/bin:$PATH`, one process at a time,
prefix `nice -n 10`):
1. `git rev-parse HEAD`
2. `lake env lean StatementTypes.lean`
3. `make commit` then `cat build/commit/commitments.txt`; compare with the `commitment` lines of the stamp manifest.
4. `lake env lean Axioms.lean | grep -E 'vanDerCorput|AUDIT-TOTAL'`

Then give, for each of `OscInt.vanDerCorput_one`, `_two`, `_three`: verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md` and against the classical statement (Stein VIII §1.2),
scope (`full` or `part`), and the commitment hash the verdict is pinned to. List any finding as BLOCKER / MAJOR /
MINOR / NIT.
