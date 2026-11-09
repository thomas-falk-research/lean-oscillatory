# Blind post-proof review: batch LE (T0E, T6F, T6E)

You are a fresh referee. Judge whether the proved Lean theorems prove what `docs/statements.md` (section "Batch LE",
with its clarifications 6–9) says, at full scope. Repository: `/home/user/lean-oscillatory` at the commit the lead names
(`. ~/.leanenv` puts Lean on the PATH; one Lean process at a time, `nice -n 10`; scratch only under `/tmp/<your name>/`;
write nothing in the repository; do not run `make` or `lake build`).

Read: `docs/statements.md` ("Batch LE"), `OscInt/Statements/LatticeExplicit.lean` (frozen; stamp
`stamps/20261108T160847Z-4a183530559f`), the final theorems `OscInt/Front/LatticeExplicitFinal.lean`, the parts and
assembly (`LatticeExplicitParts.lean`, `LatticeExplicitAssembly.lean`), `StatementTypes.lean`, `comparator-LE.json`,
`Challenge/LatticeExplicit.lean`, the replay record `docs/replay/2026-11-08-session7-LE-verify-all.txt`, the pre-proof
reviews and answers (`review/2026-11-08-LE-pre-proof-{A,B,answers}.md`), the route and its referee (`docs/proof-LE.md`,
`review/2026-11-08-LE-route-referee.md`), and `docs/STATUS.md`, `README.md`, `docs/prior_art.md` ("Lattice kernels").
You may read proofs, but judge statement-to-docs fidelity first.

For each of the three theorems: (1) is its type exactly the frozen constant (`StatementTypes.lean`, the replay's
TYPE-OK lines; the stamped file's SHA-256 against the stamp manifest)? (2) Verdict FAITHFUL / FAITHFUL-WEAKER /
FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md`, and scope (full / partial). (3) Non-vacuity: is each used on
real data somewhere that compiles (`OscInt/Front/LatticeExplicitSanity.lean`)? (4) Does the proof rest only on the
frozen, proved S1.2/S1.3 statements and Mathlib (no use of internal lemmas whose statements are unreviewed in a way
that matters)? (5) Anything the docs claim that the evidence does not support, including the order claims (statements
frozen and blind-reviewed before any proof; the route-review order, which the lead says was NOT kept). Findings as
BLOCKER / MAJOR / MINOR / NIT with file and line. First line: `git rev-parse HEAD`. Return the report as your final
message.
