# Blind post-proof review: batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

You are a fresh referee. Judge whether the proved Lean theorems prove what `docs/statements.md` (section "Batch VT",
with its clarifications 4–7) says, at full scope. Repository: `/home/user/lean-oscillatory` at the commit the lead names
(`. ~/.leanenv`; one Lean process at a time, `nice -n 10`; scratch only under `/tmp/<your name>/`; write nothing in the
repository; do not run `make` or `lake build`).

Read: `docs/statements.md` ("Batch VT"), `OscInt/Statements/Vector.lean` (frozen; stamp
`stamps/20261108T235416Z-961cebc296ef`), the final theorems `OscInt/Front/VectorFinal.lean`, the part and assembly
(`VectorParts.lean`, `VectorAssembly.lean`, `Blueprint/Vector.lean`), `StatementTypes.lean`, `comparator-VT.json`,
`Challenge/Vector.lean`, the replay record `docs/replay/2026-11-09-session7-VT-verify-all.txt`, the pre-proof reviews and
answers (`review/2026-11-08-VT-pre-proof-{A,B,answers}.md`, stamped `stamps/20261109T002419Z-45505299011a`), the route and
its referee (`docs/proof-VT.md`, `review/2026-11-09-VT-route-referee.md`), `OscInt/Front/VectorSanity.lean`,
`examples/consumer/ConsumerVector.lean`. You may read proofs, but judge statement-to-docs fidelity first.

For each of the four theorems: (1) is its type exactly the frozen constant (StatementTypes, TYPE-OK lines, the stamped
file's SHA-256 against the manifest)? (2) Verdict FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL, and scope.
(3) Non-vacuity on compiled data. (4) Does the proof rest only on the proved scalar statements of batch GD and Mathlib?
(5) Anything the docs claim that the evidence does not support, including the order claims (statements frozen and
reviewed before any proof; this time the route review was committed before the part's proof entered the repository,
with a draft in the lead's scratchpad meanwhile). Findings as BLOCKER / MAJOR / MINOR / NIT with file and line. First
line: `git rev-parse HEAD`. Return the report as your final message.
