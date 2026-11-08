# Blind post-proof review: batch GD (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L)

You are a fresh referee. Judge whether the proved Lean theorems prove what `docs/statements.md` (section "Batch GD",
with its post-stamp clarification) says, at full scope. Repository: `/home/user/lean-oscillatory` at the commit the
lead names (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time, `nice -n 10`; scratch only under
`/tmp/<your name>/`; write nothing in the repository; do not run `make` or `lake build`).

Read: `docs/statements.md` ("Batch GD" and its clarification), `OscInt/Statements/Global.lean` (frozen; stamp
`stamps/20261108T094842Z-edf7787a2845`), the final theorems `OscInt/Front/GlobalFinal.lean`, `Sharpness.lean`,
`LatticeKernel.lean`, `LatticeLimit.lean` (and `LatticeLimitFinal.lean` if present), `StatementTypes.lean`,
`comparator-GD.json`, `Challenge/Global.lean`, the replay record the lead names, and the consumer example
`examples/consumer/ConsumerLattice.lean`. You may read proofs, but judge the statement-to-docs fidelity first.

For each of the eight theorems: (1) is its type exactly the frozen constant (check `StatementTypes.lean` and the
replay's TYPE-OK lines; compare the stamped file's SHA-256 with `stamps/pins.txt` / the stamp manifest)? (2) Verdict:
FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL against `docs/statements.md`, and scope (full / partial).
(3) Non-vacuity: is each theorem used on real data somewhere that compiles (`OscInt/Front/GlobalSanity.lean`,
`examples/consumer/ConsumerLattice.lean`)? (4) Anything the docs, `docs/STATUS.md` or `README.md` claim that the
evidence does not support. Findings as BLOCKER / MAJOR / MINOR / NIT with file and line. First line: `git rev-parse
HEAD`. Return the report as your final message.
