# Answers to the LE post-proof and adversarial reviews (lead, 2026-11-08)

Reports at 7218811 (no Lean change since the replayed a1d2a64): `review/2026-11-08-LE-post-proof-A.md`,
`review/2026-11-08-LE-post-proof-B.md` (both: FAITHFUL at full scope ×3, no BLOCKER/MAJOR), and
`review/2026-11-08-LE-adversarial.md` (no BLOCKER/MAJOR; 6 MINOR, 9 NIT; re-ran the stamps, the plants and both numeric
programs, byte-identical; checked the order against the session record).

## Post-proof A and B
- **MINOR-1 (A and B): no compiled use of the proved theorems on data.** Fixed: `examples/consumer/ConsumerLatticeExplicit.lean`
  applies all six sanity theorems to the proved theorems and adds the 4761 corollary and the composed bound of
  clarification 8 (B NIT-3); compiled by `make quick` (Makefile `entry-point`).
- **MINOR-2 (B) / MINOR-2 (A): STATUS, README not updated; prior_art said "machine-checked" before the post-proof
  reviews.** Fixed: three STATUS rows and a batch paragraph (with "owner decision pending" on the step-5 question, as
  promised in the pre-proof answers); README rows; prior_art now cites the replay and the post-proof reviews.
- **MINOR-3 (B): order wording.** Fixed in `docs/STATUS.md` and `docs/proof-LE.md`: "by git order and the lead's
  session record", as for API3.
- **NITs.** `docs/proof-LE.md` line 5 corrected (A NIT-1, B NIT-1). Replay cited as "replay of a1d2a64" (A NIT-2).
  A NIT-3 (git dates are not evidence) folded into the order wording. B NIT-2 (assembly docstring): as adversarial n1,
  not edited (see below).

## Adversarial
- **m1 (front-facing records incomplete; CHANGELOG "the D4 constant").** Fixed: README intro and table carry the
  "classical, separable" caveat and batch LE; CHANGELOG gains batch LE (48 statements), the session-7 tool changes and
  the disclosure, and the GD entry now says the constant is also the Cauchy–Watson Bessel constant. HANDOFF is
  rewritten at the end of the session.
- **m2 (no non-separable GD instance; Q(3) tests only GD-F).** Agreed; stated in `docs/prior_art.md`, the design doc §4
  and ROADMAP item 2.
- **m3 (symlinked stamp directory skipped), m4 (manifest coverage not checked), n4 (truncated .ots panics).** Tool
  changes in `tools/src/bin/stamp.rs`, made in a separate commit with tests (see its message); answered there.
- **m5 (order not checkable by a third party).** Agreed; wording as for post-proof B MINOR-3.
- **m6 (design-doc imprecisions).** Fixed in `docs/design/vector-amplitudes.md` §1 (integrability of the product; the
  junk branch is unreachable under the frozen hypotheses and would need C ≥ 0, which the statement at A = 0 gives);
  `ContinuousLinearMap.norm_restrictScalars` added to `MathlibNames.lean`.
- **n1 (pieces of length π/2).** Not edited in `OscInt/Front/LatticeExplicitAssembly.lean`, to keep the replayed Lean
  sources byte-identical to a1d2a64; corrected in `docs/proof-LE.md`.
- **n2.** As post-proof A MINOR-2.
- **n3 (plant coverage).** Recorded: `latticeKernel1` is not planted (its body is tied to the frozen `latticeKernel` only
  by T6F's proof, for integer ξ; for real ξ, T0E's meaning rests on reading the definition); no plant on T6E's constant
  or restricting x; the first plant run survives in commit 4a18353. Future plant generators should write each run to
  its own directory.
- **n5 (pin paths not validated), n7 (actionlint via the Go checksum database, apt shellcheck unpinned).** Recorded as
  follow-ups; not changed this session.
- **n6 (numerics not discriminating against too-small constants).** `docs/statements.md`, Batch LE, clarification 10.
- **n8 (Q(1) at (−π, −π)).** Clause added to the design doc §4.
- **n9 (replay start time reconstructed; "alone" not in the log).** Agreed; the next replay wrapper logs `date -u` at
  start and end. The run was alone: no other Lean process was started by the lead or any agent while it ran (the
  three post-proof referees were launched after it finished).
