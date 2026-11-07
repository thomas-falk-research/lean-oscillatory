# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (30 entries); every rule in it is binding.

## What exists (end of session 4, 2026-11-07)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). 27 pinned statements, each with a row in `docs/STATUS.md` whose
  status is derived from evidence: S1 (three van der Corput lemmas), S2.1, S2.2, S3, S4.1, S4.1′, S4.2, S4.3, S4.4,
  front-end batch 1 (F1, F2) and, new this session, front-end batch 2 (fourteen statements: conversions C1–C9, C7′
  and Mathlib-idiom front ends FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′).
- **Entry point:** `import OscInt.API` (imports-only; implementation in `OscInt/Front/`; `tools/check_entry_point.sh`
  checks it exposes every statement and proving theorem). For a phase given by a formula:
  `examples/consumer/ConsumerFormula.lean` and the helpers `OscInt.API.Poly` (`OscInt/Front/Poly.lean`).
- Final record: `docs/replay/2026-11-07-session4-final-verify-all.txt` (`make verify-all` on c462966, alone on the
  machine). Earlier session-4 records: `2026-11-07-session4-baseline-quick.txt` (baseline on cb39601),
  `2026-11-07-API2-verify-all-9e5540a.txt` (FAIL: OOM and a network reset; explained in the answers).
- Reviews of batch 2: `review/2026-11-07-API2-*` (pre-proof FAITHFUL ×2, post-proof FAITHFUL ×2, adversarial: no
  BLOCKER, six MAJOR, all answered in `review/2026-11-07-API2-answers.md`).
- Design and exploration: `docs/constants.md` (P5), `docs/design/torus-lattice.md` (P9a).

## What was done this session (with commits)
- P0 release hygiene: version 0.3.0 everywhere; CHANGELOG with "Statement changes"; release notes with SHA-256 pins
  (`docs/release-notes/v0.3.0.md`); `tools/check_release_pin.sh` + CI `release-pin` (the README's tag must exist and
  point to the recorded release commit; 25 self-test cases); `examples/consumer-release/` + CI `consumer-release`;
  GammaFree.lean was already stamped (2e8707a, b46af0a).
- P1 conversion layer and front ends, statement first: statements 4acb308, stamp a610a7a, reviews 8a710fc, route
  e1e735d, proofs 9e5540a (agents D, Q, F, N; lead's assembly), fixes after review b46af0a, c462966.
- P2 (partial): helper lemmas `OscInt/Front/Poly.lean`; no tactic.
- P5 explored, P9a designed (documents above).

## Owner decisions (stop and ask)
- **Release v0.3.0.** Tag `v0.3.0` at the commit whose full hash is in `docs/release-notes/v0.3.0.commit` (the release
  commit: it adds the final replay record to c462966; nothing else changes). Steps: `docs/release-notes/v0.3.0.md`,
  "Publishing". Do not tag 2e8707a (withdrawn; adversarial M1, M6). Until the tag exists CI job `release-pin` is red
  by design; every other job should be green.
- Merge the session's branch `claude/sleepy-thompson-37yj33` (no pull request was opened).
- P5: whether to formalise explicit constants along the existing route (crude, ~10⁸–10¹² × powers; would not close the
  downstream 20-orders gap) or to invest in asymptotics (P4) first; `docs/constants.md` recommends the cheap local
  step (L6, L1) at most.
- P2: whether to allow a tactic library (metaprogramming is forbidden in library files by the guard; a separate,
  unaudited `lean_lib` whose output the kernel checks would need a guard-policy change and an adversarial review).
- Still the owner's: venue, outreach, Mathlib PRs, branch protection, Reservoir listing, a human expert review of the
  statements, Mathlib built from source on a second machine, publishing the release.

## Not done, and why
- C7′ explicit-data witness (`HasFDerivAt` data for x³ + y²): timeboxed out; C7′ is proved and reviewed, its
  hypotheses are not yet witnessed in Lean.
- P3 (classical fold hypothesis, family versions of S2.2/S4.1′, local smoothness), P4 (asymptotics), P6 (vector-valued
  amplitudes), P7 beyond the bridge examples, P8 (doc-gen4, scaffolder, linters, incremental commitments,
  closure-diff), P9b–e: not started. P1 + the review cycle took the session; each of these is a full statement
  batch (write, stamp, two blind reviews, route, agents, replay, two post-proof reviews, adversarial).
- OpenTimestamps proofs of the new stamp are pending (normal; upgrade later).

## Next (in this order)
1. Publish v0.3.0 (owner), then confirm CI `release-pin` and `consumer-release` go green.
2. P3, first item: a fold estimate requiring FoldOrNondeg only at critical points of Ψσ + p· (new frozen statement;
   the S3 route localises at points of K, so the non-critical points go through S2.1 — check numerically first).
   Stamp the reviews before launching agents (lessons 29).
3. P4: nondegenerate stationary phase leading term in 2D with O(m⁻²) remainder; pre-register the numeric check
   (`numerics/`) before proving.
4. P2 tactic decision, then `oscint_hyps` with negative controls; C7′ witness.
5. Closure-diff tool (ROADMAP §3) before any Mathlib upgrade.

## Process notes for the next lead
- `leanchecker M` checks every module with prefix `M` in parallel: keep the root the only module with submodules
  (lessons 30, enforced by `tools/check_entry_point.sh`).
- Run the final `verify-all` alone (lessons 28): about 90 minutes on this 4-core, 14 GB container.
- `make stamp` refuses a dirty tree after ten minutes of work: park new files first (lessons 25).
- Proof agents with exact interfaces and `#check`ed names finished in 2–5 minutes each (four parts in parallel).

## Commands
```bash
lake exe cache get
make quick                 # build, guard, audit, statement types, Gamma-free, statements.json, entry point (~7 min)
make verify-all            # about 90 minutes; needs zstd, bubblewrap and a full clone; run alone
make release-pin           # needs network; red until the release tag exists
make statements            # regenerate stamps/statements.json after a pin or StatementTypes change
make stamp
```
