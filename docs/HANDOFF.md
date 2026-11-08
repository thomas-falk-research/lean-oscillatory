# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (35 entries); every rule in it is binding.

## What exists (end of session 5, 2026-11-08)
- Lean v4.35.0, Mathlib `56a0058`. 37 pinned statements, each with a row in `docs/STATUS.md`, all proved: S1, S2.1,
  S2.2, S3, S4.1, S4.1′, S4.2–S4.4, front-end batches 1 (F1, F2), 2 (C1–C9, C7′, FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′) and,
  new this session, batch 3 (API3): S2.2F (family stationary phase), S3c (fold with the classical hypothesis, only at
  critical points), C10 (joint smoothness ⇒ `FamilyCk`), FE-S2.1L/S2.2L/S3L (Mathlib idiom, compact families, smooth
  only on `V ×ˢ U`), FE-S4.1′L (D4 with a phase smooth near 0), FE-S2.1l/S2.2l/S3l (one phase, smooth on `U`).
- Entry point `import OscInt.API` (74 names). Consumer examples: `examples/consumer/ConsumerFormula.lean` (batch 2),
  `ConsumerLocal.lean` (arccos dispersion family; phase singular outside the support), `ConsumerLocalChecks.lean`
  (non-vacuity), all compiled by `make quick`.
- v0.3.0 is published (tag → 7098f09). `main` = 6acef2a (merge of PR #4) at the start of this session; this session's
  work is on branch `claude/gracious-bohr-4sgzuy` (pull request to `main`: see the final commit message or the PR list).
- Records this session: `docs/replay/2026-11-08-session5-baseline-quick.txt` (6acef2a), `…-external-downstream-dry-run-v0.3.0.txt`
  (v0.3.0 by tag: build and checker PASS), `…-API3-sanity-plants.txt` and `docs/replay/plants/2026-11-08-API3/`,
  `…-session5-API3-verify-all.txt` (a638f70, verify-all PASS 9/9, 93 min, alone on the machine).
- Reviews: `review/2026-11-08-API3-*` (pre-proof FAITHFUL and TRUE ×2; post-proof FAITHFUL ×2; adversarial: three MAJOR
  on the sanity layer and five MINOR, answered in `review/2026-11-08-API3-answers.md`).

## What was done this session (with commits)
- P0: handover corrected (PR #4 already merged, v0.3.0 already published; lessons 31). Release-pin check 4 (the tag's
  commit must be in HEAD) bb8619f; check 5 (raw commit pins) and a real-git self-test after the adversarial review.
  External downstream dry run of v0.3.0 by tag: PASS. README no longer says unpublished.
- P1 + P2 + P3(a) as one statement batch (API3): statements 9d03130, stamp e42dcd3, pre-proof reviews, conditional
  sanity file and route 7bb4579, review stamp 06c3c66, proofs 3b05946 and a638f70 (agents P1, P2; lead's re-assemblies
  and bridges), replay 11a9ecf, post-proof and adversarial reviews and the fixes after them in the records commit.
  Acceptance of P2 (arccos-type phase via `ContDiffOn` of arccos; a phase singular outside the support):
  `examples/consumer/ConsumerLocal.lean`.
- P3(b): protocol pre-registered (`docs/prereg/2026-11-08-P3b-leading-term.md`, committed before the run) and program
  `numerics/src/bin/spleading.rs`; run after that commit: RESULT PASS (`numerics/results-spleading-2026-11-08.txt`: four
  cases, leading-term error ≤ 0.16 % at m = 640, remainder slopes −1.93 to −2.00; the control without e^{iπ sgn/4}
  fails, so the check discriminates). Numerics are tooling, not evidence. No Lean statement yet.

## Owner decisions (stop and ask)
- **CONTRIBUTING step 5 after a test-layer MAJOR.** Both API3 pre-proof referees judged every statement faithful but
  found the sanity theorems restating hypotheses (lessons 11). The lead answered with sanity theorems through the
  statement constants (all ten covered, planted controls, falsity of the plants proved) instead of a re-freeze, and
  the adversarial referee called this a departure from the written rule (M3). Decide: (i) ratify an amended step 5
  ("a MAJOR confined to the test layer, with every statement judged faithful by both referees, may be answered by
  sanity theorems through the statement constants covering every statement, with planted controls"), or (ii) order a
  re-freeze of the ten texts as API3′ with bundled hypothesis `def`s (proofs carry over). Until then STATUS marks the
  ten rows "owner decision pending".
- Merge the session's pull request (CI must be green on its head: `quick`, `verify`, `release-pin`).
- Release v0.4.0 (minor: ten statements added, none changed) when you want the batch published; prepare the notes the
  way `docs/release-notes/v0.3.0.md` does (the release-pin check now also requires the tag's commit to be on `main`).
- Still the owner's: P5 tactic policy (metaprogramming is forbidden in library files; a tactic needs a separate,
  unaudited `lean_lib` and an adversarial review), venue and outreach, Mathlib PRs (`docs/upstream.md`), branch
  protection, Reservoir listing, a human expert review of the statements, Mathlib built from source on a second
  machine, the Zenodo DOI of v0.3.0 in `CITATION.cff`.

## Not done, and why
- S4.1′ uniform over a compact family: not a re-assembly (the D4 normal form would have to be uniform in the
  parameter); deferred, recorded in `docs/statements.md` (batch 3, modelling choices).
- P3(b) Lean statement and proof of the 2D leading term; P4 (lattice kernels T0–T6), P5 (tactic), P6 (constants),
  P7 (breadth), P8 (doc-gen4, API index, CLI, faster loops, upstream PRs, Reservoir, applications page): not started.
  The API3 batch with its full review cycle (two pre-proof, two post-proof, one adversarial review, two sanity agents,
  a 94-minute replay) took the session.
- Open non-vacuity checks (post-proof referees): the hemisphere phase on the Euclidean disc through FE-S2.2l with a
  non-symmetric linear term; the arccos phase through FE-S2.2l at a critical point (Hessian of arccos).
- A local form of C10 (families only continuous in σ, e.g. the rescaled family of S4) and a `ContDiffOn` form of C10:
  candidates for the next batch (pre-proof referees m3, m4).

## Next (in this order)
1. Owner: the step-5 decision; merge; v0.4.0 if wanted.
2. P3(b): read the pre-registered numeric result; write the leading-term statement (2D nondegenerate, remainder
   O(m⁻²)) as a new batch, with sanity theorems through the constant from the start (lessons 33).
3. P4 T0 (1D lattice kernel t^{-1/3} from S1.2/S1.3), then T1/T2, T6 (`docs/design/torus-lattice.md`), after the
   prior-art sweep the design doc asks for.
4. P8 machine-readable API index (`stamps/statements.json` plus hypotheses in words and a compiled usage snippet).

## Process notes for the next lead
- Run `make quick` before every push (lessons 35); unshallow the clone before `stamp-verify` (lessons 32).
- Freeze the tree while referees run: write briefs and records in the scratchpad until they finish (lessons 16).
- Write sanity theorems through the statement constant, with a planted copy per statement, before the stamp
  (lessons 33); they cannot catch a plant that weakens a hypothesis.
- Proof agents with exact signatures and `#check`ed names: P1 in about 1 minute, P2 in about 3 minutes this session.

## Commands
```bash
lake exe cache get
make quick                 # build, guard, audit, statement types, Gamma-free, statements.json, entry point (~7 min warm)
make verify-all            # about 94 minutes; needs zstd, bubblewrap and a full clone; run alone
tools/check_release_pin.sh --self-test && tools/check_release_pin.sh
make statements            # regenerate stamps/statements.json after a pin or StatementTypes change
make stamp
```
