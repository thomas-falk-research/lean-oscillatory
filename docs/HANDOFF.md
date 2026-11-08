# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (42 entries); every rule in it is binding.

## What exists (session 7, 2026-11-08)
- Lean v4.35.0, Mathlib `56a0058`. **48 pinned statements, all proved**, each with a row in `docs/STATUS.md`: S1–S4,
  front-end batches 1–3, batch GD (eight; session 6) and, new this session, **batch LE** (three):
  - T0E `latticeKernel1Explicit`: |∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 24·2^{1/4} t^{−1/2} + 36·2^{1/6} t^{−1/3} (t > 0, ξ real);
  - T6F `latticeKernelFactor`: the 2D kernel of T6 is the product of two 1D kernels;
  - T6E `latticeLaplacianExplicit`: |K(t, x)| ≤ (A+B)² t^{−2/3} ≈ 4754 t^{−2/3} for t ≥ 1.
  These constants are explicit but weak: they beat the trivial bounds only for t > 518 (1D) and t > 1321 (2D).
- Replay record: `docs/replay/2026-11-08-session7-LE-verify-all.txt` (a1d2a64, PASS 9/9, 127 min, alone on the machine).
  Reviews: pre-proof FAITHFUL and TRUE ×2, route referee, post-proof FAITHFUL ×2, adversarial no BLOCKER/MAJOR
  (`review/2026-11-08-LE-*`).
- Disclosure: T6 and T6L are classical (the kernel factorises into 1D Bessel kernels), `docs/prior_art.md`.
- Entry point `import OscInt.API` (96 names). Consumer examples compiled by `make quick` now include
  `examples/consumer/ConsumerLatticeExplicit.lean`.
- Tools: `stamp verify-every` verifies every stamp directory and rejects symlinks, stray entries, defective manifests
  (header, full commit that is an ancestor of HEAD, hashed set = `git ls-tree` of the commit) and truncated `.ots`
  files; it writes nothing into `stamps/`. CI pip installs are hash-locked (`tools/requirements-ci*.txt`).
- GD-N has a sanity datum smooth only on U (`OscInt/Front/GlobalNondegLocalSanity.lean`, follow-up b2).
- Branch `claude/stoic-allen-lxasbf`, pushed; no pull request (the owner opens one when wanted). `main` = 96f55a2 with
  CI green (`ci` and `verify` both success).

## Owner decisions (stop and ask)
1. **CONTRIBUTING step 5**, now with two cases: API3's test-layer MAJOR (memo `docs/decisions/2026-11-08-step5-memo.md`)
   and LE's documentation-only MAJOR (pre-proof referee A; answered by docs, no re-freeze;
   `review/2026-11-08-LE-pre-proof-answers.md`). Thirteen STATUS rows say "owner decision pending".
2. **v0.4.0** (notes `docs/release-notes/v0.4.0.md`, which predate batch LE: decide whether LE goes in, then redo the pins
   with `tools/release_preflight.sh`).
3. AI-authorship wording (adversarial finding f1 of session 6), branch protection, P5 tactic policy, discoverability.
4. Human expert review: deferred by the owner under `docs/policy.md` (wording rule, calibration plan, triggers).

## Session-7 order (owner, `docs/ROADMAP.md`) and where it stands
0. Session-6 follow-ups a1, f4, f5, b2: **done**.
1. Batch LE: **done** (above).
2. **Batch VV (next)**: vector-valued amplitudes, accepted only when a non-separable model compiles end to end.
   - Route: duality (Hahn–Banach), no proof port: `docs/design/vector-amplitudes.md` §1 (checked by the adversarial
     referee in Lean).
   - Acceptance model, chosen by a pre-registered classification (`docs/prereg/2026-11-08-VV-classify.md`, result
     `numerics/results-classify-vv-2026-11-08.txt`): the Qi–Wu–Zhang band at m = 3, nondegenerate or fold everywhere
     (so GD-F, rate t^{−5/6}). QWZ at m = 1, 0.5 and the triangular lattice have cusps.
   - Main risk: the Lean classification of Q(3) on the whole torus. Not started.
3. Strichartz (non-endpoint), then 4. the family D4 bound: not started.

## Process notes for the next lead
- `make quick` before every push (lessons 35, 37). The final `make verify-all` takes about 2 hours on a 4-core machine,
  longer than the session tool's 2-hour background limit: start it detached (`nohup setsid …`) and wait on its log;
  log `date -u` at start and end (adversarial n9).
- Do not write proofs while a referee reads the tree (lessons 16, 42).
- Follow-ups recorded, not done: pin paths not validated in `stamp` (n5); actionlint and shellcheck not hash-pinned
  (n7); `latticeKernel1` is not covered by planted controls (n3).
