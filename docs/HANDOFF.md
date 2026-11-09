# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (43 entries); every rule in it is binding.

## What exists (session 7, 2026-11-08/09)
- Lean v4.35.0, Mathlib `56a0058`. **52 pinned statements, all proved**, each with a row in `docs/STATUS.md`: S1–S4,
  front-end batches 1–3, batch GD (eight; session 6) and, new this session, **batch VT** (four: GD-C-V, GD-V, GD-F-V,
  GD-N-V, the global decay estimates for amplitudes in any complex Banach space `E : Type`, one constant for every E;
  replay `docs/replay/2026-11-09-session7-VT-verify-all.txt`, d261c19, PASS 9/9) and **batch LE** (three):
  - T0E `latticeKernel1Explicit`: |∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 24·2^{1/4} t^{−1/2} + 36·2^{1/6} t^{−1/3} (t > 0, ξ real);
  - T6F `latticeKernelFactor`: the 2D kernel of T6 is the product of two 1D kernels;
  - T6E `latticeLaplacianExplicit`: |K(t, x)| ≤ (A+B)² t^{−2/3} ≈ 4754 t^{−2/3} for t ≥ 1.
  These constants are explicit but weak: they beat the trivial bounds only for t > 518 (1D) and t > 1321 (2D).
- Replay record: `docs/replay/2026-11-08-session7-LE-verify-all.txt` (a1d2a64, PASS 9/9, 127 min, alone on the machine).
  Reviews: pre-proof FAITHFUL and TRUE ×2, route referee, post-proof FAITHFUL ×2, adversarial no BLOCKER/MAJOR
  (`review/2026-11-08-LE-*`).
- Disclosure: T6 and T6L are classical (the kernel factorises into 1D Bessel kernels), `docs/prior_art.md`.
- Entry point `import OscInt.API` (104 names). Consumer examples compiled by `make quick` now include
  `examples/consumer/ConsumerLatticeExplicit.lean`.
- Tools: `stamp verify-every` verifies every stamp directory and rejects symlinks, stray entries, defective manifests
  (header, full commit that is an ancestor of HEAD, hashed set = `git ls-tree` of the commit) and truncated `.ots`
  files; it writes nothing into `stamps/`. CI pip installs are hash-locked (`tools/requirements-ci*.txt`).
- GD-N has a sanity datum smooth only on U (`OscInt/Front/GlobalNondegLocalSanity.lean`, follow-up b2).
- Branch `claude/stoic-allen-lxasbf`, pushed; no pull request (the owner opens one when wanted). `main` = 96f55a2 with
  CI green (`ci` and `verify` both success).

## Owner decisions (stop and ask)
1. **CONTRIBUTING step 5: decided 2026-11-09, option (iii).** One-time waivers for API3's test-layer MAJOR and LE's
   documentation-only MAJOR (recorded in the 13 STATUS rows and the answers files); step 2 amended (conditional sanity
   theorems with planted copies before the stamp); step 5 gains a clause for documentation-only MAJORs.
2. **v0.4.0: prepared in this branch** (versions bumped, CHANGELOG section, notes with pins for batches 3, GD, LE and VT;
   `tools/release_preflight.sh 0.4.0` passes). After the merge: Actions → `release-candidate` on `main`, then the three
   commands it prints (`docs/release-notes/v0.4.0.md`, "Publishing").
3. AI-authorship wording (adversarial finding f1 of session 6), branch protection, P5 tactic policy, discoverability.
4. Human expert review: deferred by the owner under `docs/policy.md` (wording rule, calibration plan, triggers).

## Session-7 order (owner, `docs/ROADMAP.md`) and where it stands
0. Session-6 follow-ups a1, f4, f5, b2: **done**.
1. Batch LE: **done** (above).
2. **Batch VV**: the vector-valued transfer is **done** (batch VT). The owner's acceptance test (a non-separable two-band
   model compiled end to end) is **not met**: the candidate QWZ m = 3 failed its pre-registered decay check (t^{−2/3}
   observed) and has four exact cusp points, which the grid classifier missed (erratum `docs/design/vector-amplitudes.md`
   §6, lessons 43). QWZ m = 1, 0.5 and the triangular lattice also have cusps. Next: a model search with symmetry-line
   checks and a sub-grid cusp control (option A), a model whose classification can be done in closed form (option B), or
   Strichartz first (option C): plans and recommendation in `docs/design/vector-amplitudes.md` §7; owner's choice.
3. Strichartz (non-endpoint), then 4. the family D4 bound: not started.

## Process notes for the next lead
- `make quick` before every push (lessons 35, 37). The final `make verify-all` takes about 2 hours on a 4-core machine,
  longer than the session tool's 2-hour background limit: start it detached (`nohup setsid …`) and wait on its log;
  log `date -u` at start and end (adversarial n9).
- Do not write proofs while a referee reads the tree (lessons 16, 42).
- Follow-ups recorded, not done: pin paths not validated in `stamp` (n5); actionlint and shellcheck not hash-pinned
  (n7); `latticeKernel1` is not covered by planted controls (n3).
