# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (45 entries); every rule in it is binding.

## Session 8 (2026-11-09): what changed, and where to start
- **v0.4.0 reconciled** (ROADMAP I0): pins PR #9 and DOI PR #10 merged; Zenodo 10.5281/zenodo.24088811 in
  `CITATION.cff`, README, CHANGELOG. #10's last `verify` run had all 17 jobs green but no `verdict` job (GitHub-side;
  re-run refused); the owner merged on the 17 jobs (recorded in ROADMAP I0).
- **Industry programme** (owner direction: a library for the whole industry, not one consumer): ROADMAP section
  "Industry programme" (I0–I6); input class decided (`docs/decisions/2026-11-09-input-language.md`).
- **CENSUS** (ROADMAP I1): specification `docs/prereg/2026-11-09-CENSUS-spec.md` and registration
  `docs/prereg/2026-11-09-CENSUS-prereg.md`, both DRAFT (spec-fidelity referee not yet run; no implementation exists;
  nothing run). Exact spec checks `numerics/census/spec_checks.py`, 35/35 (`numerics/results-census-spec-2026-11-09.txt`).
  Prior art (logged sweep `review/2026-11-09-CENSUS-prior-art-sweep.md`; its brief is not recorded, owner decision):
  per-model classifications exist for discrete Klein–Gordon, lattice wave, triangular lattice, King's graph, graphene
  (`docs/prior_art.md`, "Singularities of lattice dispersion relations"); they all point to the A3 bound.
- **Batch A3, statement-first phase complete; nothing proved.** S1.k (k-th derivative van der Corput, constant
  5·2^{k−1} − 2), S5.1 (stable cusp, t^{−3/4} uniform in the linear term), S5.1′ (any A3 point): `OscInt/Statements/Cusp.lean`,
  stamp `stamps/20261109T201548Z-fcb46d9a6239` (pinned; `make commit` 55/55), sanity `OscInt/Front/CuspSanity.lean`,
  plants `docs/replay/2026-11-09-A3-sanity-plants.txt` (run after the stamp: deviation recorded), pre-proof reviews
  FAITHFUL and TRUE ×2 (`review/2026-11-09-A3-pre-proof-{A,B}.md`, answers, reviews stamped
  `stamps/20261109T214121Z-47c1360ccd6f`). STATUS rows: "stated and reviewed, not proved".
- **Corrections made public:** Landau's constant 0.7857 (not 0.7858; `docs/prior_art.md`); the arccos family's
  quantum-walk/photonic attribution was unverified (`docs/applications.md`).
- **Next, in order:** (1) `docs/proof-A3.md` route document + route referee before any proof: S1.k by induction from the
  existing S1 parts (both referees outline it); S5.1 by anisotropic rescaling + S3 on annuli + S2.1 (mirrors S4.1′), or
  the cheaper route both referees name (1D stationary phase in the transverse variable with parameters, then S1.k at
  k = 4), which also proves S5.1′; the missing tool is that parametrised 1D stationary-phase lemma. (2) CENSUS
  spec-fidelity referee (prompt drafted in the session scratchpad, not committed), then implementations A and B.
  (3) LeanCert experiment (ROADMAP I2), its own pre-registration first. (4) Global assembly with A3 points: a pointwise
  classification plus compactness, not a finite set (non-stable A3 points form curves; both A3 referees).
- **Owner items open:** whether referee prompts are recorded (CONTRIBUTING step 5 says yes; the owner chose not to record
  the CENSUS sweep brief); human or other-family statement review (all reviews so far are same-family AI).
- **Container notes:** the session container had no Lean: install from `toolchain.sha256` as
  `.github/actions/setup-lean/action.yml` does (it needs `zstd`; `apt-get install zstd bubblewrap`), then
  `lake exe cache get`. `make quick` takes ~13 min warm; `make stamp` ~13 min; all five timestamp endpoints were
  reachable through the proxy.

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
