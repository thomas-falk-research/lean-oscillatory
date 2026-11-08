# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (40 entries); every rule in it is binding.

## What exists (end of session 6, 2026-11-08)
- Lean v4.35.0, Mathlib `56a0058`. 45 pinned statements, each with a row in `docs/STATUS.md`, all proved: S1–S4,
  front-end batches 1–3 (37 statements, as at the end of session 5) and, new this session, batch GD (eight):
  GD-C, GD, GD-F, GD-N (global decay from a local classification: nondegenerate / fold / finitely many D4 points, rate
  `m^{-2/3}`, `m^{-5/6}`, `m^{-1}`, uniformly over a compact set of linear terms or over all of them), SH (sharpness
  lemma), T1 (torus unfolding weight), T6 (2D lattice-Laplacian kernel `O(t^{-2/3})` uniformly in `x ∈ ℤ²`), T6L (its
  diagonal leading term with constant `Γ(1/3)² 48^{1/6}/√3`).
- Entry point `import OscInt.API` (90 names). Consumer examples compiled by `make quick`: `ConsumerFormula.lean`,
  `ConsumerLocal.lean`, `ConsumerLocalChecks.lean`, and new `ConsumerLattice.lean` (ℓ¹ → ℓ^∞ dispersive estimate
  `t^{-2/3}` for the 2D lattice Schrödinger propagator, its sharpness, and GD on x³ + y³, a formula phase with all three
  point types).
- API index `docs/api.json` (generated, `make api` / `make api-check`), `examples/api/Snippets.lean`, decision tree
  `docs/which-theorem.md`, `docs/cookbook.md`, `docs/applications.md`, `docs/downstream.md`, issue template.
- `main` = 34f8793 at the start of this session; this session's work is on branch `claude/wizardly-tesla-bqjaxv`
  (pull request to `main`: see the PR list).

- CI and release redesigned (`docs/decisions/2026-11-08-ci-release-review.md`): workflows `ci`, `verify` (parallel
  replay, `verify / verdict`), `release-candidate`, `post-release`, `mathlib-from-source`; composite action
  `setup-lean`; Dependabot. The owner creates tags and releases (decision 2026-11-08); CI prepares and checks.
- Licensing: REUSE 3.3 compliant (`reuse lint`, in CI); citation metadata aligned with ORCID and Zenodo
  (`CITATION.cff`, `.zenodo.json`, `codemeta.json`, README "How to cite"); derived S1 files keep Joris Roos's copyright.
- Replay record of this session: `docs/replay/2026-11-08-session6-GD-verify-all.txt` (c62a621, PASS 9/9, 107 min).

## Owner decisions (stop and ask)
1. **CONTRIBUTING step 5** (unchanged from session 5, now prepared): memo `docs/decisions/2026-11-08-step5-memo.md`,
   reviewed by a fresh adversarial referee (`review/2026-11-08-step5-rule-referee.md`, answers
   `review/2026-11-08-step5-rule-answers.md`). Options (iii) keep step 5 + one-time waiver + step-2 amendment
   (recommended), (i) a general test-layer exception (referee's corrected text), (ii) re-freeze API3 as API3′. Exact
   texts are in the memo. Batch GD did not need it (no MAJOR in its pre-proof reviews).
2. **Merge** the session's pull request (CI green on its head: `ci / quick`, `ci / tools`, `ci / consumer`,
   `verify / verdict`; these are also the checks to require under branch protection, an owner item).
3. **v0.4.0**: notes `docs/release-notes/v0.4.0.md` (batch 3 and batch GD; pins checked by `tools/release_preflight.sh`).
   Steps are in the notes: version bump and CHANGELOG heading, dispatch `release-candidate` on `main`, run the three
   commands it prints, merge the `post-release` pins pull request. Owner decisions taken this session: CI never
   writes tags or releases; no environment reviewers; Dependabot on; "Allow GitHub Actions to create and approve pull
   requests" enabled.
   Also yours (from the discoverability review): link the Zenodo DOIs on ORCID (0 works listed today; DataCite
   search & link, auto-update), a short arXiv preprint (`docs/outreach.md`), a Google Scholar profile, swMATH,
   Software Heritage "Save code now".
4. Still the owner's: P5 tactic policy (an unaudited `lean_lib` for an `oscint_hyps` tactic, or keep extending
   `OscInt/Front/Poly.lean`), venue and outreach (`docs/outreach.md`: Zulip draft, Reservoir, upstream PRs, preprint
   outline), branch protection, a human expert review of the statements, Mathlib from source on a second machine (the v0.3.0 version DOI is now in `CITATION.cff`).

## What was done this session (with commits)
- P0: memo and rule referee (bbafeeb, 3581074); API3 plant re-run and erratum (3581074); v0.4.0 notes prepared.
- P1 batch GD: classification pre-registered and run (3581074, then PASS: `numerics/results-classify-2026-11-08.txt`);
  statements edf7787, stamp + pins b71615c; pre-proof reviews FAITHFUL and TRUE ×2, sanity extended to 15 plants,
  reviews stamped 8c8d7b0 → ff79840; proofs 2aae8dd, c62a621 (agents GD-P1–P4, lead's assemblies); verify-all PASS
  9/9 on c62a621 (`docs/replay/2026-11-08-session6-GD-verify-all.txt`); post-proof FAITHFUL ×2, scope full, and an
  adversarial review with no BLOCKER/MAJOR (`review/2026-11-08-GD-*`, answers `review/2026-11-08-GD-post-proof-answers.md`).
- Review follow-ups not done (tool changes, recorded in the answers): verify every review-stamp directory, not only
  pinned ones (adversarial a1); `stamp verify` writes `.blob` files into stamp directories (f4); hash-pinned pip
  installs for `reuse`/`cffconvert` need a lock file (f5); a GD-N sanity datum smooth only on U (b2).
- P4: API index, generator with self-test, agent evaluation (`docs/replay/2026-11-08-api-eval.md`: 3/3 tasks), docs.
- P8: `docs/applications.md`, `docs/downstream.md`, `docs/outreach.md` (drafts for the owner).

## Not done, and why
- P1: the D4 statement uniform over a compact family (FE-S4.1′ for families) — needs the D4 normal form uniformly in
  the parameter; not attempted. The arccos family's global decay in Lean — the classification is numerical only (four
  D4 points, folds elsewhere); a Lean proof along the transcendental degenerate curve is open.
- P2: the 2D leading term is a design doc with a draft statement (`docs/design/leading-term.md`), not frozen (the
  proof needs a Morse lemma with C^k control); the Airy fold leading term is a draft with a candidate constant and a
  check to pre-register; the sharpness lemma is done (SH) and applied to T6L.
- P3: T0 (1D lattice kernel), the cone statements T4/T5′/T6′, `AddCircle` front ends and the two-band (matrix) model
  (needs vector-valued amplitudes, P5) — not started.
- P4: numerics CLI for user phases; tactic (owner decision).
- P5 (breadth), P6 (constants, certified-numerics demonstrator), P7 (incremental `make commit`, closure-diff tool,
  scheduled next-Mathlib job, D4 assembly refactor, linters, doc-gen4 site): not started. The batch with its full
  review cycle and the replay took the session.

## Next (in this order)
1. Owner: decisions 1–3.
2. Vector-valued amplitudes (P5) — unblocks the two-band lattice model and spectral projections; then the T0 1D
   kernel and the cone statements on top of GD.
3. The family D4 bound, then the arccos family through GD (Lean classification lemma along the degenerate curve).
4. P6 certified-numerics demonstrator (a Lean-checked C, m₀ for one phase).

## Process notes for the next lead
- `make quick` before every push (lessons 35, 37); an untracked in-progress proof file breaks the guard/audit count,
  so finish or park it before running `make quick`.
- Sanity data in every branch of every case split (lessons 38); generate plants with
  `docs/replay/plants/2026-11-08-GD/plants_gd.py.txt` as the template.
- Cite only records that exist (lessons 36).
- Proof agents with exact blueprint propositions and checked names: GD-P1–P3 took 2–3 minutes each, GD-P4 4 minutes.
