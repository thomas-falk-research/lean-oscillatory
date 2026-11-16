# Changelog

Versions follow semantic versioning from v0.3.0 (`docs/policy.md`): before 1.0.0, a minor version (0.y.0) may change
statements and says so under "Statement changes"; a patch (0.y.Z) changes no statement, commitment, statement file
or `proved_by` name. Every release lists its statement changes, even when there are none.

## Unreleased (after v0.6.0)

Not a release. Statement changes since v0.6.0, for the next minor release:

### Statement changes

Batch PA (`OscInt/Statements/PeriodicAnalytic.lean`, stamp `stamps/20261116T130956Z-276d8d7f9605`): three new entries,
- PA-C `FourierCoeffStripStatement` (`proved_by` `OscInt.API.fourierCoeffStrip`);
- PA-T `TrapezoidalRuleStatement` (`proved_by` `OscInt.API.trapezoidalRule`);
- LC-1 `LatticeKernel1LightConeStatement` (`proved_by` `OscInt.API.latticeKernel1LightCone`).

Batch KL (`OscInt/Statements/KusminLandau.lean`, same stamp): three new entries,
- KL-D `KusminLandauStatement` (`proved_by` `OscInt.API.kusminLandau`);
- KL-C `KusminLandauTwoOverPiStatement` (`proved_by` `OscInt.API.kusminLandauTwoOverPi`);
- KL-F `KusminLandauDerivStatement` (`proved_by` `OscInt.API.kusminLandauDeriv`).

No existing statement's text, file, commitment or stamp changed. The six are proved in Lean (build, axiom audit,
statement types, kernel re-check per module); their isolated replay and post-proof reviews are pending, so
`docs/STATUS.md` does not yet call them machine-checked as stated.

### Proofs

Statement-first, as before: frozen and stamped, sanity layers with planted controls, blind pre-proof reviews
(answers stamped `stamps/20261116T152412Z-9c9a8767b806`), routes `docs/proof-PA.md` and `docs/proof-KL.md` with
blueprints and assemblies compiled before any part, one route referee per batch
(`review/2026-11-16-PA-KL-route-answers.md`), then the parts by proof agents. Lead, referees and provers are AI
agents of one model family.

### Added

- Tools, experimental and not published: the certificate contract `docs/contract/certificate-v0.md`, a Python
  checker `python/oscint_cert/` and an independent Rust checker `rust/oscint-cert/`.
- A registered, not run, protocol for a continuous-time quantum walk on a qubit chain
  (`docs/prereg/2026-11-16-CTQW-chain.md`, `experiments/ctqw-chain/`).
- `docs/design/unlock-map.md`, `docs/funding/` (a draft application package), `docs/design/batch-FR-draft.md` (draft
  statements for finite rings and open chains; not frozen).
- `examples/consumer/ConsumerPeriodicAnalytic.lean`, `examples/consumer/ConsumerKusminLandau.lean`: unconditional
  uses of the six new theorems (normalised Fourier coefficients, a stopping rule for the trapezoidal rule, the light
  cone at one e-folding per site, exponential sums with a linear phase); compiled by `make quick`.

## v0.6.0 — 2026-11-15

A minor release. Before 1.0.0 a minor release may change statements; this one changes no existing statement's text,
file, commitment or stamp. It sets `proved_by` for the four statements of batch LS, which were stated, frozen and
reviewed in v0.5.0 and are now proved and machine-checked as stated (`docs/policy.md`: `null` → a theorem is a minor
change), and adds the two statements of batch D4U, stated, frozen, reviewed, proved and machine-checked as stated
since v0.5.0. All 65 statements are now machine-checked as stated (`docs/STATUS.md`). Compared with the v0.5.0 tag on
2026-11-14, field for field, the changes in `stamps/statements.json` are these four `proved_by` fields and the two new
entries;
`tools/oscint_check.py` is byte-identical to v0.5.0's. Toolchain `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, both unchanged. Release notes and pins: `docs/release-notes/v0.6.0.md`.

### Statement changes

Batch LS (`OscInt/Statements/LatticeGroup.lean`, stamp `stamps/20261112T215742Z-d18e0780abdb`, unchanged): `proved_by`
goes from `null` to a theorem for
- LS-E `LatticeSchrodingerExistsStatement`: `OscInt.API.latticeSchrodingerExists`;
- LS-K `LatticeSchrodingerKernelStatement`: `OscInt.API.latticeSchrodingerKernel`;
- LS-D `LatticeSchrodingerDispersiveStatement`: `OscInt.API.latticeSchrodingerDispersive`;
- LS-D′ `LatticeSchrodingerDecayStatement`: `OscInt.API.latticeSchrodingerDecay`.

Batch D4U (`OscInt/Statements/D4Uniform.lean`, stamp `stamps/20261115T122915Z-33c56db38f65`): two new entries,
- S4.2U `D4LimitUniformStatement` (`proved_by` `OscInt.API.d4LimitUniform`);
- S4.2O `D4LimitOffsetStatement` (`proved_by` `OscInt.API.d4LimitOffset`).

No other entry changed.

### Proofs

Batch LS: proved in Lean on 2026-11-14
(`OscInt/Front/LatticeGroup{Op,Exp,Unique,Stencil,FourierStencil,Series,Conv,Bound,Envelope,Final}.lean`). The parts
were drafted by an external reviewer with an AI tool and repaired to elaborate by the lead's proof agents with 32
mechanical changes (`docs/replay/2026-11-14-LS-packet-repairs.diff`; disclosure in `docs/prior_art.md`; answers
`review/2026-11-14-external-R4-answers.md`). Isolated replay of 1bc377b:
`docs/replay/2026-11-14-session11-LS-verify-all.txt`. Post-proof reviews: `review/2026-11-14-LS-post-proof-answers.md`.
Isolated replay of 35dc5c0, after the post-review Lean changes (docstrings, one import, the local lemma `box_volume`):
`docs/replay/2026-11-14-session11-LS-final-verify-all.txt`, comparator-LS accepted by six kernels.

Batch D4U: stated, frozen and stamped (33c56db), blind-reviewed (answers `review/2026-11-15-D4U-pre-proof-answers.md`,
review stamp `stamps/20261115T133952Z-9e9c6245f582`), route `docs/proof-D4U.md` (route referee SOUND), proved in Lean
(`OscInt/Front/D4Uniform{Assembly,Parts,Modulation,Final}.lean`), post-proof reviews answered
(`review/2026-11-15-D4U-post-proof-answers.md`). The question, a hand proof and Lean drafts of the same shape came from
an external research packet, disclosed (`review/2026-11-15-D4U-packet-answers.md`). Isolated replay of 720363d: `docs/replay/2026-11-15-session12-D4U-verify-all.txt`.

### Added

- `examples/consumer/ConsumerD4Uniform.lean`: unconditionally, the D4 limit along offsets that move with t (lattice
  rounding) with the closed-form constant, and the eventual lower bound it gives through the sharpness lemma SH.

- `OscInt/Front/D4UniformSanity.lean`: sanity theorems through the D4U statement constants, with a family that is not
  finite-dimensional, bites, and planted controls (`docs/replay/2026-11-15-D4U-sanity-plants.txt`).
- `numerics/review/d4u_interface_checks.py`.
- `examples/consumer/ConsumerLatticeSchrodinger.lean`: unconditional time derivatives of the LS kernel at `t = 0`.

### Release pipeline

The v0.5.0 release was tagged while the push run of `ci.yml` on its commit had been cancelled at a timeout, and its
pins pull request needed a hand fix. After an audit of the release pipeline:
- `release-candidate.yml` also runs `ci.yml` (made callable) on the release commit, so docs-check, `make quick`, REUSE,
  the `CITATION.cff` schema, actionlint and the downstream consumer gate the release.
- New `tools/publish_release.sh`: the owner's single publishing command. Before anything is public (Zenodo mints a
  permanent DOI on publishing) it checks the candidate run, the exact asset set, `SHA256SUMS`, that the assets equal
  the files of the release commit, that the release body is the one built from that commit's notes (the candidate run
  builds it with the same function), each attestation pinned to `release-candidate.yml` on `main` for that commit,
  and that no release exists and any tag is annotated and points at the commit; then it tags, creates the release as
  a draft, checks the draft's assets and publishes it. `--dry-run` stops before the tag; `--self-test` plants 12
  defects.
- `tools/release_preflight.sh` now compares the release with the previous tag: the version is greater, a patch leaves
  `stamps/statements.json` byte-identical, from 1.0.0 a minor only adds entries or sets a `proved_by` that was null,
  and every changed entry's label is named in the notes' and the CHANGELOG's statement changes. It also requires the
  three release dates to agree, every `rev =` in the notes to be the new tag, and every `proved_by` theorem to be
  covered by a comparator configuration (28 planted defects in its self-test, and the previous-tag order).
- `post-release.yml`: attestations are verified with the signer workflow, source ref and commit pinned; the release
  must have exactly the three assets; the downstream check covers every proved statement instead of three; the pins
  step runs only on publishing, can be re-run after a partial failure, and also dispatches `verify.yml`.
- The release candidate's calls of `verify.yml` and `ci.yml` have their own concurrency groups, so they no longer
  queue behind, or get replaced by, the push run of the same commit.
- Earlier, at 43a13fb: the `ci` consumer job's timeout went from 60 to 90 minutes, and the pins step moves every pin
  that docs-check checks (it had missed `docs/downstream.md`).

### Changes

- The v0.5.0 version DOI `10.5281/zenodo.24205167` recorded in `CITATION.cff` and the README.
- Answers to the external R3 packet (`review/2026-11-13-external-R3-answers.md`, with the reviewer's reply and a
  citation check of its application survey; lead's checks `numerics/review/r3_packet_checks.py`) and to the R4 packet
  and W2 addendum (`review/2026-11-14-external-R4-answers.md`; `numerics/review/r4_packet_checks.py`).
  `docs/calibration.md`: the Clopper–Pearson bounds of its table are now rounded outwards (three printed values were
  not bounds; no reading changes).
- `docs/lessons.md` 50: keep a cloud session busy while a detached replay runs; two cut-off replays recorded as
  partial (`docs/replay/2026-11-14-session11-d760beb-partial.txt`, `docs/replay/2026-11-14-session11-1bc377b-partial.txt`).

## v0.5.0 — 2026-11-13

A minor release. Before 1.0.0 a minor release may change statements; this one changes none. It adds 11 statements:
- **seven proved and machine-checked as stated:** batch A3 (S1.k, S5.1, S5.1′), batch LE2 (T0E′, T6E′) and batch HC
  (TdF, TdE′);
- **four stated, frozen and reviewed but not proved:** batch LS (LS-E, LS-K, LS-D, LS-D′), whose `proved_by` is
  `null` in `stamps/statements.json`. Their proofs will come in a later minor release.

There are 63 statements in all, 59 of them machine-checked as stated (`docs/STATUS.md`). The 52 entries of v0.4.0 in
`stamps/statements.json` are unchanged, field for field (compared with the v0.4.0 tag on 2026-11-13). Toolchain
`leanprover/lean4:v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, both unchanged. Release notes
and pins: `docs/release-notes/v0.5.0.md`.

### Statement changes

Batch A3 (sessions 8–10): three new statements, frozen, reviewed and **proved**: S1.k (`VdCkStatement`), S5.1
(`CuspBoundStatement`) and S5.1′ (`CuspBoundGenStatement`) in `OscInt/Statements/Cusp.lean`, stamp
`stamps/20261109T201548Z-fcb46d9a6239`; `proved_by` `OscInt.API.vdCk`, `cuspBound`, `cuspBoundGen` (since 93a8a8d);
machine-checked as stated since the isolated replay of 1f7d041 (`docs/STATUS.md`).

Batch LE2 (session 10): two new statements, frozen, reviewed and **proved**: T0E′
(`LatticeKernel1CubeRootStatement`, `OscInt.API.latticeKernel1CubeRoot`) and T6E′ (`LatticeLaplacianCubeRootStatement`,
`OscInt.API.latticeLaplacianCubeRoot`) in `OscInt/Statements/LatticeCubeRoot.lean`, stamp
`stamps/20261110T234417Z-0532b1cf8880`. They imply the frozen T0E and T6E, which are unchanged.

Batch HC (session 10): two new statements, frozen, reviewed and **proved**: TdF
(`HypercubicKernelFactorStatement`, `OscInt.API.hypercubicKernelFactor`) and TdE′ (`HypercubicCubeRootStatement`,
`OscInt.API.hypercubicCubeRoot`) in `OscInt/Statements/Hypercubic.lean`, stamp `stamps/20261112T120616Z-c56beb57ff8c`.

Batch LS (session 10): four new statements, frozen and reviewed, **not proved**: LS-E
(`LatticeSchrodingerExistsStatement`), LS-K (`LatticeSchrodingerKernelStatement`), LS-D
(`LatticeSchrodingerDispersiveStatement`) and LS-D′ (`LatticeSchrodingerDecayStatement`) in
`OscInt/Statements/LatticeGroup.lean`, stamp `stamps/20261112T215742Z-d18e0780abdb`.

### Changes

- Package metadata for v0.5.0 (`lakefile.toml`, `CITATION.cff`, `codemeta.json`, `.zenodo.json`): a new abstract
  covering the cusp and lattice results, and more keywords. README rewritten around what is proved; documentation
  index, decision tree (`docs/which-theorem.md`), ROADMAP and hand-off updated.
- Batch A3 proved in Lean (S1.k, S5.1, S5.1′), from an external packet drafted with an OpenAI model and integrated by
  the lead with five elaboration fixes (`review/2026-11-12-A3-packet-answers.md`); post-proof reviews answered
  (`review/2026-11-12-A3-post-proof-answers.md`); "Parts as proved" in `docs/proof-A3.md`.
- Batch A3 replayed in isolation on 1f7d041 (`docs/replay/2026-11-13-session10-A3-verify-all.txt`): comparator-A3
  accepted by six kernels; S1.k, S5.1 and S5.1′ are machine-checked as stated. A first attempt was stopped by the
  session's two-hour limit on background tasks and is disclosed in the record.
- Batch LS (the free lattice Schrödinger group): statements, sanity layer and planted controls, two blind pre-proof
  reviews (`review/2026-11-12-LS-pre-proof-answers.md`), review stamp; route `docs/proof-LS.md` with nine parts in
  `Blueprint/LatticeGroup.lean` and a compiled assembly, refereed (revision section in the route).
- Answers to the external application-chains dossier (`review/2026-11-13-application-chains-answers.md`): six hand
  propositions and an imaging block bound checked (TRUE, not machine-checked); lead's checks
  `numerics/review/application_chains_checks.py`; four corrections to `docs/applications.md`.
- Consumer example `examples/consumer/ConsumerWhistler.lean`: whistler packet at the inflection of the dispersion (S1.3).
- Partial, non-isolated replay of e814510 kept for the record (`docs/replay/2026-11-12-session10-e814510-partial.txt`).
- Answers to the external research packet on lattice NLS and domain connections
  (`review/2026-11-12-DNLS-packet-answers.md`): kernel-to-group identification, global ℓ² dynamics and explicit
  small-data decay checked (hand proofs, not machine-checked); lead's checks `numerics/review/dnls_checks.py` (record
  `numerics/results-dnls-checks-2026-11-12.txt`).
- Answers to the external R2 packet (`review/2026-11-12-R2-KG-answers.md`): an explicit cube-root bound for the 1D
  discrete Klein–Gordon kernel at every mass, checked (TRUE, not machine-checked) and recorded as a ROADMAP candidate;
  lead's checks `numerics/review/kg_checks.py` (record `numerics/results-kg-checks-2026-11-12.txt`). Addendum after an
  external audit: C* is within a factor below 1.9 of the best universal mass-normalised coefficient (exact check
  `numerics/review/kg_factor_check.py`, record `numerics/results-kg-factor-check-2026-11-12.txt`).
- Batch HC: the hypercubic lattice kernel on ℤ^d factorises, and `|K_d(t, x)| ≤ (8(1 + √7)/3)^d t^{−d/3}` for every
  `d`, `t > 0` and `x`; statement-first, blind-reviewed, routed and refereed, proved in Lean, replayed
  (`docs/replay/2026-11-12-session10-HC-verify-all.txt`); post-proof answers `review/2026-11-12-HC-post-proof-answers.md`.
- Consumer examples `examples/consumer/ConsumerColdPlasma.lean` (cold-plasma transverse waves, `τ^{−1}` uniformly in the
  observation point) and `examples/consumer/ConsumerPhaseMixing.lean` (phase mixing of free streaming).
- Scoping `docs/design/dnls-scoping.md`: small-data decay for the discrete NLS from TdE′ (not a commitment).
- Numerical interface check `numerics/review/hc_interface_checks.py` (record
  `numerics/results-hc-interface-checks-2026-11-12.txt`).
- Batch LE2: the cube-root bound `|∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 8(1 + √7)/3 · t^{−1/3}` for every `t > 0` and real
  `ξ`, and its 2D form; useful from `t ≈ 3.70` instead of 518 and 1321. From an external reviewer's hand proof
  (AI-use disclosure in `docs/prior_art.md`), re-derived, blind-reviewed, routed and refereed, proved in Lean, replayed
  (`docs/replay/2026-11-11-session10-LE2-verify-all.txt`).
- Answers to the external follow-up submissions (`review/2026-11-10-external-followup-answers.md`): the cube-root bound,
  the QWZ critical-mass results (candidate evidence), and the photonic and plasma application studies.
- Consumer example `examples/consumer/ConsumerPhotonLattice.lean`: single-photon transition probabilities on a
  cosine-band lattice, nontrivial from `2κt ≥ 4` with T0E′.
- Batch A3 statement-first phase: sanity data and planted controls, two blind pre-proof reviews (FAITHFUL, TRUE),
  reviews stamped (`stamps/20261109T214121Z-47c1360ccd6f`).
- CENSUS (ROADMAP I1): specification and registration, both DRAFT; exact spec checks 39/39
  (`numerics/results-census-spec-2026-11-10.txt`); control K-QWZm and a sealed held-out set added before registration;
  revised after the spec-fidelity referee (`review/2026-11-10-CENSUS-spec-answers.md`), with the machine-readable corpus
  `numerics/census/corpus.json`.
- External reviews, answered item by item with independent checks (the reviews themselves are not recorded, owner
  privacy rule; answers `review/2026-11-10-external-*-answers.md`); `docs/prior_art.md` marks S1.k anticipated.
- ROADMAP: industry programme (I0–I7), dimension-generic track (I3a, I3b), gated candidate list.

## v0.4.0 — 2026-11-09

DOI [10.5281/zenodo.24088811](https://doi.org/10.5281/zenodo.24088811) (all versions:
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328)). Release commit 87a418a, verified by
`release-candidate` run 42567796580 (full replay); the Zenodo archive embeds that commit and its `stamps/statements.json`
and `tools/oscint_check.py` match the release pins.

### Statement changes (batch LE, session 7)
No existing statement changed. Added (`OscInt/Statements/LatticeExplicit.lean`, stamp
`stamps/20261108T160847Z-4a183530559f`, reviews stamped at `stamps/20261108T164514Z-c91a9a8bb0b6`): T0E
`LatticeKernel1ExplicitStatement`, T6F `LatticeKernelFactorStatement`, T6E `LatticeLaplacianExplicitStatement`
(48 statements). Proof status: `docs/STATUS.md`.

### Statement changes (batch VT, session 7)
No existing statement changed. Added (`OscInt/Statements/Vector.lean`, stamp `stamps/20261108T235416Z-961cebc296ef`,
reviews stamped at `stamps/20261109T002419Z-45505299011a`): GD-C-V `GlobalDecayCritVecStatement`, GD-V
`GlobalDecayVecStatement`, GD-F-V `GlobalFoldVecStatement`, GD-N-V `GlobalNondegVecStatement` (52 statements).

### Batch VT (new)
- The global decay estimates GD-C, GD, GD-F, GD-N for amplitudes with values in any complex Banach space `E : Type`
  (matrices, ℂⁿ, ℓ^∞, operators), with the scalar constant, proved by duality (Hahn–Banach); a universe-polymorphic
  transfer lemma `OscInt.VectorAux.transfer`. Consumer example `examples/consumer/ConsumerVector.lean`.
- Not met: the owner's VV acceptance test (a non-separable two-band model end to end). The QWZ m = 3 candidate failed its
  decay check and has exact cusp points (erratum, `docs/design/vector-amplitudes.md` §6).

### Batch LE and session-7 records
- Explicit constants: |I(t, ξ)| ≤ 24·2^{1/4} t^{−1/2} + 36·2^{1/6} t^{−1/3} for the 1D lattice kernel (from S1.2, S1.3),
  the factorisation K(t, x) = I(t, x₁) I(t, x₂), and |K(t, x)| ≤ (A+B)² t^{−2/3} ≈ 4754 t^{−2/3} for t ≥ 1. Honest but
  weak: they beat the trivial bounds only for t > 518 and t > 1321. Consumer example
  `examples/consumer/ConsumerLatticeExplicit.lean`.
- Disclosure: T6 and T6L are classical (the 2D kernel factorises into 1D Bessel kernels; Landau's bound; the
  Cauchy–Watson asymptotic), `docs/prior_art.md`.
- `docs/policy.md`: the owner's deferral of a human expert review, with its wording rule, calibration plan and triggers.
- Batch VV groundwork: design `docs/design/vector-amplitudes.md` (duality route); pre-registered classification
  (`docs/prereg/2026-11-08-VV-classify.md`) reported the QWZ band at m = 3 as nondegenerate-or-fold everywhere; that was a
  grid artifact (erratum, `docs/design/vector-amplitudes.md` §6: four exact cusp points), and its decay check failed
  (t^{−2/3} observed). m = 1, 0.5 and the triangular lattice have cusps. No VV acceptance model yet.
- Tools: `stamp verify-every` verifies every stamp directory (review stamps included) and writes nothing into
  `stamps/`; CI installs `reuse`/`cffconvert` hash-locked (`tools/requirements-ci*.txt`); a GD-N sanity datum smooth
  only on U (`OscInt/Front/GlobalNondegLocalSanity.lean`).

### Statement changes (batch GD, session 6)
Against v0.3.0 and front-end batch 3: **no existing statement changed** (stamped files unchanged; `make commit` against
the pinned stamps). Added (`OscInt/Statements/Global.lean`, stamp `stamps/20261108T094842Z-edf7787a2845`, reviews
stamped at `stamps/20261108T102629Z-8c8d7b090adb`): GD-C `GlobalDecayCritStatement`, GD `GlobalDecayStatement`, GD-F
`GlobalFoldStatement`, GD-N `GlobalNondegStatement`, SH `SharpnessStatement`, T1 `TorusUnfoldStatement`, T6
`LatticeLaplacianDecayStatement`, T6L `LatticeLaplacianLimitStatement` (45 statements). Proof status: `docs/STATUS.md`.

### Batch GD (new)
- Global decay from a local classification: a phase smooth on an open set gives `m^{-2/3}` uniformly over a compact
  set of linear terms when its critical points for those terms (in a compact set, outside finitely many D4 points) are
  nondegenerate or folds (GD-C), and over all linear terms when every point outside the D4 points is (GD); `m^{-5/6}` and `m^{-1}` over all linear terms
  without D4 points or without degenerate points.
- The sharpness lemma (a limit with nonzero constant gives a matching lower bound and excludes faster rates).
- The torus unfolding weight, the 2D lattice-Laplacian dispersive estimate `t^{-2/3}` uniformly in `x ∈ ℤ²`, and its
  diagonal leading term with the constant `Γ(1/3)² 48^{1/6}/√3` (the D4 constant of the umbilic at (π/2, π/2), and
  also the classical Cauchy–Watson Bessel constant: the kernel factorises, `docs/prior_art.md`); consumer example
  `examples/consumer/ConsumerLattice.lean` (ℓ¹ → ℓ^∞ estimate, sharpness, GD on x³ + y³).
- Sanity theorems through all eight constants with 15 planted controls before any proof
  (`docs/replay/2026-11-08-GD-sanity-plants.txt`); numeric pre-registration of the classification and of the
  lattice limit (`docs/prereg/2026-11-08-P1-classify.md`, PASS).

### API, docs and tooling (session 6)
- `docs/api.json`: machine-readable index of every statement (frozen Lean text, plain-word hypotheses and conclusion,
  rate, uniformity, smoothness, see-also, helpers, conventions) generated by `tools/gen_api.py` from
  `stamps/statements.json`, the statement files and `docs/api/annotations.json`; `examples/api/Snippets.lean` compiled in
  `make quick`; drift fails `make quick` (`make api-check`, self-test `tools/test_gen_api.sh` with 6 planted defects).
  Evaluated by a fresh agent with only the index and README (3/3 tasks, `docs/replay/2026-11-08-api-eval.md`).
- `docs/which-theorem.md` (decision tree), `docs/cookbook.md`, `docs/applications.md`, `docs/downstream.md`,
  `docs/design/leading-term.md`, `.github/ISSUE_TEMPLATE/phase-does-not-fit.md`.
- Owner memo on CONTRIBUTING step 5 (`docs/decisions/2026-11-08-step5-memo.md`, refereed); v0.4.0 notes prepared.
- Records: API3 plant re-run and an erratum in the API3 answers (a cited record part did not exist).

### CI and release (session 6; `docs/decisions/2026-11-08-ci-release-review.md`)
- One composite action `setup-lean` (pinned toolchain archive, SHA-256 checked on every run, retries, cached; no
  elan, whose installer fetched an unpinned latest binary and made every push of the session red during a GitHub
  outage). Workflows by purpose: `ci` (quick, tools, consumer; pull requests and `main`), `verify` (the replay as
  parallel jobs after one clean build, a comparator matrix, one `verify / verdict` check; non-draft pull requests to
  `main`, `main`, weekly), `release-candidate` (dispatch; preflight `tools/release_preflight.sh`, full replay on the
  exact commit, assets with `SHA256SUMS` and a Sigstore attestation, the owner's tag and release commands),
  `post-release` (on publishing: tag on `main` with a successful candidate run, attested assets, consumer build
  against the tag, pins pull request), `mathlib-from-source` (dispatch); Dependabot for the pinned actions.
  The owner creates tags and releases; CI never does.

### Licensing and citation (session 6)
- REUSE 3.3 compliant (`reuse lint` in `ci / tools`): licence texts in `LICENSES/` (Apache-2.0, CC-BY-4.0,
  LicenseRef-PublicCertificate for the third-party TSA roots and tokens), comment headers in source files
  (Mathlib-style for Lean), `REUSE.toml` for frozen, generated, record and documentation files. The van der Corput
  files derived from roos-j/lean-oscillatory keep Joris Roos's copyright with a modification notice.
- `CITATION.cff` aligned with ORCID (Thomas Falk III), author email, both licences, the v0.3.0 version DOI, verified
  references (Mathlib, Lean 4, Roos–Praveen, Stein) and MSC2020 codes; `.zenodo.json` refreshed; `codemeta.json`
  added; README "How to cite".

### Statement changes (front-end batch 3, session 5)
Against v0.3.0: **no existing statement changed** (`make commit`: every commitment equals its pinned stamp,
`docs/replay/2026-11-08-session5-API3-verify-all.txt`). Added (front-end batch 3, `OscInt/Statements/Family.lean`, stamp
`stamps/20261108T002603Z-9d03130c8f3a`): S2.2F `StationaryPhaseFamilyStatement`, S3c `FoldCritStatement`, C10
`FamilyCkOfUncurryStatement`, FE-S2.1L `NonStationaryLocalStatement`, FE-S2.2L `StationaryPhaseLocalStatement`, FE-S3L
`FoldLocalStatement`, FE-S4.1′L `D4BoundLocalStatement`, FE-S2.1l `NonStationaryOnStatement`, FE-S2.2l
`StationaryPhaseOnStatement`, FE-S3l `FoldOnStatement`; all ten proved (`proved_by` in `stamps/statements.json`, 37
statements). A release containing them is a minor release (0.4.0).

### Front-end batch 3 (new)
- Uniformity over compact families of phases for nondegenerate stationary phase (S2.2F) and, with the classical
  hypothesis (fold-or-nondegenerate only at critical points), for the fold estimate (S3c, strictly stronger than S3).
- Local smoothness: front ends for S2.1, S2.2, S3 (families indexed by a compact set of a real normed space, smooth
  on `V ×ˢ U`) and S4.1′, and single-phase forms, assuming `ContDiffOn` on an open set containing the amplitude's
  support; the phase may be arbitrary (even discontinuous) outside it.
- C10: `ContDiff` of the uncurried family gives `FamilyCk`.
- Sanity theorems that apply the statement constants to separating data, for all ten statements, with planted
  negative controls (`OscInt/Front/FamilySanity.lean`, `FamilySanity2.lean`,
  `docs/replay/2026-11-08-API3-sanity-plants.txt`).

### Tooling and CI
- `tools/check_release_pin.sh` check 4: the pinned release commit must be contained in HEAD (CI `release-pin` checks
  out full history); check 5: a raw commit pin must be a commit contained in HEAD; the self-test runs the real ancestry
  predicate on a git fixture (adversarial review m1, m2).
- Consumer examples `examples/consumer/ConsumerLocal.lean` (arccos dispersion family, phase singular outside the
  support) and `ConsumerLocalChecks.lean` (non-vacuity and plant falsity), compiled by `make quick`.
- Numerics: pre-registered protocol for the 2D stationary-phase leading term (`docs/prereg/`), program
  `numerics/src/bin/spleading.rs`.
- External downstream dry run of v0.3.0 by tag: `docs/replay/2026-11-08-external-downstream-dry-run-v0.3.0.txt`.

## v0.3.0 — 2026-11-07 (published by the owner; tag `v0.3.0` → 7098f09)

The owner publishes releases; the steps, the SHA-256 pins and (after the release commit) its full hash are in
`docs/release-notes/v0.3.0.md` and `docs/release-notes/v0.3.0.commit`. A first preparation at 2e8707a was withdrawn
after the adversarial review (`review/2026-11-07-API2-adversarial.md`, M1, M6): v0.3.0 is the session's final commit.

### Statement changes
Against v0.2.0 (`stamps/pins.txt` at tag `v0.2.0` and now): **no existing statement changed**. The eleven statement
constants of v0.2.0 keep their statement files byte for byte and their commitments (`make commit`: every commitment
equals its pinned stamp; this session's records under `docs/replay/2026-11-07-*`).
- Added (front-end batch 1): `AmpBoundOfContDiffStatement` (F1), `D4LimitClosedFormStatement` (F2), file
  `OscInt/Statements/FrontEnd.lean`, stamp `stamps/20261107T012459Z-2d5356432156`.
- Added (front-end batch 2): fourteen statements in `OscInt/Statements/Convert.lean`, stamp
  `stamps/20261107T101640Z-4acb308f54f4`: C1 `DdEqIteratedStatement`, C2 `DddEqIteratedStatement`, C3
  `HessDetEqDetStatement`, C4 `CubicCoeffsEqStatement`, C5 `DiscEqCubicDiscrStatement`, C6
  `DiscNeZeroIffIsolatedStatement`, C7 `FoldOrNondegIffStatement`, C7′ `FoldOrNondegOfHasFDerivStatement`, C8
  `GradLowerIffStatement`, C9 `AmpBoundConvStatement`, FE-S2.1 `NonStationaryFEStatement`, FE-S2.2
  `StationaryPhaseFEStatement`, FE-S3 `FoldFEStatement`, FE-S4.1′ `D4BoundFEStatement`.
- `proved_by` set: S4.4 (`OscInt.d4ConstantClosedForm`), F1, F2, and all fourteen batch-2 statements (`OscInt.API.*`).
- New: `stamps/statements.json` itself (v0.2.0 had none); 27 statements.

### Front-end batch 2 (new; statement-first order restored)
- Conversions from Mathlib's idiom to the frozen encodings: `iteratedFDeriv` ↔ `dd`/`ddd` (C1, C2), `hessDet` ↔
  `Matrix.det` of the Hessian matrix (C3), `cubicCoeffs` ↔ the coefficients of D³φ(0)[κ,κ,κ]/6 (C4), `disc` ↔
  Mathlib's `Cubic.discr` (C5), `disc ≠ 0` ↔ isolated critical point (C6), `FoldOrNondeg` ↔ kernel/rank form of the
  Hessian matrix (C7) and from `HasFDerivAt` data (C7′), `GradLower` ↔ Euclidean and max-norm bounds (C8), `AmpBound` ↔
  `ContDiff` + `HasCompactSupport` (C9).
- Front ends for S2.1, S2.2, S3, S4.1′ with `ContDiff`, `tsupport`, `iteratedFDeriv` bounds and linear terms as
  continuous linear functionals (one phase each). Entry point unchanged: `import OscInt.API` (now exposes them).
- Hypothesis helpers `OscInt/Front/Poly.lean` (P2): derivative data of explicit polynomial phases from `ring`
  identities; `examples/consumer/ConsumerFormula.lean`: FE-S3 and FE-S4.1′ on phases given only by a formula.
- Order: statements stamped (RFC 3161 ×3) and reviewed blind (FAITHFUL ×2) before any Lean proof; post-proof
  FAITHFUL ×2; adversarial review answered (`review/2026-11-07-API2-*`). What is and is not evidenced about the order:
  `docs/statements.md`, clarification of 2026-11-07 (lessons 29).

### Machine-checked as stated
- **S4.4** closed forms of the D4 constant (`OscInt.d4ConstantClosedForm`): ∫₀^∞ cos u · u^{−1/3} du = Γ(2/3)/2, and
  c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) for Disc C < 0, c_C = Γ(1/3)²/(Disc C)^{1/6} for Disc C > 0. With S4.2 this is
  the brief's S4 limit with its closed-form constant. Route `docs/proof-S44.md` (real-variable: Fubini and dominated
  convergence for the cosine moment, the chart u = tan θ, GL₂ covariance of the angular integral, reduction to two
  normal forms, Beta integrals, Legendre duplication and Euler reflection); the hand-off's Abel/complex-rate route
  was replaced because `Complex.integral_cpow_mul_exp_neg_mul_Ioi` takes a real rate (lessons 19).
- `OscInt.d4Constant_example`: the closed form on x³ + 2x²y + 3xy² + 5y³ (disc −367).
- Front-end batch 1 (`OscInt/API.lean`, the new entry point): F1 `OscInt.API.ampBoundOfContDiff` (a Cⁿ amplitude with
  compact support satisfies `AmpBound`) and F2 `OscInt.API.d4LimitClosedForm` (the D4 limit with its closed-form
  constant for one C² amplitude, both umbilics); bridges drafted before the statement review, disclosed. Non-vacuity
  and bite: `OscInt/Front/Sanity.lean`.

### Depending on OscInt (new)
- `stamps/statements.json`: every pinned statement with label, summary, proving theorem, statement file and SHA-256,
  commitment, stamp and stamped commit; generated (`make statements`) and checked in CI (`statements-check`).
- `tools/oscint_check.py`: a downstream CI checks the toolchain and Mathlib, the statement file hashes, that each
  statement constant comes from its frozen file, syntactic statement types, axioms, a kernel replay of every OscInt
  module and recomputed commitments; it detects drift, not tampering (README); negative controls, one per check, in
  `tools/test_oscint_check.sh` (the first version, found breakable by the adversarial review, is not released).
- `examples/consumer/`: a tested downstream Lake project; README section "Depending on OscInt".
- `docs/policy.md`: semantic versions from v0.3.0, the stable surface, deprecation, and the Mathlib re-freeze rule.

### Developer experience
- `make quick` (fast loop and pull-request job), `make verify-all ONLY="…"` (partial runs, labelled as such),
  a preflight in `verify-all` for missing system tools and shallow clones (lessons 21); CI split into `quick`,
  `verify` (every push, weekly), `consumer`; `CONTRIBUTING.md`.
- Build noise: `allowNonModules = true` (0 warnings), the Lean step runs once per `verify-all` (`build/lean.ok`),
  `ite_false` for the deprecated `if_false`, the Rust toolchain installed explicitly in CI.
- `tools/check_release_pin.sh` and CI job `release-pin`: CI fails while README, `docs/policy.md` or the consumer
  examples pin a release tag that does not exist, that does not point to the commit recorded in
  `docs/release-notes/<tag>.commit`, or whose notes do not give the SHA-256 of `stamps/statements.json` and
  `tools/oscint_check.py` at that commit (25 self-test cases; hardened after the adversarial review).
- `tools/check_entry_point.sh` (in `make quick`): `import OscInt.API` exposes every statement and proving theorem of
  `stamps/statements.json`.
- `examples/consumer-release/` and CI job `consumer-release`: a downstream project requiring OscInt from GitHub by its
  release tag, built and checked against the pinned SHA-256 (runs once the tag exists).

### Fixed
- Downstream projects that import only `OscInt.API` could not run `tools/oscint_check.py` (it needs every OscInt and
  Blueprint module built): README, the checker's docstring and error message, and CI `consumer-release` now run
  `lake build OscInt Blueprint` first (found by an external dry run, `docs/replay/2026-11-07-external-downstream-dry-run.txt`).
- `lakefile.toml` said version 0.1.0 (then 0.2.0); it, `CITATION.cff` and `.zenodo.json` now say 0.3.0.
- README told users to pin `v0.3.0` before that tag existed; this is now detected (`release-pin`), and README says
  the release is pending.
- `docs/policy.md` showed the pin in `lakefile.lean` syntax next to README's `lakefile.toml`; both use TOML now.
- `docs/ROADMAP.md` and `docs/HANDOFF.md` listed "put `GammaFree.lean` into the next stamp" as open; it already is
  (manifest of `stamps/20261107T012459Z-2d5356432156`, SHA-256 `5dc19eb4…`, the file's current hash).

### Documentation
- `docs/ROADMAP.md`: downstream feedback folded in (explicit constants, local smoothness, asymptotic expansions,
  parametric uniformity, stable dependency with a machine-readable statement list, periodic and lattice settings,
  Keel–Tao).

## v0.2.0 — 2026-11-06

DOI [10.5281/zenodo.24021329](https://doi.org/10.5281/zenodo.24021329) (all versions:
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328)). First release. Machine-checked as stated (`docs/STATUS.md`; record `docs/replay/2026-11-06-S4b-final-verify-all.txt`):

- S1 one-dimensional van der Corput lemma with amplitude, constants 3, 8, 18 (`OscInt.vanDerCorput_one/two/three`;
  proof ported from roos-j/lean-oscillatory, Mathlib PR #39406).
- S2.1 non-stationary phase, O(m^{-N}), uniform over compact families and all linear terms (`OscInt.nonStationary`).
- S2.2 nondegenerate stationary phase, O(m^{-1}), uniform in the linear term (`OscInt.stationaryPhase`).
- S3 uniform fold estimate, O(m^{-5/6}) (`OscInt.fold`).
- S4.1 uniform D4⁺ estimate t^{-2/3}, uniform in the linear term (`OscInt.d4Bound`); S4.1′ the same for both umbilics,
  `disc ≠ 0` (`OscInt.d4BoundNe`).
- S4.2 D4 limit t^{2/3}∫e^{itφ}A → c_C A(0), c_C defined without the Gamma function (`OscInt.d4Limit`).
- S4.3 c_C > 0 by an alternating-series argument, proof Gamma/Beta/Mellin-free by name (`OscInt.d4ConstantPos`).

Not yet proved: S4.4, the closed forms of c_C (statement frozen and reviewed). The brief's limit with the constant
Γ(1/3)²/(√3|Disc|^{1/6}) is S4.2 together with S4.4.

Trust chain: statements stamped (RFC 3161 ×3, OpenTimestamps pending) and blind-reviewed before proofs; axiom audit
(`propext`, `Classical.choice`, `Quot.sound` only); `lake comparator` against the frozen challenges; replay by
`leanchecker` per module and six export kernels (Lean, Lean paranoid, lean4lean, nanoda, con-leche, con-ron), with
nanoda also built from source in CI. Reviews are by AI referees (calibrated: 8/8 planted errors caught); no human
review yet. Toolchain: Lean v4.35.0, Mathlib `56a0058`.
