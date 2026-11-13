# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (49 entries); every rule in it is binding.

## Start here (end of session 10, 2026-11-13)

**State.** 63 pinned statements; 59 are machine-checked as stated (`docs/STATUS.md`). The four of batch LS (the free
lattice Schrödinger group on ℓ²(ℤ^d)) are stated, frozen, reviewed and routed, and not proved. Session 10 completed
batches LE2, HC and A3 end to end.

**Release v0.5.0 is prepared on this branch, not published.**
- Prepared: versions set in `lakefile.toml`, `CITATION.cff`, `codemeta.json` and `.zenodo.json`; the CHANGELOG
  section; notes with pins in `docs/release-notes/v0.5.0.md`. `tools/release_preflight.sh 0.5.0` passes.
- It ships LS with `proved_by` null; the owner chose this on 2026-11-13, rather than waiting for LS.
- Owner steps: merge the release pull request to `main`, run `release-candidate` with version `0.5.0`, tag and publish
  (the commands are in the notes, "Publishing"), then merge the `post-release` pins pull request and record the
  Zenodo DOI.
- If the release is published after 2026-11-13, change the three dates first.

**Next, in order:**
1. **Batch LS proofs.**
   - Route: `docs/proof-LS.md`. Read "Revision after the route referee" first: P-conv must use the exponential series
     over ℂ, P-exp goes through `restrictScalars`, and the uniqueness part is P-unique.
   - The nine parts are interfaces in `Blueprint/LatticeGroup.lean`. The compiled assembly is
     `OscInt/Front/LatticeGroupAssembly.lean`.
   - No part proof exists in the tree. Drafts and probes from session 10 lived in the session scratchpad, which does
     not survive the container.
   - Then the final file (LatticeGroupFinal, named in the route), an **isolated** `make verify-all`, the post-proof
     reviews (A, B, adversarial), the records, and a minor release (v0.6.0) that sets `proved_by`.
2. CENSUS held-out pool (ROADMAP I1), then its implementations.
3. LeanCert experiment (I2).
4. I3: global assembly with A3 points; then I3a and I3b.
5. Optional, a separate change: the six style warnings of `OscInt/Cusp/Implicit4.lean` (lines 131, 227, 229). A proof
   change, so it needs a build, an axiom audit and a replay record.

**Candidates waiting for the owner (ROADMAP "Candidates"):**
- the discrete Klein–Gordon kernel bound (R2);
- the two-port memory consumer and the imaging block consumer (the application-chains dossier);
- QWZ at the critical mass.

**Process, learned the hard way this session:**
- **Lessons 49.** No Lean, `lake`, `make` or Lean-running referee while `make verify-all` runs. Launch referees
  before it starts or after it ends.
- **Run the replay detached.** A full replay takes about 2 h 50 min. Start it with `setsid nohup` and a process
  watcher (as in the A3 record's header). A harness background task is killed after 2 hours.
- **Count from the session record, not from memory.** The "six probes" error (lessons 49) came from counting from
  memory.

## Session 11 (2026-11-13): external R3 packet answered; nothing frozen, nothing proved
- **R3 packet** (three archives and a decision brief, same external reviewer). It triages six targets and selects T5,
  an evidence profile, and T8, a Fourier error package. Answers: `review/2026-11-13-external-R3-answers.md`.
  - **Mathematics:** TRUE as hand mathematics and classical. No novelty; the packet claims none.
  - **Already here:** T8's signed −π-grid alias identity and its parity trap were recorded on 2026-11-10 (dossier C6).
  - **T5:** no new guarantee for OscInt, and three MAJOR design defects.
  - **The draft Lean:** does not parse as shipped; it elaborates after three repairs.
  - **Lead's checks:** 26/26 (`numerics/results-r3-packet-checks-2026-11-13.txt`).
  - **Referees:** four fresh-context referees found no BLOCKER.
- **Fixed in this repository:** `docs/calibration.md` rounded Clopper–Pearson bounds in the unsafe direction (table
  corrected, dated note); the `review/README.md` index was brought up to date. ROADMAP I7 gains a pointer; its gates are
  unchanged.
- **Disclosed deviation (lessons 16):** the lead's check script was untracked in the tree for about two minutes while
  referees ran. All four referees said they did not see it, with the evidence in the answers file.
- **Container:** the pinned toolchain was installed from `toolchain.sha256` and the Mathlib cache fetched in about
  four minutes.
- **Remote state at session start differs from "Start here" (lessons 31).** v0.5.0 is published: GitHub release
  2026-11-13T19:02:37Z, tag on 2cf118d, `release-candidate` and `post-release` green. The pins pull request
  ([thomas-falk-research/lean-oscillatory#14](https://github.com/thomas-falk-research/lean-oscillatory/pull/14),
  branch `release/v0.5.0-pins`) has red `ci`, for two reasons. Neither is fixed yet; both await the owner.
  - `quick` fails `docs-check pins`: `docs/downstream.md:12` still pins v0.4.0. The pins step of
    `.github/workflows/post-release.yml` (lines 115–116) runs `sed` over three named files. `tools/check_docs.py` checks
    every `rev = "vX.Y.Z"` in `README.md` and `docs/*.md`, so every release's pins pull request will fail until the
    two lists agree.
  - `consumer` is cancelled at its 60-minute limit (`.github/workflows/ci.yml:75`) on slow runners, also on `main` run
    158. Every finished step passed. The green PR #13 run took 48 minutes (checker 19, controls 24); the failing runs
    spent 26–28 minutes in the checker alone.
- **Next steps:** unchanged ("Start here" above), plus the two CI fixes above once the owner decides.

## Session 10, continued (2026-11-12/13): batch A3 machine-checked as stated; batch LS stated, reviewed and routed; external packets

**State at this commit.**
- **Batch A3 (S1.k, S5.1, S5.1′) is proved in Lean.**
  - It came from an external packet drafted with an OpenAI model and was integrated at 93a8a8d with five elaboration
    fixes (`review/2026-11-12-A3-packet-answers.md`).
  - Post-proof reviews: FAITHFUL ×3, parts SOUND. The adversarial review's three MAJORs are answered
    (`review/2026-11-12-A3-post-proof-answers.md`).
  - **Machine-checked as stated:** the isolated replay of 1f7d041
    (`docs/replay/2026-11-13-session10-A3-verify-all.txt`) accepted comparator-A3 with six kernels; verify-all is
    INCOMPLETE only because comparator-LS has no solution yet.
  - The replay takes about 2 h 50 min. Run it detached (`setsid nohup`): a first attempt, run as a harness background
    task, was killed by the two-hour limit on background tasks.
- **Batch LS (the free lattice Schrödinger group on ℤ^d: LS-E, LS-K, LS-D, LS-D′).**
  - Frozen (stamp `20261112T215742Z-d18e0780abdb`) and blind-reviewed (answers
    `review/2026-11-12-LS-pre-proof-answers.md`).
  - Route `docs/proof-LS.md`: nine parts in `Blueprint/LatticeGroup.lean`, compiled assembly
    `OscInt/Front/LatticeGroupAssembly.lean`, refereed with no BLOCKER.
  - Read the section "Revision after the route referee" before proving: P-conv must use the exponential series over ℂ.
  - Next: prove the nine parts (drafts and probes are not in the tree), then the final file (LatticeGroupFinal, named in the route), a
    replay and the post-proof reviews.
- **External packets answered, all in the lead's words (lessons 46):**
  - R2 Klein–Gordon kernel (`review/2026-11-12-R2-KG-answers.md`);
  - lattice NLS (`review/2026-11-12-DNLS-packet-answers.md`);
  - the A3 Lean packet (above);
  - the application-chains dossier (`review/2026-11-13-application-chains-answers.md`). It is TRUE as hand mathematics
    and classical or known in part, with two consumer candidates in the ROADMAP. It found four errors in
    `docs/applications.md` (fixed) and the lessons-28 problem below.
- **Replay isolation.** The replay of e814510 was not isolated: the LS route referee ran Lean during it (lessons 49).
  A container restart then cut it off. It is kept, labelled, at `docs/replay/2026-11-12-session10-e814510-partial.txt`;
  it is not an acceptance record.
- **Consumer** `examples/consumer/ConsumerWhistler.lean` (S1.3 at the whistler inflection; upper bound only).
- **Lessons:** 49.

## Session 10, continued (2026-11-12): batch HC proved end to end; plasma consumers; DNLS scoped
- **Owner request 2026-11-12:** bets 1 and 3, then scope bet 2.
- **Batch HC (bet 1): TdF and TdE′, machine-checked as stated.**
  - TdF: the d-dimensional hypercubic kernel K_d(t, x) = ∫_{[−π,π]^d} e^{i(t Σ cos k_j + x·k)} dk factorises into 1D
    kernels. TdE′: |K_d(t, x)| ≤ (8(1 + √7)/3)^d t^{−d/3} for every d, t > 0 and x ∈ ℤ^d.
  - Records:
    - statements: `OscInt/Statements/Hypercubic.lean`, stamp `20261112T120616Z-c56beb57ff8c`;
    - pre-proof reviews: FAITHFUL and TRUE ×2, review stamp `20261112T123958Z-8e4f8c5cbcaf`;
    - route: `docs/proof-HC.md`, refereed (no BLOCKER or MAJOR);
    - part and assembly: `OscInt/Front/Hypercubic{Fubini,Assembly,Final}.lean` (Mathlib's finite-product Fubini);
    - replay: `docs/replay/2026-11-12-session10-HC-verify-all.txt` on 5a5f714. Every step passes; the comparator is INCOMPLETE only because comparator-A3 has no
      solution yet;
    - post-proof reviews: FAITHFUL ×2. The adversarial review's two MAJORs (the DNLS scoping condition; evidence for the
      referee windows) are answered in `review/2026-11-12-HC-post-proof-answers.md`.
  - Prior art: the rate and the factorisation are anticipated (Stefanov–Kevrekidis 2005); the constant is new only
    through T0E′ (`docs/prior_art.md`).
- **Plasma consumers (bet 3):** `examples/consumer/ConsumerColdPlasma.lean` (cold-plasma transverse waves, τ^{−1} via
  GD-N) and `examples/consumer/ConsumerPhaseMixing.lean` (phase mixing of free streaming, via FE-S2.1). Linear,
  idealised models; the physics reductions are paper steps.
- **DNLS scoping (bet 2):** `docs/design/dnls-scoping.md`, corrected after the adversarial review: decay of small
  solutions whenever (d/3)(2p − 1) > 1, in every dimension. Next step is a route document for ℓ² well-posedness and the
  kernel-to-group identification, with every Mathlib name checked (the go/no-go).
- **External R2 packet (discrete Klein–Gordon kernel):** TRUE by the lead's checks and a fresh-context referee, not
  machine-checked; a ROADMAP candidate awaiting the owner (`review/2026-11-12-R2-KG-answers.md`). If promoted, the LE2
  scalar layer generalises mechanically; the new Lean work is the KG level-set geometry, the pieces and m → 0.
- **Lessons:** 48 (provenance facts are captured when they happen).
- **No CI ran:** the branch has no pull request; the local replays are the evidence.

## Session 10 (2026-11-10/11): batch LE2 proved end to end; external follow-up answered
- **External follow-up (2026-11-10), four packets from the same reviewer**, answered in
  `review/2026-11-10-external-followup-answers.md`, the lead's words only (lessons 46).
  - Packets: a cube-root cosine bound (Result 1); QWZ at the critical mass m = 2 (Result 2 and an audit with a further
    t^{−4/3} theorem); a photonic application study; a plasma application study.
  - All four are correct.
  - The QWZ results and the plasma study were checked by fresh-context checkers with their own code. The QWZ results
    stay candidate evidence (owner decision); see ROADMAP "Candidates".
  - Lead's checks: `numerics/review/followup_checks.py` (43/43 exact).
- **Batch LE2 (owner decision 2026-11-10): T0E′ and T6E′, machine-checked as stated.**
  - Statements: `|I(t, ξ)| ≤ 8(1 + √7)/3 · t^{−1/3}` for t > 0 and real ξ, and the 2D form with the constant squared.
    They are useful from t ≈ 3.70, against 518 and 1321 for T0E and T6E.
  - Records:
    - statements: `OscInt/Statements/LatticeCubeRoot.lean`, stamp `20261110T234417Z-0532b1cf8880`;
    - pre-proof reviews: FAITHFUL and TRUE ×2, review stamp `20261111T005634Z-bf8af89bc235`;
    - route: `docs/proof-LE2.md`. The route referee's one MAJOR (an unjustified monotonicity step) is fixed by a split
      at v = 1/8;
    - parts: `OscInt/Front/LatticeCubeRoot*.lean`, by proof agents after the route review;
    - replay: `docs/replay/2026-11-11-session10-LE2-verify-all.txt` on 68aec60. Every step passes; the comparator is
      INCOMPLETE only because comparator-A3 has no solution yet;
    - post-proof reviews: FAITHFUL ×2. The adversarial review's three MAJORs were documentation, answered in
      `review/2026-11-11-LE2-post-proof-answers.md`.
  - The constant is within a factor 1.9706 of the best: rigorous by hand. The Lean bite proves the best constant
    exceeds C*/2.
  - AI-use disclosure: `docs/prior_art.md`.
- **Consumer** `examples/consumer/ConsumerPhotonLattice.lean`: single-photon probabilities on a cosine-band lattice,
  nontrivial from 2κt ≥ 519 with T0E and from 2κt ≥ 4 with T0E′.
- **Lessons:** 47 (sanity data in the non-trivial regime of an explicit bound). The adversarial review also found two
  commits made while referees read the tree (lessons 16): disclosed, not repeated.
- **No CI ran:** the branch has no pull request. The local replay is the evidence. The owner opens a pull request when
  wanted.
- **Owner items open (new):** whether the packet SHA-256 prefixes in the follow-up answers stay (they identify unpublished
  packets). Earlier owner items are unchanged.
- **Next, in order:**
  1. As before: `docs/proof-A3.md` parts and replay (A3 route reviewed at b719ba4).
  2. CENSUS held-out pool.
  3. LeanCert (I2).
  4. I3a, I3b.
  5. Optional: a cold-plasma GD-N consumer (`review/2026-11-10-external-followup-answers.md`; mind the max-norm hazard).

## Session 9 (2026-11-10): external reviews checked; a hand proof of S5.1′; nothing proved in Lean, nothing frozen
- **Privacy rule (owner, 2026-11-10; lessons 46).** No chat transcripts, prompts (the owner's, reviewers' or
  referees'), or verbatim AI-conversation text in the repository or its history. External reviews are recorded only as
  the lead's answers, in the lead's own words, with independent checks.
- **External reviews (2026-11-10), several rounds from one external reviewer.** Answers: `review/2026-11-10-external-dossier-answers.md`,
  `…-external-audit-answers.md`, `…-external-results-answers.md`. Checks, all passing: `numerics/review/dossier_checks.py`
  (27/27), `audit_checks.py` (4/4), `cusp_proof_checks.py` (7/7).
- **A complete hand proof of frozen S5.1′ (hence S5.1)**, with C² amplitudes, uniform in the linear term. It was
  checked by the lead and by a fresh-context referee (no FATAL or MAJOR finding), and is re-derived in the lead's words
  in `review/2026-11-10-external-results-answers.md`.
  - Route: the exact dephased transverse integral (already proved, L6 core, j = 2, 3) plus a fourth-order van der
    Corput estimate derived from S1.3. **I3a is not needed for S5.1′.**
  - Next for A3: `docs/proof-A3.md` along that route, with parts P-V4, P-core4, P-jet4 (a C⁴ implicit curve on a
    neighbourhood), P-far and assembly; then the route referee. Nothing is proved until replayed.
- **Owner decisions (2026-11-10):**
  - ROADMAP I3a and I3b: the dimension-generic track. I3b states its hypothesis intrinsically (corank 2, nondegenerate
    cubic on the Hessian's kernel), with a counterexample phase as a bite datum. I3a must fix its input derivative
    budget, with a C²-only counterexample as a bite datum.
  - CENSUS (draft): control K-QWZm (the QWZ family at four masses), and a sealed held-out set H selected by the lead
    with three mitigations (sealed pool, drand-seeded draw, owner custody).
- **CENSUS spec-fidelity referee (2026-11-10):** one BLOCKER (B's NS-ADJACENT label), nine MAJOR, all repaired before
  freezing; answers `review/2026-11-10-CENSUS-spec-answers.md`, changes in spec §8. Main changes: the normalised cusp
  invariant `ĝ4 = g4/|v|⁴`; a new type X (zero cubic); one-dimensional components with special points; the
  machine-readable corpus `numerics/census/corpus.json`; B's label order and budget-exhaustion rule; the held-out
  inclusion rule and draw encoding. Exact checks 39/39 (`numerics/results-census-spec-2026-11-10.txt`). A new exact
  fact: QWZ m = 1 (M07) has lines of A≥4 points, so it is not GD-covered (check M07-LINES). A second fresh referee
  checked the repairs (no BLOCKER; four MAJOR on the wiring around them, repaired: special points cross-checked, B's
  undecidable fields `null`, components counted under F-NI alone, a mechanical held-out inclusion rule). The spec is
  **FROZEN** (commit in `docs/prereg/LEDGER.md`); the registration is still DRAFT.
  - ROADMAP I7: the Fourier-grid certificate, outside the core, with a stop rule.
  - ROADMAP "Candidates (not commitments)": four promotion gates.
  - ROADMAP "Standing: repository hygiene": first pass done.
- **Disclosure fixes:** `docs/prior_art.md` marks S1.k ANTICIPATED (Roos–Praveen `…_order_ge_two`, Mathlib PR #39406,
  open); ROADMAP I3's Ikromov–Müller wording is weakened.
- **Owner decisions later the same day:**
  - A3 formalisation comes before I3a (ROADMAP I3).
  - The S5.1′ route carries an AI-use disclosure naming the tool (OpenAI ChatGPT 6), in `docs/prior_art.md`. This
    follows publishing practice (COPE, ICMJE): disclosure, not authorship or credit.
  - The lead selects the CENSUS held-out set, with mitigations (spec §3): a sealed pool of at least 12, a draw seeded
    by drand, and owner custody of the salt, pool and H. To do before any implementation is commissioned.
- **Owner items open:**
  - the earlier records of prompts and AI reviews on `main` (`review/prompts/`, verbatim referee reports, query logs),
    which the privacy rule now covers. Removing them from `main`'s history would invalidate every stamp. Owner to decide.
- `main` CI on 58a86d0: `ci` and `verify` both success.
- Next, in order:
  1. `docs/proof-A3.md` along the S5.1′ route, the route referee, then the parts and the replay.
  2. CENSUS: `numerics/census/validate_pool.py`, then the held-out pool (spec §3 rule) sealed with the owner, then
     implementations A and B and their development runs, then the pre-registration referee and registration.
  3. The LeanCert experiment (I2).
  4. I3a, then I3b.

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

## What existed at the end of session 7 (2026-11-08/09; historical)
Since then batch A3 has added three pinned statements that are stated and reviewed but **not proved** (S1.k, S5.1,
S5.1′): 55 pinned, 52 proved (`docs/STATUS.md`). Branch names, commits and counts below are as of session 7.
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
2. **Releases.** v0.4.0 is published. v0.5.0 is prepared in this branch (versions, CHANGELOG section, notes with
   pins; `tools/release_preflight.sh 0.5.0` passes). After the merge: Actions → `release-candidate` on `main`, then the
   commands it prints (`docs/release-notes/v0.5.0.md`, "Publishing").
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
- `make quick` before every push (lessons 35, 37). The final `make verify-all` takes about 2 h 50 min on a 4-core machine
  (2026-11-13), longer than the session tool's 2-hour background limit: start it detached (`nohup setsid …`) and wait on its log;
  log `date -u` at start and end (adversarial n9).
- Do not write proofs while a referee reads the tree (lessons 16, 42).
- Follow-ups recorded, not done: pin paths not validated in `stamp` (n5); actionlint and shellcheck not hash-pinned
  (n7); `latticeKernel1` is not covered by planted controls (n3).
