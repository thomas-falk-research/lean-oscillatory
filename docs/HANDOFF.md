<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Hand-off

For a reader who saw nothing. Read "Rules in force" at the top of `docs/lessons.md` first; it distils the numbered entries
below it, and every rule is binding.

## Resume here (session 13, 2026-11-16; kept current at every checkpoint)

- **Two branches (owner decision 2026-11-19, `docs/decisions/2026-11-19-next-batch-spl.md`).** The release
  candidate v0.7.0 is the branch `claude/dreamy-ptolemy-7hs5wb` at 66a88bc (pull request 19) and is not to be
  changed. This branch, `claude/batch-sp-leading-term`, starts from 66a88bc and carries the next batch, **SPL: the
  one-variable stationary-phase leading term with an explicit remainder**; no pull request; rebase onto `main`
  after v0.7.0 is published. State of the batch: the session log's last rows. Order of work: prior-art gate,
  registered numerics, proof plan with a plan referee, statements and freeze, blind review, proofs
  (`CONTRIBUTING.md`); no Lean proof text before the answers to the blind review are stamped.
- **Batch SPL, state on 2026-11-19 (nothing is running):** done: opening note
  (`docs/design/batch-SPL-opening.md`), prior-art gate (identity classical in substance, Erdélyi; constant not
  found; Olver 1974 unread), registered numeric test PASS 12 of 12 (`docs/prereg/LEDGER.md`), proof on paper in
  its second version (`docs/proof-SPL.md`), plan referee answered
  (`review/2026-11-19-SPL-plan-referee-answers.md`). **Exact next step:** write "Batch SPL" in
  `docs/statements.md` and a new statement file StationaryLeading.lean under OscInt/Statements/ (statements SPL-I, SPL-S, SPL-K with 7/8,
  SPL-A; class: C³ with `g, g′, g″, g‴` integrable; SPL-N is not in this freeze) with a sanity layer and recorded
  plants, challenge file and comparator; `make quick`; freeze, `make stamp`, pins; then two blind referees.
  **Done by 2026-11-20 00:10Z:** statement file `OscInt/Statements/StationaryLeading.lean` (draft text unchanged
  since a7fa3dc), sanity layer (96 theorems), 42 planted controls re-run by the lead, challenge file and
  `comparator-SPL.json`, prose in `docs/statements.md`. **Frozen 2026-11-20:** stamp `stamps/20261120T002727Z-5491b10bc8ae` on 5491b10
  (three RFC 3161 tokens, 00:27:34Z), pinned; registry has 90 statements, 4 not proved. **Blind review done 2026-11-20:** four verdicts
  FAITHFUL, no counterexample, no BLOCKER, no MAJOR (`review/2026-11-20-SPL-preproof-answers.md`); the answers are
  stamped (`stamps/20261120T011816Z-3e07630da3a5`, 01:18:24Z). **Exact next step: the Lean proofs**, by the route
  of `docs/proof-SPL.md` (second version, with its addendum): Lemma 1 (Fresnel primitive: Cauchy bound, the limit
  L exists), Lemma 2 (primitives of the kernel, bounds), Proposition 3 (three integrations by parts on a
  half-line; reflection), Lemma 4 (L from `integral_gaussian_complex`), SPL-I, SPL-S (first-moment lemma), SPL-K
  (through `OscInt.API.secondDerivSharp` and `vdc2ProfileBound`), SPL-A (four bumps, triple primitive). Final
  theorems under the challenge names of `comparator-SPL.json`; then `make quick`, post-proof reviews, the full
  replay. Nine external reports and their checks are answered in
  `review/2026-11-19-SPL-external-sessions-answers.md`; section 11 there lists the candidates for later freezes. Release v0.7.0: pull request 19
  was merged by the owner on 2026-11-20 00:06Z (merge commit 06f8e47 on `main`); the owner dispatches
  `release-candidate` and publishes; after that, merge `main` into this branch (never rebase: a stamp names
  5491b10) and run `make anchors` for the three stamps of 2026-11-19/20. The owner may bring reports of external sessions of another model family
  (blind derivation, literature, general phase); answer them under `review/` like the earlier external reviews.
- **Work item (2026-11-19): release candidate v0.7.0.** All 86 pinned statements are proved; the 21 of session 13
  (batches PA, KL, FR, VC2, HW) were machine-checked as stated by the isolated replay of fafd5b8
  (`docs/replay/2026-11-19-session13-verify-all.txt`). Since then, on the owner's instruction, the tree was made
  ready for a release: answers to five external reviews and their corrections, a corrected replay driver, the
  author's name and licence inside every file that can carry them (attribution blocks on the 41 frozen Lean files
  and on 199 records), a validated bibliography (`docs/references.bib`), refreshed guides and metadata, community
  files, and the release content of v0.7.0 (versions, `CHANGELOG.md` section, `docs/release-notes/v0.7.0.md`).
- **Last verified state:** 2113b54: `make verify-all` RESULT PASS (2026-11-19, 18:14:41Z to 21:10:51Z, isolated, the
  corrected driver, raw output kept; `docs/replay/2026-11-19-v0.7.0-verify-all.txt`); the same commit passed on a
  clean GitHub runner (`verify.yml` run 44585759180). It is the replay of record for all 86 statements and for
  v0.7.0. Commits after 2113b54 change documents, metadata notes and records only. The release candidate with
  its replay record is stamped: `stamps/20261119T213636Z-1aa26b0f21a7` on 1aa26b0 (three RFC 3161 tokens verified,
  21:36:44Z; OpenTimestamps pending). Nothing is running. A replay launched earlier on 580e34d was stopped unfinished on the
  owner's instruction and proves nothing.
- **Exact next command:** on 2026-11-20 or later, `make anchors OTS_PYTHON=<pinned environment>/bin/python` (two
  stamps are pending: `20261119T124850Z-9ae784e80e32` and `20261119T213636Z-1aa26b0f21a7`), then commit
  `anchors/ots/`. `tools/release_preflight.sh 0.7.0` must print
  "ready" (the date in `CITATION.cff`, `codemeta.json` and the CHANGELOG heading is 2026-11-20; the owner may
  change it). Publishing is the owner's: merge the pull request, dispatch `release-candidate` on `main`, then
  `tools/publish_release.sh` (`CONTRIBUTING.md`); the post-release pull request moves the install pins to v0.7.0.
- **External review (2026-11-19; an AI system of another model family, one batch per conversation, pinned to
  9ae784e; it cannot run Lean): all five reports answered**
  (`review/2026-11-19-{VC2,PA,FR,KL,HW}-external-review-answers.md`). All 21 statements faithful, true, route sound;
  every finding was against records, tools or process. Lessons 64 to 67.
- **Owner decisions of 2026-11-19 (all recorded under `docs/decisions/`):** a one-time waiver of step 5 for six
  batches, marked on 23 rows; the wording "before any Lean proof of it exists"; attribution blocks in frozen files
  and records; release preparation. **For the owner, outside the repository** (the lead gave the exact text in
  the session): GitHub private vulnerability reporting on; a Software Heritage "save code now" request; optional
  listings (Reservoir needs two stars; Mathlib's downstream list; zbMATH Open). Decided by the owner on 2026-11-19:
  no funding and no competing interests (stated in the README and the Zenodo notes); the author's name stays
  "Falk III, Thomas" in the citation metadata.
- **Attribution rule from now on:** a new statement file and a new record are written with their copyright and
  licence lines; the fixed block is only for the files that existed on 2026-11-19 (`CONTRIBUTING.md`, lessons 67).
- **Replay driver:** fixed and tested (`tools/src/bin/replay.rs`); raw output of every step under
  `build/replay/raw/`; the fail-closed rerun of the replay step on 237c5b2 passed
  (`docs/replay/2026-11-19-lean-replay-fail-closed.txt`).
- **Hardware run on IBM Quantum (pre-registration `docs/prereg/2026-11-16-CTQW-chain.md` with Addenda 1 and 2):
  built and reviewed three times, nothing submitted, nothing may be submitted without the owner's word for that
  one instruction.** Files under `experiments/ctqw-chain/hardware/`; the workflow `.github/workflows/ctqw-hardware.yml`
  runs on a push that changes `SUBMIT-TRIGGER` and refuses unless the GitHub environment `ibm-hardware` exists with a
  required reviewer and no administrator bypass, and unless no credential is visible outside that environment.
  Waiting on the owner: create that environment, move the two secrets into it, delete the repository-level
  secrets. Owed by the lead before the first submission: `make stamp` of the commit with the final script and
  Addendum 2. The session's container holds the same credentials in its environment; they are not to be used from
  here.
- **Batch FR (finite ring, open chain; seven statements FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P):** in the tree
  for its freeze: `OscInt/Statements/FiniteRing.lean`, sanity layer `OscInt/Front/FiniteRingSanity.lean` with planted
  controls (`docs/replay/2026-11-16-FR-sanity-plants.txt`), `Challenge/FiniteRing.lean`, `comparator-FR.json`, prose in
  `docs/statements.md`. **Frozen**: stamp `stamps/20261116T205833Z-0748dde3c341` on the statements commit 0748dde, pinned.
  Blind pre-proof reviews A and B: all seven FAITHFUL, no counterexample, no BLOCKER; three MAJOR against the
  sanity layer, answered by `OscInt/Front/FiniteRingSanity2.lean` and a second plant run
  (`review/2026-11-16-FR-pre-proof-answers.md`, `docs/replay/2026-11-16-FR-sanity-plants-second.txt`). The answers are stamped
  (`stamps/20261116T225756Z-5792039264f0`). **Proved in Lean** (2026-11-16/17): `OscInt.API.ringKernelSolves`, `ringUnique`,
  `ringCosetSum`, `ringFiniteSize`, `chainKernelSolves`, `chainUnique`, `chainFiniteSize`
  (`OscInt/Front/FiniteRingFinal.lean`; route, referee, parts: `docs/proof-FR.md`). Post-proof reviews A, B, C answered
  (`review/2026-11-17-FR-post-proof-answers.md`) and stamped (`stamps/20261117T010311Z-a93c4e1e44f7`). Left: the
  isolated replay (with PA and KL).
- **Batch VC2 (sharp second-derivative van der Corput bound; four statements VC2-S, VC2-A, VC2-N, VC2-K):** in the
  tree for its freeze (`OscInt/Statements/SecondDerivSharp.lean`, sanity layer, plants, challenge,
  `comparator-VC2.json`, prose). **Frozen**: stamp `stamps/20261116T222541Z-5b72549117b1`, pinned. Blind pre-proof reviews A and B are in
  (session log, 2026-11-16 23:14 row): FAITHFUL, no counterexample, three MAJOR against the sanity layer; a second
  sanity layer exists in the lead's scratch (if lost: redo from the findings in the log). Answers `review/2026-11-17-VC2-pre-proof-answers.md`,
  stamped `stamps/20261117T010311Z-a93c4e1e44f7`. Route `docs/proof-VC2.md`, blueprint `Blueprint/SecondDerivSharp.lean` (the definition `Vdc2Side` and five
  propositions) and the lead's assembly `OscInt/Front/SecondDerivSharpAssembly.lean` (VC2-S from the turning point
  and the one-sided bound; VC2-K from VC2-S, VC2-N and the amplitude transfer of S1) are in the tree and compile;
  interface checks `numerics/review/vc2_interface_checks.py`. Route referee: sound
  (`review/2026-11-17-VC2-route-answers.md`). **All four statements are proved in Lean**: six parts
  (`OscInt/Front/SecondDerivSharp{Turn,Head,Tail,Side,Profile,Attained}.lean`), final theorems
  `OscInt/Front/SecondDerivSharpFinal.lean`, consumer example `examples/consumer/ConsumerSecondDerivSharp.lean`,
  integration checks `docs/replay/2026-11-17-VC2-integration-checks.txt`. Post-proof reviews answered
  (`review/2026-11-19-VC2-post-proof-answers.md`: FAITHFUL ×4, SOUND ×4, no failing regime; no BLOCKER, no MAJOR;
  findings against the wording of the records, corrected; stamped `stamps/20261119T124850Z-9ae784e80e32`).
  Machine-checked as stated since the replay of fafd5b8. The constant is classical; the theorem is classical
  for f″ ≥ λ by citation only (originals unread); nothing is claimed as new.
- **Batch HW (the Hadamard walk on the line, explicit t^{−1/3} bound; four statements HW-R, HW-K, HW-D, HW-L):** in
  the tree for its freeze (`OscInt/Statements/HadamardWalk.lean`, sanity layer, plants, challenge,
  `comparator-HW.json`, prose with the route). **Frozen**: stamp `stamps/20261116T225756Z-5792039264f0`, pinned; the same stamp is the stamp of the FR
  review answers. Blind reviews A and B are in (FAITHFUL, no counterexample; two MAJOR against the sanity layer; a
  second sanity layer, in the tree). Answers `review/2026-11-17-HW-pre-proof-answers.md`, stamped
  `stamps/20261117T010311Z-a93c4e1e44f7`. Route `docs/proof-HW.md` (route referee: sound; `review/2026-11-17-HW-route-answers.md`), blueprint
  `Blueprint/HadamardWalk.lean`, the lead's assembly and the four parts (`OscInt/Front/HadamardWalk{Assembly,KernelRec,Phase,KernelBound,Linear,Final}.lean`)
  are in the tree: **all four statements are proved in Lean** (integration checks `docs/replay/2026-11-17-HW-integration-checks.txt`;
  consumer example `examples/consumer/ConsumerHadamardWalk.lean`). Post-proof reviews answered
  (`review/2026-11-17-HW-post-proof-answers.md`: FAITHFUL ×4, SOUND ×4, no failing regime; no BLOCKER, no MAJOR;
  findings against the records, corrected; stamped `stamps/20261119T124850Z-9ae784e80e32`). Machine-checked as stated since
  the replay of fafd5b8. A gap the reviews found and nobody closed: no machine-read list says which lemmas a
  proved statement depends on, so a change to a sanity lemma does not mark the rows that use it. For the next
  batch (post-proof review of VC2): planted mutations must also change every definition a statement uses, not only
  the statement texts. Known mathematics with explicit constants, not sharp; a route on paper is in the prose.
- **Also done in session 13, each complete on its own:** `docs/design/unlock-map.md` (the map and the plan);
  the quantum-walk protocol `docs/prereg/2026-11-16-CTQW-chain.md` with `experiments/ctqw-chain/` (registered, not run;
  a hardware run needs the owner's approval); the second checker `rust/oscint-cert/` and the differential test;
  `docs/funding/` (the application package for the EuroHPC cut-off of 1 December 2026, 10:00 CET; the owner must
  settle eligibility and copy the portal's form fields); `docs/contract/certificate-v0.md` with the reference checker
  `python/oscint_cert/` (version 0.2.1, 32 tests pass; revision 3 of the contract; third differential run 0 of 1463); the prior-art disclosure of 2026-11-16 in `docs/prior_art.md`.
- **Disk:** before a full replay `tools/replay_preflight.py check` must pass (it replaced the fixed 15 GB floor).
- **Session log:** `docs/progress/2026-11-16-session13-log.md`.

## Session 12 (2026-11-15; historical, superseded by "Resume here")

**State.** 65 pinned statements; all 65 machine-checked as stated. The last two, batch D4U (S4.2U, S4.2O: the D4
limit uniformly over C²-totally bounded amplitude families and over bounded linear offsets), since the isolated
`make verify-all` of 720363d (RESULT PASS, 2026-11-15 15:00:14–18:04:12Z, comparator-D4U accepted by six kernels;
`docs/replay/2026-11-15-session12-D4U-verify-all.txt`; two cut-off attempts in
`docs/replay/2026-11-15-session12-D4U-partial.txt`). Why: a downstream project (two-dimensional
split-step quantum walks) needs the D4 limit along lattice sites whose offset from the moving D4 point stays bounded.

**Batch D4U, in order** (each step with its record):
1. Statements (`docs/statements.md` batch D4U; `OscInt/Statements/D4Uniform.lean`), sanity layer and plants, frozen at
   33c56db, stamp `stamps/20261115T122915Z-33c56db38f65`.
2. Blind pre-proof reviews (A FAITHFUL, B TRUE; one MAJOR against the sanity layer, answered by a family that is not
   finite-dimensional and a second plant run): `review/2026-11-15-D4U-pre-proof-answers.md`; review stamp
   `stamps/20261115T133952Z-9e9c6245f582`.
3. Route `docs/proof-D4U.md` with the compiled assembly before any part (route referee SOUND), parts P-radius and
   P-linear (lead) and P-mod (proof agent), integrated at 07ff140 (audit 1352 of 1352;
   `docs/replay/2026-11-15-D4U-integration-checks.txt`).
4. Post-proof reviews (A FAITHFUL, B SOUND, adversarial C: two MAJOR against the process records, answered):
   `review/2026-11-15-D4U-post-proof-answers.md`; the packet record `review/2026-11-15-D4U-packet-answers.md`.

**Disclosed limits.** A hand proof and Lean drafts of the same shape came from an external packet (OpenAI model,
version not stated) that the lead read and elaborated in scratch before writing the statements; the claim is "no Lean
proof in the repository before the reviews were answered and stamped", not independence of the proof. One planted
control (C⁰ in place of C² in the net) is NOT DETECTED; dropping uniformity is a true weakening that no sanity layer can
detect.

**Next, in order:**
1. Done: v0.6.0 is published (GitHub release 2026-11-15T22:06:53Z, tag on 12093c3, published with
   `tools/publish_release.sh`; batch D4U is part of it, owner decision 2026-11-15). Its Zenodo version DOI is
   `10.5281/zenodo.24263138` (read from the Zenodo API on 2026-11-15: version 0.6.0, concept DOI
   `10.5281/zenodo.24021328`), recorded in `CITATION.cff` and the README. Its post-release pins pull request
   [thomas-falk-research/lean-oscillatory#17](https://github.com/thomas-falk-research/lean-oscillatory/pull/17) is merged
   (2026-11-16T00:07:32Z, 1a71395).
2. OpenTimestamps for both D4U stamps: done since (upgraded copies in `anchors/ots/`).
3. The machine's disk allowance ran out during the replay (lessons 50-style cut-off): check `df` before a replay and
   keep at least 15 GB free. (Since replaced: `tools/replay_preflight.py check` must pass, lessons rule 7.)

## Session 11 (2026-11-14; historical, superseded by "Resume here")

**State.** 63 pinned statements; all 63 are machine-checked as stated (`docs/STATUS.md`). The last four, batch LS (the
free lattice Schrödinger group on ℓ²(ℤ^d)), were **proved in Lean** on 2026-11-14, **post-proof reviewed** (A FAITHFUL,
B SOUND, adversarial three MAJOR answered, `review/2026-11-14-LS-post-proof-answers.md`) and **replayed** after the
post-review Lean changes (isolated `make verify-all` on 35dc5c0, RESULT PASS, comparator-LS accepted by six kernels,
`docs/replay/2026-11-14-session11-LS-final-verify-all.txt`; the earlier replay of 1bc377b is kept). The proofs
were drafted by an external reviewer with an AI tool (R4 packet) and made to elaborate by the lead's proof agents with
32 mechanical changes (`review/2026-11-14-external-R4-answers.md`).

**Release v0.5.0 is published** (GitHub release 2026-11-13T19:02:37Z, tag on 2cf118d). Its pins pull request
[thomas-falk-research/lean-oscillatory#14](https://github.com/thomas-falk-research/lean-oscillatory/pull/14) is merged
(cb2f648). Its Zenodo version DOI is `10.5281/zenodo.24205167` (read from the Zenodo API on 2026-11-14, recorded
in `CITATION.cff` and the README in the v0.6.0 preparation).

**Release v0.6.0** (published by the owner on 2026-11-15; at the time of this section it was prepared:
`docs/release-notes/v0.6.0.md`; owner decision 2026-11-14: one pull
request with the release content and the pipeline fixes of the session-11 release audit). The owner publishes, with
the steps in those notes; publishing now goes through `tools/publish_release.sh`.

**Next, in order:**
1. **Finish batch LS:**
   1. Done: the isolated `make verify-all` on 1bc377b passed (`docs/replay/2026-11-14-session11-LS-verify-all.txt`).
      Two earlier attempts were cut off by container reclaims and are recorded as partial (lessons 50).
   2. Done: post-proof reviews A, B and adversarial, answered (`review/2026-11-14-LS-post-proof-answers.md`).
   3. Done: the isolated `make verify-all` on 35dc5c0, which contains the post-review Lean changes, passed
      (`docs/replay/2026-11-14-session11-LS-final-verify-all.txt`).
   4. Done: the records (STATUS rows "machine-checked as stated (replay of 35dc5c0)", CHANGELOG, README and the
      pages that track status).
   5. Prepared: the minor release v0.6.0 that sets `proved_by` (owner publishes; steps in
      `docs/release-notes/v0.6.0.md`, "Publishing").
2. CENSUS held-out pool (ROADMAP I1), then its implementations.
3. LeanCert experiment (I2).
4. I3: global assembly with A3 points; then I3a and I3b.
5. Optional, a separate change: the six style warnings of `OscInt/Cusp/Implicit4.lean` (lines 131, 227, 229). A proof
   change, so it needs a build, an axiom audit and a replay record.

**Owner item (new, batch LS post-proof review, `review/2026-11-14-LS-post-proof-answers.md` item 7):** the ten LS
proof files, drafted by the external reviewer, carry the project's copyright and licence header (as the A3 files do);
no licence grant from the external reviewer is recorded.

**Candidates waiting for the owner (ROADMAP "Candidates"):**
- the discrete Klein–Gordon kernel bound (R2);
- the two-port memory consumer and the imaging block consumer (the application-chains dossier);
- QWZ at the critical mass.

**Process, learned the hard way this session:**
- **Lessons 49.** No Lean, `lake`, `make` or Lean-running referee while `make verify-all` runs. Launch referees
  before it starts or after it ends.
- **Run the replay detached and keep the session busy (lessons 50).** A full replay takes about 3 h. Start it with
  `setsid nohup` and a process watcher (as in the A3 record's header). A harness background task is killed after
  2 hours, but an idle cloud session's container is reclaimed within minutes, killing detached processes too: keep a
  background task waiting on the replay log and re-arm it at the two-hour limit.
- **Count from the session record, not from memory.** The "six probes" error (lessons 49) came from counting from
  memory.

## Session 11, continued (2026-11-14): external R4 packet; batch LS proved in Lean and replayed
- **R4 packet** (answers `review/2026-11-14-external-R4-answers.md`): W1 proof drafts for batch LS, and W2 explicit
  constants.
- **W1.**
  - **As shipped, none of the ten Lean files compiled.**
  - **Repair:** two proof agents made them elaborate with 32 mechanical changes. There was no change of route,
    statement or lemma.
  - **The lead verified it in a fresh build:**
    - the frozen types are exact;
    - the axioms are within the allowlist;
    - per-module `leanchecker` passes on all ten modules, with negative controls.
  - **Integrated:**
    - `OscInt/Front/LatticeGroup*.lean`;
    - `OscInt.API.latticeSchrodinger{Exists,Kernel,Dispersive,Decay}`;
    - `proved_by` set;
    - STATUS rows first at "machine-checked by build, axiom audit and per-module leanchecker"; now as in the state
      above.
- **W2.** TRUE as hand mathematics; two referees found no BLOCKER or MAJOR. The useful pieces are:
  - the sharp quadratic bound (Q);
  - the sharper local L6 and L1.

  They are recorded as a ROADMAP candidate. The general one-phase constant (G) is correct but useless at realistic
  parameters.
- **Repository fixes.**
  - `docs/constants.md`: the `λ` binder in the §4.2 Lean sketch did not parse, and the packet copied it; the core
    constant's line citation was wrong.
  - `main` merged into this branch; it was at cb2f648, with PR #14 merged.
- **Checks:**
  - `numerics/results-r4-packet-checks-2026-11-14.txt`, 8/8;
  - the packet's programs, run sandboxed, reproduce their expected outputs.
- **W2 sanity follow-up:** the reviewer's analytic Lean sanity layer for the W2 candidates compiles after 24 mechanical
  repairs. It has eight one-premise sanity theorems, and the lead checked it (answers file, addendum). It stays outside
  the tree, because W2 is not frozen.
- **Compile harness for scratch builds of new modules.** Mirror `.lake/build/lib/lean/OscInt` into a scratch library
  placed FIRST on `LEAN_PATH`, and pass `--root=<scratch src>` (Lean 4.35 requires both).

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
  branch `release/v0.5.0-pins`) has red `ci`, for two reasons. Both workflows are fixed on this branch at 43a13fb
  (owner request); PR #14 itself still needs `docs/downstream.md:12` moved to v0.5.0 on its own branch.
  - `quick` fails `docs-check pins`: `docs/downstream.md:12` still pins v0.4.0. The pins step of
    `.github/workflows/post-release.yml` (lines 115–116) runs `sed` over three named files. `tools/check_docs.py` checks
    every `rev = "vX.Y.Z"` in `README.md` and `docs/*.md`, so every release's pins pull request will fail until the
    two lists agree.
  - `consumer` is cancelled at its 60-minute limit (`.github/workflows/ci.yml:75`) on slow runners, also on `main` run
    158. Every finished step passed. The green PR #13 run took 48 minutes (checker 19, controls 24); the failing runs
    spent 26–28 minutes in the checker alone.
- **Also in this session:** the reviewer's reply to the R3 answers (an addendum in the answers file). It withdraws its
  T5-first and freeze-T8 recommendations. Its application survey (gravitational-wave lensing and others) is assessed
  there; there is no ROADMAP change.
- **Next steps:** unchanged ("Start here" above). Before or with merging this branch, fix PR #14 as above.

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
Since then batch A3 added three pinned statements (S1.k, S5.1, S5.1′), stated and reviewed and at that time not
proved (they were proved on 2026-11-13; today all 86 pinned statements are proved, `docs/STATUS.md`). Branch names, commits and counts below are as of session 7.
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
2. **Releases.** v0.4.0, v0.5.0 and v0.6.0 are published; the next release is the owner's decision. (As written
   at the time: v0.5.0 is prepared in this branch (versions, CHANGELOG section, notes with
   pins; `tools/release_preflight.sh 0.5.0` passes). After the merge: Actions → `release-candidate` on `main`, then the
   commands it prints (`docs/release-notes/v0.5.0.md`, "Publishing").)
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
