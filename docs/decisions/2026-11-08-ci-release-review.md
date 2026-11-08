# CI and release review (session 6, 2026-11-08)

Requested by the owner: "seriously review all of our GH actions workflows … the release needs to be done much better
and independent … parallelize … triggers and checks … best practice … theater/ceremony … the last PR and release
experience was very poor and manual and disjointed."

Evidence used: `.github/workflows/ci.yml` at c62a621 (the only workflow, 222 lines, `actionlint` 1.7.7 clean); the
GitHub Actions run list (60 most recent of 132 runs, via the API, 2026-11-08 ~11:10Z); job logs of runs 42472688274
(c62a621) and 42422972911 (tag v0.3.0); the replay record `docs/replay/2026-11-08-session5-API3-verify-all.txt`
(per-step timings); the v0.3.0 publishing steps in `docs/release-notes/v0.3.0.md`.

## 1. Findings (severity, evidence, consequence)

**F1 — HIGH, reliability and supply chain: the "pinned" Lean install fetches an unpinned binary, with no retry.**
Every job runs `elan-init.sh` (hash-checked) with `--default-toolchain none`; the script then downloads
`releases/latest/download/elan-…tar.gz`, i.e. whatever elan is newest, unverified. On 2026-11-08 GitHub's release
assets returned 502/504 for hours (seen locally and in CI): all five pushes of this session's branch are red at that
step (runs 42466687937 … 42472688274, 0–4 min), before any OscInt check ran. The red status says nothing about the
code. The pinned toolchain archive's SHA-256 is already in `toolchain.sha256`; elan is not needed in CI at all.

**F2 — HIGH, cost: everything is rebuilt from nothing in every job.** `quick`, `verify`, `consumer`,
`consumer-release` each install the toolchain, download the 9 031-file Mathlib cache and build OscInt (~6–9 min each)
with no `actions/cache`. A push costs four Mathlib downloads and four builds.

**F3 — HIGH, cost and noise: the 93-minute replay runs on every push to every branch.** `verify` has `on: push`
(lessons 3) with `cancel-in-progress`; agent sessions push every few minutes, so 21 of 60 runs are *cancelled* and
most branch replays never finish. The replay that is actually evidence is the local `make verify-all` recorded in
`docs/replay/`; the CI replay is the independent second machine, and it only matters on the commit that merges.

**F4 — MEDIUM, cost: push and pull_request both trigger on PR branches.** 3c13edb ran twice (91 and 96 min).

**F5 — HIGH, release process: the release is red by construction and takes three manual, disjointed steps.**
The tag is created by hand in the GitHub UI; the tag push's own CI run fails (`release-pin`: the
`docs/release-notes/<tag>.commit` file can only be committed *after* the tag), as v0.3.0's run 42422972911 did; then
a follow-up commit adds the `.commit` file, another changes README and `examples/consumer-release` to the new tag,
and someone re-runs `release-pin`. Pins in the notes are computed by hand in a session. Nothing builds the release
artifacts in CI, nothing attests them, and the release body is pasted from a file.

**F6 — MEDIUM, maintainability: one workflow with an input flag gating every job.** Five jobs carry
`if: !inputs.mathlib_from_source && …`; the elan block is copied five times; triggers are mixed in one `on:`.

**F7 — MEDIUM, wall time: the replay is serial where it could be parallel.** From the last record: six export
kernels 940 s serial (lean4lean alone 521 s), 78 per-module `leanchecker` runs × ~5 s ≈ 6.5 min, commitments ≈ 9 min
(two producers), 11 comparator configurations (time not recorded; by subtraction the largest part,
CONJECTURED ≈ 40–50 min). These are independent once the build exists.

**F8 — LOW, ceremony: checks that run where they cannot fail usefully.** `consumer-release` rebuilds the *released*
tag's Mathlib and OscInt on every pull request (up to 120 min), although a PR cannot change a published release; it
belongs to the release workflow and a weekly schedule. `release-pin` on tag pushes is guaranteed red (F5).

**F9 — LOW, gaps.** No required status checks (branch protection is an owner item, ROADMAP §6), no Dependabot for
the SHA-pinned actions, no scheduled build against the next Mathlib (ROADMAP P7), no per-step timing in CI output.

What is already good and stays: `permissions: contents: read` at the top; every action pinned by commit SHA;
`fetch-depth: 0` where history is read; checker verdicts read from success lines, not exit codes (lessons 2); the
nanoda-from-source step; separate jobs so one failure does not mask another (lessons 9).

## 2. Options

**A. Patch the current workflow** (pin the toolchain archive, add caches, drop `push` on PR branches).
Fixes F1, F2, F4 in an hour; leaves F3, F5–F8. The release stays manual.

**B. Restructure into purpose-specific workflows, with a dispatch-only release workflow** (recommended; as amended
by the owner's decisions in §4: CI prepares and checks, the owner tags and publishes).
- `.github/actions/setup-lean` (composite): download the pinned `lean-<ver>-linux.tar.zst` with retries, verify it
  against `toolchain.sha256`, cache it by hash; restore the Mathlib packages cache keyed on `lake-manifest.json`.
  No elan. (F1, F2, F6.)
- `ci.yml` — fast feedback: `pull_request`, `push` to `main`, `merge_group`. Jobs in parallel: `quick` (`make
  quick`, with an incremental build cache for `.lake/build`: Lake re-checks every trace, so a restored cache only
  saves time), `tools` (Rust unit tests, `check_release_pin.sh --self-test`, `test_gen_api.sh`, `actionlint`),
  `consumer` (downstream project + checker controls). Concurrency cancels superseded PR runs. (F3, F4.)
- `verify.yml` — evidence: `pull_request` to `main` when the PR is not a draft (and on `ready_for_review`), `push` to
  `main`, weekly, dispatch, and `workflow_call` (for the release). A clean `build` job (no build cache: evidence is
  built from sources) uploads the build tree; parallel jobs then run the replay pieces: `audit` (lean + statement
  types), `kernels` (matrix over the export checkers), `leanchecker` (per-module, sharded), `commitments`,
  `comparator` (matrix over `comparator-*.json`), `stamps` (verify-toolchain, stamp-verify, statements-check), and a
  final `verdict` job that requires every piece and prints one summary (the same PASS/FAIL lines as `verify-all`).
  `make verify-all` stays the single local command and the recorded evidence. (F3, F7.)
- `release.yml` — `workflow_dispatch` with input `version`, environment `release` (the owner can require approval):
  preflight (ref is `main`, `lakefile.toml`/`CITATION.cff`/`.zenodo.json` carry the version, CHANGELOG has the
  section, notes file exists); `verify` via `workflow_call` on that exact commit; assets (`stamps/statements.json`,
  `tools/oscint_check.py`, `SHA256SUMS`, notes with the pins inserted by the job, not by hand); build provenance
  attestation (`actions/attest-build-provenance`, Sigstore); create the tag and the GitHub release (the only job with
  `contents: write`); then `consumer-release` against the new tag; then a bot pull request that writes
  `docs/release-notes/<tag>.commit` and moves README / `examples/consumer-release` to the new tag (the existing
  `release-pin` check then passes on that PR, never red on a tag). (F5, F8.)
- `mathlib-from-source.yml` (dispatch) and `mathlib-next.yml` (weekly, report-only, never changes pins) split out.
  (F6, F9.)
Cost: a day of work, plus an adversarial review (tool/policy change). Risk: the release job holds `contents: write`
and creates tags; mitigated by dispatch-only, the `release` environment, preflight refusing anything but `main`,
and the tag pointing at a commit whose `verify` ran in the same workflow.

**C. B plus a self-hosted or larger runner for the replay.** Larger runners cut the build and kernels further but
cost money and add an owner-managed machine; the parallel jobs of B get most of the gain on free runners. Not
recommended now.

## 3. Recommendation and what is decided where
**B.** It removes the false reds (F1), cuts runner time per push from ~4 builds + a 93-min replay to one cached
`quick` (~10 min, CONJECTURED until measured) plus the replay only on ready PRs and `main`, and turns the release into
one dispatch whose output (tag, notes, pins, assets, attestation, the follow-up PR) is produced by CI from a verified
commit. Owner decisions (taken 2026-11-08, §4; the release part of this paragraph is superseded there): (1) whether CI may create tags and releases at all (B's `release.yml`
needs `contents: write` in one job); (2) the `release` environment's required reviewers; (3) branch protection with
the required checks `ci / quick`, `ci / tools`, `verify / verdict`; (4) Dependabot for actions. Policy text that
changes with B: `docs/policy.md` ("Releases") and the publishing section of the release-notes template — the owner
no longer creates the tag by hand; `.commit` is written by the release workflow's follow-up PR.

## 4. Owner decisions (2026-11-08)
1. CI does **not** create tags or releases; the owner does. B's `release.yml` is therefore split: `release-candidate`
   (dispatch, read-only except the attestation) and `post-release` (on `release: published`, checks and the pins
   pull request).
2. No environment reviewers (solo maintainer); no `release` environment.
3. Branch protection: on the owner's list. Required checks to set then: `ci / quick`, `ci / tools`, `ci / consumer`,
   `verify / verdict`.
4. Dependabot for the SHA-pinned actions: yes (`.github/dependabot.yml`, weekly, grouped).
5. Repository setting "Allow GitHub Actions to create and approve pull requests": enabled by the owner (2026-11-08),
   so `post-release` opens the pins pull request itself.

## 5. Implemented in this pull request
Files: `.github/actions/setup-lean/action.yml`; `.github/workflows/ci.yml` (replaced), `verify.yml`,
`release-candidate.yml`, `post-release.yml`, `mathlib-from-source.yml`; `.github/dependabot.yml`;
`tools/release_preflight.sh` (with `--self-test`, 9 planted defects). All workflows pass `actionlint` 1.7.7 with
shellcheck (run locally; `ci / tools` runs it on every pull request). Action SHAs were read from the tags with
`git ls-remote` (cache v6.0.0, upload-artifact v7.0.1, download-artifact v8.0.1, attest-build-provenance v4.1.1;
checkout v7.0.1 unchanged).
- F1: `setup-lean` downloads the pinned archive with retries and checks its SHA-256 on every run (also on a cache
  hit); no elan; the archive is kept in `build/toolchain/` so `verify-toolchain` reuses it.
- F2: the toolchain is cached by hash; `quick` restores an incremental `.lake/build`; `verify` builds clean once and
  shares the build tree with the parallel jobs as an artifact.
- F3, F4: `ci.yml` on `pull_request` and `push` to `main`; `verify.yml` on non-draft pull requests to `main`,
  `main`, weekly, dispatch and `workflow_call`; superseded pull-request runs are cancelled, `main` runs never.
- F5, F8: `release-candidate` (preflight, full replay on the exact commit, assets with `SHA256SUMS` and a Sigstore
  attestation, the release body, and the owner's three commands in the run summary); the owner tags and publishes;
  `post-release` checks that the tag is on `main`, has a successful candidate run, that the published assets equal
  the attested ones, builds `examples/consumer-release` against the tag, and opens the pins pull request (needs the
  repository setting "Allow GitHub Actions to create and approve pull requests"; otherwise it prints the compare
  link). `consumer-release` no longer runs on every pull request; `release-pin` runs in `ci / tools` only, so a tag
  push never produces a red run.
- F6: workflows by purpose plus one composite action; no input flags gating jobs.
- F7: `verify` runs `static`, `replay` (+ nanoda from source), `commitments` and a comparator matrix (one job per
  `challenge:` pin, 11 today; the build job fails if a `comparator*.json` lacks a pin) in parallel after one build;
  `verify / verdict` is the single required check.
Not done: `mathlib-next.yml` (weekly report-only build against the next Mathlib, ROADMAP P7). First real runs: this
pull request exercises `ci.yml` and `verify.yml`; `release-candidate` can be dispatched on `main` at any time without
side effects (it writes only an attestation and an artifact), so it is testable before the first release.
