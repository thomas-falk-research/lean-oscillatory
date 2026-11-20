<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Versioning, stability and upgrade policy

Adopted 2026-11-06 (session 3). Applies from v0.3.0. Changing this policy is a CHANGELOG entry.

## What is stable
The **stable surface** of OscInt is:
1. the statement constants `OscInt.Statements.*Statement` listed in `stamps/statements.json`, with the commitment
   recorded there (the SHA-256 of the statement's definitional closure, `docs/commitment-format.md`);
2. the theorems proving them (`proved_by` in `stamps/statements.json`), whose types are syntactically the statement
   constants (`StatementTypes.lean`);
3. the front-end theorems in `OscInt/API.lean`, each with a frozen statement of
   its own.
Everything else (`OscInt.D4.*`, `OscInt.StationaryPhase.*`, `OscInt.Blueprint.*`, auxiliary namespaces) is internal:
it may be renamed or removed in any release. Depend on it only if you accept that.

## Versions (semantic versioning, from v0.3.0)
- **Patch** (x.y.Z): no change to any statement constant, commitment, statement file or `proved_by` name. Proof
  refactors, tools, docs, CI. `stamps/statements.json` is byte-identical (it carries no version number), so a
  downstream pin of its SHA-256 survives a patch release. (A patch adds no stamp: stamps only freeze new statements,
  which only a minor release adds. A new stamp does change the file even for unchanged statement files, because each
  `statement_files` entry names the newest stamp that covers the file; adversarial review 2026-11-07, m8.)
- **Minor** (x.Y.0, from 1.0.0): adds statements or theorems; existing entries of `stamps/statements.json` unchanged,
  except `proved_by` going from `null` to a theorem.
- **Major** (X.0.0): may change commitments, e.g. a Mathlib upgrade (below).
- **Before 1.0.0** the minor version plays the role of the major one: 0.y.0 may do anything a major release may, and
  says so in the CHANGELOG under "Statement changes", listing every changed commitment; 0.y.Z is a patch.
A downstream project pins a release by commit hash and the SHA-256 of `stamps/statements.json` from the release notes
(`tools/oscint_check.py --expect-sha256`). A change to the statement list then fails its check until someone reads
the CHANGELOG. This detects drift; what it does not detect is in README, "Depending on OscInt".

## Never in place
A stamped statement file is never edited (lessons 10; `make commit`, `statements check`); the one exception is the
fixed attribution block at its end (next section). A statement that has to
change becomes a new constant with a new name (for example `D4LimitStatement₂` or `D4LimitLocalStatement`),
written, stamped, pinned and blind-reviewed like any other (`CONTRIBUTING.md`). The old constant, its proof and its
pin stay until removed under the deprecation rule.

## Attribution in frozen files and records (owner decision 2026-11-19)

A statement file is its frozen bytes followed by one fixed attribution block (author, licence); the frozen bytes are
what a stamp pins and what `stamps/statements.json` records by SHA-256, so those values did not change when the
block was added, and adding it is neither a statement change nor a re-freeze. A challenge file ends with the same
block; its pin is the SHA-256 of its export, which a trailing comment does not change. A record (review answers,
replay records, logs, pre-registrations, decision memos, release notes, result files) ends with an attribution block
and is otherwise never edited. The block is a constant of the tools; a byte changed before it, in it or after it
fails the checks. Details and what remains without a line of its own: `docs/decisions/2026-11-19-attribution-blocks.md`.
Licences: the Zenodo record names the code licence (Apache-2.0) only, because its metadata takes one licence; the
documentation is CC BY 4.0, as `CITATION.cff`, `codemeta.json`, `NOTICE` and the record's notes say.

## Deprecation
A stable name is removed only after one minor release in which it is marked `@[deprecated NewName (since :=
"YYYY-MM-DD")]` and listed under "Deprecated" in the CHANGELOG. Statement constants are never deprecated while a
pinned stamp refers to them; they are superseded (the new constant's entry names the old one in its docstring).

## Mathlib and toolchain upgrades (the re-freeze rule)
A commitment is a hash of the statement's definitional closure, which includes Mathlib's definitions (ℝ, the
integral, `fderiv`, `Real.rpow`, …). A Mathlib upgrade can therefore change commitments without anyone touching
OscInt's statement files. Procedure:
1. On a branch, bump `lean-toolchain`, the Mathlib `rev` in `lakefile.toml` and `lake-manifest.json`; record the
   versions and the `#check` probes of `MathlibNames.lean` (lesson 1). Fix proofs; statement files stay byte for
   byte (the guard and `make commit` check this).
2. `make commit`. For each statement whose commitment is **unchanged**: nothing more to do; the old stamp still
   pins it (the commitment says the closure is identical up to binder names, `docs/commitment-format.md`).
3. For each statement whose commitment **changed**: Mathlib changed a definition it depends on, and the old review
   and stamp no longer certify the new closure. Today this means a re-freeze as a new statement: the same text under
   a new constant name (for example `D4LimitStatement₂`), stamped, pinned and reviewed by two blind referees like any
   new statement, with the old constant superseded under the deprecation rule. A cheaper rule, "one referee reads the
   list of changed constants and answers SAME-MEANING or CHANGED", needs a tool that the repository does not have yet:
   the closure text numbers its lines globally, so a `diff` of two closures of thousands of constants is unreadable.
   Technical debt, ROADMAP §3: per-constant canonical hashes with local numbering, and a tool that lists the changed
   constants and prints their old and new values. Until it exists, the cheaper rule is not used.
   A machine-checked equivalence `OldStatement ↔ NewStatement` is not available across a Mathlib version (the two
   closures live in different environments).
   If a frozen statement file no longer elaborates under the new Mathlib, the upgrade waits: the file cannot change,
   so the statement is restated in a new file under a new name (as above) before the upgrade lands, and the old
   theorem stays available on the last release that has it.
4. The full replay (`make verify-all`) on the upgraded tree, recorded in `docs/replay/`; then the release.
5. Planned, not yet in place (ROADMAP §3): a scheduled CI job that builds against the newest Mathlib weekly and only
   warns; it never changes pins.

## What a downstream project should do
- The owner creates release tags and GitHub releases (decision 2026-11-08); a tag is created only on a `main` commit
  that passed a `release-candidate` run (preflight, the full replay and `ci.yml` on that commit), with the assets
  that run built and attested, and only with `tools/publish_release.sh`, which checks all of this before anything is
  public; `post-release` checks this after publishing (`docs/decisions/2026-11-08-ci-release-review.md`).
  Verify an asset of v0.4.0 or later (v0.3.0 predates `release-candidate.yml`) with `gh attestation verify <file>
  --repo thomas-falk-research/lean-oscillatory --signer-workflow
  thomas-falk-research/lean-oscillatory/.github/workflows/release-candidate.yml --source-ref refs/heads/main
  --source-digest <the commit in docs/release-notes/<tag>.commit>`; without the last three flags any workflow, ref or
  commit of the repository would be accepted.
- Pin a release tag (in `lakefile.toml`: `rev = "v0.6.0"` under `[[require]] name = "oscint"`, README) and the
  SHA-256 of `stamps/statements.json` from that release's notes (`docs/release-notes/<tag>.md`); against tampering,
  pin the full commit hash recorded in `docs/release-notes/<tag>.commit` instead of the tag name.
- Run `python3 .lake/packages/oscint/tools/oscint_check.py --statement <each statement you use> --expect-sha256 <pin>`
  in CI. The full check, with kernel replay and recomputed commitments, is the default and takes about 20 minutes;
  `--fast` skips both and reports PARTIAL, never PASS. Use the checker of the release you depend on: from v0.7.0 a
  statement file ends with a fixed attribution block and the recorded SHA-256 is of the bytes before it, so a
  checker copied from v0.6.0 or earlier reports every statement file of a later release as edited
  (`docs/decisions/2026-11-19-attribution-blocks.md`).
- Use the theorems listed as `proved_by`, not internal lemmas; or accept that internal names can change in a patch.
- On an OscInt upgrade, read the CHANGELOG's "Statement changes" section before updating the pin.

## Human expert review of statements (owner decision 2026-11-08, session 7)
The owner chose to defer a commissioned human expert review of statement fidelity until the library is more mature.
The deferral holds under three conditions.
1. **Wording.** Until a human expert has reviewed a statement, every public text (README, release notes, Zenodo
   description, `CITATION.cff` abstract, outreach) describes it as "machine-checked; statement fidelity reviewed by AI
   referees, not yet by a human expert". Never "verified" or "peer-reviewed" alone. `docs/STATUS.md` already says this
   per batch; keep it there.
2. **Strengthen the AI layer meanwhile.**
   - Calibration: plant known fidelity errors in copies of statements, measure the referees' catch rate and report it
     with a Clopper–Pearson interval; until then AI verdicts carry unknown weight.
   - Independence: where possible a second model family or prompt for fidelity reviews; disagreements recorded.
   - Judgement-free evidence first: limit theorems that land on a classical constant (T6L reproduces the Cauchy–Watson
     asymptotic of `Jₙ(n)`), explicit constants checked against external reference values (batch LE against Landau's
     constant), and non-vacuity examples.
   - A review packet grows with each frozen batch: a one-page plain-English reading per statement, its non-vacuity
     examples and known limitations, so the eventual request is one ready document.
3. **Triggers.** A human expert review is requested before the first of: an arXiv preprint or paper submission; a
   public claim of "first machine-checked" anything; a Mathlib pull request that rests on OscInt statements; outreach
   aimed at downstream users (as opposed to listing or archiving the project). Releases, Software Heritage, swMATH
   and Reservoir listings do not wait for it, provided condition 1 holds.
Prior-art disclosures (for example T6/T6L being classical, `docs/prior_art.md`) are made as soon as they are found;
they are not review results and never wait.
