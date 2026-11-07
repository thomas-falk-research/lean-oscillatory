9e5540ac7a07bd677156575352bbdc708aaea87b

# Adversarial referee report: API2 batch, v0.3.0 release preparation, and the release-pin check

**Scope.** Repository `/home/user/lean-oscillatory` at 9e5540a, branch `claude/sleepy-thompson-37yj33`. I did not edit the repository, git state or `build/`, and ran no `make` targets. All my work used a bare clone and a working clone under `/tmp/advAPI2/` (`origin.git`, `work`) and Lean probes in `/tmp/advAPI2/lean/`, each run alone under `nice -n 10`.

**Verdicts**
- **(a) "The fourteen batch-2 statements are machine-checked as stated and were frozen and reviewed before any proof."**
  - The statements look faithful and true. Their proofs are thin bridges from the frozen S2.1, S2.2, S3 and S4.1′ theorems, and they use only `propext`, `Classical.choice` and `Quot.sound`.
  - But "machine-checked as stated" has no evidence yet: no post-proof reviews, no verify-all record, no STATUS rows.
  - The "before any proof … written or drafted" claim is stronger than the evidence, and the repository's own documents contradict it in one place.
- **(b) "v0.3.0 is prepared."**
  - The SHA-256 pins are correct for 2e8707a.
  - "No existing statement changed" is true.
  - The tree at the release commit contradicts itself, and the release notes point to a verify-all record that does not exist.
- **(c) "CI fails when the README's pinned tag does not exist."** True for the syntax `rev = "vX.Y.Z"`. Not true in general:
  - A `v0.3.0` tag on the wrong commit passes the check.
  - A README pin in other valid syntax is not seen at all.

## BLOCKER
None.

## MAJOR

**M1. `release-pin` accepts a `v0.3.0` tag on the wrong commit** (`tools/check_release_pin.sh:16-40`, `docs/release-notes/v0.3.0.md:9-14`)
- **What the check does.** It only compares the SHA-256 of `stamps/statements.json` and `tools/oscint_check.py` at the tag with the table in the notes.
- **Six commits share both hashes** (`44aacc38…`, `f45b18d5…`): 2ddcbe0, 9a79382, db6b207, cb39601, 2e8707a and 4acb308.
- **Reproduced** in `/tmp/advAPI2`. I moved the remote tag to each commit and ran the script.
  - Tag on 4acb308: `release-pin: PASS`, rc 0.
  - Tag on 2ddcbe0: PASS.
  - Tag on db6b207: PASS.
  - Tag on a610a7a: correctly fails. Tag on 9e5540a: correctly fails.
- **Why 4acb308 is bad.** It holds the 14 batch-2 statements unstamped, unreviewed and unproved, and `import OscInt` exposes them.
- **Why 2ddcbe0 is bad.** Its `lakefile.toml` says `version = "0.2.0"`.
- **Same blind spot downstream.** `consumer-release` checks only the same `statements.json` hash and three old statements, so it would also go green.
- **Unrelated history also passes.** A tag on any commit, even outside this history, that carries the same two files passes.
- **Fix.**
  - Put the full commit hash of the release in the release notes (and in README/policy, which tell users to pin by commit).
  - Require `git rev-parse "$tag^{commit}"` to equal it.
  - Optionally also pin `lakefile.toml`'s version, or a manifest hash of the whole tree.

**M2. The README pin scanner misses common pin syntaxes, so a wrong README pin can pass** (`tools/check_release_pin.sh:11-13, 68-69`)
- **Not matched:**
  - TOML literal strings: `rev = 'v0.4.0'`.
  - A tab before `=`: `rev<TAB>= "v0.4.0"`.
  - The Reservoir form of `lakefile.lean`: `require "owner" / "oscint" @ git "v0.4.0"`.
  - `rev = "refs/tags/v0.4.0"`.
  - Pre-releases: `"v0.4.0-rc1"`.
- **Matched but shouldn't be:** pins inside comments (`# rev = "v0.4.0"`) count as pins.
- **End-to-end reproduction.**
  - I set README line 43 to `rev = 'v0.4.0'`. `docs/policy.md` and the comment in `examples/consumer/lakefile.toml` still say `"v0.3.0"`.
  - With the remote tag v0.3.0 on 2e8707a, the result was `release-pin: PASS`. The README tells users to pin a tag that does not exist, and CI is green.
- **Why.** The "no pin in README" condition is computed over the union of three files, not over README alone.
- **The lakefile actually used is not scanned.** `examples/consumer-release/lakefile.toml`, the one that is built against the tag, is not among the scanned files.
- **Fix.**
  - Parse each file on its own and require at least one pin in README itself.
  - Accept `'…'` and `@ git "…"`, and reject unrecognised `rev =`/`@` forms instead of skipping them.
  - Ignore comment lines, or require that they agree.
  - Add the `consumer-release` lakefile to the scanned files.
  - Add self-tests for each of these cases.

**M3. The order claim is stronger than the evidence, and contradicts the repository's own proof route** (`docs/statements.md:209-213`, `docs/statements.md:300-306`, `docs/proof-API2.md:3-6`, `review/2026-11-07-API2-pre-proof-answers.md:7-13`)
- **What is claimed.** `statements.md` says the batch was "blind-reviewed before any proof of them is written or drafted, in the repository or in scratch".
- **What contradicts it.** `docs/proof-API2.md` says it was "Drafted during the statement-review window in the lead's scratch directory". That draft contains worked proofs: the C6 certificates computed with sympy, and step-by-step routes for C1–C4. So a proof draft existed in the lead's scratch before both reviews were in.
- **What the evidence supports.** I verified the stamp `stamps/20261107T101640Z-4acb308f54f4`:
  - The manifest names commit 4acb308. All 307 file hashes match `git ls-tree` of 4acb308 exactly.
  - The manifest's SHA-256 (`dbc493e1…`) is the imprint of all three RFC 3161 tokens: DigiCert 10:16:43Z, FreeTSA 10:16:42Z, Sectigo 10:16:43Z.
  - `openssl ts -verify` gives OK for all three against `stamps/roots/` (Sectigo via `usertrust-rsa.pem`).
  - So the statements provably existed by 10:16:43Z.
- **What has no evidence.**
  - Nothing timestamps the reviews (8a710fc, 10:40:06, self-reported committer date). Both review files have the same mtime (10:39:42.2254…), so one process wrote both.
  - Nothing timestamps the start of proof work.
- **The file mtimes make the claim implausible** (weak evidence):
  - `review/prompts/API2-briefs.md`: 10:41:27.
  - `OscInt/API/ConvertNorm.lean` (176 lines): final at 10:43:08, 101 s later.
  - `ConvertDisc.lean`: 10:43:47. `ConvertDeriv.lean`: 10:43:51.
- **The answers file says the opposite of the mtimes.** It says `ConvertSanity.lean` was added "before any batch-2 proof". Its mtime is 10:44:33, after ConvertNorm, ConvertDisc and ConvertDeriv. It was committed in the same commit as the proofs (9e5540a).
- **Fix.**
  - Narrow the claim to what is evidenced: "statements stamped at 10:16:43Z (RFC 3161 ×3); review and proof order self-reported".
  - Reconcile `proof-API2.md` with `statements.md`: either a route drafted during review counts as a proof draft, or the statement must say "no Lean proof".
  - In future, stamp the reviews (and the sanity file) before launching proof agents.

**M4. Prose now overclaims "machine-checked as stated" for the 14 new statements** (`README.md:13`, `docs/HANDOFF.md:6-11`)
- **The claim.** Both say "every pinned statement is machine-checked as stated". Since a610a7a, `stamps/pins.txt` pins 27 statements.
- **The evidence for the 14 new ones:**
  - no rows in `docs/STATUS.md`;
  - no post-proof review (the prompts exist, the reviews don't);
  - no comparator or verify-all record (`make verify-all` on 9e5540a is only running now);
  - only "make quick" in a commit message.
- **It was also false earlier.** Between a610a7a and 8a710fc the same sentence covered 14 pinned statements with no proofs at all.
- **The rest of the prose is stale.**
  - `HANDOFF.md` still says "end of session 3".
  - It lists the batch-2 conversions as "Next" item 2.
  - It points to CHANGELOG "Unreleased" for the v0.3.0 notes, but `CHANGELOG.md:9` says "Nothing yet".
  - CHANGELOG "Unreleased" does not record the 14 added statements, their pins or the changed `statements.json`, although the CHANGELOG preamble says every release lists its statement changes.
- **Fix.**
  - Scope the README and HANDOFF sentences to the statements that have STATUS rows ("every statement with a STATUS row…").
  - Add the batch-2 STATUS rows as "proved; post-proof review and replay pending".
  - Add the batch-2 entries to CHANGELOG "Unreleased".

**M5. `import OscInt.API`, the documented entry point, does not expose any batch-2 theorem or statement** (`OscInt/API.lean:1-15`, `README.md:55-66`)
- **The cause.** `OscInt/API/Convert.lean` imports `OscInt.API`, so `OscInt.API` cannot import it back.
- **Probe** (`/tmp/advAPI2/lean/P1.lean`, `import OscInt.API`): the following are all "Unknown constant":
  - `OscInt.API.d4BoundFE`
  - `OscInt.API.foldFE`
  - `OscInt.API.dd_iteratedFDeriv`
  - `OscInt.Statements.D4BoundFEStatement`
- **What the docs promise.**
  - `OscInt/API.lean` says "it imports every final theorem of OscInt".
  - README says to import `OscInt.API` and use theorems by their statement names.
  - `stamps/statements.json` lists `proved_by: OscInt.API.d4BoundFE` and the other 13 new ones under the `OscInt.API` namespace.
- **Who notices.** Only `ConsumerFormula.lean` works, and only because it does `import OscInt`.
- **Fix.**
  - Move the front-end proofs into modules that `OscInt/API.lean` imports, and rename the old API file (e.g. an `OscInt.API.Core`).
  - Or document `import OscInt.API.Convert` as the entry point.
  - Add a consumer test that does `import OscInt.API` and `#check`s every `proved_by` in `statements.json`.

**M6. The release tree contradicts itself, and the cited verify-all record does not exist** (`docs/release-notes/v0.3.0.md:41-45`; `CHANGELOG.md` at 2e8707a, lines 16-19, 66-67; `docs/HANDOFF.md` at 2e8707a, lines 22-29, 43)
- **The release notes** say "the session-4 baseline record for it is listed in docs/HANDOFF.md". `HANDOFF.md` lists no such record, either at 2e8707a or at HEAD.
- **The CHANGELOG** cites "this session's verify-all record listed in the release notes". The notes list none.
- **The only session-4 record** is `make quick` on cb39601. No verify-all ran on 2e8707a.
- **At the tag itself, `HANDOFF.md`:**
  - still tells the owner to "Bump lakefile.toml, CITATION.cff, .zenodo.json to 0.3.0" and to put the SHA-256 into the notes, both already done;
  - says the notes are in CHANGELOG "Unreleased", which is empty;
  - lists "Put GammaFree.lean into the next stamp" as open, while the same commit's CHANGELOG "Fixed" says HANDOFF no longer lists it. It still does at HEAD (`docs/HANDOFF.md:43`).
- **Fix.**
  - Before tagging, run `make verify-all` on the release commit and cite its record.
  - Fix the dangling references and the HANDOFF text in the commit that gets tagged. That means re-preparing the release on a new commit and updating the pinned commit (see M1).

## MINOR

**m1. A stale local tag can mask a wrong remote tag** (`check_release_pin.sh:74-75`)
- **Mechanism.** `git fetch … "refs/tags/$tag:refs/tags/$tag" || true` does not force-update. When a local tag exists, the fetch is refused, the error is swallowed, and `git show` reads the local tag. The `ls-remote` call only checked that the name exists on the remote.
- **Reproduced.** Remote tag on 9e5540a (wrong), local tag on 2e8707a: PASS.
- **Who is affected.** Developers running `make release-pin`. Fresh CI checkouts are not affected.
- **Side effect.** The script also writes tags into the caller's repository.
- **Fix.** Fetch into a private ref (e.g. `refs/release-pin/$tag`) with `+` (force), and compare it with the object id from `ls-remote`.

**m2. Duplicate table rows pass** (`check_release_pin.sh:33`)
- **Mechanism.** `grep -q` accepts the notes if any row matches.
- **Reproduced.** A wrong row (`deadbeef`) next to the right one for `stamps/statements.json`: PASS.
- **Knock-on.** `ci.yml:86` would then pass a two-line `$pin` to `--expect-sha256`.
- **Also unchecked.** The `--expect-sha256` value in the notes' code block (line 26) is never compared with the table.
- **Fix.** Require exactly one row per file, and check the code-block value too.

**m3. The script's diagnostics are dead or misleading** (`check_release_pin.sh:68-69`)
- **Mechanism.** With `set -euo pipefail`, an empty scan makes `tags=$(scan …)` exit 1 silently, so the "no pinned tag found in README.md" message never prints.
- **Reproduced.**
  - All pins changed to `"main"`: rc 1, no output.
  - `docs/policy.md` missing: rc 2, no output, even though README has a valid pin.
- **Fix.** Use `|| true` inside `scan` and test for emptiness explicitly. Report missing files by name.

**m4. The self-test covers less than "negative controls" suggests** (`check_release_pin.sh:42-63`)
- **Covered (6 cases):** missing tag, missing notes, wrong checker hash, correct pin, prefix tag, and `scan` on one TOML file.
- **Not covered:**
  - a wrong `statements.json` hash;
  - a tag on the wrong commit (M1);
  - other pin syntaxes (M2);
  - duplicate rows (m2);
  - `ls-remote` or fetch failure;
  - a stale local tag (m1);
  - the real `git show` path (it is replaced by `fake_show`).
- **Fix.** Add a case for each.

**m5. `consumer-release` trusts more than it states** (`.github/workflows/ci.yml:62-89`)
- **What it trusts.**
  - `lake update` resolves the tag again, with no committed manifest. Nothing checks that `.lake/packages/oscint` is at the commit `release-pin` checked, or at 2e8707a.
  - The checker it runs is the package's own copy, i.e. the code under test checks itself.
  - `lake exe cache get` trusts the Mathlib binary cache.
  - It checks only three statements.
- **Fix.**
  - Assert `git -C .lake/packages/oscint rev-parse HEAD` equals the pinned commit.
  - Hash the package's `tools/oscint_check.py` against the notes before running it.
  - Run the repository's own copy of the checker against the package.

**m6. Accepted referee requests were not implemented**
- **The answers say** referee B's MINOR 4 is "Accepted".
- **Missing from the repository:**
  - the C8 example with gradient (3, 4);
  - C7′ with explicit D₁, D₂, D₃;
  - FE-S2.1's gradient hypothesis plus its bite;
  - the FE-S4.1′ bite x²y + x⁴.
- **Search result.** `grep` over all `.lean` files finds no use of `foldOrNondeg_of_hasFDeriv`, `nonStationaryFE`, `stationaryPhaseFE` or `ampBound_conv` outside `StatementTypes.lean`.
- **Consequence.** The hypotheses of FE-S2.1, FE-S2.2 and C7′ are never shown to be satisfiable in Lean.
- **Fix.** Add the checks, or change the disposition to "partially accepted".

**m7. The notes and policy say "pin the commit hash", but the notes don't give one** (`docs/release-notes/v0.3.0.md:29-30`, `docs/policy.md:25`)
- The commit appears only in `HANDOFF.md` on a later branch head.
- **Fix:** put the full commit hash in the notes (this also serves M1).

**m8. A patch release can't keep `statements.json` byte-identical** (`docs/policy.md:17-19`)
- Policy says `statements.json` is byte-identical across patches. But `statement_files[].stamp` is rewritten to the newest stamp for files that did not change: five rows changed between 2e8707a and HEAD with identical file SHA-256.
- So any new stamp changes the pinned hash, even when no statement entry changed. That breaks the patch guarantee as soon as a stamp is added.
- **Fix:** record the stamp that first froze each file, or drop the field.

## NIT

- **n1.** `CHANGELOG.md:63` lists, under "Fixed", that README told users to pin v0.3.0 before the tag existed. README still does; the problem is now only detected, not fixed.
- **n2.** At HEAD, `lakefile.toml`, `CITATION.cff` and `.zenodo.json` say 0.3.0, but the tree has moved past the release (14 new statements). Mark it as a development version (e.g. 0.4.0-dev).
- **n3.** The release notes say the release commit differs from 2ddcbe0 "only in documentation, CI, … examples/ and version numbers". It also changes docstrings in `OscInt/API.lean` and `OscInt/API/Sanity.lean`. Harmless, but say so.
- **n4.** In `check_release_pin.sh:33` the file name is used unescaped inside a regex (the `.` matches any character).

## Checked and found sound

- **Statements match the docs.** `OscInt/Statements/Convert.lean` matches `docs/statements.md` (lines 208–306) for all 14 statements. Points I checked:
  - argument order of `dd`/`ddd` versus `iteratedFDeriv`, and the symmetry it needs;
  - the `cubicCoeffs` factors 1/6, 1/2, 1/2, 1/6 against the FE-S4.1′ identity 6(ax³+bx²y+cxy²+dy³);
  - `disc` equals `Cubic.discr` (x³−3xy² gives 108, 1,2,3,5 gives −367);
  - C6 with `𝓝[≠]`, and q = 0;
  - the operator norm on the max-norm product is |L e₁|+|L e₂|, with C8's √2 conversion in both directions;
  - `FoldCondSpan` forces a one-dimensional kernel;
  - FE-S4.1′ has no Dφ(0) hypothesis, which is harmless because it is uniform over L;
  - no junk values: every `fderiv`/`iteratedFDeriv` is guarded by `ContDiff`/`ContDiffAt`/`DifferentiableAt`/`HasFDerivAt`, and the integrands are integrable.
- **Bridges.** `OscInt/API/Convert.lean` derives each front end from `OscInt.nonStationary`, `stationaryPhase`, `fold` and `d4BoundNe` through `vecOf`. `#print axioms` for `d4BoundFE`, `nonStationaryFE`, `foldOrNondeg_of_hasFDeriv` and `disc_ne_zero_iff_isolated` gives only `[propext, Classical.choice, Quot.sound]`.
- **Registration.** `StatementTypes.lean` has the 14 `#assert_type_is` lines, and `comparator-API2.json` lists all 14 theorems.
- **Release hashes.**
  - `git show 2e8707a:stamps/statements.json | sha256sum` = `44aacc38d4d16cc8a7b514acc67c12a19ac8ca78f92123e46bb1e3d7cd641f77`.
  - `git show 2e8707a:tools/oscint_check.py | sha256sum` = `f45b18d520f8901a3568c45e107fadda5572df06c609458ff13eb7d81d503706`.
  - Both match the notes.
- **"Statement changes" claim.** Between v0.2.0 and 2e8707a:
  - `stamps/pins.txt` adds exactly the two F1/F2 lines plus `comparator-API1`;
  - there is no diff in the five old statement files, `lean-toolchain` or `lake-manifest.json`;
  - between 2e8707a and HEAD, the 13 old `statements.json` entries are byte-identical.
- **What the check does catch.**
  - With no `v0.3.0` tag (local or remote, GitHub has only v0.2.0): FAIL, rc 1.
  - With the tag on a610a7a or 9e5540a: FAIL on the `statements.json` hash.
