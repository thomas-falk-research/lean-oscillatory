11a9ecfc89706e6868700b8fe3cf28256309254f

# Adversarial review of API3 and the session-5 release-pin change

I left the repository, git state, `build/` and `.lake` untouched. All scratch work is under `/tmp/advAPI3/`. I ran Lean three times, one process at a time, with `nice -n 10 lake env lean`.

## Verdict on the three claims

- **(a) Holds with qualifications.**
  - **Proved:** all ten constants are proved, and each matches its statement exactly. `/tmp/advAPI3/Check.lean` contains `example : XStatement := OscInt.API.x` for all ten. Every `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
  - **Statements unchanged:** `git diff 9d03130 HEAD -- OscInt/Statements Challenge` is empty.
  - **Stamps are sound:**
    - Each manifest names the commit it claims (9d03130…, 7bb4579…).
    - Each manifest's file list is exactly `git ls-tree` of that commit, and every SHA-256 matches.
    - The statement commitments are identical in both stamps.
    - For the review stamp, all three RFC 3161 tokens verify against `stamps/roots` (`openssl ts -verify`: OK ×3).
    - For both stamps, the token imprints equal the manifest SHA-256.
  - **No proof in either manifest:** neither manifest contains `Front/{Family,FamilyC10,Cutoff,Local}.lean`. The second contains only `FamilySanity.lean`, the reviews, the answers and the route.
  - **Qualification:** "as stated" has no post-proof fidelity review yet; only the prompt exists at HEAD.
- **(b) Only partly holds.** See M1 and M2.
- **(c) Holds for tag pins.** It does not hold for raw commit pins (m1).

## Findings

**MAJOR M1. Five of the ten statements still have no sanity theorem through their constant, so the pre-proof MAJOR is answered for half the batch.**
- **Where:** `OscInt/Front/FamilySanity.lean`; `review/2026-11-08-API3-pre-proof-answers.md` (section M1); `docs/statements.md` clarification (6).
- **What:**
  - `NonStationaryLocalStatement`, `StationaryPhaseLocalStatement`, `FoldLocalStatement`, `D4BoundLocalStatement` and `NonStationaryOnStatement` are referenced only by their proofs, `StatementTypes.lean` and `Challenge/Family.lean`. I checked with a grep over all `.lean` files.
  - Referee B's own named plants therefore remain undetectable by any sanity layer: `V ×ˢ U → S ×ˢ K`, and `K ⊆ U` reversed in the family forms.
  - The answers file lists as "not caught" only `p ↦ 0` in S2.2F and `L ↦ 0` in FE-S2.2l/S3l. Clarification (6) reads as if the layer covers the batch.
- **Fix:**
  - Add sanity theorems through the five constants: an `S ⊊ V` family for FE-S2.1L/S2.2L/S3L, a generic cubic for FE-S4.1′L, and the kink phase for FE-S2.1l.
  - Or state in the answers and the docs that these five have no sanity layer, and list them as open.

**MAJOR M2. The sign bites ignore the `k ∈ K` binder, so meaningful plants in S2.2F pass. I reproduced this.**
- **Where:** `FamilySanity.lean`, `stationaryPhaseFamily_sign_bite` (and `foldCrit_sign_bite`). The binder is the `_` in `fun σ p hp k _ hk`.
- **What:** `/tmp/advAPI3/R2-missed.lean` compiles with exit 0 for three planted copies with verbatim bite bodies:
  - S2.2F with `∀ k ∈ K` replaced by `∀ k, k ∈ K' → …`: the Hessian condition is checked on the wrong set.
  - S2.2F with `∀ k ∈ Set.univ`: nondegeneracy is demanded at every critical point of ℝ², which is a weaker statement than the docs.
  - S3c with `∀ k ∈ Set.univ`, against `foldCrit_sign_bite`. For S3c this is caught by `foldCrit_fold_bite`, which types `k ∈ closedBall 0 2`. For S2.2F nothing catches it.
- **Fix:** give S2.2F a bite that uses `k ∈ K`, i.e. a critical point outside K that is degenerate. Add these plants to the "not caught" list.

**MAJOR M3. Not re-freezing after a MAJOR departs from a written, unconditional rule. In substance it is defensible but incomplete.**
- **Where:** `CONTRIBUTING.md:41-42`; `docs/lessons.md` §11.
- **Why the rule applies:** §11 is a statement-authoring rule ("hypotheses are bundled as named `def`s used by both the statement and its sanity theorem"). The frozen `Family.lean` breaks it, and step 5 says a MAJOR "means a new statement, never an edit". The answers add an exception that is not in the rule ("here no statement is wrong").
- **Why it is defensible:**
  - Re-freezing with bundled defs would not change the meaning of the statements.
  - Testing through the whole constant catches more than def-bundling, for the constants it covers.
  - The deviation is disclosed and put to the owner.
- **Why it still looks like a weakened rule to get green:**
  - The substitute covers 5 of 10 statements (M1) and misses demonstrated plants (M2).
  - The lexical check that §11 envisages was not added.
- **Fix:** either the owner ratifies an amended CONTRIBUTING step 5 (a MAJOR confined to the test layer may be answered by sanity through the constants, with full coverage), or re-freeze as API3′. Until then, docs should not call the MAJOR "answered".

**MINOR m1. `check_release_pin.sh` accepts a raw 40-hex commit pin with no check at all: no existence check, no ancestry check.**
- **Where:** `tools/check_release_pin.sh:38` emits `commit <hex>`; `run_checks` (`:93`) loops only over `tag` lines.
- **Reproduced:** I copied the script to `/tmp/advAPI3/crp.sh` and added a self-test case with `rev = "3333…"` in `examples/consumer-release/lakefile.toml`. It returns rc 0 ("FAIL self-test … rc 0, want 1").
- **Scenario:** main's consumer-release lakefile, or `docs/policy.md`, pins a commit that main does not contain, or that does not exist. CI `release-pin` stays green, which contradicts claim (c) as worded.
- **Fix:** for `commit` pins, require `git cat-file -e` after fetching and `ANCESTOR`, or reject hash pins outright. Add a self-test case.

**MINOR m2. The self-test never exercises the real ancestry path.**
- **Where:** the self-test (`:107-109`, `:146`) uses `fake_anc`; the real `in_head` (`:161`) is never run by the self-test.
- **What I checked by hand** in a real-git experiment (`/tmp/advAPI3/git/`):
  - A tag on an unmerged branch: FAIL, as intended.
  - After the merge: PASS.
  - A `--depth 1` clone: FAIL, fail-closed.
  - `2>/dev/null` only hides the message; a merge-base error still exits non-zero, so the check fails.
  - I found no path where a release commit not contained in main passes.
- **Risk:** a regression in `in_head` (wrong argument order, `|| true`) would keep the self-test green.
- **Fix:** add a self-test that builds a three-commit temporary git repository and runs the real `in_head`.

**MINOR m3. The order claim in the docs is stronger than the stamped evidence.**
- **Where:** `docs/statements.md` §batch 3, "Order" ("before any Lean proof … is written, in the repository or in scratch"); answers, "Order of work"; `docs/proof-API3.md` header.
- **What the stamps prove:** the reviews existed by 01:05:48Z, and no proof was in the stamped trees. They cannot prove that nothing existed "in scratch".
- **Corroboration, ephemeral only:** birth times in `/tmp` are consistent with the claim.
  - `/tmp/lead` was born at 01:06:25, and `R1.lean` (2773 bytes) was written at 01:06:25, 26 s after the stamp commit.
  - `/tmp/agent-P1` was born at 01:06:19.
  - `/tmp/agent-P2` was born at 01:06:56; `Cutoff.lean` was written in one go at 01:08:22.
  - `Local.lean`, `Cutoff.lean`, `API.lean` and `StatementTypes.lean` landed in the repository at 01:09:40, 3 m 52 s after the stamp.
- **Fix:** word the claim as "no proof was committed before the review stamp; that none existed in scratch rests on the lead's statement (scratch birth times consistent)".

**MINOR m4. The negative controls show that the proof script is brittle, not that the plants are semantically detected. The plant files are not in the repository.**
- **Where:** `docs/replay/2026-11-08-API3-sanity-plants.txt`.
- **What:** every "rejected" is a type mismatch of the existing proof term. Any syntactic edit, harmless or not, would be rejected the same way. The file says this honestly ("CONJECTURED-by-hand for falsity").
- **Reproduced:** `zero-p-foldcrit`, copied from the lead's scratchpad to `/tmp/advAPI3/R1-zero-p.lean`, is rejected at 18:34 exactly as recorded.
- **Problem:** the plant `.lean` files live only in the session scratchpad.
- **Fix:** commit the plant files (e.g. under `docs/replay/plants/`) and the missed-plant cases from M2.

**MINOR m5. The prose at HEAD is stale. This is understatement, not overclaiming.**
- `docs/STATUS.md` has no rows for the ten API3 statements.
- `docs/HANDOFF.md`:
  - It still describes session 4: "27 pinned statements, each with a row in STATUS", while `stamps/pins.txt` now pins 37.
  - It still says "release-pin red until the tag exists" (`:14`, `:36`, `:78`), but v0.3.0 is published and check 4 passes on HEAD (7098f09 is an ancestor).
- `CHANGELOG.md`:
  - "Unreleased: Nothing yet", although ten statements, `comparator-API3.json` and 37 `statements.json` entries were added. `docs/policy.md` requires statement changes to be listed.
  - "v0.3.0 … not yet published".
- `docs/session-5-checklist.json`, item P1+P2+P3a: "review stamp next, then proofs". Both are done (06c3c66, a638f70, verify-all PASS on a638f70).
- The updates appear to be parked in the lead's scratch (`park2/status-rows.md`, `changelog-unreleased.md`) and were not committed.
- `README.md:50` correctly scopes `release-pin` to tags and does not mention API3. It has no overclaim.
- **Fix:** commit the STATUS rows, the HANDOFF update, the CHANGELOG Unreleased entry and the checklist status. Keep "machine-checked as stated" out of all of them until the post-proof reviews exist.

**NIT n1.** The stamped S3c bite (`K′ = {(−3,−3)}`) and the S2.2F `Bool` witness remain in the frozen file with docstrings that overstate them: the S3c bite is covered by S2.2, and the `Bool` witness is a finite family. This is already acknowledged in clarification (5) and cannot change. No action needed beyond what the docs already say.

**NIT n2.** The OpenTimestamps file `stamps/20261108T010546Z-7bb457958327/manifest.b.pool.ots` is 200 bytes, against 235–237 for the others. It is probably a bare pending attestation. I did not verify it; the RFC 3161 tokens carry the claim.

## Checked with no finding

- **Statements against `docs/statements.md`:** quantifier order (`∃ C` after the data and before `A, M, σ, p/L, m`), signs (`+ lin p`, `+ L`), exponents, and `ContDiffOn` on the open set `V ×ˢ U` all match.
- **Junk values:** none arise.
  - Every `fderiv`, `hessianMatrix` and `iteratedFDeriv` is evaluated at `k ∈ K ⊆ U` with `σ ∈ S ⊆ V`, where the phase is C⁴ near `k`.
  - S2.2F and S3c have global `FamilyCk 4`.
  - The integrand vanishes outside `tsupport A ⊆ K`.
- **Max norm:** the norm in FE-S2.1L is the operator norm dual to the max norm; it only changes the constant `c`. The square ball in FE-S4.1′L is harmless because the prover chooses δ.
- **Satisfiability:** every hypothesis set is satisfiable; the sanity witnesses compile.
- **Proofs:** `Family.lean`, `FamilyC10.lean`, `Cutoff.lean` and `Local.lean` are clean re-assemblies plus a cut-off and germ argument. There is no `sorry` and no non-standard axiom.
- **Challenge and comparator:** `Challenge/Family.lean` is 10 sorried theorems over the frozen defs, and `comparator-API3.json` names all ten.

## Scratch files

- `/tmp/advAPI3/Check.lean`
- `/tmp/advAPI3/R1-zero-p.lean`
- `/tmp/advAPI3/R2-missed.lean`
- `/tmp/advAPI3/crp.sh`
- `/tmp/advAPI3/git/`