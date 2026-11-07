# Answers to the post-proof and adversarial reviews of front-end batch 2 and the v0.3.0 preparation

Reviews, all on commit 9e5540a: post-proof `review/2026-11-07-API2-post-proof-A.md`, `…-B.md` (FAITHFUL ×2 on all
fourteen theorems, scope full, no BLOCKER or MAJOR); adversarial `review/2026-11-07-API2-adversarial.md` (no BLOCKER,
six MAJOR, eight MINOR, four NIT). Prompts: `review/prompts/API2-post-proof.md`, `API2-adversarial.md`.

## Replay incident
`make verify-all` on 9e5540a (record `docs/replay/2026-11-07-API2-verify-all-9e5540a.txt`) reported
`FAIL leanchecker OscInt.API (59.5s) non-zero exit:` with empty output; the memory cgroup's OOM killer stopped
`leanchecker` at 13.5 GB. Referee B believed its concurrent Lean run was the cause; re-run alone, the step was
killed again at 13.46 GB peak (limit 14.3 GB), so the cause is the repository: `leanchecker M` replays every module
whose name starts with `M` in parallel tasks (`LeanChecker.lean`, toolchain source), and batch 2 had added eight
`OscInt.API.*` modules. Fix: the implementation files moved to `OscInt/Front/` (names unchanged), `OscInt.API` is
imports-only, and `tools/check_entry_point.sh` fails if any module except the root has submodules (lessons 30). The
same record's `verify-toolchain` FAIL is a network reset while downloading the toolchain archive (curl 56). Every
other step of that run passed: 71 per-module `leanchecker`, six export kernels on 65 225 declarations, 27 of 27
commitments, 9 of 9 comparator configurations, five stamps, `statements.json`. The release commit's own run is the
record cited by STATUS.

## Adversarial MAJORs
| Finding | Answer |
|---|---|
| M1 a `v0.3.0` tag on any of six commits passes `release-pin` | Fixed. The release notes now come with `docs/release-notes/v0.3.0.commit` (the full hash of the release commit, written in the commit after it); `tools/check_release_pin.sh` requires the remote tag, peeled, to be exactly that commit, then hashes both pinned files at that commit. Self-test case "tag on another commit rejected (even with equal checker hash)". |
| M2 pin syntaxes missed; README not checked on its own; consumer-release lakefile not scanned | Fixed. Single quotes, any spacing, `@ git "…"`, `refs/tags/`, pre-release suffixes are recognised; comment lines are ignored; any other `rev =`/`@` value that is not a tag or a full commit hash fails; README must pin a tag itself; `examples/consumer-release/lakefile.toml` is scanned. Each case has a negative and (for syntaxes) a positive control: 25 self-test cases. |
| M3 order claim stronger than the evidence; contradicts `docs/proof-API2.md` | Accepted. Claim narrowed in `docs/statements.md`: the statements are timestamped (RFC 3161 ×3, 10:16:43Z); the order "reviews before proofs" rests on git history and is self-reported; the route (mathematics, sympy certificates) was drafted during the review window, which the process allows, so the claim is "no Lean proof before the reviews", not "no proof draft". `ConvertSanity.lean` was written while the proof agents ran, not before (the answers file said otherwise; corrected). Rule for next batches (lessons 29): stamp the reviews before launching proof agents. |
| M4 README and HANDOFF claimed "every pinned statement machine-checked" while batch 2 had no evidence | Accepted. Wording scoped to statements with a STATUS row; batch-2 STATUS rows derived from the evidence now in hand (post-proof FAITHFUL ×2, the final verify-all record). |
| M5 `import OscInt.API` did not expose batch 2 | Fixed. The former `OscInt/API.lean` content moved to `OscInt/Front/Core.lean` and every `OscInt/API/*.lean` to `OscInt/Front/` (same declarations and names); `OscInt/API.lean` imports `Front.{Core, Convert, ConvertSanity, Poly, Sanity, Examples}` and declares nothing. New check `tools/check_entry_point.sh` (in `make quick` and CI): `import OscInt.API` must expose every statement constant and every `proved_by` in `stamps/statements.json`; self-test plants a missing name. |
| M6 the release commit's documents contradicted themselves and cited a missing record | Fixed by re-preparing v0.3.0 on the session's final commit (which includes batch 2), with its own `verify-all` record cited by name, HANDOFF and CHANGELOG consistent at that commit. 2e8707a is no longer the release commit. |

## Adversarial MINORs and NITs
| Finding | Answer |
|---|---|
| m1 stale local tag masks the remote | Fixed: fetch into `refs/release-pin/<tag>` with `+`, never into `refs/tags`; the commit compared is the remote's (`ls-remote`, peeled). |
| m2 duplicate rows; `--expect-sha256` in the notes unchecked | Fixed: exactly one row per file; every `--expect-sha256` in the notes must equal the row. Self-tests. |
| m3 dead diagnostics under `set -e` | Fixed: no `set -e`; missing scanned files are reported by name; empty README pin reported. |
| m4 self-test coverage | Extended to 25 cases (above). The real `git show` path is exercised by the CI run, not by the self-test (stated in the script). |
| m5 `consumer-release` trusts the package | Partly fixed: the job asserts that `.lake/packages/oscint` is at the commit recorded in `docs/release-notes/<tag>.commit` and that the package's `tools/oscint_check.py` has the SHA-256 in the notes before running it, and runs this repository's copy. The Mathlib cache stays trusted (README). |
| m6 accepted referee requests not implemented | Partly fixed: `OscInt/Front/Examples.lean` (through the bridges) adds C8 on gradient (3, 4) (max-norm operator norm 7, `GradLower` 5 holds, 5.1 fails), FE-S2.1 for Ψ = k₁ with its bite (`L = −fst`), FE-S2.2 on the saddle (Hessian matrix diag(2, −2)), and FE-S4.1′ on the hyperbolic cubic (disc −367). **Not done:** C7′ with explicit `D₁, D₂, D₃` (building the bilinear-map-valued derivatives by hand exceeded its timebox; C7′ remains proved and reviewed FAITHFUL ×2, its hypotheses are not yet witnessed in Lean). Open item in `docs/HANDOFF.md`. |
| m7 notes give no commit hash | Fixed with M1 (`.commit` file; README and policy point to it). |
| m8 `statements.json` changes when a new stamp is added | Policy corrected: a patch release adds no stamp (stamps freeze new statements, which only minor releases add), so the file is byte-identical across patches; the generator's `stamp` field records the newest stamp covering a file, and that is now documented. |
| n1 "Fixed" overstated | Reworded: "detected by `release-pin`". |
| n2 version at HEAD | v0.3.0 is now the final commit itself (includes batch 2); no dev suffix needed. |
| n3 release-notes wording about 2ddcbe0 | Removed (the notes now cite this session's record). |
| n4 unescaped file name in a regex | Fixed (`grep -F`). |

## Post-proof findings
| Finding | Answer |
|---|---|
| A-MINOR 1 / adversarial m6 | As m6. |
| A-MINOR 2 / adversarial M3 | As M3. |
| A-NIT 3, B-MINOR 1 the acceptance file is not checked by `make` | `make quick` (target `entry-point`) now elaborates `examples/consumer/ConsumerFormula.lean` against the root build, and the CI `consumer` job builds it as a separate package (default target). |
| B-MINOR 2 hyperbolic D4 only at hypothesis level | Added `OscInt.API.Examples.fe41_hyperbolic` (x³ + 2x²y + 3xy² + 5y³, disc −367) through `d4BoundFE`. |
| B-NIT 1 helper location | Answers file corrected: `NormAux.norm_prod_functional` in `ConvertNorm.lean`, an equality. |
| B-NIT 2, A-NIT 4, A-NIT 5 | Cosmetic / recorded; `coeffs_eq_of_forms` moved into the `ConvertAux` block. |
