# Answers to the post-proof reviews of batch FR (2026-11-17)

Subject: the seven theorems `OscInt.API.ringKernelSolves`, `ringUnique`, `ringCosetSum`, `ringFiniteSize`,
`chainKernelSolves`, `chainUnique`, `chainFiniteSize` and the records about them, at 50a2da8 (the integration commit
ae3b157 plus one row of the session log). Three fresh-context referees, read-only: A fidelity, B soundness of the
formal proof, C adversarial. All three are AI agents of the lead's model family; no calibration copy with planted
errors was run. Their briefs and reports are not recorded verbatim (rule 19); the SHA-256 of the briefs are in the
session log's launch record, those of the reports in the row that records their end. Each finding is restated here
in the lead's words. The tree was not written between the launch and the end of the last referee.

| Referee | Run time (harness record) | Verdict |
|---|---|---|
| A (fidelity) | 603 s | all seven FAITHFUL, scope full; no BLOCKER, no MAJOR; 3 MINOR, 6 NIT |
| B (soundness) | 660 s | all seven SOUND; no BLOCKER, no MAJOR; 1 MINOR, 2 NIT |
| C (adversarial) | 864 s | no regime found in which a statement fails; records ACCURATE on status; no BLOCKER; 1 MAJOR, 5 MINOR, 3 NIT |

What they did, by their own account. A: each theorem's type is syntactically the bare statement constant, axioms
propext, Classical.choice, Quot.sound; no shadowing definition of a kernel; the eight FR source files recompiled as
one scratch file without the built proof objects; the statement file's SHA-256 equals the stamp manifest,
`stamps/statements.json` and the blob at 0748dde; three RFC 3161 tokens verified; a fresh elaboration of the stamped
text is identical to the built constants; Lean read against the prose symbol by symbol. B: all seven proof files
read in full; their bodies recompiled as one scratch file and each file in place; `leanchecker` exit code 0 on 16
modules (FR and the PA modules they use); no forbidden construct in `OscInt/` or `Blueprint/`; the five blueprint
propositions non-vacuous; the lead's interface checks reproduced byte for byte. C: certified scans (25 110
comparisons for FR-P, 7371 for FC-P, 0 violations); both stamps verified (six tokens; both manifests equal their
commit trees); no proof file in git before 6ef8939; 24 numbers of the records recomputed, 21 agree.
Not checked by any of them: the isolated replay, the comparator, a second kernel implementation.

## Findings and answers

| # | Finding | Severity | Answer |
|---|---|---|---|
| C-F1, A-F2 | `CHANGELOG.md`, "Unreleased", said nothing of batch FR (nor of VC2, HW), listed 6 new statements where there are 21, and still called the FR draft "not frozen". | MAJOR (C), MINOR (A) | Accepted; an omission of the lead at integration. The section now lists the 21 new entries (13 with a proving theorem, 8 without) and the FR proof chain. |
| A-F1, C-F2 | `README.md` said "six further statements are proved and await that replay" two lines above "13 more". | MINOR | Corrected to thirteen. |
| A-F3 | The API annotations put "(constant 2 best possible as a supremum)" and "(not sharp)" inside the conclusion fields of FR-P and FC-P; neither is part of a theorem or proved in Lean. | MINOR | Accepted. Both remarks are removed from the conclusions; the FR-P entry now carries the caveat on the representative of r. |
| B-F2 | All seven theorems depend on batch-PA code, not FR-S alone: FR-K, FR-U, FC-K, FC-U through two roots-of-unity lemmas of the alias file; FR-S through PA-C, the Fourier series fact and the aliasing lemma; FR-P and FC-P also through LC-1. Each is used within its hypotheses. | MINOR | Accepted; the lead's records had named the dependency for FR-S only. Said now in STATUS ("what the rows rest on"), in the header of the final file and in the CHANGELOG: none of the seven is machine-checked as stated before batch PA is replayed. |
| C-F3, A-NIT | `docs/HANDOFF.md` had two stale sentences (sanity layer and route "in the lead's scratch"). | MINOR | Removed. |
| C-F4a | Session log: "12 Mathlib names added"; the diff has 10 (two of the twelve were already listed). | MINOR/NIT | Correction row in the log. |
| C-F4b | `review/2026-11-16-FR-pre-proof-answers.md`, A1: "Thirteen false mutations … all were accepted". Twelve pass every script; the thirteenth (P3) passes two of three. | MINOR/NIT | Correct; the answers file overstated the defect by one. That file is a stamped record and is not edited; the correction is this row and a row in the log. |
| C-F4c | "Three agents could not write their report file": the scratch holds a report file for one part of five. | MINOR/NIT | Correct: four left none (three were refused the write and returned text; FR3 named a file that does not exist). `docs/proof-FR.md` corrected; correction row in the log. |
| C-F5, A-NIT | No "what the rows rest on" note for batch FR in STATUS; no entry on the calibration page; no scratch listing at the stamp. | MINOR | Accepted. The STATUS paragraph and the calibration note are added. A scratch listing was taken after these reviews (`docs/replay/2026-11-17-session13-scratch-listing.txt`); none exists from 22:58Z, and the paragraph says what a listing can and cannot show. |
| C-F6 | The order claim. Verifiable: statement text by 20:58:41Z, review answers by 22:58:03Z, no blueprint, assembly or part in git before 6ef8939. Not verifiable: absence of proof text outside git, and the session log states it as fact. The lead's full paper route (20:46:26Z, with blueprint names) predates the first token and both blind reviews. | MINOR (wording) | Accepted. The STATUS paragraph states the claim at the strength it has: "no Lean proof text before the stamp of the answers", not "no proof"; the log's sentence stays as the lead's statement and is labelled so there. |
| A-NIT | "nearest images" wording repeated in STATUS and the FC-P annotation; FR-P annotation without the caveat on r; the final file's header called the explicit bounds "classical" though they were not searched in print; no Lean bridge from `lineKernel` to the kernel of batch LS at d = 1. | NIT | The first three are corrected. The bridge is true on paper (TdF with d = 1) and is not a statement of this batch; noted here. |
| B-F1 | The docstrings of `chainFiniteSize` and `chainKernelSolves` omitted the range hypotheses the statements carry. | NIT | Corrected (docstrings only; the theorems are unchanged). |
| C-F7 | FC-P holds for all integers x, y: the assembly uses 0 < x + y only to replace \|x + y\| by x + y. The referee compiled a proof in its scratch (three standard axioms). The records said "no violation known". | NIT | Recorded as the referee's result, not as a theorem of the library: the frozen statement is weaker than it could be and is not changed. Clarification i in `docs/statements.md`. |
| C-F8 | Regimes in which the statements say nothing: FR-P for \|r\| ≥ N (the right side exceeds 1); both bounds once 2\|t\| reaches the nearest image; M = 0. Not in the prose: FR-U and FC-U are about solutions on all of ℝ; a solution given on an interval is not covered as stated. | NIT | Clarification i. |
| C-F9 | A false mutant no layer can detect: FR-U with the period hypothesis at t = 0 only (a null solution built from a function flat at 0). | NIT | Recorded in clarification i; it is why FR-U needs the period at every time. |
| B-F3 | The referee's own 30-digit check of FR-P showed a false excess where the right side is 1e-40; none at 90 and 150 digits. | NIT | A tooling note; the lead's check script decides on balls. |

## What stands after these answers

- The seven statements are proved in Lean as stated (types, axioms, per-module kernel re-check, three reviews). They
  are not machine-checked as stated until the isolated replay, and not before batch PA is.
- The Lean file `OscInt/Front/FiniteRingFinal.lean` changed after the reviews in comments only (header and two
  docstrings); `make quick` was run again on the result (session log).
- Everything in "What is still not covered" of the pre-proof answers still holds for the sanity layers; the proof
  now closes those gaps for the statements themselves (a mutated statement would not have this proof).

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
