# Answers to the post-proof reviews of batch D4U (S4.2U, S4.2O)

Three fresh-context referees read the batch at 07ff140, after the parts were integrated and before the replay: A
(fidelity), B (soundness of the formal proof) and C (adversarial). All three are Claude instances, like the lead; their
prompts and reports are not recorded (lessons 46), and each finding is restated below in the lead's words. Each ran
small Lean checks in its own scratch directory (no `lake build`, no `make`); no replay was running; nothing was
committed while they read the tree. Written by the session-12 lead.

| Referee | Launched at commit | Launched (UTC) | Run time |
|---|---|---|---|
| A (fidelity) | 07ff140 | 14:20:21 | 228.5 s |
| B (soundness) | 07ff140 | 14:20:21 | 162.1 s |
| C (adversarial) | 07ff140 | 14:20:21 | 486.9 s |

Launch time from the lead's clock just before the three launches; run times from the session's task records. One
correction was sent to referee A after launch (a file name lost from its brief: `StatementTypes.lean`).

## Verdicts

| | A (fidelity) | B (soundness) | C (adversarial) |
|---|---|---|---|
| `OscInt.API.d4LimitUniform` : S4.2U | FAITHFUL, scope full | SOUND | no regime found in which the statement fails |
| `OscInt.API.d4LimitOffset` : S4.2O | FAITHFUL, scope full | SOUND | same |

No BLOCKER. Two MAJOR findings (C), both against the records of the batch's process, not against the Lean, the
statements or the mathematics; answered below. The Lean is unchanged by the answers except for two docstrings.

**What the referees checked, in brief.**
- A: the types (the two `#assert_type_is` lines, an independent `example`, and that each type is exactly the bare
  statement constant), the axioms (standard three only), that the built statement constants equal a fresh elaboration
  of the stamped file (so no stale olean), the stamp byte for byte (SHA-256 of the statement file in the manifest and
  in `stamps/statements.json`, the two commitments), no hidden hypotheses, and that S4.2U and S4.2O each imply S4.2
  (compiled). No overstatement found in STATUS, the API annotations or the docstrings.
- B: every D4U proof file in full; no forbidden construct; a fresh compile of all proof bodies in one scratch file
  against their dependencies only; the proved S4.1′ and S4.2 used within their frozen hypotheses; each part matches its
  blueprint proposition and the route; the interface checks reproduced.
- C: the RFC 3161 tokens of both stamps verified against the pinned roots (6 of 6), each manifest's file hashes against
  its commit, the git order (statements, stamp, pre-proof referees, answers, review stamp, route, route referee, answers,
  parts), a recompilation of the proof files, and an attempt to break the mathematics (none found).

## Findings and answers

1. **MAJOR (C).** The order and authorship claims were stronger than the facts: before the freeze the lead elaborated,
   in scratch, the packet's Lean drafts, which contained a reduction of both statements to S4.1′ and S4.2 (essentially
   the assembly), yet the records said "no proof before the reviews" held for "the lead's Lean", that "the route below
   is the lead's", and that the Lean proofs were the lead's; and there was no record of the packet or of the scratch
   work, unlike batches A3 and LS.
   **Answer.** Accepted. New record `review/2026-11-15-D4U-packet-answers.md` (what the packet contained, the referee
   check of its hand proof, the lead's scratch elaboration of its drafts 11:03:44–11:13:33 UTC, before the statements
   were first committed at 11:50:11, and how the batch relates: the route follows the packet's decomposition, two part
   names are the packet's). Claims corrected to "no Lean proof in the repository before the reviews were answered and
   stamped" in `review/2026-11-15-D4U-pre-proof-answers.md`, `docs/proof-D4U.md`, the docstring of
   `OscInt/Front/D4UniformFinal.lean`, and the STATUS rows (provenance note as for F1/F2, LS, A3).
2. **MAJOR (C).** The AI-use disclosure cited a referee check of the packet's hand proof with no record.
   **Answer.** Accepted: recorded in the packet answers file (verdict, findings in the lead's words, run time, script
   times). The packet does not state its model version; the record says so.
3. **MINOR (C).** Clarification 2 in `docs/statements.md` said that at |y| ~ t there is no stationary point (false in
   general: a linear term of size t can place a critical point inside the ball, as modelling choice 3 says) and stated
   the range |y| = o(t^{1/3}) as a consequence of numerics.
   **Answer.** Accepted: clarification rewritten; the o(t^{1/3}) range labelled CONJECTURED; dated correction note.
4. **MINOR (C).** The plant summary overstated detection by lessons 44: only three planted statements of the second run
   are refuted by witnesses; definition-level witnesses and data-only rejections of true weakenings were counted as
   refutations; and a plant that drops uniformity, the batch's content, cannot be detected semantically.
   **Answer.** Accepted: counts corrected in the pre-proof answers and a correction appended to the plant record, which
   now says plainly that dropping uniformity is a true weakening that no sanity layer can detect. The generated
   theorem name `witness_not_AmpTotallyBounded` for the positive witness is noted there (the recorded files are kept as
   run).
5. **MINOR (C).** The tree changed while pre-proof referee B's agent was still running (sanity extension written at
   13:10:42; the agent ended about 13:12:13), against lessons 16.
   **Answer.** Accepted: disclosed in the pre-proof answers (B's report had been delivered at about 13:08:12; the
   remaining run was its own background work).
6. **MINOR (C).** Pre-proof referee A compiled the linearity of `oscInt2` in the amplitude, a lemma of part P-linear
   (lessons 24, in spirit).
   **Answer.** Accepted: added to the lessons-24 disclosure in the pre-proof answers.
7. **MINOR (A).** The STATUS claim "per-module leanchecker" had no record in the tree (lessons 36).
   **Answer.** Accepted: `docs/replay/2026-11-15-D4U-integration-checks.txt` (re-run on 07ff140, clean tree: the seven
   D4U modules, exit 0 each; the audit lines), cited in the STATUS rows. The replay will re-check everything.
8. **NIT (A).** The docstring of `d4LimitOffset` should say "for each fixed R". **Answer.** Done.
9. **NIT (A).** "pre: FAITHFUL and TRUE ×2" in STATUS could be read as two of each. **Answer.** Rows now say "A
   FAITHFUL, B TRUE".
10. **NIT (B, C).** "Moved unchanged" for the assembly: the namespace changed, so the full names did. **Answer.** Wording
    corrected in `docs/proof-D4U.md` and the assembly docstring.
11. **NIT (B).** The final docstring named the model vendor outside the AI-use item and was narrower than the disclosure.
    **Answer.** Done with finding 1 (the docstring now points to the disclosure and the packet record).
12. **NIT (C).** The route-referee record lacked its finish time and the P-mod agent its launch record. **Answer.** Added
    in `docs/proof-D4U.md` (finish about 13:54:53; P-mod agent launched after d952b77, run time 118.0 s).
13. **NIT (C).** The ATB-C0 remark "the proof pins the order" is an argument, not detection. **Answer.** Said so in the
    plant-record correction.
14. **NIT (B, C).** The route says T = max T₀ 1 while the Lean intersects with `eventually_ge_atTop 1`; the API docstrings
    cite no textbook (CONTRIBUTING step 11). **Answer.** The first is equivalent and already recorded; the second is
    part of the records step after the replay.

Strongest case against the batch (C, accepted as stated): the theorems are a short corollary of S4.1′ and S4.2 and are
kernel-checked; the statement-first order protects the statements' fidelity, not the independence of the proof, which
followed an external packet that the lead had read and elaborated before writing the statements.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
