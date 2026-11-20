# Answers to the post-proof reviews of batch VC2 (VC2-S, VC2-A, VC2-N, VC2-K)

Three fresh-context referees read the integration commit 7bb81e3 (the tree they saw is 9d9b231, which adds one log
row): A fidelity, B soundness, C adversarial. All three are AI agents of the same model family as the lead and the
provers; no calibration copy with planted errors was run for this batch (`docs/calibration.md`). Their briefs and
reports are not recorded verbatim (rule 19); the SHA-256 values of the brief files and of the report files and the
run times are in the session log (`docs/progress/2026-11-16-session13-log.md`). The lead wrote nothing in the tree
between the launch and the last report.

An interruption, disclosed. The reviews were launched on 2026-11-17 at 03:03:31Z. Referee A finished at 03:14:59Z.
Referees B and C were stopped at about 03:15Z to 03:16Z when the account's usage limit was reached, and so was the
lead; the session's machine restarted at least twice before the lead resumed on 2026-11-19 at 09:03Z. The
repository was unchanged (HEAD 9d9b231, clean tree, equal to the pushed branch) and the referees' directories were
intact. The lead resumed B and C by message with the same briefs; a new launch was not made, so each of the two
kept its own earlier context. B reports that all six items of its brief had run before the interruption and that
it re-ran them afterwards with identical outputs; C's report separates what it checked before and after.
By the house rule a launch with no recorded finish is dead and is relaunched; here the lead resumed instead,
because the tree was unchanged and the referees' files were complete enough to continue. A reader who wants the
stricter reading should treat B and C as one review each that took two days of wall time.

Isolation (lesson 61). Each referee had its brief, working directory and report in a directory of its own outside
the lead's scratch; the brief listed six permitted git commands and the paths that may be read. Isolation was
still by instruction only; none of the three reports a departure.

## Verdicts

| | A (fidelity) | B (soundness) | C (adversarial) |
|---|---|---|---|
| VC2-S | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| VC2-A | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| VC2-N | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| VC2-K | FAITHFUL, full | SOUND | no regime found in which the statement fails |

Records, by C: accurate in every number, hash, count and time it recomputed (19 items); overstated in wording in
four places. No BLOCKER and no MAJOR from any of the three. A: 3 MINOR, 4 NIT. B: 0 MINOR, 4 NIT. C: 6 MINOR,
9 NIT. No finding is against a proof or a statement.

What the referees did themselves, by their reports. A: each theorem's type is the bare frozen constant with no
universe parameter; the three axioms; no shadowing definition; the statement file equal at four commits, in the
manifest and in the index; the three tokens of the statement stamp; the four commitments recomputed from the built
environment; a fresh elaboration without the library gives the same terms. B: all eight proof files read in full
and recompiled as they are; `leanchecker` exit code 0 on ten modules; the closure of the four theorems at module
and at declaration level; the numerical part recomputed in exact rationals (moments, five coefficients, six cells,
largest end value 3.472924); each blueprint proposition non-vacuous; `w` in `Vdc2OneSideFacts` is produced before
the side; the interface checks reproduced byte for byte. C: the ten sources recompiled with a negative control that
fails as it should; both stamps (six tokens) and both manifests against their commit trees; no blueprint, assembly
or part file in the history before the stamp of the answers; certified numerics against the Lean text; a mutation
study of the profile (below).

Not checked by any of them: a clean rebuild, the comparator, independent kernels (the isolated replay does these);
the literature (nobody here has read the papers the constant is attributed to).

## Findings and answers

| # | Finding (in the lead's words) | Severity | Answer |
|---|---|---|---|
| 1 | The decimal 3.3643… of the sharp constant is given under "proved in Lean" in the README, the STATUS row and two annotations, and it is not a theorem of the library: in Lean, 335007/100000 ≤ A(441/200) and A ≤ 7/2 on [0, π]; the decimal is ball arithmetic and floating point outside Lean. (A, C) | MINOR | Accepted. The prose of the statements had said so; the summaries had not. README (bullet and row), STATUS (row and paragraph), CHANGELOG and the annotations of VC2-S and VC2-N now say "numerically 3.3643…; in Lean 3.35 < sup A ≤ 7/2". The lead had also said it without the caveat in chat and corrected it there. |
| 2 | "Classical" is stated flatly (STATUS, the header of the final file, the route, HANDOFF, the annotation "classical: Kershner"), where the project's own clarification c says that the attribution is cited from tables and titles, the originals are unread, and whether the classical theorem covers the class of VC2-S is not known to the lead. (A, C) | MINOR | Accepted; the error was on the modest side but it is a claim beyond the cited evidence. All five places now say: the constant is classical; the theorem is classical for f″ ≥ λ by citation, originals unread; for the class of VC2-S it is not known to the lead whether it is in print. No novelty is claimed in either direction. |
| 3 | The README row calls the constant "the largest modulus of a Fresnel partial integral"; clarification c had corrected exactly that (it is the two-sided integral; the one-sided maximum is 1.6822). (A, C) | MINOR | Accepted; corrected in the README row. HANDOFF did not carry the phrase (grep), contrary to the finding's second location. |
| 4 | STATUS says "no Lean proof text before the stamp of the review answers". The freeze commit holds Lean proofs of A(w) ≤ 26/5 for every w ≤ π (witness files of the plant runs), of A(1/2) ≤ 1 and of the instance w = 1/2 of VC2-A (first sanity layer); the HW paragraph discloses the like, the VC2 paragraph did not. (C) | MINOR | Accepted. STATUS now says "no Lean proof of the four statements as frozen" and names the three items (eight witness files and the two scripts that generate them, by grep); clarification g of the prose corrects "the layer proves no upper bound". No proof file imports or copies them (closure by B and C). |
| 5 | The pre-proof answers say that after a proof of VC2-N the gap of the undetected mutation "w only in [0, 441/200]" closes by itself. It does not: a witness needs A ≤ c with c below about 3.358, and the proof gives 7/2 (its cells reach 3.4729). (C) | MINOR | Accepted; the lead's sentence was wrong. The stamped answers are not edited; clarification g, item 2, corrects it. What the proofs settle is that the frozen statements are theorems. |
| 6 | No plant mutates the definition of the profile, on which three statements hang; the factor 2 replaced by 41/20 passes both sanity layers except for a script-only error, keeps VC2-S and VC2-N true and makes VC2-A false; the proof of VC2-A rejects it. Further true weakenings that no datum sees are listed (VC2-N and VC2-A for w ≤ 441/200 only; VC2-K with p fixed). (C) | MINOR | Accepted as a gap of the plant record, which is history and is not edited; clarification g, item 3. For the next batch: plants must also mutate every definition a statement uses (hand-off). |
| 7 | `docs/calibration.md` lists only the pre-proof referees of VC2. (C) | MINOR | It now lists every referee of the batch. |
| 8 | CHANGELOG: "two lemmas of batch S1"; four are used. (A, C) | NIT | Corrected. |
| 9 | "One line appended" to the file of VC3: two were (an empty line and the closing line). (A, B, C) | NIT | Corrected in the route and the integration record. |
| 10 | Annotation of VC2-K: "φ C² on [a, b]" is stronger than the Lean hypotheses. (A, B) | NIT | Replaced by the hypotheses as they are. The same words in the annotation of S1.2 are left for a separate pass over older rows. |
| 11 | `Vdc2Side.mono` in the assembly is used by no theorem and exists three times. (B) | NIT | Left in (no Lean change after the reviews beyond one comment); noted in the route. |
| 12 | STATUS says the hashes of the saved report summaries are in the session log; they are in the route. (C) | NIT | Corrected. |
| 13 | STATUS names only the paper proof in the phase variable as older than the freeze; its rewrite in x is older too. (C) | NIT | Added. |
| 14 | Route revision: "about 400 cells"; 262 suffice. (C) | NIT | Noted in the route with the referee's number; the lead has re-run neither count. |
| 15 | Second plant summary, case X1: 0.0173 should be 0.0167. (C) | NIT | Recomputed by the lead (2 sin(21)/100 = 0.016733); clarification g, item 4; the summary is history. |
| 16 | A closure taken through `import OscInt.API` shows a sanity module for VC2-S and VC2-K (an equation lemma of the profile). (C) | NIT | Explained in STATUS so that a later closure is not misread. |
| 17 | The integration record mixes tool output with the lead's own lines; `make quick` is only in the log. (C) | NIT | A note in the record says which is which. |
| 18 | The briefs name 7bb81e3 and "about 1400 lines"; the tree read was 9d9b231 and the eight files have 1267 lines. (A, B) | NIT | The launch row says "that commit plus this row"; the line count in the brief was the lead's estimate. |

## What is still not covered

The isolated replay (six kernels and the comparator) of the commit that holds these theorems; until it is recorded
the four rows say "proved in Lean". A human reader. A calibration of these referees. The literature: whether the
theorem for the class of VC2-S is in print. Plants that mutate the profile. The decimal value of the sharp constant
inside Lean.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
