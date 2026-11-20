# Answers to the post-proof reviews of batch HW (HW-R, HW-K, HW-D, HW-L)

Three fresh-context referees read the integration commit 6533583 (the tree they saw is a11b0a6, which adds one
log row): A fidelity, B soundness, C adversarial. All three are AI agents of the same model family as the lead and
the provers; no calibration copy with planted errors was run for this batch (`docs/calibration.md`). Their briefs
and reports are not recorded verbatim (rule 19); the SHA-256 values of the brief files and of the report files and
the run times are in the session log (`docs/progress/2026-11-16-session13-log.md`). The lead wrote nothing in the
tree while they ran.

What "fresh-context" did and did not mean here (referee C, MINOR 3, accepted): the three referees ran on the lead's
machine, with the lead's scratch directory readable, including the paper route, every brief, the reports of the
earlier referees and each other's working directories; they were not told to stay out of it. C reports that it
could read all of that and opened none of A's or B's files. The same held for the blind pre-proof referees and for
the four provers. Isolation was by instruction, not by a sandbox. From the next round on, packets are snapshots
outside the scratch tree and the brief says so (`docs/lessons.md`, 61).

## Verdicts

| | A (fidelity) | B (soundness) | C (adversarial) |
|---|---|---|---|
| HW-R | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| HW-K | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| HW-D | FAITHFUL, full | SOUND | no regime found in which the statement fails |
| HW-L | FAITHFUL, full against the prose (finite support only, as modelling choice 5 says) | SOUND | no regime found in which the statement fails |

Records: ACCURATE (C). No BLOCKER and no MAJOR from any of the three. A: 1 MINOR, 5 NIT. B: 1 MINOR, 2 NIT.
C: 4 MINOR, 8 NIT. No finding is against a proof or a statement; one Lean docstring and two Lean file headers
change (comments only).

What the referees did themselves, by their reports. A: each theorem's type is the bare frozen constant, with no
universe parameter; axioms propext, Classical.choice, Quot.sound; no shadowing definition; the statement file equals
the stamped one (manifest, statements index, git blob); the three RFC 3161 tokens of both stamps verify; the built
constants equal a fresh elaboration of the stamped file. B: the whole batch recompiled from source in its own
directory (statements, first sanity layer, blueprint, six proof files); the ten final and part theorems on the three
axioms; a negative control that fails as it should; `leanchecker` exit code 0 on two modules; no forbidden construct;
each of the five blueprint propositions non-vacuous; the interface checks reproduced byte for byte. C: the kernel
from the Lean definition by rigorous integration at 20 points against the exact recursion; HW-R as integer
identities at every site for t ≤ 400; HW-K and HW-D certified at every site for every t ≤ 3000 (smallest ratio of
bound to supremum 14.50 for the kernel; largest amplitude 1.62085 t^{−1/3}); all six tokens; both manifests against
their commit trees; no proof text of the batch in the history before the stamp of the answers.

Not checked by any of them: a clean rebuild, the comparator, independent kernels (the isolated replay does these);
the cited papers; the timestamp authorities' roots against the outside world. That no proof was drafted outside git
before the stamp remains the lead's word.

## Findings and answers

| # | Finding (in the lead's words) | Severity | Answer |
|---|---|---|---|
| 1 | The records say HW-R rests on six lemmas of the first sanity layer. That is the direct count. The closure of the proof holds thirteen theorems of that layer and one of the sanity layer of batch GD (`GlobalSanity.integral_exp_int_mul`), named in no HW record; HW-D and HW-L inherit all fourteen; and "four identities of the dispersion relation" is wrong (one is; the others are Euler's formula and two non-vanishing facts). Found by A (NIT), B (MINOR) and C (MINOR), each from its own closure computation. | MINOR | Accepted; the lead had counted the names the part cites and had not computed the closure. STATUS ("Batch HW, what the rows rest on") now lists the fourteen and says which statements inherit them; the route and the CHANGELOG are corrected. The lemmas are not copied into the part: they are kernel-checked theorems, and what matters for the order claim is that they existed before the freeze, which STATUS says. There is no machine-read dependency list in this repository that would mark the three rows stale when one of the fourteen changes; that is a gap, noted in the hand-off. |
| 2 | README, the API index and the consumer example do not say where the bounds have content: HW-K is implied by the L¹ bound 1.18034 of the kernel for t ≤ 1679; HW-D and HW-L by conservation of the ℓ² norm for t ≤ 59319; the consumer's probability bound 6084 t^{−2/3} is below 1 only for t > 474552, a number recorded nowhere. (C) | MINOR | Accepted. The lead recomputed the three thresholds (1680 and 1.18034 by quadrature in 30 digits; 39³ = 59319; 78³ = 474552) and added them to the README row and bullet, the three annotations, the consumer header, the CHANGELOG and STATUS. |
| 3 | Isolation of referees and provers is by instruction only. (C) | MINOR | Accepted; see the second paragraph of this file, STATUS and lesson 61. |
| 4 | The record of the parts is thinner than it reads: the reports of HW1 and HW2 were returned as text and not saved, so two rows of the "Deviations" column have no recoverable source, and "no agent reported a git command" rests on them; three of the four part files were single writes. (C) | MINOR | Accepted. The route's "Parts as integrated" now says so. No Lean change. |
| 5 | README row of HW-L omits "finite support". (A) | MINOR | Accepted; added. The Lean statement, STATUS, the docstrings and the annotation had it. |
| 6 | "machine-checked as stated since v0.1": the first release is v0.2.0. (A) | NIT | Corrected in STATUS and the route. |
| 7 | Two annotations quote 0.95 and 1.61, numbers that clarification b had corrected. (A) | NIT | Replaced by the numbers of clarification b. |
| 8 | README dates the blind review to 2026-11-16; it ended on the 17th. (A, C) | NIT | Corrected. |
| 9 | `docs/calibration.md` names only the pre-proof referees of HW. (A, C) | NIT | It now names the route referee and this round. |
| 10 | "margin 0.13 %" in the parts table is the margin of the squared inequality; as written it is 0.065 %. (B, C) | NIT | Corrected (recomputed: 0.0650 % and 0.1301 %). |
| 11 | The docstring of `hwKB_num_one` says "this is" for an inequality that is slightly stronger than the one it names. (B) | NIT | Docstring changed to "with (3√3/2)^{1/2} ≤ 50/31 this gives …". The part file is therefore no longer byte-identical to the delivery; the route and the integration record say so and give the new SHA-256. |
| 12 | STATUS: "existed by 22:58:03Z"; one of the three tokens says 22:58:04Z. (C) | NIT | Corrected. |
| 13 | The plant summary and item 8 of the prose call "HW-K without 1 ≤ t" a true weakening; it is an equivalent statement. (C) | NIT | The plant summary and the stamped prose are history and are not edited; clarification g of `docs/statements.md` says it. |
| 14 | Both plant runs mutate HW-D and HW-L in both components at once; one-sided plants were not run (the data at t = 1 and t = 3 would refute them). (C) | NIT | Accepted as a limit of the plant record; not run. The proofs close the gap for the statements as frozen. |
| 15 | Wording stronger than "one model family": the header of the final file ("refereed"), and "independently" in clarification f. (C) | NIT | The header now says who read the route; clarification g says what "independently" meant. |
| 16 | The session log does not mention the stash of 01:06:51Z after the second restart. (C) | NIT | A log row now does (the lead confirmed the dangling commit: records and stamp files, no Lean). |

An incident, reported by referee C itself: at 02:09:50Z it ran `git fsck --lost-found`, which writes: it created a
directory of 41 files under `.git`. No ref, index entry or tracked file changed. The lead looked at the directory
(two subdirectories, 1.4 MB) and removed it before writing these answers. The brief allowed read-only git and did
not list the allowed commands; lesson 61.

## What is still not covered

The isolated replay (six kernels and the comparator) of the commit that holds these theorems; until it is recorded
the four rows say "proved in Lean". A human reader. A calibration of these referees. One-sided plants of HW-D and
HW-L. The conjecture |K(t, x)| ≤ t^{−1/3} (clarification f) is open.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
