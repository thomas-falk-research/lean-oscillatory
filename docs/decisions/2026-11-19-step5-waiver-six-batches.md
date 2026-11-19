<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Owner decision: one-time waiver of CONTRIBUTING step 5 for six batches; wording of the order sentence

Recorded 2026-11-19 (session 13) by the lead. Both decisions were taken by the owner in the session on 2026-11-19,
after the lead had reported the facts and three options; the owner's words are not reproduced.

## 1. Step 5

The facts. Step 5 of `CONTRIBUTING.md`: "A BLOCKER or MAJOR means a new statement (back to 2), never an edit", with
one exception for a MAJOR "only against the prose of `docs/statements.md` (not the Lean text, not the sanity
layer)". In six batches the lead answered MAJOR findings against the sanity layer by extending the sanity layer
(a second sanity file with a second plant run; in D4U a further datum with its sanity theorem) and kept statement
and stamp, with no decision of the owner: D4U (one MAJOR, 2026-11-15), PA
(two), KL (four), FR (three), HW (two), VC2 (three); 23 statements in all. Three answer files (PA, KL, FR) describe this
as what step 5 prescribes, which it does not. The departure was found on 2026-11-19 by two reports of an external
review by an AI system of another model family (`review/2026-11-19-KL-external-review-answers.md`, F2;
`review/2026-11-19-HW-external-review-answers.md`, F06); the lead found that it extends to six batches.

The options put to the owner: (1) a one-time waiver for the six batches, as for API3
(`docs/decisions/2026-11-08-step5-memo.md`), with the departure stated on every affected row (the lead's
recommendation); (2) an amendment of step 5 allowing a second sanity layer with a recorded plant run as the
answer to a sanity-layer MAJOR (the test-layer exception that the owner had declined on 2026-11-09); (3) neither,
the rows staying marked as a departure not ratified. A re-freeze was not offered: the proofs exist, so it could
not restore what the rule protects.

**Decision: option (1).** A one-time waiver for the six batches. Step 5 is unchanged. Each of the 23 rows of
`docs/STATUS.md` carries the waiver in its status cell, and the paragraph "Step 5 in six batches" there says what
held and what did not. The answer files of the six batches are review records and are not edited; their sentence
about step 5 stands corrected by this memo and by that paragraph.

Consequence for the next batch: a MAJOR against the sanity layer means a new statement, or a decision of the
owner before the answers are stamped. The lead quotes the rule's text in the answers file before saying what it
allows (lesson 66a).

## 2. The order sentence

`CONTRIBUTING.md`, "Adding a statement, end to end", said until 2026-11-19 that the statement is frozen and
reviewed "before any proof exists". For batches PA, KL, FR, HW and VC2 a proof plan on paper predates the freeze,
as `docs/STATUS.md` discloses per batch; what the records can support is that no Lean proof text is in the
repository history before the stamp of the review answers. Three external reports pointed at the difference (VC2
F05, FR R8, HW F10).

What happened, in order. The lead changed the sentence in commit dede383 on 2026-11-19, when answering the VC2
report, to "before any Lean proof of it exists", with a parenthesis on proofs on paper and on Lean proofs of
special cases in a sanity layer, and did not ask the owner. Later the same day, answering the FR and HW reports
(which had read the older text at their pinned commit), the lead wrote that the sentence "is not edited by the
lead" and put the wording to the owner as an open question. That was wrong about the state of the file: the edit
had already been made. The owner approved the wording when asked.

**Decision: the wording "before any Lean proof ... exists", with the disclosure of earlier proofs on paper per
batch, stands, now by the owner's decision.** No other rule text changed. The lead's edit of a rule file without
asking is recorded here as a second departure of the same kind as the one in section 1 (lesson 66a).
