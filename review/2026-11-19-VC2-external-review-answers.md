# Answers to an external review of batch VC2 (2026-11-19)

The first review of this repository by a model of a different family from the one that wrote, proved and
refereed everything else. The owner ran it; the lead wrote the request and answers the report here. The reviewer
could not install or run Lean. The request and the report are not recorded verbatim (rule 19); SHA-256 of the
report (a PDF of 43 pages) 16b42e8e22c056f1200595becfc607948c35538d765f82b31f78f37d30132649, of its evidence
archive (103 files: its scripts with their outputs, copies of the sources it read)
781a06afaf1f4085d0577c1d57c6722899b0365ea74ee114ac7e8aef40a16ec7; both are kept by the owner. Each finding is
restated in the lead's words. Nobody on the project's side is a human reader of the mathematics; the reviewer is an
AI system too.

What was asked. One batch, at the pinned commit 9ae784e, in three phases: (A) the statements and the prose as
frozen, with its own reading, refutation attempts and literature search written and frozen before anything else is
opened; (B) the proof route and the Lean sources, read as text; (C) the records and the earlier reviews. Rules of
evidence: every file relied on read in full and quoted; every Lean convention looked up in the Mathlib source;
every number from code shown; every citation labelled by how it was read. No verdict of an earlier review and no
known weak point was in the request.

What its access log says, and what the lead makes of it. It read the pinned commit through a connector (direct
raw access failed), the statement files and the 65 requested lines of the prose in phase A, froze eight files with
hashes before phase B, and opened phase C thirteen minutes later. It discloses one exposure that is the lead's
doing: the route page `docs/proof-VC2.md` was on the list for phase B and its later sections restate findings of
earlier reviews. Its phase A record predates that. Blindness is otherwise by its own account; the lead cannot
check it. It used delegated readers and says which files the root read itself.

## Verdicts of the reviewer

Overall: "only with these caveats". Per statement, three verdicts each.

| | Fidelity (Lean text against prose) | Truth of the Lean text | Proof route |
|---|---|---|---|
| VC2-S | faithful, at the level of the source and the Mathlib interfaces it checked | verified mathematically through V1 to V6 | sound; no missing hypothesis or false intermediate proposition found |
| VC2-A | faithful to the one-sided inequality | verified independently (projection and evenness) | sound |
| VC2-N | faithful | verified independently, by a certificate of its own (a degree-five sine bound and 256 exact Bernstein cells), and again with the certificate of the Lean source | sound with the certificate of the source; the route's paragraph alone was incomplete |
| VC2-K | faithful after unfolding the S1 definitions | verified mathematically from VC2-S and VC2-N, Darboux, the mean value inequality and integration by parts | sound |

In each row it adds: that the Lean files elaborate and that a kernel accepted them is NOT VERIFIED by it. The
caveats it attaches to relying on the batch: the replay is archived evidence, not something it ran; a count in the
replay record's header is wrong; two diagnostic scripts did not fail the process on a failed check; the preprint
and the published version of one cited paper must be told apart; the classical attribution rests on unread
originals; the decimal of the sharp constant is not a Lean theorem; reviews by one model family, timestamps and
the calibration of other batches are not a measure of correctness or independence for this batch.

What it did that nobody on this project had done. It read the published version of Rogers's paper (by its
account, in an extracted text) and compared it with the arXiv preprint; it certified VC2-N by a route that shares
nothing with the proof; it tested VC2-S on a family of phases whose derivative is unbounded at an end point
(f(x) = x²/2 − c√x), in exact arithmetic; it read the definitions of exp, sin, cos, π, the interval integral,
`Real.sqrt`, real powers and the complex norm at the Mathlib pin and quoted them; it showed by exact arithmetic
that the mutation "factor 2 of the profile replaced by 41/20" keeps VC2-S and VC2-N true and makes VC2-A false.

## Findings and answers

The reviewer's severity is given first; where the lead's differs, it says so.

| # | Finding (in the lead's words) | Severity | Checked by the lead | Answer |
|---|---|---|---|---|
| F01 | `docs/prior_art.md` said "Rogers did not know it: his LaTeX source does not cite Kershner". That holds for the preprint of 2003; the published paper of 2005 credits Kershner for the sharp constant at n = 2 (p. 3549). What an author knew cannot be read off a preprint. | MINOR | The arXiv record has one version (3 November 2003); its HTML has no "Kershner" in text or bibliography and says that numerical experiments suggest the value (fetched for the lead on 2026-11-19). The published text could not be opened by the lead: the page the reviewer used returned no text to the lead's fetch. | Accepted. The paragraph is rewritten to say what each version says and who read what; the inference is withdrawn. The reviewer's reading of the published page is recorded as its reading, not the lead's. |
| F02 | `numerics/review/vc2_statement_checks.py` prints FAIL lines and "SOME FAIL" and still exits with code 0. | MINOR | Confirmed by reading; six more scripts of the same shape found (FR, HW, PA/KL interface, and three older ones). | Accepted and fixed in all nine: a failed check now fails the process. Each still exits 0 on today's run; two were run with a check forced to fail and exit 1. No workflow or Makefile target calls these scripts, so no gate ever relied on the exit code. |
| F03 | `numerics/review/vc2_interface_checks.py`: the last check (the grid maximum of A) does not enter the exit code. | MINOR | Confirmed. | Fixed; a forced failure of that check now exits 1. New results file `numerics/results-vc2-interface-checks-2026-11-19.txt`. |
| F04 | The header of the replay record says per-module leanchecker ran on 202 modules; the log lists 201, and the 202nd line is the export check. | BLOCKER for record accuracy only | Confirmed: `grep -c` gives 201. The lead had counted lines whose second word is "leanchecker". | Accepted; the lead's error. The record is stamped and is not edited: `docs/replay/2026-11-19-session13-verify-all.erratum.txt`, and a correction row in the session log. No module is missing. |
| F05 | `CONTRIBUTING.md`: "a reader checks the kernel, three axioms, and a short frozen statement, and nothing else", and "frozen and reviewed before any proof exists", say more than holds: the reader also trusts the definitions and the pinned environment, and for VC2 a proof on paper and Lean proofs of special cases are older than the freeze. | MINOR (scope of wording) | Confirmed. | Both sentences reworded. |
| F06 | The grid of that script is called "step 0.001"; it has 3142 points with spacing π/3141. | NIT | Confirmed. | Label corrected. |
| F07 | The frozen prose calls the existential form of VC2-S "strictly stronger" than the bound with sup A; it is equivalent. | BLOCKER as a preserved record error, RESOLVED | Already clarification a (2026-11-17). | Nothing to add. The reviewer found it in phase A without knowing the clarification, which is the kind of agreement the phases were for. |
| F08 | The docstring of `vdc2Profile` in the frozen file does not describe the definition (at w = 1/2, A ≤ 2/3 while the largest real part over rotations is at least 39/20). | BLOCKER as a preserved description error, RESOLVED | Already clarification b. | Nothing to add; the frozen file is not edited. |
| F09 | The route's V8 names no cells: as a standalone argument it has a gap. The Lean source closes it. | MAJOR for the route alone, CLOSED in the source | The lead recomputed the six cells in exact rationals: largest end value 3.4729240977…, 0.0270759… below 7/2. | Accepted. The route now carries the certificate (`docs/proof-VC2.md`, "Corrections after the external review"). |
| F10 | V4's "2πn" in the induction step and the prose's "within 6 %" (which denominator?) are under-explained. | NIT | Confirmed. | Route correction (2); clarification h (1) of the prose. |

## The reviewer's questions

1. Which theorem of Kershner covers the increment formulation? Not known; nobody here has read Kershner. The
   uncertainty stays in STATUS. For this class the evidence is the Lean proof and, now, the reviewer's
   reconstruction.
2. Preprint against publication: done (F01).
3. What consumes the scripts' exit codes? Nothing automated; they were run by hand and their output read. They now
   fail properly (F02, F03).
4. The count 202: answered (F04).
5. A durable bundle with checker revisions, raw axiom output, exports and comparator inputs: the replay log names
   the checkers and prints the hashes of the exports; the exports themselves and the per-theorem axiom output are
   build products that are not archived. That is a gap; it is recorded in the hand-off, not closed here.
6. The slogans in CONTRIBUTING: scoped (F05).
7. A journal-facing account of A, of attainment and of the constant of VC2-K: clarification h (2).
8. Which historical claims are the author's attestation only: the STATUS paragraph of the batch says which
   (no Lean proof text outside git before the stamp; blindness; run times).
9. The long decimal of the maximum: it rests on ball arithmetic by an earlier referee outside Lean, whose code is
   not in the tree. It is advertised nowhere as a theorem; if it is ever wanted as one, it needs a statement of its
   own.
10. V8 and the shorthand: done (F09, F10).

## What this review does and does not change

It adds one reading by a different model family, with its own computations, to five same-family reviews. It does
not make the batch human-reviewed, it ran no Lean, and one review of one batch is not a calibration. The statement
"every referee is of one model family" in the STATUS paragraph of this batch is amended to say so. Its strongest
objection stands and is not answered by any fix: a kernel can accept a proof of a proposition that is not the
intended one, and reviews do not remove that risk; what reduces it is that the reviewer read the definitions and
found the four statements to mean what the prose says.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
