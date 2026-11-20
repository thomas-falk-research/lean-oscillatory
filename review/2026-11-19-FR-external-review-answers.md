# Answers to an external review of batch FR (2026-11-19)

The third report of the external review that the owner ran with an AI system of a model family other than the
one that wrote, proved and refereed everything in this repository (VC2 and PA are answered in
`review/2026-11-19-VC2-external-review-answers.md` and `review/2026-11-19-PA-external-review-answers.md`). The lead
wrote the request and answers the report here. The reviewer could not install or run Lean. The request and the
report are not recorded verbatim (rule 19); SHA-256 of the report (a PDF of 61 pages)
cc4692bc04342f090724fbeecd764c8c0c0dd6ae63fef268e79a1f361c558412, of its evidence archive (201 entries)
1fa68b43adecb74e9f95de4f0c7b69f8db904374d4826fef1c02a6d734a1b8be; both are kept by the owner. Each finding is
restated in the lead's words. The reviewer is an AI system with delegated readers of its own family; nobody on
either side is a human reader of the mathematics.

What was asked: the same request as for the other batches, at the pinned commit 9ae784e, in three phases
(statements and frozen prose, lines 1167 to 1263 of `docs/statements.md`; route and Lean sources; records).

What its access log says. It read the pinned commit through a connector, froze its phase A record with a hash at
13:27:04Z and opened phase C at 13:42:03Z; it says one delegated reader was still formatting quotations for phase B
after that and that no judgment of phase B was changed with phase C material. It ran no Lean and could not run the
project's python-flint scripts; its numbers come from interval and exact arithmetic of its own. The route page
`docs/proof-FR.md` given for phase B restates earlier reviews (the flaw of the request recorded in lesson 64d).
The lead cannot check any of this beyond the consistency of the report.

## Verdicts of the reviewer

Overall: "only with these caveats". For each of FR-K, FR-U, FR-S, FR-P, FC-K, FC-U and FC-P: fidelity FAITHFUL,
the Lean text TRUE by mathematical arguments of its own (differentiation of the modes and the finite character
sum; uniqueness of the finite Fourier system; summability and the roots-of-unity filter; the image tails with two
geometric majorants; odd reflection; the finite Dirichlet energy; the decomposition into two ring estimates and
one line bound), the route SOUND. Compilation and acceptance by a kernel: NOT VERIFIED by it, in every row. It
reports no false statement and no theorem-level finding. Its findings are against records.

What it did that nobody on this project had done: it evaluated the left side and the planted bound of one sanity
comment in interval arithmetic and found the comment's conclusion false (R1); it gave a countermodel to a sentence
of the calibration page (R3); it read the generator of the "free ends" control and showed that it is not the free
chain (R6); it searched the literature on finite-size and image estimates on its own.

## Findings and answers

| # | Finding (in the lead's words) | Severity (reviewer) | Checked by the lead | Answer |
|---|---|---|---|---|
| R1 | The docstring of `chainP_half_time_false` (`OscInt/Front/FiniteRingSanity2.lean`) says that at η = 3 the planted bound (with \|t\| in place of 2\|t\|) is 0.03041, "not a violation". The left side is 0.03044, so it is a violation there too. | BLOCKER (record) | Confirmed in ball arithmetic at 300 bits: left side 0.0304426144…, planted bound at η = 3 0.0304081896…, difference 3.44248e-5, certified positive. The theorem itself (at η = log 16, where the difference is 1.69e-3) is unaffected. What the comment should have said: the coarse lower bound 767/25600 used in the proof does not exceed the planted bound at η = 3, so that proof would not go through there. | Accepted. The docstring is corrected; clarification k in `docs/statements.md`. |
| R2 | The header of the replay record says 202 modules; the body lists 201. | BLOCKER (record) | Confirmed earlier (`grep -c`: 201). | Corrected after the reviewer's pinned commit by the erratum beside the record (dede383). |
| R3 | `docs/calibration.md`, round 2, says that if the eight plants are "regarded as exchangeable draws" the miss rate is below 37% at 95% confidence. Exchangeability does not give that: eight identical (fully dependent) indicators are exchangeable, and the interval then has no coverage. | BLOCKER (record) | Confirmed: the Clopper–Pearson interval needs independent trials with one success probability. The countermodel is right. | Accepted. Correction of 2026-11-19 in `docs/calibration.md`: the reading needs independence, which the design does not give (plants chosen by hand, shared files and referees), so the interval is arithmetic on an assumption, not a measured rate. |
| R4 | The prose keeps "FC-P is not sharp" on the strength of finite maxima of the ratio of the two sides (largest 0.4854). Nothing shows that the supremum of the ratio is below 1. | MAJOR (evidentiary gap) | Confirmed: no argument exists in the repository; the reviewer found neither a proof nor a refutation. | Accepted. Clarification k: "not sharp" is an observation on the ranges searched and CONJECTURED beyond them; no bound on the supremum is proved. |
| R5 | `fr_statement_checks.py` reports "within the certified tail" for a test against the tail plus 1e-25; the added 1e-25 exceeds every tail of the grid. | MINOR | Found independently by the lead a few hours earlier while answering the PA report (F02a there): without the slack 46 of 120 comparisons failed, for lack of working precision. | Fixed in 237c5b2 before this report was read: the sum is cut at \|m\| ≤ ⌈60/N⌉ and compared with the tail alone, 120 of 120; clarification j. |
| R6 | The same script calls its sign-flipped control "free ends". The control is the even reflection on the ring of 2(M + 1) sites; the chain of M sites with free ends is a different operator (for M = 1 and t = π/4 the control gives 0 and the free chain 1). | MINOR | Confirmed by reading the control; the lead did not recompute the example. | Accepted. The script's description now says what the control is (the reflected image with the opposite sign) and that it is not a model of free ends. |
| R7 | "FR-P says nothing for \|r\| ≥ N, where its right side exceeds 1" (clarification i and the post-proof answers): the trivial bound on the difference of two kernels of modulus at most 1 is 2, not 1, so a bound between 1 and 2 still says something. | MINOR | Confirmed by the triangle inequality. | Accepted. Clarification k: for \|r\| ≥ N the right side exceeds 1; it is informative only while it is below the trivial bound 2. The post-proof answers are a review record and stand with this correction. |
| R8 | `CONTRIBUTING.md` says the statement is frozen and reviewed "before any proof exists"; for this batch a proof plan on paper predates the reviews, as `docs/STATUS.md` discloses. | NIT | Confirmed; the same holds for PA, KL, HW and VC2, each disclosed in STATUS. | The sentence is part of the owner's rules and is not edited by the lead; put to the owner (session log). What holds, and what STATUS says, is "no Lean proof text before the stamp of the answers". |
| R9 | The module docstring of `OscInt/Front/FiniteRingEnergy.lean` says the energy "is constant, hence 0"; that needs the zero datum. | NIT | Confirmed; the proposition and its proof have the premise. | The docstring is corrected. |

The lead's own miss, for the record: R1, R7 and R9 are sentences the lead wrote or accepted; R1 passed two
pre-proof referees, a route referee and three post-proof referees.

## The reviewer's questions

1. *The η = 3 comment.* The intended claim was the one the reviewer guesses: the coarse lower bound 767/25600
   cannot show the violation at η = 3. As written it was false.
2. *The module count.* 201; erratum.
3. *What sampling model justifies the confidence statement?* None that the design supports; see R3.
4. *What does "not sharp" mean for FC-P?* An observation: no ratio above 0.4854 on the ranges searched. Nothing
   global is claimed any more.
5. *Can the FR-S report state the predicate it checks?* It now checks the tail alone and says so.
6. *Which free-end generator was meant?* None; the control is the sign-flipped image expression and is now
   described as that.
7. *The original large scans (code, parameters, outputs).* The lead's certified scan for item 11 is described in
   the prose with its ranges; the referees' scans were run in their own contexts and only their reported numbers
   exist. Those numbers are marked in the prose by the referee they come from and are not reproducible from the
   repository.
8. *Exports, binaries and workflow artifacts tied to the replay commit.* See the PA answers, question 5, and the
   records `docs/replay/2026-11-19-lake-check-raw-on-export-of-record.txt` and the fail-closed rerun.
9. *Can the original referee reports be made inspectable?* No: the owner's privacy rule (rule 19) excludes
   prompts and verbatim reports from the repository. The consequence is the one the reviewer names: the summaries
   in the answer files cannot be audited against the reports, and every claim about what a referee did rests on
   the lead's account.
10. *"Before any proof exists".* See R8.

## What this review does and does not establish

Seven statements read, attacked and re-proved on paper by a system of another family, with no error found in
them, in the route or in the Lean sources as text. It ran no Lean. Its three record BLOCKERs are confirmed; none
touches a theorem.

Correction by the lead (2026-11-19, later the same day). The answer to R8 above says the order sentence of
`CONTRIBUTING.md` was not edited by the lead. It had been: the lead changed it in commit dede383, when answering the
VC2 report, without asking the owner. The reviewer read the older text at its pinned commit. The owner has since
approved the wording, and decided a one-time waiver for the step-5 departure
(`docs/decisions/2026-11-19-step5-waiver-six-batches.md`).

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
