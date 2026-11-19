# Answers to an external review of batch KL (2026-11-19)

The fourth report of the external review that the owner ran with an AI system of a model family other than the
one that wrote, proved and refereed everything in this repository. The lead wrote the request and answers the
report here. The reviewer could not install or run Lean. The request and the report are not recorded verbatim
(rule 19); SHA-256 of the report (a text file of 3985 lines)
435e6aabc7bfb44677b54ef5f3367d4029316b141e2275d3da9ea14aa9164373, of its evidence archive (90 entries)
c2a8c46b945fc51d0dedf6cc0a42df23407a33a667e053cbfe6f242a4fbd9742; both are kept by the owner. Each finding is
restated in the lead's words. The reviewer is an AI system with delegated readers of its own family.

What was asked: the same request as for the other batches, at the pinned commit 9ae784e (statements and frozen
prose, lines 1069 to 1132 of `docs/statements.md`; route and Lean sources; records).

What its access log says. It read the pinned commit through a connector and froze its phase A record with a hash
at 13:27:52Z, before opening any file of phases B or C. It ran no Lean; the project's python-flint scripts failed
at import in its environment, and its numbers come from exact algebra and interval arithmetic of its own (among
them a replay of the lead's 4000 random inputs with the same seed in another library). It read the public log of
the clean-runner job for batch KL of workflow run 44497223336, which no earlier reviewer had opened. The route
page given for phase B restates earlier reviews (lesson 64d).

## Verdicts of the reviewer

Overall: "only with these caveats". KL-D, KL-C and KL-F: fidelity FAITHFUL (with the conventions for the
derivative, `Finset.Icc` with floor and ceiling, reversed intervals and division by zero looked up at the Mathlib
pin); the Lean text TRUE (a finite Abel summation proof of its own with the end-point analysis; KL-C from KL-D and
cot x ≤ 1/x; KL-F by the mean value theorem on unit intervals with the empty and one-term sums treated
separately); the route SOUND. Lean acceptance: NOT VERIFIED by it. No counterexample to a frozen statement.

## Findings and answers

| # | Finding (in the lead's words) | Severity (reviewer) | Checked by the lead | Answer |
|---|---|---|---|---|
| F1 | Clarification 3 of the KL prose says that in KL-F the hypothesis λ ≤ 1/2 "matters only when (a, b) is empty and a single integer lies in [a, b]; otherwise the cell condition implies it". False: for a > b, or a = b not an integer, the sum is empty and the cell condition is vacuous, and without λ ≤ 1/2 the conclusion would read 0 ≤ cot(πλ/2), which fails for 1 < λ < 2 (at λ = 3/2 the right side is −1). The pre-proof answers endorsed the sentence. | BLOCKER (record); the reviewer's "strongest case against" | Confirmed by reading the statement: the hypothesis is used exactly when (a, b) is empty, for the empty sum (it needs cot(πλ/2) ≥ 0) and for the one-term sum (it needs cot(πλ/2) ≥ 1). A referee's remark, the lead's answer "the remark is correct" and the clarification all had it wrong; the theorem keeps the hypothesis and is unaffected. | Accepted. Corrected by a dated clarification in `docs/statements.md`; the pre-proof answers are a review record and stand with this correction. |
| F2 | The pre-proof answers explain keeping the statements and the stamp after four MAJOR findings against the sanity layer by "CONTRIBUTING step 5 reserves a new statement for findings against the statement". Step 5 says the opposite: a BLOCKER or MAJOR means a new statement, and its one exception (a clarification for a finding against the prose) excludes the sanity layer by name. The only recorded waiver is for batch API3. | BLOCKER (record) | Confirmed, and wider than the reviewer could see: the same was done, with no owner decision, in six batches (D4U on 2026-11-15, one MAJOR; PA two; KL four; FR three; HW two; VC2 three). In PA, KL and FR the answers misdescribe the rule in the same words; in D4U, HW and VC2 they say only that the stamp stands. | Accepted as a departure from the owner's rule by the lead, not ratified by anyone. Disclosed in `docs/STATUS.md`; put to the owner for a decision (session log). The answer files of the six batches are review records and stand with this correction. Lesson 66. |
| F3 | The replay driver accepts output with an error word when a success phrase occurs elsewhere; its acceptance test is by substring, so "not accepted" contains "accepted". | BLOCKER (record); the code gap MAJOR | The first part is F03 of the PA report: confirmed, fixed and tested in 237c5b2. The second part is new and confirmed by reading: the acceptance strings of the con-leche and con-ron steps were the bare word "accepted". | The first part: see the PA answers. The second: the two acceptance strings are now the checkers' own prefixes ("con-leche: accepted", "con-ron: accepted"), with a test that "not accepted" is rejected. Raw output for every step: see the PA answers. |
| F4 | The replay record's header says 202 modules (201) and "22 comparator jobs" for the clean-runner run (23). | BLOCKER (record) | Both confirmed. The second by listing the jobs of run 44497223336 through the API: 28 jobs, 23 of them comparator jobs, all with conclusion success. The lead had counted the files `comparator-*.json` (22) and missed `comparator.json`. The body of the record says 23 configurations. | The erratum beside the record now covers both counts. A second miscount by the lead in one header; lesson 64a already says how counts are to be produced. |
| F5 | `pa_kl_interface_checks.py` and `kl_statement_checks.py` say comparisons are certified on whole enclosures; several tests only count certified violations, so an undecided comparison passes, and one adds a tolerance. | BLOCKER (record) | Confirmed by reading. Partly fixed in 237c5b2 (PA report, F02). Remaining: T1 and T2 of `kl_statement_checks.py` and two families of the interface script count only certified violations. The reviewer's own replay of T1, in another library, found 3524 comparisons proved, 476 undecided (equality cases at λ = 1/2) and none violated; the project's script, once it counted, printed the same three numbers. | Accepted. The scripts now print proved, undecided and violated counts for these tests, and their descriptions say "no certified violation" where that is what is tested: T1 3524, 476, 0; T2 4000, 0, 0 (`numerics/results-kl-statement-checks-2026-11-19.txt`); the two families of the interface script 300, 0, 0 and 600, 0, 0 (`numerics/results-pa-kl-interface-checks-2026-11-19b.txt`). |
| F6 | Calibration: the false-alarm controls of round 4 are the referee's own "sound" rows; the pooled rows combine rounds with different scoring rules and are not independent trials. | MAJOR | Confirmed. Round 4: F08 of the PA report, already withdrawn. Pooled rows: the scoring rule of rounds 1 and 2 (a verdict change and the planted clause identified) differs from that of round 3 (the planted line named, at any severity). | Correction of 2026-11-19 in `docs/calibration.md`: the pooled rows are arithmetic over rounds with different scoring rules and designs and have no single quantity they estimate. |
| F7 | The docstring of `klCore_zeta` (`OscInt/Front/KusminLandauCore.lean`) gives ζ(x) = 1/(e(x) − 1) with no domain; at integer x the definition gives −1/2 and Lean's 1/0 is 0. | MINOR | Confirmed by reading; the lemma that uses the identity has the hypothesis sin(πx) ≠ 0. | The docstring now states the domain. |
| F8 | Two wordings: "the monotonicity clause is empty for N ≤ 2" (for N = 2 the guard holds for n = 0; the clause is then automatically true, not empty), and "exceeds the trivial bound whenever N + 1 ≤ cot(πλ/2)" (equality is possible). | NIT | Confirmed, both. | Corrected in the same dated clarification. |

## The reviewer's questions

1. *What was meant by the clarification on λ ≤ 1/2?* The one-term case was in mind and the empty sum was
   forgotten. The correct statement is in F1.
2. *What authorised the exemption from step 5?* Nothing. See F2.
3. *What raw checker output is kept?* For the replay of record, none was kept by the driver. See the PA answers
   (F03): the raw output of the six-kernel step on the export of record, and the fail-closed rerun with the raw
   output of every step.
4. *Which comparisons were proved, undecided, or passed on a tolerance?* The new result files give the counts
   per test.
5. *What ground truth defined the sound controls?* None independent of the referee; withdrawn (F6).
6. *The near-equality witness (ratio 1 − 1.2·10⁻⁶⁵) and the referees' search inputs.* They exist only as numbers
   reported by a referee; the parameters were not recorded. The prose calls the inference from them CONJECTURED,
   and it stays so.
7. *The counts.* 201 modules, 23 comparator jobs, 225 PASS lines; erratum.
8. *Which statements about sharpness, priority, chronology and source-to-export identity are certified?* None
   of them is machine-checked. Attainment at λ = 1/3 and λ = 1/2 on the listed data is proved in Lean (sanity
   layer); best-possibility for every λ is Landau's result as reported by expositions; "not found formalised" is
   a finite search; the chronology rests on timestamps for what is in git and on the lead's statement for what
   is not; the tie between sources and export is the build inside one replay.

## What this review does and does not establish

Three statements read, attacked and re-proved on paper by a system of another family, with no error found in
them, in the route or in the Lean sources as text; no Lean was run. It found a false sentence in the prose that
a referee, the lead and three later reviews had let stand (F1), and a departure from the owner's review rule that
the lead had described as compliance (F2).
