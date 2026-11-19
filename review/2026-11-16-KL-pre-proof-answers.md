# Answers to the blind pre-proof reviews of batch KL (KL-D, KL-C, KL-F)

Two fresh-context referees read the frozen batch at acc035d (stamp `stamps/20261116T130956Z-276d8d7f9605`, which is on
the statements commit 276d8d7; acc035d adds the pins and records), before any Lean proof of these statements existed
anywhere. Referee A checked fidelity; referee B tried to refute the Lean text with its own code. A third referee
reviewed a copy with four planted errors (calibration, `docs/calibration.md`, round 3).
- All three are Claude instances, like the lead; "fresh-context" does not mean a different model family or a human.
- Their briefs and reports are not recorded (privacy rule 19); the briefs' SHA-256 are in the session log
  (`docs/progress/2026-11-16-session13-log.md`). Each finding is restated below in the lead's words.
- The tree was frozen from the launch until the last referee of either batch had ended: the lead made no commit and
  wrote no file into the tree in that window (the session log and git show this; the lead worked in scratch).
- What the referees compiled. Referee A elaborated the frozen definitions and compiled witnesses that *mutated*
  copies of the statements are false; it proved nothing about the statements themselves. Referee B ran no Lean.
  Neither outlined a proof route. Referee A ran `git status --porcelain` once, against its brief, and said so; it
  changes nothing.

| Referee | Reviewed | Launched (UTC) | Finished | Run time (harness record) |
|---|---|---|---|---|
| A (fidelity) | acc035d | 13:19:47 | before 13:39:34 | 923 s |
| B (truth) | acc035d | 13:19:47 | before 14:00:38 | 1961 s |
| calibration copy | planted snapshot of acc035d | 13:19:47 | before 13:28:02 | 475 s |

The launch time is the lead's clock when the launch calls returned; the finish times are upper bounds from the
lead's scratch event log.

## Verdicts

| | Referee A (fidelity) | Referee B (truth) |
|---|---|---|
| KL-D | FAITHFUL | no counterexample (about 1.7·10⁹ sequences screened, about 108,000 decided in ball or exact cyclotomic arithmetic) |
| KL-C | FAITHFUL | no counterexample (largest ratio of the two sides 1 − 8.2·10⁻¹¹, at λ = 1/100001) |
| KL-F | FAITHFUL | no counterexample (36,000 piecewise-linear derivatives, 600 smooth phases, 84 ramps) |

No BLOCKER. Four MAJOR (referee A), all against the sanity layer and the plant record, none against the Lean text
or the prose. The statements and the stamp stand. The MAJORs are answered by a second sanity file and a second plant
run, committed with this file (below), not by a re-freeze: the statement text is untouched, and CONTRIBUTING step 5
reserves a new statement for findings against the statement.

Referee B's evidence on sharpness, which the prose relies on: the ratio |S|/cot(πλ/2) is exactly 1 on about 75,000
sequences, all with λ = 1/2 or λ a fraction with odd numerator and denominator, and below 1 otherwise, as Landau's
theorem says; Cheng and Graham's bound 1/(πλ) + 1 was violated 703,388 times in the same search.

## Findings and answers

**A1 (MAJOR, sanity layer). The monotonicity guard is not pinned.** Changing `n + 1 < N` to `n + 2 < N` in
`DiffsMonotoneIn` leaves every sanity theorem compiling, and makes KL-D false (the sequence 0, 1/3, 1, 4/3 has
|S| = 2 > √3). The calibration referee found the same gap. *Answer:* accepted. `OscInt/Front/KusminLandauSanity2.lean`
adds that sequence with a bite on the hypothesis, and the second plant run has the mutation with a compiled witness.

**A2 (MAJOR, sanity layer). The interval of KL-F's hypotheses is not pinned.** Reversing the interval in
`HasDerivOn f f' a b`, or dropping that hypothesis, leaves the sanity file unchanged; the mutant is false (f = 0 with
the claimed derivative 1/2 on [0, 2]: three terms equal to 1). *Answer:* accepted; plants with that witness added.

**A3 (MAJOR, sanity layer). KL-F has no datum that protects its bound.** All three data are at λ = 1/4 with |S| at
most 1.474 against 2.414, so Cheng and Graham's bound would pass them. *Answer:* accepted in part. Added: f(x) = x/2
on [0, 2] at λ = 1/2, where the bound of KL-F is attained (so any smaller constant at λ = 1/2 is refuted). Not
closed: a plant that replaces KL-F's bound by 1/(πλ) + 1 is refuted only by a ramp at λ = 1/5 that has no exact form
(|S| ≈ 2.76 against 2.5915, the referee's numerics); it is recorded as NOT DETECTED. KL-F's bound is the same
expression as KL-D's, whose constant is protected by equality data.

**A4 (MAJOR, sanity layer). "One cell for all differences" has no datum.** The prose's own example 0, 1/4, 1, 9/4, 4
(differences in two cells) is not in the sanity file. *Answer:* accepted; the sequence is added with the bite
"for every k the hypothesis fails", and a plant that lets the cell depend on n is refuted by it.

**A5 (MINOR). `0 < lam` weakened to `0 ≤ lam` is accepted by the scripts in all three statements and is false**
(division by zero is zero in Lean). The first run had this plant for KL-D only. *Answer:* plants added for KL-C and KL-F.

**A6 (MINOR). No datum at λ = 1/2 for KL-C and KL-F; `lam ≤ 1/2` in KL-F bites only when a = b is an integer.**
*Answer:* data at λ = 1/2 added for both. The remark about KL-F is correct and is added to the prose (clarification 3).

**A7 (MINOR). The lower end of the cell and a negative k have no datum.** *Answer:* a datum with k = −1 is added.
"Lower end dropped" is not planted: recorded as a gap.

**A8 (MINOR). All KL-F data have integer end points**, so the ceiling and floor are separated only by a script.
*Answer:* a datum on [−1/2, 3/2] is added, and the swapped form is refuted at a = b = 1/2 (the mutated sum has two terms).

**A9 (MINOR, prose). Modelling choice 6 says the sanity layer uses the sequence 0, 1/5, 2/5, 6/5, 2. It does not;**
it uses 0, 1/6, 1/3, 1/2, 4/3, 13/6, 3 (|S| = √13), chosen because its terms are exact with √3 only. *Answer:* a
prose error by the lead; corrected by clarification 1 in `docs/statements.md`.

**A10 (NIT). KL-C follows from KL-D; KL-F covers a ≥ b silently; "two additions" omits N = 0; "textbook form" is
loose.** *Answer:* all true; clarification 4.

**B1 (MINOR). Zero slack.** KL-D is attained on odd/odd λ and KL-F at λ = 1/2, so a strict inequality would be
false. *Answer:* noted; the statements are non-strict.

**B2 (MINOR, prose). Modelling choice 7 is wrong at λ = 1/2:** the derivative form does attain the bound there
(f′ constant equal to k + 1/2 with an odd number of integers in [a, b]). Referee A and the calibration referee say
the same. *Answer:* a prose error by the lead; corrected by clarification 2. For λ < 1/2 referee B found ratios up
to 1 − 1.2·10⁻⁶⁵ and no equality, so "a supremum, not attained, for λ < 1/2" is CONJECTURED from that search, not proved.

**B3 (NIT). The monotonicity clause is empty for N ≤ 2,** so the equality datum 0, 1/3, 1 does not exercise it; the
pin theorems are tautologies. *Answer:* the first is A1's gap from another side and is closed with it; the pins are
the repository's convention.

## From the calibration referee, against the unplanted layer

It reviewed a planted copy, so its verdicts are not about this batch; but four of its findings concern files that
were not planted, and they agree with A1, A3, A8 and A9 above. They are answered there.

## What changed, and what did not

- Unchanged: `OscInt/Statements/KusminLandau.lean`, the challenge and comparator files, the first sanity file and the
  first plant run (the reviewed records).
- Added: `OscInt/Front/KusminLandauSanity2.lean`; the second plant run under
  `docs/replay/plants/2026-11-16-KL-second/` with its record `docs/replay/2026-11-16-KL-sanity-plants-second.txt`; four
  dated clarifications in `docs/statements.md`.
- Still not detected, on the record: Cheng and Graham's constant substituted in KL-F (A3); "lower end of the cell
  dropped" (A7).

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
