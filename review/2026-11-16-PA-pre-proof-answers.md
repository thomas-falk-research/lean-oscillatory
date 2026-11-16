# Answers to the blind pre-proof reviews of batch PA (PA-C, PA-T, LC-1)

Two fresh-context referees read the frozen batch at acc035d (stamp `stamps/20261116T130956Z-276d8d7f9605`, which is on
the statements commit 276d8d7; acc035d adds the pins and records), before any Lean proof of these statements existed
anywhere. Referee A checked fidelity; referee B tried to refute the Lean text with its own code. A third referee
reviewed a copy with four planted errors (calibration, `docs/calibration.md`, round 3).
- All three are Claude instances, like the lead; "fresh-context" does not mean a different model family or a human.
- Their briefs and reports are not recorded (privacy rule 19); the briefs' SHA-256 are in the session log
  (`docs/progress/2026-11-16-session13-log.md`). Each finding is restated below in the lead's words.
- The tree was frozen from the launch until the last referee of either batch had ended: the lead made no commit and
  wrote no file into the tree in that window (the session log and git show this; the lead worked in scratch).
- What the referees compiled. Referee A elaborated the frozen definitions (`#print` with numeric types) and compiled
  witnesses that *mutated* copies of the statements are false, together with two data facts
  (`latticeKernel1 0 (1/2) = 4`; a half-integer mode of the constant function). It proved nothing about the statements
  themselves and outlined no route. Referee B ran no Lean.

| Referee | Reviewed | Launched (UTC) | Finished | Run time (harness record) |
|---|---|---|---|---|
| A (fidelity) | acc035d | 13:19:47 | before 13:39:34 | 964 s |
| B (truth) | acc035d | 13:19:47 | report written by 14:36:47; agent ended before 14:37:14 | 4634 s |
| calibration copy | planted snapshot of acc035d | 13:19:47 | before 13:39:34 | 891 s |

The launch time is the lead's clock when the launch calls returned; the finish times are upper bounds from the
lead's scratch event log.

## Verdicts

| | Referee A (fidelity) | Referee B (truth) |
|---|---|---|
| PA-C | FAITHFUL | no counterexample (9787 comparisons on 314 functions; the bound is attained exactly by `c·e^{ikz}`) |
| PA-T | FAITHFUL | no counterexample (13766 comparisons; largest ratio of the two sides 1 − 2.65·10⁻²⁶¹, not attained) |
| LC-1 | FAITHFUL | no counterexample (47,334 strict comparisons; equality exactly at t = 0, n = 0) |

Every comparison of referee B was decided on python-flint balls (128 to 2000 bits), none by floating point. Its
functions included poles at distance down to 1e-6 outside the strip, Blaschke products and singular inner functions
with boundary singularities, lacunary and one-sided spectra, growth up to M = 1.8·10⁷⁰³⁸, widths from a = 1e-6 to
a = 200, and candidates from a linear programme that maximises the trapezoidal error under the bound.

No BLOCKER. Two MAJOR (referee A), both against the sanity layer and the plant record, none against the Lean text or
the prose. The statements and the stamp stand. The MAJORs are answered by a second sanity file and a second plant
run, committed with this file, not by a re-freeze: the statement text is untouched, and CONTRIBUTING step 5 reserves
a new statement for findings against the statement.

Referee A read the published paper: Theorem 3.2, its equations (3.1), (3.2), (3.5) and (3.18), Theorem 3.1, the
sharpness example of Theorem 2.2 and the historical remark on Davis all agree with the prose. It confirmed that LC-1,
optimised over η, equals the right side of DLMF 10.14.5 (to 1e-39) and that 10.14.8 is the inequality named after
Kapteyn. Davis (1959) and Siegel (1953) were not opened by anyone.

## Findings and answers

**A1 (MAJOR, sanity layer). The node positions of the trapezoidal sum are not pinned.** Both PA-T data have every
node value equal to v(0) (7 cos 3z at N = 3; a single node at N = 1). With the nodes mutated to a natural-number
division (every node 0) both sanity theorems still compile through the mutated statement, which is false. No plant
touched `trapezoidalSum`. The calibration referee found the same gap. *Answer:* accepted.
`OscInt/Front/PeriodicAnalyticSanity2.lean` pins the sum at N = 4 and N = 6, where the node values differ, and the
second plant run refutes two node mutations by compiled witnesses.

**A2 (MAJOR, sanity layer). Integrality of n (LC-1) and of k (PA-C) has no datum on which it bites,** although
modelling choice 6 says the bound fails for non-integer frequencies. *Answer:* accepted; two bites are added
(`latticeKernel1 0 (1/2) = 4 > 2π/e`; the half-integer mode of the constant 1) and both mutations are planted and
refuted. The referee's numerics confirm the prose: |I(1, 20.5)| = 0.0975596 against the end-point term 0.0975610.

**A3 (MINOR, borderline MAJOR). The "− 1" in PA-T's denominator is not tested.** The mutant 4πM e^{−aN} holds on
both data for every a and is false: a trigonometric polynomial of degree 6 at a = ln 3, N = 1 exceeds it by 1.4%
(the referee's linear program and a high-precision bound; the calibration referee found a four-mode example with a
1% margin). *Answer:* the plant is recorded in the second run as NOT DETECTED by a compiled witness. Referee B certified a
counterexample to the mutated statement in ball arithmetic (B2), so its falsity is established at rung L2, outside
Lean. This is the one constant of the batch whose exact form rests on the review and on the proof alone.

**A4 (MINOR). The coefficient of |t| sinh η in LC-1 is not pinned** (|t| replaced by |t|/2 is false but passes).
*Answer:* planted in the second run and NOT DETECTED: the mutant holds for n = 0 and n = 1 and fails only from
|n| = 2 on (at n = 2 by a factor of at most about 1.08, the sanity agent's numerics), and a witness needs a
second-order expansion of the kernel that was not written.

**A5 (MINOR). Weakenings are invisible to the layer, and one comment overstates** ("tests |k|" on an even datum).
*Answer:* true. `|n|` replaced by `n`, ℤ by ℕ and a closed strip are weakenings; they are recorded as such. The
comment stays, because the first sanity file is a reviewed record; this answer is its correction.

**A6 (NIT, prose).** The text in quotation marks after "Theorem 3.2" is a condensed paraphrase, not the paper's
words; "cosh η = |n|/|t|" needs t ≠ 0. *Answer:* clarification 1 and 2 in `docs/statements.md`.

**A7 (NIT, Lean text).** The header says "blind-reviewed" in the past tense; the pins are `X = X`. *Answer:* the
header follows the earlier batches and is true from this commit on; the file cannot be edited. The pins are the
repository's convention.

**B1 (MINOR, prose). PA-C and LC-1 are attained with equality,** not only in a limit: PA-C by `v = c·e^{ikz}` with
`M = |c| e^{a|k|}`, LC-1 at t = 0, n = 0. Modelling choice 8 says "attained in the limit" of both ratios. *Answer:* a
wording error by the lead; clarification 3. Any strict form, or any constant below 2π, would be false.

**B2 (MINOR). The "− 1" of PA-T is load-bearing, and the family c·cos(Nz) cannot see it.** Referee B certified, in
ball arithmetic, a counterexample to the statement with denominator `e^{aN}`: a function proposed by its linear
programme at `e^a = 2`, N = 1, with ratio 1.00779 of the two sides. It asked whether the sanity layer relies on
cosine data only. *Answer:* it does (A3). The second plant run records this mutation as refuted by certified
numerics outside Lean (the referee's computation, which the lead did not re-run), and as NOT DETECTED by a compiled
witness. The referee's table also shows how far the bound is from sharp at moderate aN: the best ratio found is
0.50 at `e^{aN} = 2` and 0.90 at `e^{aN} = 10`.

**B3 (NIT). Where the statements have no content:** PA-T for `aN ≤ ln 2` (the right side exceeds the trivial bound),
LC-1 inside the light cone and at η = 0, PA-C at k = 0, and every statement for M < 0 (vacuous) or M = 0 (v = 0).
*Answer:* true; clarification 4.

**Limits referee B states.** 354 LC-1 comparisons were decided through the Bessel identification
`|I(t, n)| = 2π|J_n(t)|` because the literal quadrature could not resolve values below 2⁻³⁰⁰; the identification
agreed with the literal quadrature at all 273 points where both were computed. Two elliptic-function cases timed
out. Equalities are stated from exact evaluation, since balls cannot certify them.

## From the calibration referee, against the unplanted layer

It reviewed a planted copy, so its verdicts are not about this batch. Its findings against files that were not
planted: the bound is never tested off the real axis (the only bite uses z = 0); PA-T is tested only where v is
constant on the nodes (A1); `e^{aN} − 1` against `e^{aN}` (A3); differentiability on a thinner strip passes every
script; no datum at k = 0. *Answer:* plants for the off-axis bound, with compiled witnesses, and a datum at k = 0
are added; the thinner strip is detected by a compiled witness in the second run.

## What changed, and what did not

- Unchanged: `OscInt/Statements/PeriodicAnalytic.lean`, the challenge and comparator files, the first sanity file and
  the first plant run (the reviewed records).
- Added: `OscInt/Front/PeriodicAnalyticSanity2.lean`; the second plant run under
  `docs/replay/plants/2026-11-16-PA-second/` with its record `docs/replay/2026-11-16-PA-sanity-plants-second.txt`; dated
  clarifications in `docs/statements.md`.
- Still not detected by a compiled witness, on the record: the "− 1" of PA-T (A3; refuted at L2 by referee B) and
  the coefficient of |t| in LC-1 (A4). Differentiability on a thinner strip, which the lead expected to stay
  undetected, is detected: the sanity agent found an exact datum (`e^{iz}` on |Im z| < 1, extended by 0).
