# Answers to the blind pre-proof reviews of batch FR (FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P)

Two fresh-context referees read the frozen batch at 3cbaa23 (stamp `stamps/20261116T205833Z-0748dde3c341`, which is on
the statements commit 0748dde; 3cbaa23 adds the pins and records), before any Lean proof of these statements existed
in the repository. Referee A checked fidelity; referee B tried to refute the Lean text with its own code.
- Both are Claude instances, like the lead and like the agents that wrote the two sanity layers; "fresh-context"
  does not mean a different model family or a human. No calibration copy with planted errors was run for this batch
  (rounds 1 to 4 are in `docs/calibration.md`); the detection rate measured there is for those rounds.
- Their briefs and reports are not recorded (privacy rule 19); SHA-256 of the brief files (in the lead's event file,
  written before the launch) and of the report files are in the session log
  (`docs/progress/2026-11-16-session13-log.md`). Each finding is restated below in the lead's words.
- The tree was frozen from the launch until both had ended: the lead made no commit and wrote no file into the tree
  in that window (the session log and git show this; the lead worked in scratch).
- What the referees compiled. Referee A elaborated the frozen definitions and statements (`#print` with explicit
  parentheses) and compiled thirteen *mutated* copies of the statements together with verbatim copies of the sanity
  scripts, to show that the scripts accept them. It proved nothing about the statements and was given no route.
  Referee B ran no Lean.

| Referee | Reviewed | Launched (UTC) | Run time (harness record) |
|---|---|---|---|
| A (fidelity) | 3cbaa23 | just after 21:06:27 | 924 s |
| B (truth) | 3cbaa23 | just after 21:06:27 | 1414 s |

## Verdicts

| | Referee A (fidelity) | Referee B (truth) |
|---|---|---|
| FR-K | FAITHFUL | no counterexample (1376 cases × 3 clauses in ball arithmetic; the unit datum exactly in 11 540 pairs (N, r)) |
| FR-U | FAITHFUL | no counterexample (5460 cases against the matrix exponential of the ring Laplacian) |
| FR-S | FAITHFUL | no counterexample (624 cases, partial sums with a rigorous tail bound) |
| FR-P | FAITHFUL | no counterexample (236 760 certified comparisons; supremum of the ratio of the two sides 1, not attained) |
| FC-K | FAITHFUL | no counterexample (2800 derivative cases; walls and datum in the same cases) |
| FC-U | FAITHFUL | no counterexample (2212 cases against the matrix exponential of the Dirichlet Laplacian) |
| FC-P | FAITHFUL | no counterexample (161 036 certified comparisons; largest ratio 0.4854) |

Referee B's comparisons for FR-P and FC-P were decided on Arb balls from exact rational parameters, with the
precision doubled until decided (up to 262 144 bits); two grid points of FR-P beyond that were settled by an exact
identity. Equalities (FR-K, FR-U, FR-S, FC-K, FC-U) are checked to the width of an enclosure (1e-82 or better), not
exactly, except the unit datum of FR-K (exact integer arithmetic). The derivative clauses were checked with rigorous
Taylor arithmetic on the defining sums. FR-U and FC-U can only be tested through the solution exp(itΔ)u₀; a failure
of uniqueness would not be seen. Limits of that review: N ≤ 1000 and M ≤ 200 on the certified grid (single points to
N = 10⁵, M = 2500), |t| ≤ 1000.

No BLOCKER. Three MAJOR (referee A), all against the sanity layer and the plant record, none against the Lean text.
The statements and the stamp stand. The MAJORs are answered by a second sanity file and a second plant run,
committed with this file, not by a re-freeze: the statement text is untouched, and CONTRIBUTING step 5 reserves a
new statement for findings against the statement.

Literature. The FR section cites no publication for the seven statements, so referee A had no cited result to
compare; it confirmed numerically the Bessel form of the line kernel, the two matrix exponentials and the free-end
formula of modelling choice 6. A paper would need one reference each for the method of images and for the
sine-transform diagonalisation; none is cited here and no novelty is claimed.

## Findings and answers

**A1 (MAJOR, sanity layer). Thirteen false mutations of the Lean text pass the first layer's scripts unchanged.**
Referee A compiled each mutated statement with verbatim copies of the sanity theorems that take the statement as
hypothesis; all were accepted, and each mutation has a numerical counterexample. The causes: the ring equation was
exercised only at N = 2, where the two neighbours of a site coincide; the chain equation only at M = 1, where there
is no bond; FR-S only at t = 0; FR-P through the constant only at N = 1, r = ±1; FC-U only with a one-term sum.
*Answer:* accepted. `OscInt/Front/FiniteRingSanity2.lean` adds: FR-K on the ring of 4 sites at r = 1 (distinct
neighbours; the derivative i e^{−4it}) and its unit datum at r = 2 and r = 4; FR-U with the mode iˣ e^{−2is}, which is
not even in x; FR-P at N = 2, r = 2 and at a negative time; FC-K at a wall site of the chain of 1 site and on the
bond of the chain of 2 sites at every time (C₂(t; 1, 1) = e^{−2it} cos t, C₂(t; 2, 1) = i e^{−2it} sin t, from the ring
of 6 sites in closed form); FC-U on the chain of 2 sites with a two-term sum. Second plant run
(`docs/replay/plants/2026-11-16-FR-second/`): of the referee's thirteen mutations, ten are now refuted by compiled
witnesses (K1, K2, U1, P1, P2, P3, CK1, CK2, CU1, CP2), and so is the mutation that drops both neighbour terms of
FC-K (CK3). Three are not: S1 and S2 (FR-S with the time doubled, or with the ring kernel at −t), because the layer
still has no datum of FR-S at t ≠ 0 (it would need an infinite sum of line-kernel values); and CP1 (the wall term of
FC-P with e^{−2xη}), which is not violated at M = 2 and needs M ≥ 3. They are listed below under "still not covered".

**A2 (MAJOR, sanity layer). `lineKernel` was evaluated at t = 0 only, and no plant mutated `lineKernel` or
`ringKernel`.** Dropping the phase e^{−2it}, replacing I(2t) by I(t) or by I(−2t), or cos by cos³ in the ring's
dispersion relation left every datum true. *Answer:* accepted. The second layer has two data at t = 1/4 that carry
the phase: |G(1/4, 0) − (15/16) e^{−i/2}| ≤ 33/25600 and |G(1/4, 1) − (i/4) e^{−i/2}| ≤ 1/36 (expansions of e^{is cos k} to
order 4 and 2 with exact integrals of powers of the cosine). The three mutations of `lineKernel` are refuted by
compiled witnesses (the second one only against the sharper of two forms of the datum), and the cube in the
dispersion relation is refuted at N = 6, t = 4π, r = 0, where the kernel is 1 and the mutated one is −1/3.

**A3 (MAJOR, sanity layer; partly acknowledged in the prose). FC-P had no datum with a nonzero left side.**
*Answer:* accepted. From the data above, 767/25600 ≤ |C₂(1/4; x, x) − G(1/4, 0)| for x = 1, 2 (true value 0.03044),
and FC-P is applied there through the constant for every η > 0. Six mutations of FC-P are now refuted by compiled
witnesses: the wall term dropped (plant FC-P-b of the first run, not detected then), the ring term dropped,
cosh((x + y)η) dropped, M + 1 replaced by M + 2, the wall exponent doubled, and 2|t| replaced by |t| (at η = log 16).
What the referee also showed, and what stays: four variants of FC-P are not violated on its grid (clarification h
in `docs/statements.md`), so data do not single out the frozen constants; and two true weakenings cannot be refuted
by any datum (FR-P with e^{η} in place of e^{ηN}; FC-P with M in place of M + 1 in the exponent).

**A4 (MINOR). Hypotheses without a datum on which they bite.** *Answer:* accepted for those that can bite. Planted
and refuted in the second run: `1 ≤ y` and `y ≤ M` of FC-K (CK4, CK5), the equation hypothesis of FC-U (CU2), |t|
against t in FR-P (P3). A supplementary run (three plants, same directory) refutes the three that the first brief of the second layer
had forgotten: `0 < N` of FR-U (N = 0, u = 1: the empty sum gives 1 = 0) and the two inner site hypotheses of the
unit datum of FC-K (x = −1 and x = 3 on the chain of 1 site, where the kernel at time 0 is −1). The four site hypotheses of FC-P do not bite on any tested datum: the
referee found no violation with all four removed, and the record says so (TW3, "no violation known").

**A5 (MINOR, prose). "FR-P is sharp" holds only outside the fundamental cell.** *Answer:* accepted; clarification a.

**A6 (MINOR, prose). "largest observed ratio 0.36" for FC-P depends on the range.** *Answer:* accepted;
clarification b. Referee B found the same independently (its MINOR-1).

**A7 (NIT, wording).** "two nearest images" in the header of the Lean file against "three images" in the prose;
|C_M| ≤ 1 used and not stated; the rescaling of time by κ; FR-U and FC-U are representation formulas; FR-K and FC-K
put clauses under quantifiers they do not need; one sanity theorem without an unconditional check. *Answer:*
clarifications c to g. The header of the frozen Lean file is not edited.

**B1 (MINOR, prose) = A6.** **B2 (MINOR, prose).** FR-P is nearly attained along the whole family r = ±N with t
small and N large, not only at t = 0. *Answer:* accepted; clarification a. It matters for the proof plan: the
bound for the sum over images must lose nothing, and the plan's majorant sums to exactly the right side.

**B-NIT.** FC-K carries 1 ≤ y ≤ M for clauses that do not need it (clarification g). The conjecture of item 11
(FR-P without the "− 1") is undecided: referee B's floating-point scan saw no ratio above 1 and floating point cannot
decide the extremal family. A tooling note of referee B (a fixed-precision Bessel evaluation loses about 2|t|/ln 2
bits) is recorded here because the lead's own check script uses the same library; its comparisons are on balls,
so a loss of precision widens an enclosure and cannot turn a failure into a pass.

## What is still not covered after these answers

- FR-S at t ≠ 0: no datum; the mutations S1 and S2 are not detected. FR-S at t ≠ 0 rests on referee B's 624 cases
  and on the proof.
- The wall term of FC-P off the diagonal (CP1): not detected; a violation of the mutated form needs the chain of 3
  sites at t ≠ 0.
- The "− 1" in the denominator of FR-P (plant FR-P-e of the first run): not detected; whether the statement without
  it is true is open (modelling choice 11).
- Four variants of FC-P that no datum and no scan separates from the frozen text (clarification h), and two true
  weakenings that no datum can refute.
- The four site hypotheses of FC-P have no datum on which they bite.
- Sizes: the kernels are evaluated in closed form at N ∈ {1, 2, 4, 6} and M ∈ {1, 2} only; the line kernel at the
  times 0 and ±1/4 only.
- FR-U and FC-U were tested only through solutions; a failure of uniqueness would not be seen by a numerical test.
- No calibration copy with planted errors was reviewed for this batch, and both referees and both sanity agents are
  of the lead's model family. The second layer was written by an agent of the lead from the lead's reading of referee
  A's report; the lead's brief for it contained three wrong numbers, which the agent corrected (session log).
- The plan of the proof on paper predates these reviews (`docs/statements.md`, Batch FR, "Order").

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
