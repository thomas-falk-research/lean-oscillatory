# Answers to the blind pre-proof reviews of batch HW (HW-R, HW-K, HW-D, HW-L)

Two fresh-context referees read the frozen batch at 6ef8939 (stamp `stamps/20261116T225756Z-5792039264f0`, taken on
5792039; the pins are in 970ad6b), before any Lean proof of these statements existed in the repository. Referee A
checked fidelity; referee B tried to refute the Lean text with its own code.
- Both are Claude instances, like the lead and like the agents that wrote the two sanity layers; "fresh-context" does
  not mean a different model family or a human. No calibration copy with planted errors was run for this batch.
- The prose section contains a paragraph "Route" (the lead's proof plan on paper, which predates the freeze); both
  referees could read it. No Lean proof existed.
- Their briefs and reports are not recorded (privacy rule 19); the SHA-256 of the briefs and of the reports are in
  the session log (`docs/progress/2026-11-16-session13-log.md`). Each finding is restated here in the lead's words.
- The tree was frozen from the launch (23:14:02Z) until the last referee and proof agent of that round had ended.
- Referee B was cut by a restart of the container at about 23:57Z after its report was written; it was resumed
  from its transcript and finished without relaunching the one job that had been killed (below).
- What the referees compiled: referee A elaborated the frozen definitions and statements with explicit casts and
  parentheses and three small checks; it proved nothing about the statements. Referee B ran no Lean.

| Referee | Reviewed | Launched (UTC) | Run time (harness record) |
|---|---|---|---|
| A (fidelity) | 6ef8939 | just after 23:14:02 | 538 s |
| B (truth) | 6ef8939 | just after 23:14:02 | report written before the restart; resumed at about 00:00 and finished in 48 s |

## Verdicts

| | Referee A (fidelity) | Referee B (truth) |
|---|---|---|
| HW-R | FAITHFUL | no counterexample: 40 592 certified comparisons (the walk in exact arithmetic over ℚ(√2) or in ball arithmetic against rigorous integration of the kernel as defined; every site for every t ≤ 40, and t = 100, 300, 1000, 3000), five altered forms each refuted; floating point at 15 times up to 4 000 001 (largest difference 8.1·10⁻¹²) |
| HW-K | FAITHFUL | no counterexample: certified at every site for 1 ≤ t ≤ 60 and at eight points up to t = 239 668; floating point from the definition at every site for every t ≤ 20 000 and 44 further times up to 16 000 001; largest ratio of the two sides 0.0767 |
| HW-D | FAITHFUL | no counterexample: exact integer arithmetic at every site for 1 ≤ t ≤ 3000 (36 024 000 component values); floating point at every site for every t ≤ 64 000 and 15 times up to 4 000 001; largest ratio 0.04178 |
| HW-L | FAITHFUL | no counterexample: 970 states, t ≤ 400 and t = 64 000, 200 000; largest ratio 0.04173 |

Not completed by referee B because of the restart: a certified enclosure of the walk after 59 320 steps (the first
time at which HW-D is not implied by conservation of the ℓ² norm). So where HW-D and HW-L have content the truth
review rests on floating point, with a margin of a factor 24.

No BLOCKER. Two MAJOR (referee A), both against the sanity layer, none against the Lean text. The statements and
the stamp stand. The MAJORs are answered by a second sanity file and a second plant run, committed with this file.

## Findings and answers

**A1 (MAJOR, sanity layer). A sign mutation of HW-R passes every datum:** the summand a K(t, x) replaced by
a K(t, −x). The first layer tests HW-R at t = 0 and t = 1 only, where K(0, ·) and K(1, ·) are even in x; the mutated
statement first fails at t = 2. The docstring of one sanity theorem and item 8 of the prose ("this pins … the sign
of x") claimed more than the data gave. *Answer:* accepted; an overstatement of the lead in the prose.
`OscInt/Front/HadamardWalkSanity2.lean` has the walk after three steps at every site, K(3, ·) at every site, and HW-R
at t = 2 through the constant; the mutation is refuted by a compiled witness in both components (HW-R-l, HW-R-m).
Clarification a.

**A2 (MAJOR, sanity layer; partly disclosed). No datum lies where a bound of HW-K, HW-D or HW-L is non-trivial, and
HW-L was tested at t = 1 only, with no plant on its constant or exponent.** *Answer:* accepted in part; what data
at small times can do is done. The second layer applies HW-D and HW-L at t = 3 and HW-K at t = 5 through the
constants, and refutes by compiled witnesses: the constant 39 replaced by 1 in HW-D and in HW-L (the amplitude 1/√2
at t = 3 against 3^{−1/3}), and the constants (7, 12) replaced by (1, 0) in HW-K (|K(5, 0)| = 1/2 against 5^{−1/2}).
It cannot do more: with the frozen constants no exponent mutation is refutable at small times (recorded: HW-L-f, not
detected, and for the exponent +1/3 a true weakening), and 84 t^{−5/6} first fails near t = 7749 (HW-K-f, not
detected). The whole content of the batch, the exponent −1/3 and the constants, rests on the reviews and on the
proof; the prose said so and says so again in clarification b.

**A3 (MINOR, sanity layer).** The support hypothesis of HW-L mutated to "the first component has finite support" was
not refuted by the bite datum (1, 1). *Answer:* the constant state (0, 1) refutes it (compiled; HW-L-g).

**A4 (MINOR, disclosed).** In HW-K the hypothesis t ≥ 1 carries no content. *Answer:* as in modelling choice 2; the
docstring of the frozen statement does not repeat it and is not edited.

**A5 (MINOR, literature).** "arXiv:1808.05714, section 3" is the numbering of version 1 (Proposition 3.12); in
version 3 it is Section 4, Proposition 4.12. The same paper says the constant-coin estimate "is also proved in" two
other papers and credits Sunada and Tate, whose paper the prose described only as "Airy asymptotics". *Answer:*
accepted; clarification c. (The lead read the LaTeX source of the arXiv listing without recording its version.)

**A6 (MINOR).** HW-D and HW-L bound each component by the ℓ¹ sum of |ψ₁| + |ψ₂|; with Euclidean norms on ℂ² on both
sides, as in the literature, the statements give 78, not 39. *Answer:* clarification d.

**A-NITs.** The eigenvalue remark holds for plane waves e^{−ikx}; "stays below 1.0" is an equality at t = 1; the
route constant 6.8700 is 6.86990; the route omits one inequality it uses; the name `HadamardKernelStatement` for the
representation formula; the header of the frozen file says "blind-reviewed" at the freeze; `import` of a file whose
definitions the statements do not use; two sanity theorems are checks of form only. *Answer:* clarification e for
the numbers and the route; the names and comments of the frozen file are not edited.

**B1 (MINOR). The constants are 12.6 times (HW-K) and 23.9 times (HW-D, HW-L) the asymptotically attained values**
(0.9544 t^{−1/3} and 1.6293 t^{−1/3}), so no exact datum can detect a wrong exponent or a constant wrong by such a
factor. *Answer:* confirmed; modelling choice 3 and clarification b.

**B2, B3 (MINOR). Coverage:** beyond t = 20 000 (HW-K) and 64 000 (HW-D) only a sparse grid was run; the certified
point at t = 59 320 was not completed. *Answer:* recorded above.

**B-NITs = A-NITs on the numbers**, and: "about 1.61 t^{−1/3}" is the value at t = 3000; the supremum over t ≤ 3000 is
1.6208 and the values rise to 1.6292. The datum "39/t first fails at t = 126" is confirmed exactly.

## A conjecture the reviews suggest (not a statement of the batch)

Both referees and the second sanity agent found, in floating point, that sup_x |K(t, x)| t^{1/3} equals 1 at t = 1
and is at most 0.9637 (at t = 6) for 2 ≤ t ≤ 9000, tending to about 0.9544. So |K(t, x)| ≤ t^{−1/3} for all t ≥ 1 may
be true: CONJECTURED, numerical evidence only (exact recursion in floating point, t ≤ 9000, and a grid to
1.6·10⁷); the route of this batch cannot prove it. It is registered in clarification f and nowhere claimed.

## What is still not covered after these answers

- No datum lies where a bound beats the trivial one; exponent mutations are not refutable by data at small times.
- HW-K with the product of its two terms in place of the sum (first false near t = 7749): not detected.
- Where HW-D and HW-L have content (t ≥ 59 320) the truth review is floating point only.
- No calibration copy was reviewed; all agents are of the lead's model family.
- The proof plan on paper predates the freeze and its constants are the statement's constants.
