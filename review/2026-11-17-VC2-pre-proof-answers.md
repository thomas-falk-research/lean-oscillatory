# Answers to the blind pre-proof reviews of batch VC2 (VC2-S, VC2-A, VC2-N, VC2-K)

Two fresh-context referees read the frozen batch at 6ef8939 (stamp `stamps/20261116T222541Z-5b72549117b1`, taken on
5b72549; the pins are in fc2ef42), before any Lean proof of these statements existed in the repository. Referee A
checked fidelity; referee B tried to refute the Lean text with its own code.
- Both are Claude instances, like the lead and like the agents that wrote the two sanity layers; "fresh-context" does
  not mean a different model family or a human. No calibration copy with planted errors was run for this batch.
- A proof on paper of VC2-S and VC2-A existed before the freeze and had been read by a step referee
  (`docs/statements.md`, Batch VC2, "Order"); the two blind referees were told so and were not given it.
- Their briefs and reports are not recorded (privacy rule 19); the SHA-256 of the briefs and of the reports are in
  the session log (`docs/progress/2026-11-16-session13-log.md`). Each finding is restated here in the lead's words.
- The tree was frozen from the launch (23:14:02Z) until the last referee and proof agent of that round had ended.
- Referee B was cut by a restart of the container at about 23:57Z, was resumed from its transcript and finished
  without relaunching its heavy job; what it did not complete is listed under its verdicts.
- What the referees compiled: referee A elaborated the frozen definitions and statements, compiled two mutated
  copies of the statements with copies of the sanity scripts to show that the scripts accept them, and compiled
  five refutations of statements with a hypothesis removed. It proved nothing about the statements. Referee B ran
  no Lean.

| Referee | Reviewed | Launched (UTC) | Run time (harness record) |
|---|---|---|---|
| A (fidelity) | 6ef8939 | just after 23:14:02 | 1156 s |
| B (truth) | 6ef8939 | just after 23:14:02 | interrupted by the restart; resumed at about 00:00 and finished in 199 s |

## Verdicts

| | Referee A (fidelity) | Referee B (truth) |
|---|---|---|
| VC2-S | FAITHFUL | no counterexample (about 8.6 million quadratic instances, 180 optimisation runs over non-quadratic phases, 6925 evaluations of smooth phases; floating point). Largest ratio of the two sides 1: the statement has no slack, and its instance at the extremal quadratic is an equality that numerics confirm to 2·10⁻⁶³ and cannot decide |
| VC2-A | FAITHFUL | no counterexample (59 746 exact rational w in ball arithmetic: 59 745 strict, one undecided at w = 0 where both sides are 0) |
| VC2-N | FAITHFUL | no counterexample; certified on all of [0, π] by branch and bound in ball arithmetic (595 cells): the maximum of the profile lies in [3.364317578155899106067713, 3.364317578155899106067763], at w in [2.297439573597, 2.297439573620]; 7/2 exceeds it by at least 0.1356 |
| VC2-K | FAITHFUL | no counterexample (3600 cases, floating point; largest ratio 0.9612, the ratio of the sharp constant to 7/2) |

Not completed by referee B because of the restart: Cantor-type derivatives, piecewise quadratics with free break
points, smooth families with the perturbation held away from zero, and a re-evaluation of non-quadratic candidates
in ball arithmetic. For VC2-S its evidence is therefore floating point on families that mostly returned to the
quadratic phase; the only genuinely non-quadratic smooth value it reports is 0.752 (the phase −log cos x).

No BLOCKER. Three MAJOR (referee A), all against the sanity layer, none against the Lean text. The statements and
the stamp stand. The MAJORs are answered by a second sanity file and a second plant run, committed with this
file; the statement text is untouched.

## Findings and answers

**A1 (MAJOR, sanity layer). Every datum of the first layer has a constant second derivative.** With `≤` replaced by
`=` in the increment condition, or `μ ≤ |φ″|` by `|φ″| = μ` in VC2-K, all nine sanity conclusions about VC2-S and
VC2-K are still derivable (the referee compiled it). Those two mutations are true weakenings: they restrict the
theorem to exact parabolas and no witness can refute them. *Answer:* accepted.
`OscInt/Front/SecondDerivSharpSanity2.lean` applies VC2-S and VC2-K to the phase x²/2 + x⁴/12 (second derivative
1 + x², not constant). The two mutations are planted (M1, M2): the copied scripts fail on the planted copies, and
a compiled datum shows that the quartic phase does not satisfy the planted increment condition. Verdict in the plant
record: TRUE WEAKENING, script-level evidence only. A false mutation the referee also named, f replaced by f′ inside
the exponential, is recorded as NOT DETECTED (X1); the sanity agent points out a witness on paper (λ = 1/100 on
[−100, 100]) that is not compiled.

**A2 (MAJOR, sanity layer). The power of λ and of μ was pinned from one side only, at a datum where the trivial
bound is better than the statement.** *Answer:* accepted. Two scaled data, each from the certified value at the
half-width 21/10 by a linear change of variable: curvature 1/100 on [−21, 21] (left side ≥ 33) and curvature 100 on
[−21/100, 21/100] (left side ≥ 33/100). Four mutations of the exponent are refuted by compiled witnesses: −1/3 and
−3/5 in VC2-K, 1/4 and 3/5 in VC2-S (the last with an exact but thin margin, 0.33 against 0.3281).

**A3 (MAJOR, borderline; sanity layer). The range of w in VC2-S is pinned only up to w ≈ 1.36.** The mutation
[0, π] ↦ [0, 441/200] is false and undetected, because the layer has no upper bound for the profile except the
trivial one. *Answer:* accepted as a limit, not closed: an upper bound for the profile on an interval is a piece
of VC2-N, which a sanity layer must not prove. Recorded as NOT DETECTED (W1). After a proof of VC2-N the gap
closes by itself.

**A4 (MINOR). Constants were pinned from below at 33/10.** *Answer:* the second layer certifies
67/20 < A(441/200) (the exact polynomial value is 3.350076…) and 3.358 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx|; the
mutations 7/2 ↦ 67/20 in VC2-N and in VC2-K are refuted by compiled witnesses. Constants between 3.3584 and
3.3643 remain untested by data.

**A5 (MINOR). Hypotheses with no plant.** *Answer:* five are planted and refuted in the second run with the
referee's own witnesses, which it had compiled and offered (a ≤ b in VC2-S and VC2-K; the derivative hypothesis of
VC2-S; 0 < μ and the second-derivative hypothesis of VC2-K). Not covered: the integrability component of the
amplitude hypothesis (inherited from S1).

**A6 (MINOR). The amplitude norm is tested only where the trivial bound wins; VC2-A is barely exercised.**
*Answer:* the mutation of the amplitude norm to ∫|ψ′| alone is refuted (P1). The mutation with weight 1/2 on ∫|ψ′|
and the mutation x² in place of x²/2 in VC2-A are recorded as NOT DETECTED (P2, Q1): each needs an upper bound for
an oscillatory integral or a certified cut-off amplitude, which the layer does not have.

**A7 (MINOR, prose) = B-NIT 1. Modelling choice 1 says the existential form is "strictly stronger" than the bound
with the constant sup A.** That is wrong: A is continuous on the compact [0, π], so the two forms are equivalent,
and w is not tied to f. An error of the lead. *Answer:* clarification a in `docs/statements.md`.

**A8 (MINOR, docstring) = B-NIT 2. The docstring of `vdc2Profile` in the frozen file** ("the largest real part, over
rotations …") describes the modulus of the quadratic integral, not the profile (A(1/2) = 0.648 against 1.978;
A(5) < 0). An error of the lead in a comment of a frozen file, which is not edited. *Answer:* clarification b.

**A9 (MINOR, literature).** Neither referee nor the lead has read Kershner or Finch. Referee A checked that the
tabulated constant (MathWorld, OEIS A143305) is the maximum of the profile at the same maximiser, and notes that
whether the classical theorem covers the class of VC2-S (an increment condition on f′, with f′ possibly unbounded at
the ends) is unverified. *Answer:* clarification c; the label of the theorem stays "classical, CITED, originals
unread", and the label of the statement's class is "proved on paper by the lead, refereed once".

**A-NITs.** Endpoint continuity of f is superfluous in VC2-S; `0 ≤ w` in VC2-A and the range in VC2-N are
superfluous under Lean's convention for the square root of a negative number; the letter A is used for the profile
and for the amplitude norm; one number in a docstring of the first sanity file (2.5698 where the referee gets
2.56931). *Answer:* clarification d. The number in the first sanity file's docstring is a comment about a value that
is not used by any proof; it is noted here and the file is left as reviewed.

**B1 (MINOR). VC2-S has no slack.** Its truth at the extremal quadratic is an equality. *Answer:* that is the
content of VC2-A together with VC2-S; it means a proof may lose nothing, and that numerical evidence for VC2-S can
never be more than "no violation found".

**B2 (MINOR). Referee B's own coverage of VC2-S is incomplete** (restart). *Answer:* recorded above and in "still
not covered". The lead's and the step referee's earlier searches (`numerics/review/vc2_statement_checks.py`; a
linear programme over densities) are other floating-point evidence, not a substitute.

**B-NIT 3.** That the supremum of the modulus of the quadratic integral over all half-widths is attained with
w ≤ π is certified by referee B only for w ≤ 400. *Answer:* noted in clarification c; the paper proof covers all w.

## What is still not covered after these answers

- The range of w in VC2-S from below (W1), the mutation f ↦ f′ in the exponential (X1), the integrand of VC2-A (Q1),
  the weight of ∫|ψ′| in the amplitude norm (P2): NOT DETECTED by any datum.
- M1 and M2 (the statement for exact parabolas only) are true weakenings; only script-level evidence separates
  them from the frozen text.
- No datum decides an instance of VC2-S, VC2-N or VC2-K from above: the layers prove no upper bound. Constants
  between 3.3584 and 3.3643 are untested by data.
- VC2-S rests, numerically, on floating-point searches; the truth referee's search was cut short.
- No calibration copy was reviewed; all agents are of the lead's model family.
- A proof on paper predates the freeze; the blind referees did not see it, the lead who wrote the statements did.
