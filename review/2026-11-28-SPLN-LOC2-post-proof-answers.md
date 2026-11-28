<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batches SPL-N and LOC2: answers to the post-proof reviews (2026-11-28, session 17)

Written by the lead. Three post-proof referees from fresh contexts, of the lead's model family, reviewed commit
0274fe9 (the five proofs integrated) while the tree was frozen: A (fidelity), B (soundness), C (adversarial). Launched
16:43:15Z (brief SHA-256 888b2aa832ed36a47eb6ed884478ba72c0758a3f1113ca2f05347c0c3a38c7d2); task records A 386 s, B
276 s, C 533 s; the tree was not written while they ran. Isolation by instruction. Findings in the lead's words.

**Outcome: five FAITHFUL (A), five SOUND (B), claims SUPPORTED (C); no BLOCKER. C judged the records INACCURATE
(one MAJOR, against a record, answered below). The theorems stand.**

## 1. Referee A (fidelity)

The five theorems have exactly the frozen statement types (an `#assert_type_is`-style probe, `Expr` equality); every
constant they depend on lives in the frozen statement modules, whose bytes equal the freeze manifest; the prose's
consequences compile (K2-FQ ⇒ K2-F with `D = locConstC2 χ`; SPL-NK ⇒ SPL-K; the best constant of SPL-K lies in
`(72197399/10⁸, 360987/500000]`). Findings:
- MINOR: the owed plants of the pre-proof answers A-1 (a compiled refutation of a smaller LOC2 factor) and A-2 (A5U
  with `∃ C` after `∀ α`) were not closed. Answer: an agent builds both; the record follows in this branch.
- NIT: the LOC2 prose and the `LocCombineFacts` docstring speak of Cauchy–Schwarz and `√13`; the proof uses the
  weighted inequality with constant 29/8. Answer: recorded in the revision section of `docs/proof-LOC2.md`; the
  frozen text is unaffected.
- NIT: the SPL-NU STATUS row named parts N1–N10 (N9 and N10 feed SPL-NL and SPL-NC); corrected in STATUS. The route's
  table still says SPL-NK comes from SPL-I; its revision section says SPL-S.

## 2. Referee B (soundness)

No forbidden construct, no `set_option` at all in the new files; `decide +kernel` produces `of_decide_eq_true (Eq.refl
true)` with no `Lean.ofReduceBool`; the Boolean-to-real soundness of the certificate is proved, not assumed; the 13
proof modules recompile with no output; 259 helper names, no duplicate and no shadowing. NITs: K2-FQ's periodicity
hypotheses are unused (a stronger theorem than stated; already route finding L-4); `decide +kernel` relies on the
kernel's arbitrary-precision arithmetic, part of the standard trusted kernel; the certificate lives in
compiler-generated auxiliary lemmas whose axioms propagate to the final theorems.

## 3. Referee C (adversarial)

Reproduced: the five types; the axioms; 1.96 s kernel time for the 40 cells; six negative controls of its own (target
lowered to the lower rational, first cell dropped, cell 20 dropped, cover end `4 + 1/1000`, start `1/4`, two critical
cells merged), each `false` by the kernel; the frozen files' bytes; the stamps' imprints and times; that no proof file
appears in any ref before b17ec90/0274fe9; the counts and hash prefixes of the route answers; the referee durations.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| C-1 | MAJOR (record) | `review/2026-11-28-SPLN-LOC2-route-answers.md` says the LOC2 proof agents and the LOC2 route referee overlapped. The log shows the LOC2 parts finished and kernel-checked before that referee was launched. | **Correct.** Times from the task records: QA launched 15:59:18Z and ran 549 s (ended about 16:08:27Z), QB ran 731 s (about 16:11:29Z), the LOC2 route referee was launched at 16:13:38Z. So for LOC2 the route was reviewed after the parts were complete; no part changed after the review. For SPL-N the overlap claim holds: T and L ran 627 s and 624 s from 15:47:36Z (ended about 15:58:03Z and 15:58:01Z), C ran 987 s (about 16:04:03Z), the route referee read from 15:56:33Z to about 16:23Z. The answers file is a record and is not edited; this row is the correction, and the K2-FQ STATUS row now says so. |
| C-2 | MINOR | Imprecise times in the log for the part finishes. | The task-record durations above fix them; the log row of this commit gives them. |
| C-3 | MINOR | The K2-FQ STATUS row said "no MAJOR against a part" although the LOC2 route review had a MAJOR (against the plan). | Corrected in the row: one MAJOR against the route's plan for Q2. |
| C-4 | MINOR | "Four negative controls" and "the tree checks follow" were not recorded in the tree. | The controls are now a record, `docs/replay/plants/2026-11-28-SPLN-cells-controls/README.md` (run 16:53:10Z against the tree build: four mutations `false`, three axioms). The gate run on 0274fe9 is in the session log (`make push-gate RUN=1`, 16:34:57–16:42:47Z, `make quick` PASS, 3078 of 3078 theorems clean). |
| C-5 | MINOR | The LOC2 route promised its Mathlib names in `MathlibNames.lean`. | Added (with the A5U names), checked at the pin, exit 0. |
| C-6 | MINOR | No log row for the lead's LOC2 blueprint and assembly; README and HANDOFF stale. | Log row added (file times: blueprint written 15:58:04Z and compiled 15:58:12Z, assembly written 15:58:36Z and compiled with empty output, all in scratch before the agents' launch at 15:59:18Z). README and HANDOFF are updated with the final records of this branch. |
| C-7 | NIT | "eight interface propositions" (seven); "13 new modules, leanchecker each" mixes the 12 new proof files plus the LOC2 blueprint with the 13 modules checked (9 SPL-N including the earlier assembly, 4 LOC2). | Accepted as corrections here. |
| C-8 | NIT | Other wording (agent names, A5U agents' finish rows, saved-report hashes of route referees). | Accepted; this branch's log rows give them. |
