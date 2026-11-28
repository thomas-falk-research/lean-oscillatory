<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch K2: answers to the post-proof reviews (2026-11-28)

Written by the lead. Three referees reviewed the proved batch K2 at commit 76aff95. All three ran from fresh
contexts, were of the lead's model family, compiled probes in their scratch one Lean process at a time, and wrote
nothing in the repository. Their briefs are identified by SHA-256 in `docs/progress/2026-11-28-session16-log.md`.
The reports are not reproduced; findings are in the lead's words.

**Outcome: six FAITHFUL (scope full), SOUND, claims supported after changes; no BLOCKER and no MAJOR finding from
any referee.** No finding is against a statement or a proof; every finding is against a record or a docstring, and
each is answered below.

## 1. Referee A (fidelity; harness 210 s, 22 tool uses)

- **Types.** For each of the six final theorems, the elaborated type is exactly `mkConst` of the stamped statement
  constant (`ci.type == mkConst s` is true). So no hypothesis or binder is added and no constant is substituted.
- **Axioms.** propext, Classical.choice, Quot.sound for all six; no `sorryAx`, no `Lean.ofReduceBool`.
- **Stamp.** The statement file (32b99c38…) and all 23 statement files and the challenge file equal the stamped
  manifest.
- **Shadowing.** No statement symbol is redefined or shadowed anywhere in the environment.
- **Verdict:** FAITHFUL ×6, scope full.

| ID | Severity | Finding | Answer |
|---|---|---|---|
| A-1 | MINOR | The K2-L prose omits `ε > 0`. | Clarification K2-b in `docs/statements.md`. |
| A-2 | NIT | "Closed ball" is the max-norm ball (a square). | K2-b. |
| A-3 | NIT | "The claim, if proved" is now out of date. | K2-b points to STATUS. |
| A-4 | NIT | "Every real time" in "Why" is broad. | Already narrowed by K2-a. |

## 2. Referee B (soundness; harness 339 s, 34 tool uses)

- **Dependency graph.** All six final theorems are closed terms; every part is a closed term of its blueprint Prop.
  P9 enters P11 and P12 only as a hypothesis and is supplied in the final file.
- **Forbidden constructs.** None in any new file.
- **Kernel checks.** `leanchecker` exit 0 on all 15 new modules and on the blueprint.
- **Vacuity.** None: the K2-U split is a genuine `by_cases` on TRI-K's cases, and the K2-D witnesses are genuine.
- **Verdict:** SOUND.

| ID | Severity | Finding | Answer |
|---|---|---|---|
| B-1 | NIT | The final file's docstring names only two assembly files. | Fixed. |
| B-2 | NIT | The blueprint docstring lists S5.1′ for K2-U. | Fixed: the A3 branch uses P5, the bridge and K2-L with m = 4. |
| B-3 | NIT | P7's partition differs from section 2 of the route. | `docs/proof-K2.md` section 9. |
| B-4 | NIT | Section 8 does not record P10a's direct bound or P11's dropped plateau. | Section 9. |
| B-5 | NIT | `OscInt/API.lean` imports 10 of the 15 new modules directly. | No change; the rest come in through the final file. |

## 3. Referee C (adversarial; harness 565 s, 50 tool uses)

**Compiled checks of meaning.**
- **No faster or slower rate, for every α.** `no_better_exponent` follows from K2-D with the sanity lemma
  `rate_separation`, and `no_slower_lower` follows from K2-U. So the exponent is sharp in the sense of the supremum
  over sites; no constant is claimed.
- **The spanning hypothesis of K2-L is redundant.** `reducedOrderBound_noSpan` compiles.
- **No statement is vacuous.**
- **Nothing in the records claims uniformity in α.**
- **One prior-art search.** It found only Ge–Hua–Jia–Zhou, which is already cited.
- **Verdict:** claims supported after changes.

| ID | Severity | Finding | Answer |
|---|---|---|---|
| m1 | MINOR | STATUS's K2 paragraph, README and the hand-off still say "not proved". | Fixed in all three. |
| m2 | MINOR | The hand-off describes a superseded route. | Rewritten as "route as proved". |
| m3 | MINOR | Several session-log rows carry times later than the commits that contain them, and the 04:01 correction is incomplete. | Correction row in the log, with the git commit times as the authority. |
| m4 | MINOR | The comparator and `make quick` claims have no committed output. | `docs/replay/2026-11-28-K2-integration-checks.txt` holds the raw comparator output and the `make quick` lines of 96f003e. "Machine-checked" waits for the full replay record. |
| m5 | MINOR | The owed plants A1 and A2 are not done, and STATUS does not say so. | The four relative plants are closed without hypotheses (`docs/replay/2026-11-28-K2-plants-closed.txt`). A1 and A2 are with plant agent PL, launched 04:18; their outcome will be recorded with the replay. |
| n1 | NIT | "14 parts" is wrong: there are 13, and P4 is reused. | Fixed in the hand-off. |
| n2 | NIT | The route is not updated for how the parts were proved. | Section 9 of `docs/proof-K2.md`. |
| n3 | NIT | "All real times" in the hand-off is loose. | Fixed (sup over sites; `t ≥ 1` and `t ≥ T_α`). |
| n4 | NIT | The T6L comparison is one-sided. | K2-b. |
| n5 | NIT | The sanity lemma `span_of_hyps` feeds the proofs, and STATUS's lists omit it. | Named in STATUS's K2 paragraph. |
| n6 | NIT | P10a's docstring omits the factor `a = 2^{1/m} ≥ 1`. | Section 9 states the bound with the factor. The stamped-free module docstring is left as it is: the bound it states is weaker by a factor at least 1, so it is still true. |

## 4. Status

The six STATUS rows stay "proved in Lean (post-proof reviews and replay pending)" until these answers are stamped
and a full isolated `make verify-all` passes. Then they become "machine-checked as stated".
