<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch A5U: answers to the post-proof reviews (2026-11-28, session 17)

Written by the lead. Three post-proof referees from fresh contexts, of the lead's model family, reviewed commit
7f27305 (A5U integrated) while the tree was frozen: A (fidelity), B (soundness), C (adversarial). Launched 17:05:04Z
(brief SHA-256 ba0f3ca89aa1df6d20890dfdf8c9575b0862b5434673b2716d53dc6bfbc85b64); task records A 253 s, B 268 s, C
506 s (C ended about 17:13:30Z); the tree was not written while they ran. Isolation by instruction. Saved reports
(outside the tree): A a710248e…28cc4bd1, B e9051cb6…a68677dc, C d58e3629…a4891b23. Findings in the lead's words.

**Outcome: FAITHFUL (A), SOUND (B), claims SUPPORTED (C); no BLOCKER, no MAJOR. C judged the records INACCURATE at
MINOR and NIT level (counts and the wording of the order claim), answered below. The theorem stands.**

## 1. Referee A (fidelity)

`OscInt.API.triCrossoverUpper` has the frozen type (`#check`, a syntactic check of the declared type, and an
`example` restating the frozen text); the six definitions it uses, re-typed from the source text in a fresh namespace,
are `rfl`-equal to the repository's, and the theorem proves the re-typed statement with the three standard axioms; the
frozen files' bytes equal the freeze manifest; `r` and `C` are chosen from `a₀` before `α, t, n`; the prose of
`docs/statements.md` ("Batch A5U") and its "equivalently `C min(t^{−2/3}, ε^{−1/4} t^{−3/4})`" remain accurate.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| F-1 | MINOR | The records say 18 parts; the blueprint has 17 propositions (A1–A13, A12a, B1–B3), proved in 18 modules (B1 in two). "Leanchecker on the 20 new modules" leaves one of 21 unexplained. | **Correct.** The route referee's snapshot of the blueprint has SHA-256 b1ebe548…5f01c2, identical to the committed file, so the blueprint did not change after the review: "18" was the route referee's miscount, repeated by the lead. The 21 new modules are the 18 part modules, the assembly, the final file and the blueprint; the earlier `leanchecker` loop covered the 20 under `OscInt/Front`, and the lead ran `leanchecker Blueprint.TriangularCrossover` at 17:10:13–17:10:22Z against the tree build: exit 0, empty output. Corrected in the STATUS row, the revision section of `docs/proof-A5U.md` and the final file's docstring; the route answers, the log rows and the commit message of 7f27305 are records and are corrected here. |
| F-2 | MINOR | Answer R-3 of the route answers was accepted but not carried out: the blueprint, the assembly and the part headers cite scratch paths (`stmts/proof-A5U-draft.md`, `a5u-plan/…`). | **Correct.** Done in this commit: every such reference in the 18 Lean files now points to `docs/proof-A5U.md` (whose sections 1–6 are those of the draft), to the packet answers, or to "the lead's planning notes (outside the repository)". Docstrings only; no declaration changed. |
| F-3 | NIT | The blueprint header names the namespace `OscInt.A5U`; the parts are in `OscInt.A5UAux`. | Fixed. |
| F-4 | NIT | The docstring of `A5TiltJetFacts` in the blueprint's list still describes the TRI-Q route. | Fixed (the proof computes the jets directly, as `docs/proof-A5U.md` already said). |
| F-5 | NIT | `comparator-A5U.json` pins no definitions. | As in `comparator-K2.json`; the challenge imports the frozen statement module, so the definitions are the frozen ones. The comparator file is frozen and is not changed. |

## 2. Referee B (soundness)

All 23 files of the batch (21 new modules, the blueprint and the statement) recompiled from copies with exit 0 and
empty output; two planted controls (a false theorem appended, two arguments swapped) were rejected; the axioms of the
final theorem, of `triCrossoverUpper_of` and of each of the 17 part theorems are the three standard ones; no
forbidden construct, no `set_option`, no `decide +kernel` (the only `decide`s are `Odd 3`, `Odd 5`, `Odd 7`); every
internal interface fixes its constants before `α`; the hypotheses are satisfiable, and a bite probe derives
`∃ C, ∀ t ≥ 1, ∀ n, ‖triKernel a* t n‖ ≤ C t^{−2/3}`; no helper name is defined twice. Findings: MINOR, the namespace
in the blueprint header (= F-3, fixed); NIT, scratch paths in 17 files (= F-2, fixed).

## 3. Referee C (adversarial)

Reproduced: the frozen file's hash at the freeze and at HEAD; that no A5U proof file is in any commit before 7f27305,
which follows the answers stamp; 106 statements; the type and axioms; the 21 modules compile (and a planted false
step is rejected); that every admissible window excludes `α = 0` (its own compiled probe, by K2-D at `α = 0`); the log
arithmetic of the correction row (one second off, NIT); the jet algebra and the 18 cuts of the route by hand.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| C-1 | MINOR | Part counts off by one in every record; asks for the hash of the snapshot blueprint. | = F-1. Snapshot and committed blueprint are byte-identical (b1ebe548…5f01c2); the snapshot's assembly is byte-identical to the committed assembly (3312c2c3…87b77391). |
| C-2 | MINOR | The route answers say the six proof agents were launched together and that no part changed after the review; the log shows X was launched about 16:28, and W, G2 and X finished after the referee ended. The STATUS row is silent on the overlap, unlike the corrected K2-FQ row. | **Correct about the wording.** From the task records: five agents launched 16:18:50Z; X about 16:28Z; G3 ended about 16:25:23Z, G1 16:27:25Z, B 16:31:12Z (before the route referee ended, about 16:32:43Z), W 16:42:52Z, G2 16:44:31Z, X about 16:44Z (after it). So half the parts were finished after the route review. What holds: the lead sent no message to any A5U proof agent (the session's record has two messages to agents, at 12:41:55Z and 12:48:47Z, neither to an A5U agent) and the review had no FATAL and no MAJOR, so no part was changed in response to the review; no part was in the repository before 7f27305. The STATUS row now says this. |
| C-3 | MINOR | `docs/proof-A5U.md` says it was written after the blind reviews; the log has route drafts in scratch during them. | **Correct.** The route was drafted in scratch during the blind pre-proof reviews (which did not see it) and finished and committed after their answers were stamped. The sentence in `docs/proof-A5U.md` now says so. |
| C-4 | MINOR | Owed plant A-2 not in the tree and not listed as outstanding. | Now a record: `docs/replay/plants/2026-11-28-owed-A-2-L-i/` (A-2 TRUE WEAKENING, derived from K2-U alone and from the proved `OscInt.API.triDecayUpper`; with it, LOC2's L-i is DETECTED by a compiled witness). |
| C-5 | NIT | Scratch paths in Lean files; R-3 not carried out. | = F-2, fixed. |
| C-6 | NIT | No record backs "make push-gate RUN=1 on this commit before the push" of 7f27305. | Log row added: 16:56:45–17:04:42Z, `make quick` PASS, guard 285 files and 0 violations, axiom audit 3228 of 3228 clean, TYPE-OK for the eleven K2/SPL-N/LOC2/A5U theorems, entry point 212 names, `push-gate: PASS`; pushed 17:04:44Z. |
| C-7 | NIT | The assembly is called "the lead's assembly", but an architect agent drafted it. | Fixed in its docstring: drafted by an architect agent, reviewed by the lead. |
| C-8 | NIT | `docs/proof-A5U.md` says the Mathlib names are checked in `MathlibNames.lean`; only ten were added. | Accepted as a NIT: the ten are the route's named lemmas; the parts use more Mathlib names, all checked by compilation at the pin. |

## 4. What changes

No statement, stamp or challenge. Docstrings of 18 A5U Lean files (no declaration), the STATUS row of A5U (and the
plant line of K2-FQ), `docs/proof-A5U.md` (authorship sentence and the count), the session log, and the new plant
record. The A5U row says "post-proof reviews answered"; "machine-checked as stated" waits for the final isolated
replay.
