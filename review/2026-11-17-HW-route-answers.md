# Answers to the route referee of batch HW (2026-11-17)

Subject: the route `docs/proof-HW.md`, the blueprint `Blueprint/HadamardWalk.lean` and the lead's compiled assembly
`OscInt/Front/HadamardWalkAssembly.lean`, as committed in bcad78c. One fresh-context referee, read-only, on a
snapshot of those files with the frozen statements, the interface checks and the frozen statements S1.2 and S1.3.
It proved nothing and was not allowed to run Lean: that the assembly compiles rests on the lead's build and on
`make quick` (session log, 01:28:09Z). Lead and referee are AI agents of one model family; no calibration packet
was given. The brief and the report are not recorded verbatim (rule 19); their SHA-256 values are in the session
log. A difference from the earlier batches, chosen by the lead to save time: the four proof agents were launched
together with this referee, not after its report, so the referee's notes did not reach them; it found nothing that
required a part to be redone.

Verdict: sound. No BLOCKER, no MAJOR; three MINOR; five NIT. The referee recomputed by hand and numerically (30 to
40 digits) every identity of H1 to H8, the kernel recursion, HW-R, the derivative chain, both lower bounds, the four
amplitude norms, the three constants (6.86990 ≤ 7, 11.86339 ≤ 12, 38.45358 ≤ 39), the linear decomposition, and the
shapes and constants of S1.2 and S1.3; it could not falsify a blueprint proposition.

| Finding | Severity | Answer |
|---|---|---|
| The route names two parts that do not exist (`HadamardKernelBoundFacts`, `HadamardLinearityFacts`), and the blueprint's header says six propositions where there are five. | MINOR | Accepted; slips of the lead. Route revision, item 1; the header of the blueprint is corrected. |
| The part HW3 must itself prove that `hwAmp'` is interval integrable and that \|sin k\| or \|cos k\| is at least 1/√2 on the four open arcs; no hypothesis supplies these and the parts table did not list them. | MINOR (gap) | Accepted. The part proved them (it was launched before this finding was known). Revision, item 2. |
| Slack is 0 % in the four amplitude norms, 1.1 % in the constant 12 and 1.4 % in 39; the briefs should say so. | MINOR (feasibility) | The briefs said that the amplitude norms are equalities; the parts were proved with these margins. Revision, item 3. |
| Five NITs. N1: the route gives the path of the interface script in the repository, the packet had it one level up (packet layout only). N2: the route lists the derivative chain to second order where S1.3 needs three derivatives; all three are in `HadamardPhaseFacts`. N3: for t = 1 the route and the assembly argue differently, both validly, and the route shows only the first component. N4: the packet held the statements S1.2 and S1.3, not their proofs, so the referee could not confirm that `OscInt.vanDerCorput_two` and `OscInt.vanDerCorput_three` exist and prove them; nor that the assembly compiles; nor the dates of the route's first paragraph. N5: the interface script tests the five blueprint propositions, not the two numerical inequalities of H6 (the referee checked those itself). | NIT | N1: no change. N2, N3: accepted as remarks on the route; the Lean files are what was proved, and the reviewed route text is left as it was. N4: the two theorems exist with those types (`OscInt/VanDerCorput/Final.lean`; the part HW3 applies them and compiles), and the assembly compiles (`make quick`, session log). N5: the two inequalities are now Lean lemmas inside the part HW3, the first of them in the changed form recorded in the route's parts table. |

Not verified by the referee, by its own account: that the blueprint and the assembly compile; the two theorem names
above.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
