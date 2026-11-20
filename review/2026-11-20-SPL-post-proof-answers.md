<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL: answers to the post-proof reviews (2026-11-20)

Written by the lead. Step 10 of `CONTRIBUTING.md`. Three agents with fresh contexts, all of the lead's model
family, were launched on 2026-11-20 at 03:23:29Z on the integration commit e840f8e (HEAD was 8c8e6ed, which adds a
lesson and two rows of the session log and nothing else), after the SHA-256 of each brief had been logged and
pushed. The briefs are not committed and the reports are not reproduced: every finding below is in the lead's
words, and a reader has only the lead's paraphrase (the hashes of the briefs are in the session log; the reports
were returned as text and are not hashed). The referees were read-only by instruction; each says it did not depart
from its isolation. Lean was run only through the session's lock. Finish times: A at about 03:36, B and C at about
03:43.

No calibration copy with planted errors was given to any of them (`docs/calibration.md`); what follows is three
reviews of unmeasured detection rate by agents that share the lead's blind spots.

## Verdicts

| Statement | A, fidelity | B, soundness | C, adversarial |
|---|---|---|---|
| SPL-I `StationaryLeadingIdentityStatement` | FAITHFUL, full | SOUND | no regime found in which it fails |
| SPL-S `StationaryLeadingStatement` | FAITHFUL, full | SOUND | no regime found in which it fails |
| SPL-K `StationaryLeadingSevenEighthsStatement` | FAITHFUL, full | SOUND | no regime found in which it fails |
| SPL-A `StationaryLeadingAttainedStatement` | FAITHFUL, full | SOUND | no regime found in which it fails |

Counts as the referees gave them: A, no BLOCKER, no MAJOR, 5 MINOR, 5 NIT; B, no BLOCKER, no MAJOR, no MINOR, 4
NIT; C, 1 BLOCKER, no MAJOR, 10 MINOR, 3 NIT, and for the records the judgement OVERSTATED in one place. The
BLOCKER is against a record, by the briefs' definition ("a record claims more than the evidence"); no finding of
any severity is against the Lean text of a statement or against a proof.

## What each referee did (as reported; none of it is in the repository)

- **A.** Its own Lean files: each theorem's stored type compared with the statement constant as expressions,
  without unfolding; the axioms; a scan of the environment and of the sources for shadowing definitions; the frozen
  bytes hashed by the tools' rule and by an independent cut, against the pins, the stamped manifest and the
  registry; the three timestamp tokens of the statement stamp verified against the pinned roots; the history of the
  statement file since the freeze (only the attribution block was added); a fresh elaboration of the frozen bytes
  compared with the built constants (ten definitions, equal); explicit transcriptions of each statement closed by
  `rfl`; numerics at 25 digits on a complex amplitude that is not even; the records read against the evidence.
- **B.** All ten proof files read in full (2049 lines); an independent recompilation of their bodies in one file
  under fresh namespaces (exit code 0; the fifteen named theorems on the three standard axioms; 194 declarations
  with the same types as the library's); copies of the four statements, the seven blueprint propositions and the
  two VC2 statements equal to the library's constants by `rfl`; the kernel checker on two modules (exit code 0); a
  Lean proof that P-tail and P-value together are equivalent to the third clause of P-fresnel; one instance of
  every blueprint proposition with a non-trivial conclusion, numerically at 30 to 50 digits (the Fresnel primitive
  from its power series, an amplitude of class C³ only, the bump built as in the Lean file); the use of the VC2
  theorems within their hypotheses; the closure of the four theorems (27 modules of the repository, none of them a
  sanity module); each of the four delicate proofs followed lemma by lemma; the lead's interface check reproduced
  line for line.
- **C.** Its own derivation of SPL-I; numerics on a complex Gaussian with a complex centre and on an amplitude with
  slow decay; both stamps verified (tokens against pinned roots, every manifest line against the tree of its
  commit); the order of the commits; each of the twelve source files of the batch re-elaborated as committed, with
  a negative control; more than thirty numbers, counts and hashes of the records recomputed, all matching; a search
  of Mathlib at the pin for a Fresnel integral (none); a compiled theorem that SPL-I stays true with any constant
  added to the kernel; the conditional and relative witnesses of the plant record composed with the proofs (14
  files, all compiling).

## Findings and answers

"Fixed" means: in the commit that adds this file. A commit message cannot be changed; where one is wrong the
correction is here and in the session log.

| # | Referee, severity | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | C, BLOCKER (records) | The README sentence on the batch and the message of commit e840f8e present SPL-A as the sharpness of the bound with 7/8. SPL-A is the sharpness of the kernel bound of SPL-S; the constant 7/8 is not sharp (the supremum of the kernel is about 0.722). | True, and the lead's wording. The README is fixed. The message of e840f8e stands uncorrectable; corrected here and in the session log: read "the bound with 7/8 (SPL-K), and the sharpness of the kernel bound of SPL-S (SPL-A)". The STATUS rows, the registry summaries and the API index were right. |
| 2 | C, MINOR | An answer to the blind review said that the proof of SPL-I fixes the kernel. It does not: the integral of g₃ is zero for every amplitude, so SPL-I holds with any constant added to the kernel (compiled by the referee). A mutation equivalent to the statement, in no record. | True. The stamped answers of the blind review are not edited; the correction is clarification SPL-d of `docs/statements.md`: the kernel is pinned by its oddness (in the frozen definition) with SPL-I, its supremum by SPL-S with SPL-A. The referee's theorem is recorded, re-run by the lead (`docs/replay/plants/2026-11-20-SPL-closed`). |
| 3 | A NIT, B NIT, C MINOR | STATUS still said that 7 plants are refuted only under a kernel bound that has no Lean proof; the bound is proved since the integration. No record showed the conditional and relative witnesses composed with the proofs. | Fixed. The referee's 14 compositions were re-run by the lead under the lock (2026-11-20, 03:44:29Z to 03:45:14Z; each exit code 0, standard axioms) and are recorded with their output (`docs/replay/2026-11-20-SPL-plants-closed.txt`): 36 of the 42 plants are now refuted outright. STATUS says so and no longer says "none undetected" without its scope. |
| 4 | A NIT, C MINOR | The records disagree on what descends from the route referee: STATUS said three parts, the route's section 12 and a commit message four files; the referee also wrote the first two clauses of P-fresnel, an assembly of its own and two lemmas on the route of P-value. Section 10 of the route still called the assembly the lead's. | Fixed in STATUS and in sections 10 and 12 of the route. Exactly: P-bound, P-kernel, P-line and the first two clauses of P-fresnel descend from the referee's proofs through a fresh agent's rewriting; the third clause of P-fresnel is that agent's; two small lemmas of P-value are the referee's, reused by the P-value prover (its brief pointed to them, and its report says so); the referee's assembly was not used. For those parts the route review is an author's verdict; P-tail, P-value and P-bump had a reading only. |
| 5 | C, MINOR | The sanity file predates the freeze and contains proofs that reappear in the later proof: the oddness of the kernel (one clause of P-kernel) and two lemmas on the constant of the leading term, about 25 lines. STATUS and the hand-off did not say so. | True; the sanity brief asked for exactly these facts about the definitions, and the provers were told they could read the sanity file and copy ideas under new names. STATUS now says it. No proof of a statement or of a whole proposition is in that file. |
| 6 | C, MINOR | What the order claim rests on that a stranger cannot check: that no proof text existed outside the repository before the stamp of the answers, every launch and finish time, the blindness of the referees, the content of briefs and reports. One sentence of the pre-proof answers and one commit message say "no Lean proof of a statement existed" without "in the repository". The provers delivered within minutes and the files entered byte for byte, which is also what proof text drafted earlier would look like; only the briefs could settle it. The referee found no evidence of drafting. | Accepted; STATUS now lists what is and is not verifiable, the over-broad sentence is corrected there, and the pattern of the delivery times is disclosed there. The lead's statement, which is not evidence: to the lead's knowledge no Lean proof text of the batch, other than the sanity file (finding 5), existed in the session before 01:18:24Z, and the briefs of the provers contain mathematics and Mathlib names, not Lean proofs, except that the brief of P-value pointed to the referee's two lemmas and the integrator's brief to the referee's files. The briefs are kept in the lead's scratch with their logged hashes; the owner can publish them. |
| 7 | C, MINOR | The registered numeric test was run eleven seconds after its registration commit; that commit also carries the exploration that already gave the kernel's maximum; no timestamp token lies between registration and run. As a pre-registration it has little weight. | True as to the times. STATUS says so. The records had claimed only "after the registration commit". |
| 8 | A MINOR, C MINOR | Attribution worded more firmly than the prior-art page supports: "classical" for the whole batch in README, CHANGELOG, a commit message and the header of the final file, where the page says "classical in substance" for the identity and "not found" for the bounds with this kernel; a docstring citing "1956, section 2.8" although what was read is the 1955 report, sections 2.8 and 2.9; a stale sentence in the route about how Erdélyi was read. | Fixed in README, CHANGELOG, both docstrings of the final file (a comment-only change of a Lean file; the integration record notes the new hash) and the route. The over-attribution leaned away from a novelty claim; nothing is or was worded as new. The frozen statement file's own sentence ("classical (Erdélyi)") cannot be changed; the prose and these records carry the qualified form. |
| 9 | A, MINOR | The prior-art page says its works are collected in the bibliography file; the sources of the SPL section are not there. | The page now says so. Adding them with checked identifiers is an open item (not done here: identifiers would have to be verified, not typed from memory). |
| 10 | A, MINOR | No disclosure for this batch that no calibration copy was reviewed. | Fixed in STATUS and on the calibration page. |
| 11 | A, MINOR | A README caveat written for v0.7.0 says every statement was replayed with the corrected driver; four are not replayed. | Fixed: "the 86 statements of v0.7.0". |
| 12 | A, MINOR | `llms.txt` did not say that the post-proof reviews were pending. | It now says they are answered and the replay is pending. |
| 13 | A, NIT | README says "the 21 newest statements" where batch SPL is newer. | Fixed. |
| 14 | A, NIT | The API index says "g₃ need not be continuous", the wording that a clarification had to qualify. | Fixed in the annotations (a derivative has no jump: piecewise C³ amplitudes are excluded); index regenerated. |
| 15 | A, NIT | The consumer example's docstring omits that g itself is integrable. | Fixed. |
| 16 | B, NIT | All four theorems, the identity included, depend on batch VC2 through the bound of the Fresnel primitive; the records said only that the 7/8 comes from VC2. | STATUS and the route say it now. The paper route's own bounds would have kept SPL-I free of VC2; that is a possible later refactoring, not done. |
| 17 | B, NIT | Small lemmas are proved several times across the parts. | True; parts do not import each other. Left as it is; noted in the route. |
| 18 | B, NIT | The interface-check record predates the seven-proposition blueprint and does not say that P-tail and P-value were not checked, or that its P-bump check uses the route's construction. | Noted in the route (end of section 12). The record itself is not edited. |
| 19 | C, MINOR | The route-referee answers called the referee's own assembly "independent evidence". | Reworded there. |
| 20 | C, MINOR | The blind pre-proof referees ran for about eight and eleven minutes, and the answers file was written within about a minute of the second report. | True as to the durations (session log). The lead did not record when the drafting of the answers began and cannot reconstruct it from the records; the file times are as the referee read them. STATUS gives the durations. |
| 21 | C, MINOR | The registry has a proving theorem for all 90 statements and no field for "replayed"; a downstream check of this branch treats the four like the 86. | True; STATUS says it. The branch is not a release; the replay is the next step. A status field in the registry is a possible change of the tools, for the owner. |
| 22 | C, NIT | A session-log row headed "about 00:45" is in a commit dated 00:41:14, one second before the logged launch. | The heading was written as an estimate before the launch; the launch time in the lead's scratch log is 00:41:15Z. Not edited; said here. |
| 23 | C, NIT | The integration checks and the gate ran on the working tree that became the commit, not on a checkout of it. | True and said in the record. The referee re-elaborated the committed files; the isolated replay runs on a commit. |
| 24 | C, NIT | The prior-art page said "two integrations by parts". | Corrected to three, with the date. |

Observations without a request, noted: a restated copy of `SplAmplitude` is syntactically equal to the library's
only under the statement file's own imports (A); the commitment tool accepts a statement file whose frozen hash is
in any pinned manifest while the registry tool compares against the specific stamp, so the chain fails closed (A,
from reading the code); SPL-K says nothing useful for small λ or for oscillating amplitudes, where ‖g‴‖₁ grows like
the cube of the frequency while the true remainder grows like its square (C: at frequency 20 and λ = 2000 the
bound is 22 times the truth). The last is a limit of the statement, of the kind `docs/statements.md` lists.

## What these reviews do not establish

No kernel replay by independent checkers, no comparator run and no rebuild from source were made by any referee;
that is the isolated replay, which is run after this file is committed. No one read Erdélyi's text or any other
source for these reviews. The OpenTimestamps proofs of the stamps were not checked. No human has read the
statements.
