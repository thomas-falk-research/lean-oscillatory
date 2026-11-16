# Answers to the post-proof reviews of batches PA and KL (PA-C, PA-T, LC-1, KL-D, KL-C, KL-F)

Three fresh-context referees read the batches at 2d28449, after the parts were integrated and before the replay:
A (fidelity), B (soundness of the formal proof) and C (adversarial). All three are AI agents of the same model
family as the lead and the provers; their briefs and reports are not recorded verbatim (rule 19), the briefs'
SHA-256 values are in the session log, and each finding is restated below in the lead's words. Each ran Lean on
scratch files of its own (no `lake build`, no `make`); no replay was running; nothing was written in the tree while
they read. One defect of the briefs: the verdict vocabulary they refer to was missing for B, who used SOUND / NOT
SOUND. C read the lead's scratch directory (read-only) and fetched two arXiv abstracts, both beyond its brief; it
says so.

| Referee | Launched at commit | Launched (UTC, lead's clock) | Run time (task record) |
|---|---|---|---|
| A (fidelity) | 2d28449 | about 16:15:10 | 563 s |
| B (soundness) | 2d28449 | about 16:15:10 | 720 s |
| C (adversarial) | 2d28449 | about 16:15:10 | 1422 s |

## Verdicts

| | A (fidelity) | B (soundness) | C (adversarial) |
|---|---|---|---|
| `OscInt.API.fourierCoeffStrip` : PA-C | FAITHFUL, scope full | SOUND | no regime found in which the statement fails |
| `OscInt.API.trapezoidalRule` : PA-T | FAITHFUL, scope full | SOUND | same |
| `OscInt.API.latticeKernel1LightCone` : LC-1 | FAITHFUL, scope full | SOUND | same |
| `OscInt.API.kusminLandau` : KL-D | FAITHFUL, scope full | SOUND | same |
| `OscInt.API.kusminLandauTwoOverPi` : KL-C | FAITHFUL, scope full | SOUND | same |
| `OscInt.API.kusminLandauDeriv` : KL-F | FAITHFUL, scope full | SOUND | same |

No BLOCKER. Three MAJOR findings (A: two; C: one), all against the records, none against a statement, a proof or
the mathematics. The Lean proofs are unchanged by the answers; two module docstrings and three theorem docstrings
of the lead's two final files were corrected.

**What the referees checked, in brief (their statements).**
- A: each theorem's type is syntactically the bare statement constant (own scratch file, `example` and
  `#print axioms`); no shadowing definition anywhere; the two statement files byte-identical to the stamped ones
  (manifest, `stamps/statements.json`, git blobs; three RFC 3161 tokens verified); a verbatim re-elaboration of each
  statement equals the library constant by `rfl`; each Lean statement read symbol by symbol against the prose.
- B: all nine proof files read in full; no forbidden construct, instance, variable, option or invisible character;
  an independent recompile (per batch concatenated, and nine verbatim copies), with the axioms of the six theorems
  and the six blueprint facts; planted wrong constants and a planted `sorry` were caught by its own setup;
  `leanchecker` exit code 0 on the eleven modules; no blueprint proposition is vacuous (one instance each); the two
  auxiliary definitions of the core part are used only inside it; the interface checks reproduced byte for byte.
- C: an attempt to break each statement as the Lean text states it (none found); all six recompiled, with
  `leanchecker` and `leanchecker-paranoid` on its own build; 6 of 6 timestamp tokens verified against the pinned
  roots; both manifests against the trees of their commits (1360 and 1511 files, no mismatch); no proof text in the
  git history or, by file times, in the lead's scratch before 15:24:19Z; sixteen groups of numbers recomputed.

## Findings and answers

1. **MAJOR (C).** The negative half of the order claim rests on unrecorded material: "no Lean proof … in scratch"
   is the lead's statement; the commits after the second stamp carry no timestamp of their own; briefs, reports,
   the `make quick` logs and the per-module kernel checks existed only in scratch.
   *Answer.* Accepted. (a) The claim is reworded where the records are not frozen: `docs/STATUS.md` has a paragraph
   that separates what a stranger can verify from what is the lead's word, and `docs/statements.md` points to it
   from both batches. The docstrings of the two statement files are frozen and keep their wording; this file and
   STATUS are the correction. (b) A listing of the scratch directory (times, sizes, hashes) is committed:
   `docs/replay/2026-11-16-session13-scratch-listing.txt`; its header states what a listing cannot show. (c) The
   integration checks are now an evidence file, re-run by the lead on 2d28449:
   `docs/replay/2026-11-16-PA-KL-integration-checks.txt` (17 modules, exit code 0 each; the audit lines of the batch;
   the six type assertions). (d) The commit that adds this file is stamped, which gives the proofs and these
   answers an upper time bound from three authorities. Not repaired, because it cannot be: the lead's context is
   not a file, and the briefs and reports stay unrecorded under rule 19.
2. **MAJOR (A).** README said, without qualification, that every proof is replayed by six kernel checkers; that was
   false for these six. *Answer.* Accepted and corrected: the sentence now speaks of statements that STATUS calls
   machine-checked as stated, and names the six that await the replay.
3. **MAJOR (A).** "Per-module leanchecker" and "axiom audit" for these rows were typed claims with no evidence file.
   *Answer.* Accepted; see 1(c). STATUS cites the file.
4. **MINOR (C).** The proof plan is older than the freeze: both paper routes, with the names of the blueprint
   propositions, date from 12:43Z, and a check of 24 Mathlib names for them from 12:10Z. By git, the statement files
   were first committed as drafts at 12:30:15Z (38a1062, marked not frozen), committed in their final form at
   12:55:02Z (276d8d7) and stamped at 13:10:03Z: the paper routes are younger than the committed drafts and older
   than the freeze; the name check is older than both. *Answer.* Accepted. The route headers said "before the blind
   pre-proof reviews were answered", which is true and less than the whole truth. STATUS now states the exception
   with the times; README says "before their Lean proofs". One known consequence for the statements was already
   disclosed (PA, modelling choice 2: periodicity is asked on the strip so that no identity-theorem argument is
   needed).
5. **MINOR (C).** STATUS wording: the word "machine-checked" stood in the status column before the replay; no
   sentence said that the reviewers are AI agents. *Answer.* Accepted in substance. The documentation check
   (`tools/check_docs.py`) requires the status cell of a row with a proving theorem to begin with "machine-checked",
   so the word stays; the cells now read "machine-checked only by build, axiom audit, statement types and per-module
   leanchecker (evidence file); … replay pending, so not yet machine-checked as stated", and the new STATUS
   paragraph explains the prefix and says who the reviewers are. Changing the check's rule is a change to the
   release tooling that the lead proposes and does not make.
6. **MINOR (C).** The sanity layers pass more false variants than the records listed. C exhibited six, each false
   by a certified computation and consistent with every sanity datum:

   | Variant | False because |
   |---|---|
   | PA-T with the weight 2π/(N + 1) in the trapezoidal sum | v = 1, N = 1, a = 2: error π against 4π/(e² − 1) = 1.967 |
   | LC-1 with n²η in place of \|n\|η | t = 1/2, n = 2: J₂(1/2) = 0.0306 against 0.00082 |
   | LC-1 with η + η³/6 in place of sinh η | t = 1, n = 10, η = √18 |
   | LC-1 with the exponential squared | t = 1/4, n = 1: J₁(1/4) = 0.1240 against 0.1119 |
   | KL-C with 1/(πλ) + 7/4 | λ = 1/7, a seven-term sequence: 4.381 against 3.978 |
   | KL-D with 2/(πλ) − 1/6 | λ = 1/5, Landau's sequence: 3.0777 against 3.0164 |

   *Answer.* Accepted as stated (the lead did not re-derive the six computations). The pattern is right: each bound
   is pinned at a few parameter points, the quadrature weight by nothing. The proofs exclude every false variant,
   since the frozen text itself is proved. The other direction (a frozen text weaker than intended) is not helped
   by a proof and rests on the fidelity reviews and on the data where the bounds are attained; STATUS says so.
   The sanity files and plant records are reviewed records and are not edited; a later batch that touches these
   statements should add data at λ = 1/5 and 1/7, a kernel value at \|n\| ≥ 2 and a constant function at N = 1.
   C's rational witness against Cheng and Graham's bound in the derivative form is recorded in `docs/statements.md`.
7. **MINOR (C).** What the short proof runs and the single model family can hide. Proof correctness: nothing (the
   kernel does not care). Fidelity: a shared misreading of a source would pass every layer; the lead read no primary
   source for either batch, and the docstrings gave attributions flatly. *Answer.* Accepted. The docstrings of the
   two final files now say what was read by whom, and that Landau's sharpness for every λ is not proved here. The
   part files were last written two to four minutes after launch; that is consistent with detailed routes and
   briefs and equally with reuse of earlier text, and no record can tell the two apart (finding 1).
8. **MINOR (C).** Calibration: the pooled interval of round 3 is nominal (two referees, four plants each) and its
   controls assume what is measured. *Answer.* Accepted; `docs/calibration.md` states both.
9. **MINOR (C).** Reproducibility gaps: no pin for the numerics environment; no consumer example for the two
   batches; no timestamp on the proof commit; reliance on a third-party cache for Mathlib. *Answer.* Added:
   `numerics/review/requirements-review.txt` (versions, not hashes); `examples/consumer/ConsumerPeriodicAnalytic.lean`
   and `examples/consumer/ConsumerKusminLandau.lean`, compiled by `make quick`; the stamp of this commit. Not
   changed: the Mathlib cache (the from-source workflow remains the fallback); the OpenTimestamps proofs are not
   upgraded (that would rewrite files inside stamp directories, which the lead may not do without the owner).
10. **MINOR (A).** API annotations: KL-D's rate said "sharp constant" (Lean shows attainment at λ = 1/3 only);
    LC-1's rate said "superexponential in \|n\| outside the cone" (false along rays \|n\| = c\|t\|). *Answer.* Both
    corrected in `docs/api/annotations.json`. The summary of KL-D in `stamps/statements.json` is generated from the
    frozen docstring and keeps the words "Landau's sharp form"; they name the form, and `docs/statements.md` now
    says what is and is not machine-checked about sharpness.
11. **NIT (A, B, C).** PA-C's annotation said "attained in the limit" (it is attained exactly; corrected). The
    Bessel bound was named differently in three places (now Siegel's bound, DLMF 10.14.5, with its conditions).
    The docstrings of `trapezoidalRule` and `kusminLandauDeriv` omitted N ≥ 1 and the conditions on k and λ
    (corrected). The module header of the alias part names it by the lead's internal part number (left as
    delivered, so that the recorded hash stays valid). The routes' first interface paragraph says "13 of 13" (the
    revision sections correct it). `docs/statements.md` did not point to the proofs (it does now).
12. **NIT (C), numbers and times.** Session log: "25 theorems" for the second PA sanity file (it has 24; the sum
    "51" two rows later is right); "the five assembly theorems" (the two assemblies have six `_of` theorems, eight
    theorems in all; the lead printed the axioms of five in scratch, and `make quick` audited all). The KL
    pre-proof answers say referee B finished "before 14:00:38"; the logs say 14:00:45. The hand-off said
    `make verify-all` takes about three hours; the Makefile says about two. The launch record of the proof agents
    was written at 15:57:32Z, the agents were launched at about 15:57:40Z and the commit of the record is dated
    15:57:45Z: the record was written before the launch, its commit was made five seconds into the window the log
    calls frozen. *Answer.* All accepted. The session log gets a correction row (its earlier rows stay as written);
    the hand-off is corrected; the KL pre-proof answers file is a review record and is not edited.

## What these reviews do and do not establish

Rungs. The six theorems: L4 by build, axiom audit, statement types and a kernel re-check per module; the isolated
replay with six kernels is pending, and until its record exists STATUS does not say "machine-checked as stated".
Fidelity of the statements to the classical theorems: reviewed by AI referees only (pre-proof A, post-proof A);
ASSUMED(human expert review, none has taken place, owner). The order of events: verifiable up to the limits of
finding 1.

The strongest case against the result, in C's words restated: every check was made by one model family looking at
its own work; the sources were read second-hand or not at all; and the library's distinctive claim, that statements
come before proofs, is here true of the Lean text and of the timestamps, not of the proof plan, and beyond git it
is the lead's word.
