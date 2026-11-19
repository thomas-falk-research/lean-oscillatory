# Answers to an external review of batch PA (2026-11-19)

The second report of the external review that the owner ran with an AI system of a model family other than the
one that wrote, proved and refereed everything in this repository (the first, on batch VC2, is answered in
`review/2026-11-19-VC2-external-review-answers.md`). The lead wrote the request and answers the report here. The
reviewer could not install or run Lean. The request and the report are not recorded verbatim (rule 19); SHA-256 of
the report (a PDF of 57 pages) a235c3fe21b79b80261c9fbba9d674c189e21673ac0774eca0fdb710618fdde1, of its evidence
archive (154 entries: its scripts with their outputs, its frozen phase records, copies of the sources it read)
939c2d50511352d66bc080a41fc36e31d969199e2d8c8ee2e1a6b66bf2710d0b; both are kept by the owner. Each finding is
restated in the lead's words. Nobody on the project's side is a human reader of the mathematics; the reviewer is an
AI system too, and it says it used three delegated readers of its own family (semantics, numerics, literature).

What was asked. The same request as for batch VC2, with the batch name changed: one batch at the pinned commit
9ae784e, in three phases: (A) the statements and the prose as frozen (lines 980 to 1042 of `docs/statements.md`),
with its own reading, refutation attempts and literature search written and frozen before anything else is
opened; (B) the proof route and the Lean sources, read as text; (C) the records and the earlier reviews.

What its access log says, and what the lead makes of it. It read the pinned commit through a connector (direct
raw access failed) and checked its cached files against the Git blob identifiers. It froze its phase A text with a
hash and a time (13:29:46Z) and recorded phase B before phase C. It ran no Lean and none of the project's
python-flint scripts; its numbers come from an evaluator of its own in exact rational arithmetic with outward
rounding. It discloses the same exposure as the VC2 report, which is the lead's doing: the route page
`docs/proof-PA.md`, on the list for phase B, restates findings of earlier reviews in its later sections; its phase
A record predates that. Blindness is otherwise by its own account; the lead cannot check it.

## Verdicts of the reviewer

Overall: "only with these caveats". Per statement, three verdicts each.

| | Fidelity (Lean text against prose) | Truth of the Lean text | Proof route |
|---|---|---|---|
| PA-C | faithful | true, by a rectangle argument of its own, exact equality for single harmonics, rational families and the degenerate cases | sound after the corrections the route already records |
| PA-T | faithful (quantifiers, real node arithmetic, norm, normalisation, denominator) | true, by its own Laurent-series and roots-of-unity argument with the two geometric tails | sound; each interface implies the frozen target, N = 1 and M = 0 included |
| LC-1 | faithful (real time, integer site, η ≥ 0, unnormalised kernel) | true, by a direct contour shift, the bound at η = 0, and certified series tests | sound; the case η = 0 is handled separately |

In each row it adds that compilation and acceptance by a kernel are NOT VERIFIED by it. It reports no false
statement, no gap in the route as corrected, and in the Lean sources it read no placeholder, added axiom, changed
notation, hidden hypothesis or final theorem whose type is not the frozen statement. Its caveats are about the
records and the tooling: findings F01 to F08 below.

What it did that nobody on this project had done. It built test families of its own in exact rational
arithmetic (a function with one pole on each side of the strip, for which the trapezoidal error is
2π(1/(4^N − 1) + 1/(8^N − 1)) exactly; a one-pole family with the pole near the edge of the strip). It evaluated
the lattice kernel by its power series with rational partial sums and proved tail bounds. It showed that each of
periodicity, holomorphy and the integrality of n is needed, by an exact counterexample to the statement without
it. It recomputed 28 recorded quantities, and all 195 + 105 comparisons of the lead's statement check, with full
enclosures and no quadrature. It read Trefethen and Weideman's paper in full and looked up the definitions of
`DifferentiableOn`, the complex norm, the interval integral with reversed limits, and division by zero at the
Mathlib pin. And it read the replay driver as a program and tested its acceptance rule against a model, which
no reviewer of this project had done in two weeks (F03).

## Findings and answers

The reviewer's severity is given first. Its request defined BLOCKER to include "a record asserts something
untrue"; it says that none of the four BLOCKERs makes a statement of the batch false.

| # | Finding (in the lead's words) | Severity | Checked by the lead | Answer |
|---|---|---|---|---|
| F01 | `numerics/review/pa_statement_checks.py` says a comparison passes only if it holds for the whole enclosures, but an undecided PA-C comparison whose midpoints differ by less than 1e-30 kept the result PASS. | BLOCKER (record accuracy) | Confirmed by reading (lines 67 to 70 at the pin). The recorded run of 2026-11-16 printed no UNRESOLVED line, so the branch was never taken. | Accepted. The branch is removed: an undecided comparison now counts as not passed. Run again: same 195 + 105 comparisons, same largest ratios, four controls certified false, exit code 0 (`numerics/results-pa-statement-checks-2026-11-19.txt`); with the constant 2π of PA-C replaced by π the script prints nine FALSE lines and exits 1. |
| F02 | `numerics/review/pa_kl_interface_checks.py`: check I2 is described as "at most the geometric tail" and was tested against the tail plus 1e-25; the controls of I1 and I3 passed when a comparison was merely not certified, which is not a certified violation. | BLOCKER (record accuracy) | Confirmed by reading. The same in the control of J4 (batch KL), and a slack of 1e-25 in the first J4 family that the description did not mention. | Accepted. I2 is now tested against the tail itself and passes at all 25 points. The controls of I1, I3 and J4 need a certified violation (disjoint enclosures, or a certified strict inequality) and pass. The slack of J4 is kept for exact equality cases (λ = 1/2), documented, applied only to undecided comparisons and counted: 0 of 300 in the seeded run. 17 of 17, exit code 0 (`numerics/results-pa-kl-interface-checks-2026-11-19.txt`). |
| F02a | Found by the lead while sweeping the sibling scripts for the pattern of F02: `numerics/review/fr_statement_checks.py` tested "FR-S coset sum within the certified tail" against the tail plus 1e-25, and its two "must differ" controls accepted an undecided comparison. | the lead's: MAJOR against a record of batch FR | With the slack removed, 46 of 120 FR-S comparisons failed. Cause, by printing both sides: for N = 5 and 8 the tail with \|m\| ≤ 60 is below 1e-250, smaller than the enclosures at 700 bits (about 1e-209). So those 46 comparisons had shown agreement to 1e-25, not to the tail. Not a mathematical failure. | FR-S now sums \|m\| ≤ ⌈60/N⌉ (smallest tail 5.79e-63) and compares with the tail alone: 120 of 120; with a tail smaller by e^{−4N} six comparisons fail, so the test can fail. Controls need disjoint enclosures: 25 of 25 and 600 entries certified different. 12 of 12, exit code 0 (`numerics/results-fr-statement-checks-2026-11-19.txt`). Item 10 of the FR prose overstated this check: clarification j in `docs/statements.md`. Other scripts with an added slack are floating-point scripts of earlier batches (`dossier_checks.py`, `vc2_statement_checks.py`, `d4u_interface_checks.py`); they were not changed and are listed here so that nobody takes them for certified comparisons. |
| F03 | The replay driver `tools/src/bin/replay.rs` says a step fails if its output contains PANIC, "error" or "problem". The code skipped that scan for the whole output whenever the output contained "no typechecker errors" anywhere. An output with a panic, that phrase and the acceptance line, and exit status 0, was accepted. | BLOCKER (record accuracy); the reviewer's "strongest case against" | Confirmed by reading and by a test: see the section on F03 below. | Accepted and fixed; whether the hole was ever open in a recorded run is answered below from raw output. |
| F04 | The header of the replay record says 202 modules; its body lists 201. | BLOCKER (record accuracy) | Confirmed on 2026-11-19 when the VC2 report found the same (`grep -c`: 201). | Already corrected after the reviewer's pinned commit: `docs/replay/2026-11-19-session13-verify-all.erratum.txt` (commit dede383). It was the lead's miscount; the 202nd line is the check of the export. |
| F05 | `pa_kl_interface_checks.py` printed FAIL and still ended with exit status 0. | MINOR | Confirmed at the pin. | Already corrected in dede383 (nine scripts, after the VC2 report). |
| F06 | Modelling choice 6 of the frozen prose gives the best η by cosh η = \|n\|/\|t\|, which is undefined at t = 0. | MINOR | Confirmed; the pre-proof reviews had found it, and clarification 2 says "needs t ≠ 0". | Clarification 7 now states the case t = 0, n ≠ 0 outright (no minimiser; the bound tends to 0 with η → ∞, and the kernel is 0). The frozen prose stands as stamped. |
| F07 | Three wordings say more than is true: clarification 4 says "all three for M < 0 and M = 0", and LC-1 has no M; the docstring of `halfExp_not_periodic` says "no strip", and the theorem assumes a > 0; the docstring of `stripExp` says "holomorphic on that strip only", and the function is also holomorphic where it is 0, outside the closed strip. | NIT | Confirmed, all three, by reading. | Clarification 7 in `docs/statements.md`. The two docstrings are left as they are: the Lean files are the ones that were replayed, and no statement of a theorem is affected. |
| F08 | `docs/calibration.md`, round 4 (the route referee): the false-alarm figure "0 of 5, upper bound 0.522" has as its denominator the five rows that the referee itself marked sound. Whether those controls were chosen and judged independently is not established. | MINOR | Confirmed, and the answer to its question is no: nothing was fixed in advance; the five rows are the referee's. A row a referee marks sound cannot be a row it reports as wrong, so "0 of 5" was certain beforehand. The arithmetic of the bound is right and beside the point. | The figure is withdrawn as a measurement (correction of 2026-11-19 in `docs/calibration.md`; the table row now says "not measured"). The detection figure, 8 of 8, stands. The sentence in `review/2026-11-16-PA-KL-route-answers.md` is a review record and is not edited. |

It also notes, without a finding number: the opening of `CONTRIBUTING.md` read as a complete trust claim (scoped
in dede383, after the VC2 report); the title of the proceedings volume with Davis's paper differs between two
bibliographies (the project cites the paper's title only and says it was not opened); and an entry of the Archive
of Formal Proofs on Bessel functions (M. Eberl, 3 July 2026) that the project's prior-art page did not have. The
lead had the entry page and the session's theory listing fetched on 2026-11-19: it exists, with a contour-integral
representation of J_a; the page names no Kapteyn-type bound; the theory files were not read. Added to
`docs/prior_art.md`, with the admission that the sweep of 2026-11-16 ("titles only") did not report it.

## F03: the replay driver's acceptance rule

What the code did. `verdict` put a step's output in lower case and looked for `panic`, `error`, `problem` and
`uncaught exception`; each of the four tests carried the condition "and the output does not contain
`no typechecker errors`". That phrase is the end of nanoda's success line ("Checked N declarations with no
typechecker errors"), which contains the word "errors". The condition was meant to exempt that line; it exempted
the whole output. It has been in the driver since the repository's first commit (80d59ea, 2026-11-05). The
driver's own test had the case "PANIC next to an acceptance line" and not the case "PANIC next to the exempt
phrase", so the test passed for two weeks while the comment at the top of the file promised more than the code
did.

Which steps used the rule: the per-module `leanchecker` steps (201 in the replay of record),
`leanchecker --from-export`, `leanchecker-paranoid --from-export`, `con-leche --verified`, `con-ron --verified` and
`lake check --from-export --paranoid`. The nanoda step has its own rule (any "panic" fails it and its success line
is required) and was not affected. In every step exit status 0 and the acceptance line were required throughout;
the hole was in the third condition only.

The fix. The exempt phrase is deleted from the text before the scan and nothing else is exempt. Tests added: the
reviewer's input (PANIC, the phrase, "accepted") and a second one (a "found a problem" line of one checker next
to nanoda's success line) must be rejected; nanoda's line next to an acceptance line must pass. The old rule with
the reviewer's input as a test: `cargo test` fails on that assertion (exit code 101). With the fix: the driver's
tests and all other tool tests pass. The driver now keeps the raw output of every step under `build/replay/raw/`.

Was the hole open in the replay of record? The driver kept no raw output, so that run cannot be inspected. Its
export is still on the session machine (SHA-256 9eb5c2f9…, equal to the record's). First evidence, the step with
six kernels: `lake check --from-export --paranoid` run again by hand on that export on 2026-11-19, 15:39:23Z to
15:50:19Z, exit status 0. Its raw output is 17 lines
(`docs/replay/2026-11-19-lake-check-raw-on-export-of-record.txt`): six lines "accepts the solution", no line with
panic, error or problem, and no line with the exempt phrase (in this step nanoda prints "nanoda kernel accepts the
solution"). So for this step the old rule and the new one give the same verdict on what the binaries print for
the export of record. The same file prints the header of the driver's summary (commit, source tree, SHA-256 of
the nine binaries), which the public record lacked.

Second evidence, every step: `make lean-replay` with the corrected driver on 237c5b2, in isolation, 15:59:38Z to
16:36:35Z, RESULT PASS (`docs/replay/2026-11-19-lean-replay-fail-closed.txt`): 201 modules, a fresh export with the
same SHA-256 as the export of record, six kernels, 209 PASS lines and no FAIL. The Lean sources are those of the
replay of record and the nine binaries have the same SHA-256. The raw output of all 208 steps was kept and scanned:
the 201 per-module outputs are empty; none of the steps judged by the common rule prints an error word; the exempt
phrase occurs only in the output of the nanoda step, which the driver has always judged by a separate rule. So on
what these binaries print for these sources, the rule before the fix and the rule after it give the same verdict
at every step: the hole was not open. For the run of record itself this is evidence and not proof, since its raw
output does not exist; and it says nothing about the replays of earlier commits, whose raw outputs were not kept
either. Every module of the present tree, which holds all 86 statements, is covered by this run.

Two things the raw output showed that no record had. The nanoda step prints "1 pretty printer errors: Unable to
print axioms" beside its success line on every run (the driver's comment names it; no record did). And the
six-kernel step's output is not byte-reproducible: lean4lean prints a notice for a declaration that took more than
a second, and it named a different declaration in the two runs of 2026-11-19.

A third report (batch KL) pointed at the same function from another side: the acceptance line was matched as a
bare substring, and "not accepted" contains "accepted". The acceptance strings of the con-leche and con-ron steps
are now the checkers' own prefixes, with a test. A full `make verify-all` with the corrected driver is the next
replay of record (session log).

## The reviewer's questions

1. *Raw checker output and the per-binary summary for the replay; a fail-closed rerun.* Both are above: the raw
   output of the six-kernel step on the export of record, the header of the driver's summary, and the fail-closed
   rerun with the raw output of every step. The raw files themselves are on the session machine under
   `build/replay/raw/` (not committed: they are regenerable and the directory is ignored by git); their count, the
   scan over them and a hash of their concatenation are in the rerun's record.
2. *202 or 201 modules?* 201. A header miscount by the lead; erratum beside the stamped record.
3. *Should an undecided comparison be a third result, and the tolerance explicit; strict negative controls; a
   failure exit?* Yes to each; done in the three scripts named under F01, F02 and F02a. An undecided comparison is
   printed as UNRESOLVED and fails the script; the one remaining tolerance is documented and counted; controls need
   a certified violation; every script fails the process on a failed check.
4. *Were the five sound controls of calibration round 4 chosen and judged independently before the referee's
   labels were seen?* No. They are the referee's own rows. The figure is withdrawn (F08).
5. *What should a third party reproduce to justify "machine-checked as stated" without trusting the lead's machine
   and summaries?* Clone the commit; `make verify-toolchain` (the toolchain archive is downloaded and checked
   against a pinned SHA-256, and the installed toolchain must be byte-identical to it); `make verify-all`, which
   builds the library from the sources,
   audits the axioms of every theorem, compares each API theorem's type with its frozen statement constant,
   checks every module and a fresh export with the six kernels, rebuilds the statement commitments and runs the
   comparators against the frozen challenge exports. The workflow `verify.yml` does this on a clean GitHub runner
   for any commit. What remains trusted after that is listed in the README ("What stays trusted"): the Lean kernel
   and the toolchain archive (in CI one checker, nanoda, is also built from source), the Mathlib binary cache (the `.olean` files of Mathlib are downloaded, not built, in
   the replay; one source build reproduced the statement commitments), and that the frozen statements say what is
   meant. The reviewer is right that the stale-object check compares module names and not contents, that several
   of the six kernels read one export made by one exporter, and that the independence of the checkers' code bases
   is not shown by anything in this repository.
6. *Will the documentation keep the corrected zero-time case, the scope of M and the limited role of the sanity
   data explicit?* Clarification 7 of batch PA does the first two. The third is said where the reviewer found it
   (`docs/STATUS.md`, paragraph on batches PA and KL: the sanity layers pin each bound at a few parameter points
   only) and stays.
7. *Is a stronger literature or first-formalisation claim intended?* No. The claim is "not found formalised" after
   a finite search that the prior-art page describes, with its gaps; the mathematics is classical and the page
   says so.

## What this review does and does not establish

It is the first reading of these three statements, the route and the Lean sources by a system that shares no
training with the authors, and it found no error in any of them; its own proofs and exact computations agree with
the statements. It ran no Lean, so nothing in it confirms that a file compiles or that a kernel accepted a proof.
It is one review by one AI system with delegated readers of its own family, not a human referee. Its findings are
all on the side of the project's records and tools, and three of them were worth more than the batch they were
found in: the scan in the replay driver (every row of the status table rests on that driver), the acceptance rules
of the check scripts (one sibling script had been passing 46 comparisons on a tolerance), and the false-alarm
figure of a calibration round. The lead had read all three files many times.
