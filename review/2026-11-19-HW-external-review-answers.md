# Answers to an external review of batch HW (2026-11-19)

The fifth and last report of the external review that the owner ran with an AI system of a model family other
than the one that wrote, proved and refereed everything in this repository. The lead wrote the request and
answers the report here. The reviewer could not install or run Lean. The request and the report are not recorded
verbatim (rule 19); SHA-256 of the report (a PDF of 38 pages)
d3df52d47baf5424159ad02440becd96b1404a46c905eb28861bd358423049e3, of its evidence archive (149 entries)
2ac53fb85fd9aa008d703a0b1112f9cfe4dae8f989676e7967858f1bcfe7917e; both are kept by the owner. Each finding is
restated in the lead's words. The reviewer is an AI system with three delegated readers of its own family.

What was asked: the same request as for the other batches, at the pinned commit 9ae784e (statements and frozen
prose, lines 1414 to 1512 of `docs/statements.md`; route and Lean sources; records).

What its access log says. It read the pinned commit through a connector and says no file of phases B or C was
opened before its phase A record was frozen. It points out that the frozen prose it was given for phase A already
contains the authors' proposed route and the literature leads, so its phase A was not blind to that sketch. It ran
no Lean. Its computations are exact (integer and rational arithmetic) or floating point with the scope stated.

## Verdicts of the reviewer

Overall: "only with these caveats". HW-R, HW-K, HW-D and HW-L: fidelity FAITHFUL; the Lean text TRUE by ordinary
mathematics (the recurrence from the spectral divided difference with Fourier orthogonality for the initial data;
the partition into four arcs with the concrete van der Corput estimates and rational bounds on the coefficients;
HW-D from HW-R and HW-K with t = 1 apart; HW-L by the finite decomposition into point states); the route SOUND,
with the dependence on the library's van der Corput chain traced. Lean elaboration and checking: CANNOT DETERMINE
by it. No counterexample and no way for a source file to prove less than it appears.

What it did that nobody on this project had done: it computed the walk exactly to t = 3000 and found the recorded
maximum rounded the wrong way (F01); it read the numerical scripts as programs (F02, F07); it read Maeda et al.,
arXiv:1801.03214 and 1808.05714, Sunada and Tate, and Carteret, Ismail and Richmond in full text and placed the
project's citations against them (F09); it compared the handling of the pre-proof findings with the rule in
`CONTRIBUTING.md` (F06).

## Findings and answers

| # | Finding (in the lead's words) | Severity (reviewer) | Checked by the lead | Answer |
|---|---|---|---|---|
| F01 | Clarification b says the largest component from the state (1, 0) is "1.6208 t^{−1/3} at most for t ≤ 3000". At t = 2997, site −2111, first component, the value is above 1.62084. | BLOCKER (record) | Confirmed with exact integers: the maximum over t ≤ 3000 of t^{1/3} times the largest component is 1.620846253…, at t = 2997, x = −2111; the exact test n⁶t² > (1.6208)⁶·2^{3t} holds at t = 2990 and t = 2997 and at no other t ≤ 3000. The recorded number was the maximum rounded down and presented as a bound. | Accepted. Clarification h in `docs/statements.md`: the maximum is 1.620846… (above 1.62084 and below 1.62085, both by exact comparison; `numerics/results-hw-exact-max-checks-2026-11-19.txt`). Nothing depends on it; the theorem's constant is 39. |
| F02 | The header of `numerics/review/hw_statement_checks.py` says the walk is also computed with "exact rationals times powers of √2 … via integer pairs" for small t. There is no such code; the walk uses floating √2 throughout. | BLOCKER (record) | Confirmed by reading the whole script. | Accepted. The header now says what the script does. An exact computation exists now as a separate script, `numerics/review/hw_exact_max_checks.py`, with its output (F01). |
| F03 | The header of `OscInt/Front/HadamardWalkSanity2.lean` says "the first layer tested 39 against 1/2 only". The first layer's `hwD_one` also tests 1/√2 ≤ 39 at t = 1. | BLOCKER (record) | Confirmed by reading `hwD_one` (first layer, lines 428 to 430). What is true: at t = 1 the constant 1 also holds (1/√2 ≤ 1), so the first layer could not tell 39 from 1; the datum at t = 3 can. | Accepted. The comment is corrected to say that. |
| F04 | 202 modules in the replay record's header; 201 in its body. | BLOCKER (record) | Confirmed earlier. | Erratum (dede383); see also KL F4 for a second count in the same header. |
| F05 | The pre-proof answers say "no exact datum can detect a wrong exponent". The same file records that 39/t first fails at t = 126, and an exponent of −7 fails at t = 2. | BLOCKER under a literal reading | Confirmed from the file's own text. What the referee's finding supports is narrower: because the constants are 12 to 24 times the attained values, an exponent mutation that keeps the bound above the attained values at the times an exact datum reaches is not refuted by such a datum (the recorded cases: the exponent mutation of HW-L, and HW-K with the product of its two terms, first false near t = 7749). | Accepted. Stated with that scope in a dated clarification; the answers file is a review record and stands with this correction. |
| F06 | Two MAJOR findings against the sanity layer were answered by a second sanity file, and the statements and the stamp were kept. Step 5 of `CONTRIBUTING.md` says a MAJOR means a new statement and excludes the sanity layer from its one exception; the recorded waiver is for batch API3 only. | MAJOR (process); the reviewer's "strongest case against" | Confirmed; the same in five other batches. See the KL answers, F2. | Accepted as a departure by the lead from the owner's rule, with no decision behind it. Disclosed in `docs/STATUS.md` and put to the owner. |
| F07 | The script's comparison of the trapezoidal rule with adaptive quadrature uses ten points of which nine have kernel value exactly 0 (the parity of t + x) and one is K(1, 0) = 1: no later nonzero value is compared. | MINOR | Confirmed by parity: K(t, x) vanishes unless t + x is odd, and all eight points with t ≥ 2 have t + x even. | Accepted. Six points with nonzero kernel values are added (t from 2 to 13): 7 of the 16 values now exceed 1e-3 in modulus, largest difference 2.3e-16 (`numerics/results-hw-statement-checks-2026-11-19.txt`). |
| F08 | The two HW scripts did not fail the process on a failed check. | MINOR | Confirmed at the pin. | Corrected in dede383 (after the VC2 report). |
| F09 | Prior art: Proposition 4.12 of arXiv:1808.05714 (version 3) is an estimate for one spectral branch (the evolution composed with a projection); the estimate for the whole walk is Theorem 2.1 of the same authors' arXiv:1801.03214. And Sunada and Tate's leading Airy coefficient is explicit, where the page says "implicit constants". | MINOR | The lead opened both papers of Maeda et al. on 2026-11-19: 1801.03214v2, Theorem 2.1, equation (2.14), states the ℓ¹ to ℓ^∞ bound C t^{−1/3} for t ≥ 1 and 0 < \|a\| < 1 with C depending on a, and says the estimate was first obtained by Sunada and Tate "in a slightly different form"; 1808.05714v3, Proposition 4.12, bounds the evolution composed with the projection P₊. The statement about Sunada and Tate's coefficient is the reviewer's reading; the lead did not open that paper again. | Accepted. `docs/prior_art.md` now cites Theorem 2.1 of 1801.03214 for the walk and Proposition 4.12 for one branch, and reports the remark on Sunada and Tate as the reviewer's. |
| F10 | `CONTRIBUTING.md`: "and nothing else" and "before any proof exists" say more than the README's trust list and the disclosed chronology. | MINOR | The first was scoped in dede383. The second: confirmed (FR report, R8). | The second is put to the owner with F06. |
| F11 | Calibration: the referee-chosen controls do not measure a false-alarm rate, and batch HW had no calibration round. | MINOR | Confirmed; both already on the page (the second) or corrected today (the first). | See the PA answers, F08, and the KL answers, F6. |
| F12 | The frozen prose says sup \|K(t, ·)\| t^{1/3} "stays below 1.0"; at t = 1 it equals 1. | BLOCKER in the preserved original, acknowledged | Clarification b already says so. | Stands as corrected; the frozen prose is not edited. |
| F13 | Wordings of the frozen prose on sign sensitivity and on "weakening" a hypothesis, already addressed by clarifications and the second sanity layer. | MINOR, addressed | Confirmed as addressed. | No change. |
| F14 | `docs/prior_art.md` says in one place that no formalisation of the k-th derivative van der Corput lemma with constants was found, and in another credits Roos and Praveen's. | MINOR | Confirmed: the first sentence is from a later sweep and meant "no further one". | The sentence now says so. |

## The reviewer's questions

1. *Which decision authorises keeping the stamp after sanity-layer MAJORs?* None; F06.
2. *Is "at most 1.6208" a bound or a rounded value?* A value rounded down and written as a bound; F01.
3. *Where is the exact integer-pair arithmetic?* It was never in the script; F02.
4. *202 or 201?* 201.
5. *The scope of "no exact datum can detect a wrong exponent".* F05.
6. *Which artefacts bind the checker input, the frozen definitions, the dependency versions, the challenge and
   the final theorem?* The statement commitments (two producers that must agree, `make commit`), the challenge
   exports compared by the comparators, the pinned toolchain archive and the Mathlib revision in
   `lake-manifest.json`, and the stamps over the whole tree. A reviewer who cannot run them has only the records;
   that is the limit of a review without execution, and the reviewer states it.
7. *A review protocol detailed enough to tell an omitted paraphrase from a missed finding; isolation beyond an
   instruction.* Not available under the privacy rule, and isolation of the lead's referees is by instruction
   only (lesson 61). Both limits are disclosed and neither is repaired here.
8. *Which runner consumes the scripts' results?* None: they are run by hand by the lead, and since dede383 they
   fail the process on a failed check.
9. *The prior-art entry.* F09.
10. *Which claims are theorems, which reported executions, which history?* Theorems: the four statements, as
    Lean propositions. Reported executions: every replay, comparator and plant record. History: stamps, review
    answers, chronology. "Machine-checked as stated" is a claim of the second kind about the first.

## What this review does and does not establish

Four statements read, attacked and re-proved on paper by a system of another family, with no error found in
them, in the route or in the Lean sources as text; no Lean was run. Its record findings are confirmed, and its
process finding is the most serious thing the five reports found about how the lead worked.
