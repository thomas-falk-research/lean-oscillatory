# Answers to the route referees of batches PA and KL (2026-11-16)

Subject: the routes `docs/proof-PA.md` and `docs/proof-KL.md`, the blueprints `Blueprint/PeriodicAnalytic.lean` and
`Blueprint/KusminLandau.lean`, and the lead's compiled assemblies `OscInt/Front/PeriodicAnalyticAssembly.lean` and
`OscInt/Front/KusminLandauAssembly.lean`, as committed in 4ff92c3, before any part was proved. Two fresh-context
referees, one per batch, read-only, each on a snapshot of the files; a third received a calibration packet. They
proved nothing. Lead and referees are AI agents of one model family. Their briefs and reports are not recorded
verbatim (rule 19); the briefs' SHA-256 values are in the session log, and the findings are stated here in the
lead's words. The referees were not allowed to run Lean: that the assemblies compile rests on the lead's build and
on `make quick` (session log, 15:43:24Z), not on them.

## Batch PA (`docs/proof-PA.md`, `Blueprint/PeriodicAnalytic.lean`, `OscInt/Front/PeriodicAnalyticAssembly.lean`)

Verdict: sound. No BLOCKER, no MAJOR. The referee recomputed every formula of P-shift, P-coeff, P-series, P-alias
and P-lc and tested them numerically with its own script; it could not falsify any of the four blueprint
propositions and found the alias bound sharp; it re-ran the lead's interface checks and got the same output; it
found every cited Mathlib name in the sources except the one of the second finding.

| Finding | Severity | Answer |
|---|---|---|
| P-alias: `IsPrimitiveRoot.geom_sum_eq_zero` does not give the roots-of-unity sum when 1 < gcd(k, N) < N (N = 4, k = 2). | MINOR | Accepted. `geom_sum_eq` or `mul_geom_sum` with ζ^N = 1; only "ζ = 1 implies N divides k" is needed. Route revision, item 1; proof brief. |
| P-alias: "`hasSum_int_iff…`" is not a Mathlib name; the lemma with the right shape is `HasSum.of_add_one_of_neg_add_one`. P-coeff names `le_of_tendsto` where `ge_of_tendsto` applies (the assembly uses the right one). | NIT | Accepted. Route revision, items 2 and 3. |
| The interface-check paragraph counts checks of both batches as if they were this batch's; two paths differ from the packet; the stamp's name and its time differ by seven seconds. | NIT | The count is corrected (revision, item 5). The paths are right in the repository (the packet was a flattened snapshot). The stamp directory is named at the start of the stamping run and the authorities answered seven seconds later; both times are in the session log. |
| The first Risks item is garbled, and "names are checked" is overstated for two names. | NIT | Accepted. Revision, items 4 and 6. |
| The check of the Fourier series tests a truncated sum, not the proposition in its stated shape. | NIT | Accepted as a limit of the check (revision, item 5). |

## Batch KL (`docs/proof-KL.md`, `Blueprint/KusminLandau.lean`, `OscInt/Front/KusminLandauAssembly.lean`)

Verdict: sound after corrections. No BLOCKER, no MAJOR. Every display of K-reduce, K-weights, K-abel, K-two and
K-deriv was recomputed by the referee and tested numerically (its own statement: 4000 boundary-heavy sequences and
3000 phases of the derivative form, no failure); the parts imply the three frozen statements, degenerate cases
included; both blueprint propositions are true as Lean statements; the assembly's types compose (read by hand; the
referee was not allowed to run Lean; the lead's compile and `make quick` are the evidence that it compiles).

| Finding | Severity | Answer |
|---|---|---|
| The route said every blueprint proposition was interface-tested. `KLDerivFacts` was tested by nothing, and the check of the core never sampled the ends of the cell, where the bound is attained. | MINOR | Accepted. The script gained boundary-heavy sequences, Landau's sequences (ratio 1 at λ = 1/3, 1/5, 1/7, 3/7, 1/2) and a check of the derivative form with its own control; 17 of 17 checks pass (`numerics/results-pa-kl-interface-checks-2026-11-16.txt`). |
| Mathlib has no monotonicity lemma for the cotangent and no half-angle lemma in the form the route uses; `Finset.sum_range_by_parts` is in a form that fits badly. | MINOR (feasibility) | Accepted; the cheaper paths the referee named are in the route's revision section and in the proof brief. |
| K-deriv: the reindexing is the bulk of the work; `Int.Icc_eq_finset_map` is the cheap path. | MINOR (feasibility) | Accepted; in the revision section and the brief. |
| K-deriv: the empty sum is not an instance of KL-D; it needs `0 ≤ cot(πλ/2)`. | NIT | Accepted; revision section, item 1. |
| The control of the core check was called "extremal"; it is the two-term sequence (0, 1/3). | NIT | Accepted; the script's description is corrected. |
| Two paths in the route did not match the referee's packet. | NIT | An artefact of the packet (a snapshot with a flattened layout); the paths are right in the repository. |
| K-two states an end-point case that is never used. | NIT | Accepted; revision section, item 4. |

## Calibration of the route referees (packet R-X)

A third fresh-context referee received, under the same brief, copies of both routes into which the lead had put
eight errors (four each), without the blueprint Lean files and the interface checks. Every brief said that packets
may contain planted errors. The key was written before launch (SHA-256
053f8e6d30663a7f3c0dd7c3c428d64499af8ed263542e3c018c8a51fb369a4a; `review/calibration/round4/key.txt`).

| Planted error | Found | Referee's severity |
|---|---|---|
| P-coeff: contour shifted towards the side where the exponential grows | yes, with the correction | MAJOR |
| P-alias: the geometric tail written as 1/(1 − r) | yes | MINOR |
| P-lc: `cos x` for `sin x` in the modulus of the integrand | yes | MINOR |
| Blueprint: the alias bound with M in place of 2M | yes, with a counterexample (c_k = 2^{−\|k\|}, N = 1) | BLOCKER |
| K-weights: a factor 2 in the difference of two weights | yes | MINOR |
| K-abel: the two half-angle identities swapped | yes | MINOR |
| K-deriv: the mean-value point placed in the closed interval | yes | MINOR |
| K-two: `x ≤ sin x` cited in place of `x ≤ tan x` | yes | MAJOR |

Detection 8 of 8 (95% Clopper–Pearson interval [0.630, 1], rounded outwards); no sound part was reported as wrong
(0 of 5 sound rows of its table; upper bound 0.522). The task differs from the fidelity reviews of rounds 1 to 3
(a route on paper, not a Lean statement), so this round is not pooled with them. Limits: one referee, eight
plants chosen by the lead, who also wrote the routes; plants were single-line changes; a referee that finds
planted single-line errors may still miss a structural gap. Its three further remarks were about the real text and
are taken into the PA route's revision (the roots-of-unity lemma to use; a Mathlib name the route cited that does
not exist; the empty-sum case of K-deriv, which the KL referee also found).

## What this review does and does not establish

Rung: the routes are proofs on paper, refereed once each by an AI referee whose detection rate on planted
single-line errors was 8 of 8 in one run. That supports L3 for the routes. It is not a machine check: the parts are
not proved, and STATUS is unchanged. The strongest case against relying on it: the referees and the lead share a
model family, so an error all of them would make alike is not excluded; and the referees judged the assemblies by
reading only.

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
