# Referee calibration

Purpose: measure how often a fresh-context AI statement referee, given the standard pre-proof prompt, catches a
planted statement error, and how often it raises a false alarm on an unmodified statement. A FAITHFUL verdict in
`review/` is only as good as this rate.

## Running table

| Round | Date | Statements | Planted (kinds) | Detected | Rate, 95% Clopper–Pearson | Controls | False alarms |
|---|---|---|---|---|---|---|---|
| 1 | 2026-11-05 | S1 (van der Corput) | 4 (quantifier, hypothesis, definition, weakened conclusion) | 4 | 1.00, [0.40, 1.00] | 2 | 0 (0/2, upper bound 0.84) |
| 2 | 2026-11-06 | S2.1, S2.2, S3, S4.1 (325 lines) | 4 (same kinds), planted by a separate agent | 4 | 1.00, [0.40, 1.00] | 2 | 0 (0/2, upper bound 0.84) |
| 1+2 pooled | | | 8 | 8 | 1.00, [0.63, 1.00] | 4 | 0 (0/4, upper bound 0.60) |

## Round 1 protocol (pre-registered 2026-11-05, before any referee ran)

Variants. Six copies V1–V6 of `OscInt/Statements/VanDerCorput.lean` as stamped, each with one added header line
"Review copy Vi." so no variant is byte-identical to the stamped file. Four variants each carry exactly one planted
error, one of each kind: a quantifier error, a hypothesis error, a definition error, a weakened conclusion. Two are
unmodified controls. Assignment of kinds to V1–V6 by `random.SystemRandom().shuffle`. Every variant compiles
(`lake env lean`, Lean v4.35.0, Mathlib 56a0058); in the hypothesis variant one sanity proof was adjusted to keep
compiling (proof text only). The variants are not in the repository until the reveal.

Seal. The key (variant → kind, planted text, description, variant SHA-256) and a 32-byte random salt are serialised
as `key.json`; its SHA-256 is committed below before any referee starts. The key is revealed (committed) after all
six reports are in, and its hash must match.

Referees. One fresh agent per variant, launched together, each given `review/prompts/calibration-r1.md` and the
directory of its variant only (the variant and a copy of `docs/statements.md`). Referees are told not to read the
repository; this is instructed, not enforced (no sandbox).

Scoring rule (fixed now). A planted variant is DETECTED iff the report (a) gives a verdict other than FAITHFUL
against `docs/statements.md` for a statement the plant affects, and (b) identifies the planted clause (quotes or
points to the modified Lean text). A verdict change without (b), or a finding below MAJOR without a verdict change,
counts as not detected. A control is a FALSE ALARM iff the report gives any statement a verdict other than FAITHFUL
against the docs or raises any BLOCKER/MAJOR finding. Detection rate = detected / 4 with a two-sided 95%
Clopper–Pearson interval; false-alarm count reported as k/2.

Seal SHA-256 of `key.json`: `993aba079a985ef5064ed94d3efe03b779c0add0361636274b643f864fc46d5d`.

Variant SHA-256:
- V1 `a4f5cbcf481021e947c825d0274f758d7b74265954a18bfd97ecaba45f41ec63`
- V2 `5e4970d7f551e3a7d35eb386dedb35dc5aa51c13bce579bd4ee6816c5c8cfa3a`
- V3 `89522666a6997f80394d5692becc825eb288e84e7d02763d6dc7d73c9306b567`
- V4 `c375bbe465dbc39f4cba62949908cef40fb234b4493a87ae624637e143d18de2`
- V5 `471b7d0c25144b5dfd8f23179c68c907084aa7b915d4c38636c38a941823ba6f`
- V6 `7cdd25d44019ef017abcc14d7e1f411b724f8933d0f6f250da34a5f6d86624e5`

Limitations stated in advance: n = 4 planted and 2 controls is small (4/4 gives a lower confidence bound of 0.40);
one planted error per kind; the planted errors were chosen by the lead, who also scores; blindness is by
instruction only.

## Round 1 result (scored 2026-11-05 by the pre-registered rule)

Reveal: `review/calibration/round1/key.json`, SHA-256 `993aba079a985ef5064ed94d3efe03b779c0add0361636274b643f864fc46d5d`,
equal to the sealed value above. Variants as `review/calibration/round1/V*-Statements.lean.txt` (hashes as listed);
reports verbatim as `review/calibration/round1/V*-report.md`.

| Variant | Kind | Report verdicts (VdC1 / VdC2 / VdC3) | Planted clause identified | Score |
|---|---|---|---|---|
| V1 | definition (`ampNorm`: `‖∫ψ'‖`) | UNFAITHFUL ×3, BLOCKER | yes, quoted; `¬ VdC1Statement` proved in Lean | DETECTED |
| V2 | control | FAITHFUL ×3, NITs only | — | no false alarm |
| V3 | weakened conclusion (VdC1 `+ ∫‖ψ‖`) | UNFAITHFUL / FAITHFUL / FAITHFUL, BLOCKER | yes, quoted | DETECTED |
| V4 | hypothesis (integrability of ψ′ dropped) | UNFAITHFUL ×3, BLOCKER | yes, quoted, counterexample | DETECTED |
| V5 | quantifier (VdC3 `∃ x ∈ Ioo`) | FAITHFUL / FAITHFUL / UNFAITHFUL, BLOCKER | yes, quoted, counterexample | DETECTED |
| V6 | control | FAITHFUL ×3, NITs only | — | no false alarm |

Detection 4/4, 95% Clopper–Pearson [0.398, 1] (lower bound 0.025^{1/4}); false alarms 0/2, 95% upper bound 0.842
(1 − 0.025^{1/2}). Reading: on single, isolated statement errors of these four kinds in a ~100-line file, the
referee caught every one, with the mechanism stated; n is too small to bound the miss rate below 60%. Not tested:
several simultaneous errors, errors in long statements, errors whose discovery needs Mathlib internals, and errors
planted by someone other than the scorer.

Process findings from the reports, adopted from S2 on: sanity theorems state hypotheses through the same named
definitions as the statement (V5 noted the S1 sanity theorem restates the ∀ form); sanity theorems that only
witness satisfiability cannot catch a false bound (V1, V4), so statements also get a "bite" check where it is cheap.

## Round 2 protocol (pre-registered 2026-11-06, before any referee ran)

Changes from round 1, answering its stated limitations: longer statements (S2.1, S2.2, S3 and S4.1 with all shared
definitions, merged into one 325-line standalone file); the errors were chosen and planted by a separate planter
agent, not by the lead who scores; the lead has not read the key.

Variants. Base = `OscInt/Statements/StationaryPhase.lean` followed by the body of `OscInt/Statements/D4.lean` (one
`import Mathlib`), SHA-256 `e83d94df7fddf21243bf2d8e65682618a2be06980108499e069abe5900eef3c8`. Six copies V1–V6, each
with one added header line "Review copy Vi."; four carry exactly one planted error each, one of each kind
(quantifier, hypothesis, definition, weakened conclusion), spread over the four statements where possible, chosen to
be subtle; two are controls. Assignment by `random.SystemRandom().shuffle`. Every variant compiles (`lake env lean`,
Lean v4.35.0, Mathlib 56a0058; checked by the planter and re-hashed by the lead). The shared `statements.md` is
`docs/statements.md` with S1 and every post-stamp "Clarification" paragraph removed (SHA-256
`18601e4112cc300694b7bb0ecaf8324639181d5341e6e96b15369b17b22ce88d`).

Seal. The planter wrote `key.json` (variant → kind, planted text before/after, affected statement, description,
variant SHA-256, 32-byte random salt) and reported only its hash. Seal SHA-256 of `key.json`:
`09390e03b7c0cd324805e5030e077669c8319533b8048b3a9bb6b8be162db1d6`. The key is revealed after all six reports are in.

Variant SHA-256:
- V1 `41e0ab4e4e77619ddbac0fdb61d83b9c30a88893e6f52716ab93873cc3c8a0ee`
- V2 `3d2d46913372ec2a3ff6a1e70a50b71b448b01baca2a181408280f08ac17b4b8`
- V3 `34ed0942bc5c08162837ecae5c20c40c0214fac3059fe790d3255d24c479b8c5`
- V4 `66ba7e1fa286fe3f7a9d45199f5818d0d59f13db22c951f560628bcaa15dddd5`
- V5 `de9d563d9c21ad71a90906306f5163e2725691e51659aef67083af611e7ae92e`
- V6 `b81ce110bc75c428b948a830c0272d0a6d537bacb8955f3269be24cbb1693b5a`

Referees: one fresh agent per variant with `review/prompts/calibration-r2.md` and its directory only (blindness by
instruction, no sandbox). Scoring rule: as round 1, unchanged (DETECTED iff a non-FAITHFUL verdict against
`statements.md` for an affected statement and identification of the planted clause; FALSE ALARM iff a control gets
any non-FAITHFUL verdict against the docs or any BLOCKER/MAJOR finding). Pooled with round 1 only if both rounds
are reported separately as well. Limitations stated in advance: n = 4 + 2 again; the planter is the same model
family as the referees; the scorer applies the rule after reading the key.

## Round 2 result (scored 2026-11-06 by the pre-registered rule)

Reveal: `review/calibration/round2/key.json`, SHA-256 `09390e03b7c0cd324805e5030e077669c8319533b8048b3a9bb6b8be162db1d6`,
equal to the sealed value. Variants as `review/calibration/round2/V*-Statements.lean.txt`; reports verbatim as
`V*-report.md`.

| Variant | Kind (statement) | Report verdicts (S2.1 / S2.2 / S3 / S4.1) | Planted clause identified | Score |
|---|---|---|---|---|
| V1 | control | FAITHFUL ×4, NITs | — | no false alarm |
| V2 | quantifier (S2.2 `∃ p ∈ K'`) | FAITHFUL / UNFAITHFUL, BLOCKER / FAITHFUL / FAITHFUL | yes, quoted; counterexample, hypotheses checked in Lean | DETECTED |
| V3 | control | FAITHFUL ×4, one MINOR (D4⁺ scope), NITs | — | no false alarm |
| V4 | hypothesis (S3 `∀ k ∈ K'`) | FAITHFUL / FAITHFUL / UNFAITHFUL, BLOCKER / FAITHFUL | yes, quoted; two counterexamples | DETECTED |
| V5 | definition (`cubicCoeffs` c-entry = ∂₁₁₂/2) | FAITHFUL / FAITHFUL / FAITHFUL / UNFAITHFUL, BLOCKER | yes, quoted; counterexample x³ + x²y proved in Lean | DETECTED |
| V6 | weakened conclusion (S2.1 `m ^ (N - 1)`) | FAITHFUL-WEAKER, BLOCKER / FAITHFUL / FAITHFUL / FAITHFUL | yes, quoted | DETECTED |

Detection 4/4, 95% Clopper–Pearson [0.398, 1]; false alarms 0/2 (upper bound 0.842). Pooled with round 1 (reported
separately above): 8/8, [0.631, 1] (lower bound 0.025^{1/8}); 0/4 false alarms, upper bound 0.602. Reading: single
planted errors of these four kinds, planted by someone other than the scorer, in a 325-line file with ten shared
definitions, were all caught with the mechanism stated; the miss rate per error is below 37% at 95% confidence on
this evidence. Not tested: several simultaneous errors, errors that need a Mathlib internal to see, and planters of
a different model family.

Process findings from the reports (applied to the real statements, which are unaffected: their text is the base):
the real `sanity_Fold_hyps` uses the same set for `K` and `K'`, so it cannot detect a `K`/`K'` swap (V4); the real
`sanity_D4_hyps` has `b = c = 0`, so it cannot detect a wrong mixed coefficient (V5; answered by
`OscInt/D4/Sanity.lean`, coefficients (1, 2, 3, 5)); the real S2.2 sanity theorem states the hypothesis in its own
words rather than through the statement (V2; lesson 11). See `docs/lessons.md` 17.
