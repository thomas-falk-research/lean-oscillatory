# Referee calibration

Purpose: measure how often a fresh-context AI statement referee, given the standard pre-proof prompt, catches a
planted statement error, and how often it raises a false alarm on an unmodified statement. A FAITHFUL verdict in
`review/` is only as good as this rate.

## Running table

| Round | Date | Statements | Planted (kinds) | Detected | Rate, 95% Clopper–Pearson | Controls | False alarms |
|---|---|---|---|---|---|---|---|
| 1 | 2026-11-05 | S1 (van der Corput) | 4 (quantifier, hypothesis, definition, weakened conclusion) | 4 | 1.00, [0.40, 1.00] | 2 | 0 (0/2, upper bound 0.84) |

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
