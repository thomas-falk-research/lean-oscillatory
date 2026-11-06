# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (12 entries).

## What exists (session 2, 2026-11-06)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). Library `OscInt`:
  - S1 (done): `OscInt/Statements/VanDerCorput.lean`, proofs `OscInt/VanDerCorput/`, final theorems
    `OscInt.vanDerCorput_one/_two/_three` (machine-checked as stated; `docs/STATUS.md`).
  - S2.1, S2.2, S3 statements: `OscInt/Statements/StationaryPhase.lean` (`NonStationaryStatement`,
    `StationaryPhaseStatement`, `FoldStatement`), mathematics in `docs/statements.md`, stamped
    (`stamps/20261105T234456Z-533ae0272521`, pinned in `stamps/pins.txt`), two independent blind reviews FAITHFUL ×3
    (`review/2026-11-05-S2S3-pre-proof-{A,B}.md`, answers in `…-answers.md`).
  - S2/S3 proof route on paper: `docs/proof-S2S3.md` (refereed, no BLOCKER; the final "Revision" section overrides
    the text above it).
  - Blueprint `Blueprint/StationaryPhase.lean`: infrastructure F1a–d, F2a–b (proved: `OscInt/StationaryPhase/Family`,
    `Change`, `Partition`), analytic parts R2, L1, L2, L3–L5, L6, L2–L6 assembly, N2, F3 (being proved by agents H1–H6;
    briefs `review/prompts/S2S3-briefs-analytic.md`), and the lead's assembly `OscInt/StationaryPhase/Assembly.lean`
    (S2.2 and S3 from R2, L1 and LocalCrit).
- Calibration round 1 (`docs/calibration.md`): 4/4 planted errors detected, 95% CP [0.40, 1]; 0/2 false alarms.
- Tools: `tools/` (guard, audit, replay, commit with pinned-stamp enforcement, challenge with one comparator config
  per milestone, stamp, toolchain, verify_all), `numerics/`.

## What is verified, by what
- S1: `docs/replay/2026-11-05-M1-verify-all.txt` (PASS 8/8), reviews in `review/`.
- S2/S3 infrastructure parts: lead-verified (module build, guard, `#print axioms`, type equals blueprint Prop);
  in the axiom audit (73/73 at commit ee11996).
- Not yet: S2/S3 analytic parts; final theorems `OscInt.nonStationary/stationaryPhase/fold` (challenge
  `Challenge/StationaryPhase.lean`, config `comparator-S2S3.json`); post-proof and adversarial reviews of S2/S3.
- Mathlib from source: first CI run compiled 2512 Mathlib modules in the job, then failed because
  `MathlibNames.lean` needs all of Mathlib; the job now builds all of Mathlib (`lake build Mathlib`); second run
  queued at commit 5ae5589 (result to be recorded in `docs/toolchain.md`).

## Pending owner decisions
1. S4 limit constant. The brief asks for t^{2/3}∫e^{itφ}A → c_C A(0) with c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) and
   also asks to prove c_C ≠ 0 by an alternating-series argument "not relying on Mellin/Gamma identities". With the
   closed form in the statement, c_C ≠ 0 is trivial and the limit itself needs a Gamma identity
   (∫₀^∞ cos v · v^{-1/3} dv = Γ(2/3)/2). Proposal: S4.2 states the limit with c_C defined Gamma-free as
   (1/3)(∫₀^∞ cos v · v^{-1/3} dv)(∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ) (improper integral as a limit), S4.3 proves
   c_C > 0 by the alternating series, and S4.4 states the closed form separately.
2. An independent checker built from source (nanoda at commit `8de7e0c`): the local build was refused by the
   session's safety classifier (third-party build code); options: allow it here, or build it in CI.

## Next
- Integrate H1–H6 as they land (verify each: module build, guard, axioms, type), write
  `OscInt/StationaryPhase/Final.lean`, `#assert_type_is` lines, `make verify-all`, post-proof review (two
  referees), adversarial review; then S4 statements after decision 1.

## Commands
```bash
lake exe cache get
make verify-all
make numerics
make stamp
```
