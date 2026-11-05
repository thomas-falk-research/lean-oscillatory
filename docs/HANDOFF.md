# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (9 entries).

## What exists (end of M1, 2026-11-05)
- Lake project, Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). Library `OscInt`:
  - `OscInt/Statements/VanDerCorput.lean`: S1 statements `VdC1Statement`, `VdC2Statement`, `VdC3Statement`
    (mathematics in `docs/statements.md`), pins, sanity theorems.
  - `OscInt/VanDerCorput/`: proof parts `Split` (P0), `One` (P1), `Amplitude` (P2), `Higher` (P3, P4), `Assembly`
    (lead), `Final` (`OscInt.vanDerCorput_one`, `_two`, `_three`). Route ported from J. Roos and M. Praveen,
    `roos-j/lean-oscillatory` (Mathlib PR #39406), after Stein VIII §1.2.
  - `Blueprint/VanDerCorput.lean`: the part propositions; `Challenge/VanDerCorput.lean`: `sorry` theorems for the
    comparator (not imported, not audited).
- Checks: `Axioms.lean`, `StatementTypes.lean`, `MathlibNames.lean`; Rust tools in `tools/` (guard, audit, replay,
  commit, challenge, stamp, toolchain, verify_all); `numerics/` (f64 probes; tooling only).
- Freezing: `stamps/20261105T203058Z-7516eb518dce` (manifest, three RFC 3161 tokens, two pending OpenTimestamps
  proofs); `stamps/pins.txt` pins each statement and the challenge to it.
- Reviews in `review/` (pre-proof, post-proof, adversarial; prompts in `review/prompts/`, including the agent briefs).

## What is verified, by what
- S1: `docs/STATUS.md` row and paragraph; full record `docs/replay/2026-11-05-M1-verify-all.txt`.
- Each push: CI `verify-all` (read the result after every push: lessons 9).
- Not yet run: the manual `mathlib-from-source` CI job (Mathlib binary cache still trusted); OpenTimestamps proofs
  not yet upgraded (pending until Bitcoin confirmation; upgrade with any OpenTimestamps client and commit).

## Next
- M2: infrastructure lemmas (2D integration by parts via Fubini; smooth dyadic partitions of unity from
  `ContDiffBump`; multivariate Taylor with parametric remainder; IFT with a metric-space parameter via
  `ContractingWith.fixedPoint`; finite chart covers; GL₂(ℝ)-equivalence of binary cubics with negative
  discriminant), each upstream-ready and listed in `docs/upstream.md`. Statement-first per lemma group, as for S1.
- After M2: calibration round (four planted statement errors, sealed key, Clopper–Pearson interval;
  `docs/calibration.md`), and Mathlib PR drafts (do not open without the owner's go).
- Open items: fix the S1 header comment wording at the next re-stamp (review NIT); numerics could stress the
  general hypotheses (piecewise-linear φ′ is excluded by design; unbounded integrable ψ′ is allowed and untested).

## Commands
```bash
lake exe cache get
make verify-all
make numerics
make stamp
```
`make verify-all` prints PASS / FAIL / INCOMPLETE; CI accepts INCOMPLETE with a warning.
