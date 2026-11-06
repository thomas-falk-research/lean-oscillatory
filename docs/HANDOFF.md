# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (17 entries).

## What exists (end of session 2, 2026-11-06)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). Machine-checked as stated (`docs/STATUS.md`):
  - S1 `OscInt.vanDerCorput_one/_two/_three` (`OscInt/VanDerCorput/`);
  - S2.1 `OscInt.nonStationary`, S2.2 `OscInt.stationaryPhase`, S3 `OscInt.fold` (`OscInt/StationaryPhase/`);
  - S4.1 `OscInt.d4Bound` (`OscInt/D4/`, route `docs/proof-S4.md`; D4⁺, `disc < 0`, as the brief).
  Latest full record: `docs/replay/2026-11-06-S4-verify-all.txt` (a0b1fde, PASS 8/8); later commits checked by CI.
- Reviews for every statement: two blind pre-proof, two post-proof, one adversarial, all in `review/`.
- Calibration: round 1 (S1) and round 2 (S2–S4, separate planter) both 4/4 detected, 0/2 false alarms; pooled
  8/8, 95% CP [0.63, 1] (`docs/calibration.md`).
- Mathlib built from source in CI (run 18): commitments equal the pinned stamps.
- Tools enforce pinned stamps, per-milestone comparator configs, per-module `leanchecker`, a metaprogramming guard,
  verification of every pinned stamp.

## Owner decisions
The three S4 decisions were delegated by the owner and taken on 2026-11-06 (`docs/decisions/2026-11-06-S4.md`):
c_C defined Gamma-free (S4.2–S4.4 separate); S4.1′ added for `disc ≠ 0`; nanoda built from source in CI at
`8de7e0c`. Still the owner's: venue, outreach, money, publication, Mathlib PRs.

## Next
- S4.3 (smallest): route = alternating series on [π/2 + (k−1)π, π/2 + kπ] plus certified bounds for a₀ + a₁ > 0
  (6% margin); integrability of |C|^{-2/3} for `disc ≠ 0`; must pass `GammaFree.lean`.
- S4.2: route = rescaling z = t^{-1/3}w, dominated convergence on |w| ≤ R, dyadic tail by S2.1 (N = 2), polar
  evaluation of ∫e^{iC} with cut-offs; referee the route before agents.
- S4.4: Abel limit of `integral_cpow_mul_exp_neg_mul_Ioi` for the cosine moment, Beta integrals for the two
  normal forms, GL₂ covariance.
- Freeze the tree while referees or the final `verify-all` run (lesson 16); generic sanity witnesses (lesson 17).

## Commands
```bash
lake exe cache get
make verify-all
make numerics
make stamp
```
