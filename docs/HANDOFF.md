# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (18 entries).

## What exists (end of session 2, 2026-11-06)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). Machine-checked as stated (`docs/STATUS.md`): S1 (three van der
  Corput lemmas), S2.1, S2.2, S3, S4.1 (D4⁺ bound), S4.1′ (both umbilics), S4.2 (D4 limit with the Gamma-free c_C),
  S4.3 (c_C > 0, Gamma-free by name). Latest full record: `docs/replay/2026-11-06-S4b-final-verify-all.txt` (17e5478;
  INCOMPLETE only for S4.4); CI green, including nanoda built from source at `8de7e0c`.
- Open: S4.4 (closed forms of c_C; statement frozen and reviewed). The brief's S4 limit with its closed-form
  constant is S4.2 ∧ S4.4.
- Reviews for every statement in `review/`; calibration rounds 1 and 2 (pooled 8/8, 95% CP [0.63, 1]).
- Tools: pinned stamps, per-milestone comparator configs (export hash tied to the configuration), per-module
  `leanchecker`, six export kernels, metaprogramming guard, `GammaFree.lean` (follows proofs; lesson 18).

## Owner decisions
The three S4 decisions were delegated by the owner and taken on 2026-11-06 (`docs/decisions/2026-11-06-S4.md`):
c_C defined Gamma-free (S4.2–S4.4 separate); S4.1′ added for `disc ≠ 0`; nanoda built from source in CI at
`8de7e0c`. Still the owner's: venue, outreach, money, publication, Mathlib PRs.

## Next
The longer-term plan is `docs/ROADMAP.md`; the items below are its first steps.
- S4.4: blueprint and route (cosine moment = Γ(2/3)/2 by an Abel limit of `integral_cpow_mul_exp_neg_mul_Ioi`;
  J(C) for x³ + y³ and x³ − 3xy² by Beta integrals (`Complex.betaIntegral_eq_Gamma_mul_div`); GL₂ covariance of
  c_C and of |Disc|^{1/6}; reduction of each sign class to its normal form), route referee, agents. Then a full
  `verify-all` must report PASS.
- Put `GammaFree.lean` into the next stamp.
- Mathlib from source: the owner may run it locally between sessions (no self-hosted runner: on a public repository a
  fork's pull request could run code on it). Commands: `lake build Mathlib` in a fresh clone *without*
  `lake exe cache get`, then `make commit`; it must report every commitment equal to its pinned stamp. Record the
  machine, the log's count of `Built Mathlib.*` lines and the result in `docs/toolchain.md`.
- Freeze the tree while referees or the final `verify-all` run (lesson 16); generic sanity witnesses (lesson 17);
  negative controls that exercise the checked path (lesson 18).

## Commands
```bash
lake exe cache get
make verify-all
make numerics
cd numerics && cargo run --release --locked --bin d4const   # S4 constants
make stamp
```
