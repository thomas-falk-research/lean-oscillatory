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

## Pending owner decisions
1. S4 limit constant. The brief asks for t^{2/3}∫e^{itφ}A → c_C A(0) with c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) and
   also asks to prove c_C ≠ 0 by an alternating-series argument "not relying on Mellin/Gamma identities". With the
   closed form in the statement, c_C ≠ 0 is trivial and the limit itself needs a Gamma identity
   (∫₀^∞ cos v · v^{-1/3} dv = Γ(2/3)/2). Proposal: S4.2 states the limit with c_C defined Gamma-free as
   (1/3)(∫₀^∞ cos v · v^{-1/3} dv)(∫₀^{2π} |C(cos θ, sin θ)|^{-2/3} dθ) (improper integral as a limit), S4.3 proves
   c_C > 0 by the alternating series, and S4.4 states the closed form separately.
2. An independent checker built from source (nanoda at commit `8de7e0c`): the local build was refused by the
   session's safety classifier (third-party build code); options: allow it here, or build it in CI.
3. S4.1 scope: `disc < 0` (D4⁺, as the brief) or `disc ≠ 0` (adds D4⁻); a change is a new statement.

## Next
- S4.2 after decision 1 (statement, stamp, blind review, then route; the limit uses the same dyadic pieces plus
  dominated convergence on the cubic model).
- If decision 3 is "widen": a new `disc ≠ 0` statement; the existing parts already cover it (D3 is stated for
  `disc ≠ 0`).
- Upstream candidates (`docs/upstream.md`): only with the owner's go.
- Freeze the tree while referees or the final `verify-all` run (lesson 16); generic sanity witnesses (lesson 17).

## Commands
```bash
lake exe cache get
make verify-all
make numerics
make stamp
```
