# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (16 entries).

## What exists (end of session 2, 2026-11-06)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). Machine-checked as stated (`docs/STATUS.md`):
  - S1 `OscInt.vanDerCorput_one/_two/_three` (`OscInt/VanDerCorput/`);
  - S2.1 `OscInt.nonStationary`, S2.2 `OscInt.stationaryPhase`, S3 `OscInt.fold` (`OscInt/StationaryPhase/`, final
    record `docs/replay/2026-11-06-S2S3-final-verify-all.txt`, PASS 8/8 on d932c0d; CI run 40 green on d932c0d).
- S4.1 `OscInt.Statements.D4BoundStatement` (`OscInt/Statements/D4.lean`): stamped
  (`stamps/20261106T033706Z-63564a8d78cd`), pinned, two blind reviews FAITHFUL; no proof yet. Route in
  `docs/statements.md` S4 (dyadic rescaling, S3 on annuli for bounded linear terms, S2.1 for large ones).
- Mathlib built from source in CI (run 18): 8624 modules compiled, commitments equal the pinned stamps.
- Calibration round 1: 4/4 planted errors caught (95% CP [0.40, 1]), 0/2 false alarms.
- Tools enforce: pinned stamps (`stamps/pins.txt`, last line wins, duplicates rejected), per-milestone comparator
  configs with hash-checked config files, per-module `leanchecker` for `OscInt` and `Blueprint`, a guard that forbids
  metaprogramming entry points, verification of every pinned stamp.

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
- S4.1 proof: blueprint from the route in `docs/statements.md` S4 (parts: Taylor family Φ(ε, z) = ε⁻³(φ(εz) − φ(0) −
  ε∇φ(0)·z) of class C⁴ on [0, ε₀]; fold condition for Disc < 0 cubics on the annulus and its openness; dyadic
  decomposition and rescaling of amplitudes; summation), referee the on-paper route, then agents.
- S4.2 after decision 1. Calibration round 2 (planned errors in longer statements, other planter).
- Freeze the tree while referees or the final `verify-all` run (lessons 16).

## Commands
```bash
lake exe cache get
make verify-all
make numerics
make stamp
```
