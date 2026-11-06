# Adversarial review: S4.1

You are a hostile, competent referee. Find what is wrong with the claim "S4.1 is machine-checked as stated" in
`/home/user/lean-oscillatory` (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time, `nice -n 10`;
scratch files only under `/tmp/adv4/`; do not edit repository files, git state, or `build/`; do not run `make`
targets).

Attack at least:
1. The statement (`OscInt/Statements/D4.lean` against `docs/statements.md` S4): vacuity (try to prove in Lean a
   consequence that would be absurd if the hypotheses were only trivially satisfiable; try an explicit instance where
   the bound has bite, e.g. `x³ + y³` with a fixed amplitude, and check that `t^{-2/3}` is not trivially implied by a
   weaker bound), weaker-than-claimed conclusions, Lean conventions (`Real.rpow`, `fderiv` of non-differentiable
   functions, the max norm, `cubicCoeffs`/`disc` argument order), ill-conditioned regimes (Disc → 0, |y| → ∞,
   amplitude support touching ∂B̄(0, δ), t near 1).
2. The proof route: `docs/proof-S4.md`, `Blueprint/D4.lean`, `OscInt/D4/*.lean`. Could a blueprint part have been
   "proved" through a loophole (a definition that collapses, a hypothesis that is never satisfiable in the use)?
   Does the assembly use the S3 and S2.1 theorems exactly as frozen? Is the final theorem's type the frozen constant?
3. The trust chain for S4: `comparator-S4.json`, `stamps/pins.txt`, `StatementTypes.lean`, `Axioms.lean`, the replay
   record `docs/replay/2026-11-06-S4-verify-all.txt`.
4. The prose: `docs/STATUS.md`, `docs/HANDOFF.md`, `docs/calibration.md` (round 2): overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`.
