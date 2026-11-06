# Adversarial review: S2.1, S2.2, S3

You are a hostile, competent referee. Find what is wrong with the claim "S2.1, S2.2 and S3 are machine-checked as
stated" in `/home/user/lean-oscillatory` (`export PATH=$HOME/.elan/bin:$PATH`; one Lean process at a time,
`nice -n 10`; scratch files only under `/tmp/adv2/`; do not edit repository files, git state, or `build/`; do not run
`make` targets).

Attack at least:
1. The statements (`OscInt/Statements/StationaryPhase.lean` against `docs/statements.md`): vacuity (try to prove in
   Lean a consequence that would be absurd if a hypothesis set were only trivially satisfiable; try an explicit
   instance where the bound has bite), weaker-than-claimed conclusions, Lean conventions, the meaning of `FamilyCk`,
   `AmpBound`, `FoldOrNondeg`, `GradLower`, ill-conditioned regimes (Hessian eigenvalue → 0 across the family, fold
   condition degenerating in the limit, critical points at ∂K, |p| → ∞ in S2.1).
2. The trust chain since S1: the per-milestone comparator configuration and `stamps/pins.txt` enforcement
   (`tools/src/bin/challenge.rs`, `tools/src/bin/commit.rs`), the audit's new exclusion of structure projections
   (`Axioms.lean`: can a theorem with axioms hide as a projection?), the guard (`tools/src/bin/guard.rs`), the
   blueprint (`Blueprint/StationaryPhase.lean`: could a false interface have been "proved" by an agent through some
   loophole?), and whether `docs/proof-S2S3.md` and the Lean route match.
3. The prose: `README.md`, `docs/STATUS.md`, `docs/HANDOFF.md`, `docs/calibration.md`: overclaims or understatements.
Report every finding as BLOCKER / MAJOR / MINOR / NIT with file and line, failure scenario, and fix.
First line: `git rev-parse HEAD`.
