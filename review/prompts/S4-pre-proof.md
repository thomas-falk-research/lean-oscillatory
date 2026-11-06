# Blind pre-proof statement review: S4.1 (uniform D4 bound)

You are a fresh referee with no access to any proof (none exists for S4). Judge whether the Lean statement says what
the mathematics says, and whether it is true and non-vacuous. Two referees review independently.

Read only: `docs/statements.md` (section S4; S2/S3 for the shared notation), `OscInt/Statements/D4.lean`,
`OscInt/Statements/StationaryPhase.lean` (the shared definitions `dd`, `ddd`, `lin`, `oscInt2`, `AmpBound`), and Mathlib
sources. You may compile scratch files under `/tmp/<your name>/` with `nice -n 10 lake env lean …` from the
repository root (`export PATH=$HOME/.elan/bin:$PATH`; one process at a time). Write nothing in the repository.

For `D4BoundStatement`:
1. Verdict against `docs/statements.md` (FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL) and against the
   classical result (uniform t^{-2/3} decay at a D4 (umbilic) point with C² amplitude, uniform in the linear term);
   is it TRUE? If false, give a counterexample.
2. Check `cubicCoeffs` (are a, b, c, d the coefficients of (1/6)D³φ(0)[κ³] with the `ddd` argument order?) and `disc`
   (is it the discriminant, with the sign convention under which Disc < 0 means one real linear factor, e.g.
   x³ + y³ ↦ −27?). Check the claim that Disc < 0 implies the cubic has an isolated critical point at 0.
3. Vacuity and conventions: can the hypotheses only be met trivially; does `∃ δ > 0, ∃ C` come before `A, M, y, t`;
   is the omission of ∇φ(0) = 0 correct (is the bound then still true and uniform in y ∈ ℝ²?); `Real.rpow`; the
   max-norm ball.
4. Ill-conditioned regimes: discriminant → 0 is excluded per point, but is the constant allowed to blow up as
   Disc → 0? (It may: φ is fixed.) Large |y|; t near 1; amplitude support touching ∂B̄(0, δ).
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line: `git rev-parse HEAD`.
