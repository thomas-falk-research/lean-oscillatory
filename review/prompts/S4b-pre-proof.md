# Blind pre-proof statement review: S4.1′, S4.2, S4.3, S4.4 (D4 at both umbilics, limit, constant)

You are a fresh referee with no access to any proof (none exists). Judge whether the Lean statements say what the
mathematics says, whether they are true, and whether they are non-vacuous. Two referees review independently; do
not look for the other's report.

Read only: `docs/statements.md` (section S4 in full; S2/S3 for shared notation), `docs/decisions/2026-11-06-S4.md`
(why the constant is defined this way), `OscInt/Statements/D4Limit.lean`, `OscInt/Statements/D4.lean`,
`OscInt/Statements/StationaryPhase.lean` (shared definitions), `OscInt/D4/LimitSanity.lean`, and Mathlib sources.
You may compile scratch files under `/tmp/<your name>/` with `nice -n 10 lake env lean …` from the repository root
(`export PATH=$HOME/.elan/bin:$PATH`; one process at a time). You may run the numerics probe
`numerics/target/release/d4const` (already built; read `numerics/src/bin/d4const.rs`). Write nothing in the repository.

For each of `D4BoundNeStatement`, `D4LimitStatement`, `D4ConstantPosStatement`, `D4ConstantClosedFormStatement`:
1. Verdict against `docs/statements.md` (FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL) and against the
   brief's S4 as quoted in the decision record ("at a point where ∇²φ = 0 and the cubic part C has an isolated
   critical point and negative discriminant, … t^{2/3} ∫ e^{itφ} A → c_C A(0) with c_C = Γ(1/3)²/(√3|Disc C|^{1/6})
   ≠ 0"; "prove c_C ≠ 0 via ∫₀^∞ cos(u) u^{-1/3} du > 0 by an alternating-series argument; do not rely on
   Mellin/Gamma identities"). Is it TRUE? If false, give a counterexample.
2. The constant: is `d4Constant` the correct leading coefficient (check the polar-coordinates derivation, the factor
   1/3, the real part / sine cancellation, the exponents −1/3 and −2/3)? Does `limUnder` or a non-integrable
   `angularMoment` create a junk value that makes any statement trivially true or false? Are the two closed forms in
   S4.4 right (signs of Disc, the √3)? Is S4.3 genuinely Gamma-free as a statement?
3. Vacuity and conventions: `Real.rpow` at 0 and for negative bases, `limUnder` without a limit, `fderiv ℝ φ 0 = 0`
   as a hypothesis, the order of `∃ δ` and `∀ A M`, amplitude support at ∂B̄(0, δ), complex coercions in the limit.
4. Is defining c_C by the Gamma-free formula (rather than the closed form) a faithful encoding of the brief, given
   S4.4? Is the widening to `disc ≠ 0` consistent with the brief?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line: `git rev-parse HEAD`.
