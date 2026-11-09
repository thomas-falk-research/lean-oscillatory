# Blind statement review: batch LE (T0E, T6F, T6E)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No Lean proof of these three statements exists in the repository or in the lead's scratch. **Do not prove the
statements under review, not even in your own scratch: numerical checks, counterexample searches and Lean checks of
small facts about definitions (e.g. evaluating a definition on concrete data) only** (lessons 24).

Read: `docs/statements.md` (section "Batch LE" in full; "S1" and "Batch GD" for the frozen statements and the kernel
this batch builds on), `OscInt/Statements/LatticeExplicit.lean` (the batch), `OscInt/Statements/VanDerCorput.lean`
and `OscInt/Statements/Global.lean` (shared definitions: `oscInt`, `HasDerivOn`, `AmplitudeOn`, `ampNorm`,
`latticeKernel`, `torusBox`), `OscInt/Front/LatticeExplicitSanity.lean` (sanity theorems through the constants) with
`docs/replay/2026-11-08-LE-sanity-plants.txt` (planted controls), `docs/prereg/2026-11-08-LE-lattice-constants.md`
with `numerics/results-lattice1-2026-11-08.txt` (the numeric pre-registration; tooling, not evidence),
`docs/prior_art.md` (section "Lattice kernels"), `docs/lessons.md` (entries 11, 12, 17, 24, 33), and Mathlib sources
under `.lake/packages/mathlib`. You may compile scratch files under `/tmp/<your name>/` with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root (`. ~/.leanenv` puts Lean on the PATH;
one Lean process at a time) and run numerical checks (Python, standard library, or Rust). Write nothing in the
repository.

For each statement constant in `LatticeExplicit.lean`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL (and separately
   against the classical facts: Bessel's integral, Landau's bound). Is it TRUE? If you believe it false, give a
   concrete counterexample (exact data) and check it numerically. Pay attention to: `latticeKernel1` (the oriented
   interval integral `∫ k in (-π)..π`, the cast `↑(t * cos k + ξ * k)`, real `ξ`); `Real.rpow` with exponents
   `-(1 : ℝ) / 2`, `-(1 : ℝ) / 3`, `-(2 : ℝ) / 3` (parsing: is `-(1 : ℝ) / 3` equal to `-(1/3)`?) and `(2 : ℝ) ^ ((1 :
   ℝ) / 4)`; the hypotheses `0 < t` (T0E), none (T6F), `1 ≤ t` (T6E); the casts `(x.1 : ℝ)` from ℤ in T6F and whether
   the product matches `latticeKernel`'s integral over `torusBox` with Lebesgue measure on `ℝ × ℝ`; the uniformity of
   `∀ ξ`/`∀ x` relative to the constant (it is explicit here, no `∃ C`).
2. Derivability: is T0E implied by the frozen, proved S1.2 (`VdC2Statement`, constant `8/√μ`) and S1.3
   (`VdC3Statement`, `18 μ^{−1/3}`) by the route in the docs (split at ±π/4, ±3π/4; `|cos| ≥ 1/√2` or `|sin| ≥ 1/√2` on
   each piece; amplitude 1; linear term ξ)? Check the arithmetic of the constant (3 · 8 · 2^{1/4}, 2 · 18 · 2^{1/6}),
   the hypotheses of S1.2/S1.3 on each closed piece (`HasDerivOn` on `[a, b]`, the bound on the open interval, the
   amplitude `ψ = 1` with `ψ' = 0`), and the identification of `oscInt (fun x => φ x + p * x) ψ a b` with the integrand
   of `latticeKernel1`. Is T6F true as stated (Fubini on the box; are both sides the same function of `t` for every
   real `t`, including `t ≤ 0`)? Does T6E follow from T0E and T6F for `t ≥ 1`? Name any step where it fails.
3. Vacuity and usefulness: does T6E improve on T6 in a way a downstream user can use (an explicit constant for the ℓ¹ →
   ℓ^∞ dispersive estimate of the 2D lattice Schrödinger group)? Is anything a user needs lost (e.g. small `t`, the
   normalisation `(2π)^{-2}`, non-integer `x`)? Are the constants honestly described as non-sharp?
4. The sanity theorems and planted controls: do they test the frozen text (lessons 33)? What would they miss? Which
   plants that weaken a hypothesis or strengthen a conclusion matter most here (e.g. a smaller constant)?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
