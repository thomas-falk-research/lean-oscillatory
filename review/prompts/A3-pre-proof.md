# Blind statement review: batch A3 (S1.k, S5.1, S5.1′)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No Lean proof of these three statements exists in the repository or in the lead's scratch. **Do not prove the
statements under review, not even in your own scratch: numerical checks, counterexample searches and Lean checks of
small facts about definitions (e.g. evaluating a definition on concrete data) only** (lessons 24).

Read: `docs/statements.md` (section "Batch A3" in full; "S1", "S2, S3", "S4" and "Batch GD" for the frozen statements
this batch builds on), `OscInt/Statements/Cusp.lean` (the batch), `OscInt/Statements/VanDerCorput.lean` and
`OscInt/Statements/StationaryPhase.lean` (shared definitions: `oscInt`, `HasDerivOn`, `AmplitudeOn`, `ampNorm`,
`oscInt2`, `lin`, `AmpBound`), `OscInt/Statements/Global.lean` (`IsD4Point`, the idiom `IsA3Point` follows),
`OscInt/Front/CuspSanity.lean` (sanity theorems and bite data), `numerics/a3/statement_checks.py` with
`numerics/results-a3-statements-2026-11-09.txt` (exact checks and exploratory numerics; tooling, not evidence),
`numerics/census/spec_checks.py` (checks R1–R3 of the reduced quartic), `docs/prior_art.md` (section "Singularities of
lattice dispersion relations"), `docs/lessons.md` (entries 11, 12, 17, 24, 33, 38), and Mathlib sources under
`.lake/packages/mathlib`. You may compile scratch files under `/tmp/<your name>/` with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root (`export PATH=$(ls -d
~/lean/lean-*-linux)/bin:$PATH` puts Lean on the PATH; one Lean process at a time) and run numerical checks (Python
with the environment of `numerics/census/requirements.txt`, or the standard library). Write nothing in the repository.

For each statement constant and each definition in `Cusp.lean`:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL, and separately
   against the classical mathematics (Stein's k-th derivative van der Corput lemma; the uniform estimate for an A3
   singularity of a function of two variables). Is it TRUE? If you believe it false, give a concrete counterexample
   (exact data) and check it numerically. Pay attention to: the parsing of `((5 : ℝ) * 2 ^ (k - 1) - 2)` (natural
   subtraction `k - 1` with `2 ≤ k`) and of `μ ^ (-(1 : ℝ) / (k : ℝ))`; `DerivChain` (which `D j` are constrained, and
   on which sets); the order and roles of the arguments in `iteratedFDeriv ℝ n Ψ k₀ ![…]`; whether `IsA3Point` is
   exactly "rank-one Hessian, third derivative zero along the kernel, reduced quartic nonzero", including degenerate
   choices (`v = 0`, `w` in the kernel, `w` not orthogonal to the kernel); whether the existential `∃ v w` could be
   satisfied by a point that is not A3; whether `IsStableA3Point`'s extra condition is independent of the choice of
   `w`; `ContDiff ℝ ∞` (the smooth index, not analytic: lessons 12); `AmpBound 2 (Metric.closedBall 0 δ)` with the max
   norm; `∃ δ > 0, ∃ C` before `A, M, y, t`; the uniformity over all `y ∈ ℝ²` with `t ≥ 1`; `t ^ (-(3 : ℝ) / 4)`.
2. Derivability: is S1.k provable with the stated constant `5·2^{k−1} − 2` by the classical induction with amplitude?
   Are S1.2 and S1.3 its cases k = 2, 3 (the sanity file derives them)? Is S5.1 provable by the route named in
   `docs/statements.md` (anisotropic rescaling `ε⁻⁴φ(εu, ε²s)` in kernel/transverse coordinates, the compact-family
   fold bound S3 on annuli, S2.1 for large linear terms, mirroring the proved S4.1′ route)? In particular: does the
   rescaled family satisfy `FamilyCk 4` on a compact parameter set for a C^∞ phase, and is every point of the annuli
   nondegenerate or a fold for the model `h s²/2 + (T/2)u²s + (Q/24)u⁴` (check E1)? Is S5.1′ (no coupling condition)
   provable with C² amplitudes by the route sketched there (Morse lemma with parameters in the transverse variable,
   then S1.k with k = 4)? Name any step where a route fails, and whether that makes a statement false or only unproved.
3. Vacuity and usefulness: are the hypotheses jointly satisfiable (the sanity file's data)? Do the A3 points of the
   discrete Klein–Gordon band `√(5 − 2cos k₁ − 2cos k₂)` at `(±π/2, ±π/2)` and of the QWZ band at `m = 3` satisfy
   `IsStableA3Point` after translation to the origin? Is anything a downstream user needs lost (local smoothness, a
   general point `k₀`, compact families, the global assembly with finitely many A3 points, which is not in this batch)?
4. The sanity theorems: do the bites fail exactly the condition they target (e.g. `(y + x²/2)²`: nonzero straight-line
   quartic, zero reduced quartic)? Which plants that weaken a hypothesis or strengthen a conclusion would they miss?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
