# Referee the proof route and blueprint for S4.2 (the D4 limit)

You are a fresh, hostile, competent analyst. Read `docs/statements.md` (S2/S3 for S2.1 and S3, S4 in full),
`OscInt/Statements/D4Limit.lean` (the statement `D4LimitStatement` and the definitions `cosMoment`,
`angularMoment`, `d4Constant`), `docs/proof-S42.md` (the route), `Blueprint/D4LimitS42.lean` (new parts E1–E3),
`Blueprint/D4.lean` and `Blueprint/D4Limit.lean` (parts reused from S4.1′ and S4.3, all proved or being proved),
`docs/proof-S4.md` (the S4.1′ route the piece bound comes from), and Mathlib sources (e.g. polar coordinates
`integral_comp_polarCoord_symm`, dominated convergence `tendsto_integral_filter_of_dominated_convergence`). Read no
other proof file. Do not compile; write nothing in the repository.

1. Is the route correct as mathematics, step by step (0–5)? In particular: the telescoping at scale ρ = R t^{−1/3}
   and the bound ε_j ≤ ε₀ for every outer piece; the claim that the outer sum is O(R^{−1/2}) t^{−2/3} uniformly in
   t; the rescaling identity t^{2/3}∫ e^{itφ} χ(·/ρ) A = ∫ e^{iΨ_s} χ(·/R) A(s·) with s = t^{−1/3}; the use of
   evenness to make L(R) real; the polar substitution and the uniform-in-θ bound near zeros of g; the order of
   limits in Step 5. Give a counterexample or the missing hypothesis for anything false.
2. Is each of E1–E3 TRUE as stated in Lean (watch `Real.rpow`, `tsupport`, `HasCompactSupport`, the max norm,
   `𝓝 0` versus `𝓝[>] 0` in E2, `R⁻¹ • w` at R = 0, complex coercions)? Do E1–E3, the S4.1′ parts and the S4.3
   results suffice for `D4LimitStatement` (the lead will check this in Lean; flag anything you think cannot be
   assembled)?
3. Rough size and the main Mathlib obstacles of a Lean proof of E1 (the largest part); suggest a split of E1 into
   sub-parts if it is too large for one agent.
Findings as BLOCKER / MAJOR / MINOR / NIT with the exact text; a verdict line: can E1–E3 go to proof agents as they
stand? First line: `git rev-parse HEAD`.
