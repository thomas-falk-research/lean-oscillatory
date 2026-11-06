# Referee the proof route and blueprint for S4.4

You are a fresh, hostile, competent analyst. Read, in the repository at /home/user/lean-oscillatory (commit 828309a;
do not modify anything there, do not commit, do not run `lake build` or `make`):
`docs/statements.md` (S4), `OscInt/Statements/D4Limit.lean`, `OscInt/Statements/D4.lean` (for `disc`),
`OscInt/D4/Polar.lean` (`cubicForm_neg`, `cubicForm_polar`), `OscInt/D4/Angular.lean` (`circleNondeg`), and
Mathlib sources under `.lake/packages/mathlib`. The files under review are in the scratch directory
/tmp/claude-0/-home-user-lean-oscillatory/448ffe38-12ad-59da-9f96-48c131dcaeee/scratchpad/s44/ (they will be committed
as `docs/proof-S44.md`, `Blueprint/D4ClosedForm.lean`, `OscInt/D4/ClosedForm.lean`, `OscInt/D4/GammaSixth.lean`):
`proof-S44.md`, `Blueprint_D4ClosedForm.lean`, `ClosedForm.lean` (the assembly, already elaborated by Lean against
E1, E2, E3, E5, E6c, E7 as hypotheses, axioms `propext`, `Classical.choice`, `Quot.sound` only), `GammaSixth.lean`
(E7, proved). Read no other proof file.

The assembly being machine-checked means the parts suffice. Decide, for each of E1, E2, E3, E5, E6a, E6b, E6c,
whether the Prop is TRUE as stated in Lean (watch `Real.rpow` at 0 and for negative bases — `x ^ (-(2:ℝ)/3)` for
`x = 0` is `0`; the Bochner integral of a non-integrable function is `0`; `limUnder`; interval-integral orientation;
`IntervalIntegrable` versus `IntegrableOn`; whether `cubicComp` really gives the coefficients of `C ∘ lin2 g` in the
order of `cubicForm`), whether the route's argument for each is correct and complete, and which Mathlib lemmas a
prover will need (name them; say if a name in the route does not exist at this Mathlib). You may run
`lake env lean <file>` on a file *you* write under the scratch directory to `#check` names or test a claim (one
process, under `nice -n 10`). Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text; a verdict line: can
the parts go to proof agents as they stand? First line of your report: the sha256 of each of the four scratch files
(`sha256sum`). Return the report as your final message (the lead records it verbatim under `review/`).
