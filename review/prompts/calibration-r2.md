# Statement review (calibration round 2)

You are a fresh referee with no access to any proof. Judge whether a Lean statement file says what the mathematics
says. Your directory (given in your task) contains `Statements.lean` and `statements.md`. Read only these two files
and Mathlib sources under `/home/user/lean-oscillatory/.lake/packages/mathlib/Mathlib/` to check what a Mathlib
definition means. Do not read anything else under `/home/user/lean-oscillatory` or the parent of your directory, and
do not look up any proof of these results. You may compile scratch files under your directory with
`cd /home/user/lean-oscillatory && nice -n 10 lake env lean <your dir>/<file>.lean` (Mathlib only; one process at a
time; `export PATH=$HOME/.elan/bin:$PATH`). Write nothing under `/home/user/lean-oscillatory`.

Compare `Statements.lean` with `statements.md` (sections S2, S3, S4). For each of `NonStationaryStatement`,
`StationaryPhaseStatement`, `FoldStatement`, `D4BoundStatement` give:
1. Verdict against `statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL, with reasons.
   Check every shared definition the statement uses.
2. Vacuity hunt: hypotheses that cannot be met together, definitions that collapse under Lean conventions (division
   by zero, `Real.rpow`, `fderiv` of non-differentiable functions, integrals of non-integrable functions, the max
   norm), conclusions that are trivially true or false, quantifier order.
3. Every finding labelled BLOCKER / MAJOR / MINOR / NIT, quoting the exact Lean text it concerns.
Report in Markdown; first line: the name of your directory.
