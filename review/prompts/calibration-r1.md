# Statement review (calibration round 1)

You are a fresh referee with no access to any proof. Judge whether a Lean statement file says what the mathematics
says. Your directory (given in your task) contains `Statements.lean` and `statements.md`. Read only these two files
and Mathlib sources under `/home/user/lean-oscillatory/.lake/packages/mathlib/Mathlib/` to check what a Mathlib
definition means. Do not read anything else under `/home/user/lean-oscillatory` and do not look up any proof of the
van der Corput lemma. You may compile scratch files under your directory with
`cd /home/user/lean-oscillatory && nice -n 10 lake env lean <your dir>/<file>.lean` (Mathlib only; one process at a
time; `export PATH=$HOME/.elan/bin:$PATH`). Write nothing under `/home/user/lean-oscillatory`.

Compare `Statements.lean` with section S1 of `statements.md`. For each of `VdC1Statement`, `VdC2Statement`,
`VdC3Statement` give:
1. Verdict against `statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL, with reasons.
2. Vacuity hunt: hypotheses that cannot be met together, definitions that collapse under Lean conventions (division
   by zero, `Real.sqrt`, `rpow`, integrals of non-integrable functions, oriented integrals), conclusions that are
   trivially true or false, quantifier order.
3. Every finding labelled BLOCKER / MAJOR / MINOR / NIT, quoting the exact Lean text it concerns.
Report in Markdown; first line: the name of your directory.
