import OscInt

/-!
Negative control for `tools/oscint_check.py` (lessons 18): a theorem whose type *is* `D4LimitStatement` but whose
proof uses an extra axiom. The checker must reject it when a statement list names it as the proof. Built only by
`tools/test_oscint_check.sh`; never a default target, never imported by `Consumer`.
-/

axiom controlAxiom : OscInt.Statements.D4LimitStatement

theorem controlTheorem : OscInt.Statements.D4LimitStatement := controlAxiom
