import OscInt

/-!
Negative controls for `tools/oscint_check.py` (lessons 18); used only by `tools/test_oscint_check.sh`, never a default
target, never imported by `Consumer`. Each theorem has a defect exactly one check must catch:
* `controlTheorem`: type `D4LimitStatement`, proof through an extra axiom (axiom check).
* `controlDefeq`: type `id D4LimitStatement`, definitionally but not syntactically the statement (type check).
-/

axiom controlAxiom : OscInt.Statements.D4LimitStatement

theorem controlTheorem : OscInt.Statements.D4LimitStatement := controlAxiom

theorem controlDefeq : id OscInt.Statements.D4LimitStatement := OscInt.d4Limit
