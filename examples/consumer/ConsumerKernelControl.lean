import OscInt

/-!
Negative control for the kernel replay of `tools/oscint_check.py` (lessons 3, 18): `controlUnchecked` has type
`D4LimitStatement` and no axioms, but its value `True.intro` does not have that type; it is added with kernel
checking switched off, so the build, the type check and the axiom check all accept it and only the kernel replay
(`leanchecker`) can reject it. Used only by `tools/test_oscint_check.sh`; never a default target.
-/

open Lean Elab Command

/-- The declaration the control adds: type `D4LimitStatement`, value `True.intro` (ill-typed). -/
def controlVal : TheoremVal :=
  { name := `controlUnchecked, levelParams := [], type := mkConst ``OscInt.Statements.D4LimitStatement,
    value := mkConst ``True.intro, all := [`controlUnchecked] }

set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl (Declaration.thmDecl controlVal))
