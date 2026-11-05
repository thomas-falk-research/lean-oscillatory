import OscInt

/-!
Statement-type check: for each final theorem, its type must be syntactically (`Expr` equality, no unfolding) the
statement constant reviewed and committed in `OscInt/Statements/`. Defeq-but-different types fail.
The list of pairs grows with the milestones; `tools/src/bin/guard.rs` checks every `OscInt.<X>` theorem named
in `docs/STATUS.md` as proved appears here.
-/

open Lean Elab Command

elab "#assert_type_is " thm:ident stmt:ident : command => do
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let s ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stmt
  let some ci := (← getEnv).find? t | throwError m!"unknown constant {t}"
  unless ci matches .thmInfo _ do throwError m!"{t} is not a theorem"
  unless ci.type == mkConst s [] do
    throwError m!"statement type check FAILED: the type of {t} is not the constant {s}"
  IO.println s!"TYPE-OK {t} : {s}"
