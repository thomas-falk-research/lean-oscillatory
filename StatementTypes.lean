import OscInt

/-!
Statement-type check: for each final theorem, its type must be syntactically (`Expr` equality, no unfolding) the
statement constant reviewed and committed in `OscInt/Statements/`. Defeq-but-different types fail.
The list of pairs grows with the milestones; `tools/src/bin/guard.rs` checks that every theorem named in
`comparator.json` appears here.
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

#assert_type_is OscInt.vanDerCorput_one OscInt.Statements.VdC1Statement
#assert_type_is OscInt.vanDerCorput_two OscInt.Statements.VdC2Statement
#assert_type_is OscInt.vanDerCorput_three OscInt.Statements.VdC3Statement
#assert_type_is OscInt.nonStationary OscInt.Statements.NonStationaryStatement
#assert_type_is OscInt.stationaryPhase OscInt.Statements.StationaryPhaseStatement
#assert_type_is OscInt.fold OscInt.Statements.FoldStatement
#assert_type_is OscInt.d4Bound OscInt.Statements.D4BoundStatement
