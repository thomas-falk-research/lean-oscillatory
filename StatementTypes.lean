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
#assert_type_is OscInt.d4BoundNe OscInt.Statements.D4BoundNeStatement
#assert_type_is OscInt.d4ConstantPos OscInt.Statements.D4ConstantPosStatement
#assert_type_is OscInt.d4Limit OscInt.Statements.D4LimitStatement
#assert_type_is OscInt.d4ConstantClosedForm OscInt.Statements.D4ConstantClosedFormStatement
#assert_type_is OscInt.API.ampBoundOfContDiff OscInt.Statements.AmpBoundOfContDiffStatement
#assert_type_is OscInt.API.d4LimitClosedForm OscInt.Statements.D4LimitClosedFormStatement
#assert_type_is OscInt.API.dd_iteratedFDeriv OscInt.Statements.DdEqIteratedStatement
#assert_type_is OscInt.API.ddd_iteratedFDeriv OscInt.Statements.DddEqIteratedStatement
#assert_type_is OscInt.API.hessDet_eq_det OscInt.Statements.HessDetEqDetStatement
#assert_type_is OscInt.API.cubicCoeffs_eq OscInt.Statements.CubicCoeffsEqStatement
#assert_type_is OscInt.API.disc_eq_cubic_discr OscInt.Statements.DiscEqCubicDiscrStatement
#assert_type_is OscInt.API.disc_ne_zero_iff_isolated OscInt.Statements.DiscNeZeroIffIsolatedStatement
#assert_type_is OscInt.API.foldOrNondeg_iff OscInt.Statements.FoldOrNondegIffStatement
#assert_type_is OscInt.API.foldOrNondeg_of_hasFDeriv OscInt.Statements.FoldOrNondegOfHasFDerivStatement
#assert_type_is OscInt.API.gradLower_iff OscInt.Statements.GradLowerIffStatement
#assert_type_is OscInt.API.ampBound_conv OscInt.Statements.AmpBoundConvStatement
#assert_type_is OscInt.API.nonStationaryFE OscInt.Statements.NonStationaryFEStatement
#assert_type_is OscInt.API.stationaryPhaseFE OscInt.Statements.StationaryPhaseFEStatement
#assert_type_is OscInt.API.foldFE OscInt.Statements.FoldFEStatement
#assert_type_is OscInt.API.d4BoundFE OscInt.Statements.D4BoundFEStatement
#assert_type_is OscInt.API.stationaryPhaseFamily OscInt.Statements.StationaryPhaseFamilyStatement
#assert_type_is OscInt.API.foldCrit OscInt.Statements.FoldCritStatement
#assert_type_is OscInt.API.familyCk_of_uncurry OscInt.Statements.FamilyCkOfUncurryStatement
#assert_type_is OscInt.API.nonStationaryLocal OscInt.Statements.NonStationaryLocalStatement
#assert_type_is OscInt.API.stationaryPhaseLocal OscInt.Statements.StationaryPhaseLocalStatement
#assert_type_is OscInt.API.foldLocal OscInt.Statements.FoldLocalStatement
#assert_type_is OscInt.API.d4BoundLocal OscInt.Statements.D4BoundLocalStatement
#assert_type_is OscInt.API.nonStationaryOn OscInt.Statements.NonStationaryOnStatement
#assert_type_is OscInt.API.stationaryPhaseOn OscInt.Statements.StationaryPhaseOnStatement
#assert_type_is OscInt.API.foldOn OscInt.Statements.FoldOnStatement
#assert_type_is OscInt.API.globalDecayCrit OscInt.Statements.GlobalDecayCritStatement
#assert_type_is OscInt.API.globalDecay OscInt.Statements.GlobalDecayStatement
#assert_type_is OscInt.API.globalFold OscInt.Statements.GlobalFoldStatement
#assert_type_is OscInt.API.globalNondeg OscInt.Statements.GlobalNondegStatement
#assert_type_is OscInt.API.sharpness OscInt.Statements.SharpnessStatement
#assert_type_is OscInt.API.torusUnfold OscInt.Statements.TorusUnfoldStatement
#assert_type_is OscInt.API.latticeLaplacianDecay OscInt.Statements.LatticeLaplacianDecayStatement
