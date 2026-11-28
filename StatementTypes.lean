/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

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
#assert_type_is OscInt.API.latticeLaplacianLimit OscInt.Statements.LatticeLaplacianLimitStatement
#assert_type_is OscInt.API.latticeKernel1Explicit OscInt.Statements.LatticeKernel1ExplicitStatement
#assert_type_is OscInt.API.latticeKernelFactor OscInt.Statements.LatticeKernelFactorStatement
#assert_type_is OscInt.API.latticeLaplacianExplicit OscInt.Statements.LatticeLaplacianExplicitStatement
#assert_type_is OscInt.API.globalDecayCritVec OscInt.Statements.GlobalDecayCritVecStatement
#assert_type_is OscInt.API.globalDecayVec OscInt.Statements.GlobalDecayVecStatement
#assert_type_is OscInt.API.globalFoldVec OscInt.Statements.GlobalFoldVecStatement
#assert_type_is OscInt.API.globalNondegVec OscInt.Statements.GlobalNondegVecStatement
#assert_type_is OscInt.API.latticeKernel1CubeRoot OscInt.Statements.LatticeKernel1CubeRootStatement
#assert_type_is OscInt.API.latticeLaplacianCubeRoot OscInt.Statements.LatticeLaplacianCubeRootStatement
#assert_type_is OscInt.API.hypercubicKernelFactor OscInt.Statements.HypercubicKernelFactorStatement
#assert_type_is OscInt.API.hypercubicCubeRoot OscInt.Statements.HypercubicCubeRootStatement
#assert_type_is OscInt.API.vdCk OscInt.Statements.VdCkStatement
#assert_type_is OscInt.API.cuspBoundGen OscInt.Statements.CuspBoundGenStatement
#assert_type_is OscInt.API.cuspBound OscInt.Statements.CuspBoundStatement
#assert_type_is OscInt.API.latticeSchrodingerExists OscInt.Statements.LatticeSchrodingerExistsStatement
#assert_type_is OscInt.API.latticeSchrodingerKernel OscInt.Statements.LatticeSchrodingerKernelStatement
#assert_type_is OscInt.API.latticeSchrodingerDispersive OscInt.Statements.LatticeSchrodingerDispersiveStatement
#assert_type_is OscInt.API.latticeSchrodingerDecay OscInt.Statements.LatticeSchrodingerDecayStatement
#assert_type_is OscInt.API.d4LimitUniform OscInt.Statements.D4LimitUniformStatement
#assert_type_is OscInt.API.d4LimitOffset OscInt.Statements.D4LimitOffsetStatement
#assert_type_is OscInt.API.fourierCoeffStrip OscInt.Statements.FourierCoeffStripStatement
#assert_type_is OscInt.API.trapezoidalRule OscInt.Statements.TrapezoidalRuleStatement
#assert_type_is OscInt.API.latticeKernel1LightCone OscInt.Statements.LatticeKernel1LightConeStatement
#assert_type_is OscInt.API.kusminLandau OscInt.Statements.KusminLandauStatement
#assert_type_is OscInt.API.kusminLandauTwoOverPi OscInt.Statements.KusminLandauTwoOverPiStatement
#assert_type_is OscInt.API.kusminLandauDeriv OscInt.Statements.KusminLandauDerivStatement
#assert_type_is OscInt.API.ringKernelSolves OscInt.Statements.RingKernelStatement
#assert_type_is OscInt.API.ringUnique OscInt.Statements.RingUniqueStatement
#assert_type_is OscInt.API.ringCosetSum OscInt.Statements.RingCosetSumStatement
#assert_type_is OscInt.API.ringFiniteSize OscInt.Statements.RingFiniteSizeStatement
#assert_type_is OscInt.API.chainKernelSolves OscInt.Statements.ChainKernelStatement
#assert_type_is OscInt.API.chainUnique OscInt.Statements.ChainUniqueStatement
#assert_type_is OscInt.API.chainFiniteSize OscInt.Statements.ChainFiniteSizeStatement
#assert_type_is OscInt.API.hadamardKernelFormula OscInt.Statements.HadamardKernelStatement
#assert_type_is OscInt.API.hadamardKernelBound OscInt.Statements.HadamardKernelBoundStatement
#assert_type_is OscInt.API.hadamardDecay OscInt.Statements.HadamardDecayStatement
#assert_type_is OscInt.API.hadamardDispersive OscInt.Statements.HadamardDispersiveStatement
#assert_type_is OscInt.API.secondDerivSharp OscInt.Statements.SecondDerivSharpStatement
#assert_type_is OscInt.API.secondDerivAttained OscInt.Statements.SecondDerivAttainedStatement
#assert_type_is OscInt.API.vdc2ProfileBound OscInt.Statements.Vdc2ProfileBoundStatement
#assert_type_is OscInt.API.secondDerivSevenHalves OscInt.Statements.SecondDerivSevenHalvesStatement
#assert_type_is OscInt.API.stationaryLeadingIdentity OscInt.Statements.StationaryLeadingIdentityStatement
#assert_type_is OscInt.API.stationaryLeading OscInt.Statements.StationaryLeadingStatement
#assert_type_is OscInt.API.stationaryLeadingSevenEighths OscInt.Statements.StationaryLeadingSevenEighthsStatement
#assert_type_is OscInt.API.stationaryLeadingAttained OscInt.Statements.StationaryLeadingAttainedStatement
#assert_type_is OscInt.API.triClassification OscInt.Statements.TriClassificationStatement
#assert_type_is OscInt.API.triA5Locus OscInt.Statements.TriA5LocusStatement
#assert_type_is OscInt.API.triA5Witness OscInt.Statements.TriA5WitnessStatement
#assert_type_is OscInt.API.triQuartic OscInt.Statements.TriQuarticStatement
#assert_type_is OscInt.API.monomialAsymptotic OscInt.Statements.MonomialAsymptoticStatement
#assert_type_is OscInt.API.monomialLower OscInt.Statements.MonomialLowerStatement
#assert_type_is OscInt.API.reducedOrderBound OscInt.Statements.ReducedOrderBoundStatement
#assert_type_is OscInt.API.torusLocalization OscInt.Statements.TorusLocalizationStatement
#assert_type_is OscInt.API.triDecayUpper OscInt.Statements.TriDecayUpperStatement
#assert_type_is OscInt.API.triDecayLower OscInt.Statements.TriDecayLowerStatement
