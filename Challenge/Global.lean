import OscInt.Statements.Global

/-! Frozen challenges for batch GD (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L) (`lake comparator`, `comparator-GD.json`).
`sorry` by design; never imported, not audited. -/

namespace OscInt.API

open OscInt.Statements

theorem globalDecayCrit : GlobalDecayCritStatement := sorry

theorem globalDecay : GlobalDecayStatement := sorry

theorem globalFold : GlobalFoldStatement := sorry

theorem globalNondeg : GlobalNondegStatement := sorry

theorem sharpness : SharpnessStatement := sorry

theorem torusUnfold : TorusUnfoldStatement := sorry

theorem latticeLaplacianDecay : LatticeLaplacianDecayStatement := sorry

theorem latticeLaplacianLimit : LatticeLaplacianLimitStatement := sorry

end OscInt.API
