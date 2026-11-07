import OscInt.Statements.Convert

/-! Frozen challenges for the front-end batch 2 (C1–C9, FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′) (`lake comparator`,
`comparator-API2.json`). `sorry` by design; never imported, not audited. -/

namespace OscInt.API

open OscInt.Statements

theorem dd_iteratedFDeriv : DdEqIteratedStatement := sorry

theorem ddd_iteratedFDeriv : DddEqIteratedStatement := sorry

theorem hessDet_eq_det : HessDetEqDetStatement := sorry

theorem cubicCoeffs_eq : CubicCoeffsEqStatement := sorry

theorem disc_eq_cubic_discr : DiscEqCubicDiscrStatement := sorry

theorem disc_ne_zero_iff_isolated : DiscNeZeroIffIsolatedStatement := sorry

theorem foldOrNondeg_iff : FoldOrNondegIffStatement := sorry

theorem foldOrNondeg_of_hasFDeriv : FoldOrNondegOfHasFDerivStatement := sorry

theorem gradLower_iff : GradLowerIffStatement := sorry

theorem ampBound_conv : AmpBoundConvStatement := sorry

theorem nonStationaryFE : NonStationaryFEStatement := sorry

theorem stationaryPhaseFE : StationaryPhaseFEStatement := sorry

theorem foldFE : FoldFEStatement := sorry

theorem d4BoundFE : D4BoundFEStatement := sorry

end OscInt.API
