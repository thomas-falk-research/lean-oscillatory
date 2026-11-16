import OscInt.Statements.FiniteRing

/-! Frozen challenges for batch FR (FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P) (`lake comparator`, `comparator-FR.json`).
`sorry` by design; never imported, not audited. -/

namespace OscInt.API

open OscInt.Statements

theorem ringKernelSolves : RingKernelStatement := sorry

theorem ringUnique : RingUniqueStatement := sorry

theorem ringCosetSum : RingCosetSumStatement := sorry

theorem ringFiniteSize : RingFiniteSizeStatement := sorry

theorem chainKernelSolves : ChainKernelStatement := sorry

theorem chainUnique : ChainUniqueStatement := sorry

theorem chainFiniteSize : ChainFiniteSizeStatement := sorry

end OscInt.API
