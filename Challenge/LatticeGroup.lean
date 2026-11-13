import OscInt.Statements.LatticeGroup

/-! Frozen challenges for batch LS (LS-E, LS-K, LS-D, LS-D′) (`lake comparator`, `comparator-LS.json`).
`sorry` by design; never imported, not audited. -/

namespace OscInt.API

open OscInt.Statements

theorem latticeSchrodingerExists : LatticeSchrodingerExistsStatement := sorry

theorem latticeSchrodingerKernel : LatticeSchrodingerKernelStatement := sorry

theorem latticeSchrodingerDispersive : LatticeSchrodingerDispersiveStatement := sorry

theorem latticeSchrodingerDecay : LatticeSchrodingerDecayStatement := sorry

end OscInt.API
