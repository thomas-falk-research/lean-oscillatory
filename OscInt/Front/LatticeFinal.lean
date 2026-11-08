import OscInt.Front.LatticeLimit

/-!
# T6L: the final theorem

Proof `OscInt/Front/LatticeLimit.lean` (proof agent GD-P4; route `docs/proof-GD.md` R9).
-/

namespace OscInt.API

open OscInt.Statements

/-- **T6L** (`LatticeLaplacianLimitStatement`): `(−1)ⁿ n^{2/3} K(n, (n, n)) → Γ(1/3)² 48^{1/6}/√3`. -/
theorem latticeLaplacianLimit : LatticeLaplacianLimitStatement := LatticeLimitAux.latticeLaplacianLimit_proof

end OscInt.API
