import OscInt.D4.ConstantPos
import OscInt.D4.CosMoment
import OscInt.D4.Angular
import OscInt.D4.SingularPower

/-!
# S4.3: final theorem

The type is the frozen statement constant (checked by `StatementTypes.lean` and `lake comparator` with
`comparator-S43.json`); the proof is checked Gamma/Beta/Mellin-free by `GammaFree.lean`. Route:
`docs/proof-S43.md` (refereed); assembly `OscInt.D4.d4ConstantPos_of`; parts by proof agents U, V, W.
-/

namespace OscInt

open D4

theorem d4ConstantPos : Statements.D4ConstantPosStatement :=
  d4ConstantPos_of cosIBP sinMoment circleNondeg singularPower angularPos

end OscInt
