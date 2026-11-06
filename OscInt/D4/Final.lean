import OscInt.D4.Assembly
import OscInt.D4.Basic
import OscInt.D4.Rescale
import OscInt.D4.Gauge
import OscInt.D4.Open

/-!
# S4.1: final theorem

The type is the frozen statement constant (checked by `StatementTypes.lean` and `lake comparator` with
`comparator-S4.json`). Route: `docs/proof-S4.md` (refereed); assembly `OscInt.D4.d4Bound_of`; parts in
`OscInt/D4/`.
-/

namespace OscInt

open D4

theorem d4Bound : Statements.D4BoundStatement :=
  d4Bound_of normalizeFacts rescaleFamily cubicGauge gaugeFold gaugeOpen gradBound cutoff trivialBound dyadicSum

end OscInt
