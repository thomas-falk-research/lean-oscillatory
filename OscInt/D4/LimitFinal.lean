/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.D4.LimitAssembly
import OscInt.D4.Final
import OscInt.D4.ConstantPosFinal
import OscInt.D4.Radial
import OscInt.D4.Polar
import OscInt.D4.PolarLimit
import OscInt.D4.Tail

/-!
# S4.2: final theorem

The type is the frozen statement constant (checked by `StatementTypes.lean` and `lake comparator` with
`comparator-S42.json`). Route: `docs/proof-S42.md` (refereed); assembly `OscInt.D4.d4Limit_of` (lead); new parts
E1a–E1d, E2, E3 by proof agents Y, Z, Q2, X; S4.1′ parts and S4.3 reused.
-/

namespace OscInt

open D4

theorem d4Limit : Statements.D4LimitStatement :=
  d4Limit_of rescaleFamily cubicGauge gaugeFold gaugeOpen cutoff
    (cubicCutoffLimit_of radialIdentity polarReduction circleZerosNull) innerLimit dyadicTail d4ConstantPos

end OscInt
