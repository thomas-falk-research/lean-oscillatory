/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.StationaryPhase.Assembly
import OscInt.StationaryPhase.LocalCrit
import OscInt.StationaryPhase.Localize
import OscInt.StationaryPhase.Local
import OscInt.StationaryPhase.Implicit
import OscInt.StationaryPhase.NonStat
import OscInt.StationaryPhase.Core

/-!
# S2.1, S2.2, S3: final theorems

Each theorem's type is the frozen statement constant (checked by `StatementTypes.lean` and `lake comparator` with
`comparator-S2S3.json`). Route: `docs/proof-S2S3.md` (refereed), parts in `OscInt/StationaryPhase/`.
-/

namespace OscInt

open StationaryPhase

theorem nonStationary : Statements.NonStationaryStatement := nonStationary_of nonStatCore

theorem stationaryPhase : Statements.StationaryPhaseStatement :=
  stationaryPhase_of familyAddLinear localization localNonCrit
    (localCrit_of normalForm normalizedData coreEstimate)

theorem fold : Statements.FoldStatement :=
  fold_of familyAddLinear localization localNonCrit (localCrit_of normalForm normalizedData coreEstimate)

end OscInt
