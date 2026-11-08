/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.GlobalAssembly
import OscInt.Front.GlobalLocal
import OscInt.Front.Torus
import OscInt.Front.Sharpness
import OscInt.Front.LatticeKernel

/-!
# Batch GD: the final theorems GD-C, GD, GD-F, GD-N, T1

Each theorem's type is its frozen statement constant (`OscInt/Statements/Global.lean`; `StatementTypes.lean`).
SH is `OscInt.API.sharpness` (`OscInt/Front/Sharpness.lean`), T6 is `OscInt.API.latticeLaplacianDecay`
(`OscInt/Front/LatticeKernel.lean`). Parts: GD-P1 `OscInt/Front/GlobalLocal.lean`, GD-P2 `OscInt/Front/Torus.lean`,
GD-P3 `OscInt/Front/LatticeSymbol.lean` (proof agents); assemblies by the lead (`OscInt/Front/GlobalAssembly.lean`).
-/

namespace OscInt.API

open OscInt.Statements

/-- **GD-C** (`GlobalDecayCritStatement`). -/
theorem globalDecayCrit : GlobalDecayCritStatement :=
  GlobalAux.globalDecayCrit_of GlobalLocal.d4PieceFacts GlobalLocal.bumpFacts GlobalLocal.mulBoundFacts

/-- **GD** (`GlobalDecayStatement`). -/
theorem globalDecay : GlobalDecayStatement :=
  GlobalAux.globalDecay_of GlobalLocal.d4PieceFacts GlobalLocal.bumpFacts GlobalLocal.mulBoundFacts
    GlobalLocal.largeLFacts

/-- **GD-F** (`GlobalFoldStatement`). -/
theorem globalFold : GlobalFoldStatement := GlobalAux.globalFold_of GlobalLocal.largeLFacts

/-- **GD-N** (`GlobalNondegStatement`). -/
theorem globalNondeg : GlobalNondegStatement := GlobalAux.globalNondeg_of GlobalLocal.largeLFacts

/-- **T1** (`TorusUnfoldStatement`), with the explicit weight `OscInt.API.Torus.unfoldWeight`. -/
theorem torusUnfold : TorusUnfoldStatement :=
  ⟨Torus.unfoldWeight, Torus.unfoldFacts.1, Torus.unfoldFacts.2.1, Torus.unfoldFacts.2.2.2⟩

end OscInt.API
