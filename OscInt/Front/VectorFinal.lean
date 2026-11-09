/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.VectorParts
import OscInt.Front.VectorAssembly

/-!
# Batch VT: the final theorems

Route `docs/proof-VT.md`; assembly `OscInt/Front/VectorAssembly.lean`; part `OscInt/Front/VectorParts.lean`. Each
constant is the constant of the corresponding scalar theorem of batch GD. For spaces in higher universes use
`OscInt.VectorAux.transfer` directly.
-/

namespace OscInt.API

open OscInt.Statements OscInt.VectorAux

/-- **GD-C-V** (`GlobalDecayCritVecStatement`): GD-C for amplitudes in any complex Banach space `E : Type`, one constant. -/
theorem globalDecayCritVec : GlobalDecayCritVecStatement := gdcv_of vecTransfer

/-- **GD-V** (`GlobalDecayVecStatement`): GD for amplitudes in any complex Banach space `E : Type`, one constant. -/
theorem globalDecayVec : GlobalDecayVecStatement := gdv_of vecTransfer

/-- **GD-F-V** (`GlobalFoldVecStatement`): GD-F for amplitudes in any complex Banach space `E : Type`, one constant. -/
theorem globalFoldVec : GlobalFoldVecStatement := gdfv_of vecTransfer

/-- **GD-N-V** (`GlobalNondegVecStatement`): GD-N for amplitudes in any complex Banach space `E : Type`, one constant. -/
theorem globalNondegVec : GlobalNondegVecStatement := gdnv_of vecTransfer

end OscInt.API
