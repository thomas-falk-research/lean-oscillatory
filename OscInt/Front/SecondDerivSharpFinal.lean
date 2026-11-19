/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.SecondDerivSharpAssembly
import OscInt.Front.SecondDerivSharpTurn
import OscInt.Front.SecondDerivSharpHead
import OscInt.Front.SecondDerivSharpTail
import OscInt.Front.SecondDerivSharpSide
import OscInt.Front.SecondDerivSharpProfile
import OscInt.Front.SecondDerivSharpAttained

/-!
# Batch VC2: the final theorems

Route `docs/proof-VC2.md` (read by one route referee, an AI agent of the lead's model family; "Parts as
integrated"); assembly `OscInt/Front/SecondDerivSharpAssembly.lean`; parts
`OscInt/Front/SecondDerivSharpTurn.lean` (the turning point; the speed dominates the root of the phase gained),
`OscInt/Front/SecondDerivSharpHead.lean` (a positive arc from the turning point),
`OscInt/Front/SecondDerivSharpTail.lean` (from the start of a negative arc the integral of the cosine is `≤ 0`),
`OscInt/Front/SecondDerivSharpSide.lean` (one side of the turning point, for every rotation),
`OscInt/Front/SecondDerivSharpProfile.lean` (VC2-N) and `OscInt/Front/SecondDerivSharpAttained.lean` (VC2-A).
The sharp constant is classical; the theorem is classical for `f″ ≥ λ` by citation only (`docs/prior_art.md`,
batch VC2: the originals have not been read here, and whether the classical statement covers an increment
condition without a second derivative is not known to the lead). Nothing here is claimed as new mathematics.
-/

namespace OscInt.API

open OscInt.Statements OscInt.SecondDerivSharpAux

/-- **VC2-S** (`SecondDerivSharpStatement`): if `f′` increases at rate at least `λ > 0` on `(a, b)`, then
`|∫_a^b e^{if}| ≤ A(w)/√λ` for some `w ∈ [0, π]`, with `A = vdc2Profile`. -/
theorem secondDerivSharp : SecondDerivSharpStatement :=
  secondDerivSharp_of vdc2TurningPointFacts (vdc2OneSideFacts_of (vdc2HeadFacts_of vdc2RootFacts) vdc2TailFacts)

/-- **VC2-A** (`SecondDerivAttainedStatement`): `A(w) ≤ |∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx|` for `w ≥ 0`. -/
theorem secondDerivAttained : SecondDerivAttainedStatement := secondDerivAttained_part

/-- **VC2-N** (`Vdc2ProfileBoundStatement`): `A(w) ≤ 7/2` for `0 ≤ w ≤ π`. -/
theorem vdc2ProfileBound : Vdc2ProfileBoundStatement := vdc2ProfileBound_part

/-- **VC2-K** (`SecondDerivSevenHalvesStatement`): the second-derivative test with amplitude and a linear term,
constant `7/2`. -/
theorem secondDerivSevenHalves : SecondDerivSevenHalvesStatement :=
  secondDerivSevenHalves_of secondDerivSharp vdc2ProfileBound

end OscInt.API
