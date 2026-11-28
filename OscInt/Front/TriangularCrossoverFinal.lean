/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.TriangularCrossoverAssembly
import OscInt.Front.TriangularCrossoverLevelCrossing
import OscInt.Front.TriangularCrossoverAmpNormRestrict
import OscInt.Front.TriangularCrossoverPiecewiseVdC
import OscInt.Front.TriangularCrossoverCoreMulti
import OscInt.Front.TriangularCrossoverEvenJetTaylor
import OscInt.Front.TriangularCrossoverJetSeparation
import OscInt.Front.TriangularCrossoverCrossEnvelope
import OscInt.Front.TriangularCrossoverFixedChart
import OscInt.Front.TriangularCrossoverBaseData
import OscInt.Front.TriangularCrossoverPerturbLongitudinal
import OscInt.Front.TriangularCrossoverTiltJet
import OscInt.Front.TriangularCrossoverCoreWindow
import OscInt.Front.TriangularCrossoverWindowLocal
import OscInt.Front.TriangularCrossoverLocalTransfer
import OscInt.Front.TriangularCrossoverReducedParam
import OscInt.Front.TriangularCrossoverComplement
import OscInt.Front.TriangularCrossoverTorusPatch

/-!
# Batch A5U: the final theorem

Route `docs/proof-A5U.md`; blueprint `Blueprint/TriangularCrossover.lean` (18 parts); assembly
`OscInt/Front/TriangularCrossoverAssembly.lean`. Parts by proof agents: A1–A3 (`…LevelCrossing`, `…AmpNormRestrict`,
`…PiecewiseVdC`), A4 (`…CoreMulti`), A5–A7 (`…EvenJetTaylor`, `…JetSeparation`, `…CrossEnvelope`), A8
(`…FixedChart`), A9 (`…BaseData`), A10 (`…PerturbLongitudinal`), A11 (`…TiltJet`), A12a, A12 (`…CoreWindow`,
`…WindowLocal`), A13 (`…LocalTransfer`), B1 (`…ReducedParamData`, `…ReducedParam`), B2 (`…Complement`), B3
(`…TorusPatch`), all under `OscInt/Front/TriangularCrossover*.lean`.
-/

namespace OscInt.API

open OscInt.Statements OscInt.A5UAux

/-- **A5U** Upper bound uniform across an exceptional coupling `a₀ = ±1/(2√2)`:
`|triKernel α t n| ≤ C t^{−2/3} E(|α − a₀| t^{1/3})` for `|α − a₀| ≤ r`, real `t ≥ 1` and every site. -/
theorem triCrossoverUpper : TriCrossoverUpperStatement :=
  triCrossoverUpper_of levelCrossing ampNormRestrict piecewiseVdC coreEstimateMulti evenJetTaylor jetSeparation
    crossEnvelopeFacts a5FixedChart a5BaseData perturbLongitudinal a5TiltJet a5CoreWindow a5WindowLocal
    localTransfer reducedOrderBoundParam complementLocal torusPatchParam

end OscInt.API
