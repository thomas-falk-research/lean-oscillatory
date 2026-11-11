/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeCubeRootAssembly
import OscInt.Front.LatticeCubeRootIbp
import OscInt.Front.LatticeCubeRootPieces
import OscInt.Front.LatticeCubeRootRegime8
import OscInt.Front.LatticeCubeRootRegime38

/-!
# Batch LE2: the final theorems

Route `docs/proof-LE2.md`; assembly `OscInt/Front/LatticeCubeRootAssembly.lean`; parts
`OscInt/Front/LatticeCubeRoot{Ibp,Pieces,Regime8,Regime38}.lean`. The bounds have content for `t > 3.7045`
(`(8(1 + √7)/(6π))³`, `docs/statements.md`, Batch LE2, modelling choice 4).
-/

namespace OscInt.API

open OscInt.Statements OscInt.LatticeCubeRootAux

/-- **T0E′** (`LatticeKernel1CubeRootStatement`): `|∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 8(1 + √7)/3 · t^{−1/3}` for
`t > 0`, `ξ ∈ ℝ`. Integration by parts with the end points at `±π` kept, arcsine band lengths and convexity; within a
factor 2 of the best constant. -/
theorem latticeKernel1CubeRoot : LatticeKernel1CubeRootStatement :=
  t0ep_of Ibp.symFacts
    (R8.regime8_of (Pieces.bandLow_of Ibp.ibpFacts Ibp.varFacts) (Pieces.bandHigh_of Ibp.ibpFacts Ibp.varFacts)
      (Pieces.capHigh_of Ibp.ibpFacts Ibp.varFacts) (Pieces.whole_of Ibp.ibpFacts Ibp.varFacts))
    (R38.regime38_of (Pieces.bandLow_of Ibp.ibpFacts Ibp.varFacts) (Pieces.capLow_of Ibp.ibpFacts Ibp.varFacts)
      (Pieces.capHigh_of Ibp.ibpFacts Ibp.varFacts) (Pieces.whole_of Ibp.ibpFacts Ibp.varFacts))

/-- **T6E′** (`LatticeLaplacianCubeRootStatement`): `|K(t, x)| ≤ (8(1 + √7)/3)² t^{−2/3}` for `t > 0`, uniformly in
`x ∈ ℤ²` (T6F and T0E′). -/
theorem latticeLaplacianCubeRoot : LatticeLaplacianCubeRootStatement :=
  t6ep_of latticeKernel1CubeRoot

end OscInt.API
