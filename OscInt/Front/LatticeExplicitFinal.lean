/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeExplicitParts

/-!
# Batch LE: the final theorems

Route `docs/proof-LE.md`; assembly `OscInt/Front/LatticeExplicitAssembly.lean`; parts
`OscInt/Front/LatticeExplicitParts.lean`. The bounds have content only for large `t` (T0E below the trivial `2π` for
`t > 518`, T6E below `4π²` for `t > 1321`; `docs/statements.md`, Batch LE, clarification 6).
-/

namespace OscInt.API

open OscInt.Statements OscInt.LatticeExplicitAux

/-- **T0E** (`LatticeKernel1ExplicitStatement`): `|∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 24 · 2^{1/4} t^{−1/2} +
36 · 2^{1/6} t^{−1/3}` for `t > 0`, `ξ ∈ ℝ`. From van der Corput's second- and third-derivative tests (S1.2, S1.3). -/
theorem latticeKernel1Explicit : LatticeKernel1ExplicitStatement := t0e_of leAngle lePiece2 lePiece3

/-- **T6F** (`LatticeKernelFactorStatement`): `K(t, x) = I(t, x₁) I(t, x₂)`. -/
theorem latticeKernelFactor : LatticeKernelFactorStatement := t6f

/-- **T6E** (`LatticeLaplacianExplicitStatement`): `|K(t, x)| ≤ (24 · 2^{1/4} + 36 · 2^{1/6})² t^{−2/3}` for `t ≥ 1`,
uniformly in `x ∈ ℤ²` (the constant is below `4761`, `latticeConst_bounds`). -/
theorem latticeLaplacianExplicit : LatticeLaplacianExplicitStatement :=
  t6e_of latticeKernel1Explicit latticeKernelFactor

end OscInt.API
