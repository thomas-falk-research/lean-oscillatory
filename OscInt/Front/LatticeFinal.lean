/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeLimit

/-!
# T6L: the final theorem

Proof `OscInt/Front/LatticeLimit.lean` (proof agent GD-P4; route `docs/proof-GD.md` R9).
-/

namespace OscInt.API

open OscInt.Statements

/-- **T6L** (`LatticeLaplacianLimitStatement`): `(−1)ⁿ n^{2/3} K(n, (n, n)) → Γ(1/3)² 48^{1/6}/√3`. -/
theorem latticeLaplacianLimit : LatticeLaplacianLimitStatement := LatticeLimitAux.latticeLaplacianLimit_proof

end OscInt.API
