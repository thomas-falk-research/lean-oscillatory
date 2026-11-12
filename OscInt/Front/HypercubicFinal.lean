/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.HypercubicAssembly
import OscInt.Front.HypercubicFubini

/-!
# Batch HC: the final theorems

Route `docs/proof-HC.md`; assembly `OscInt/Front/HypercubicAssembly.lean`; part `OscInt/Front/HypercubicFubini.lean`.
The rate and the factorisation are classical (Stefanov–Kevrekidis 2005, `docs/prior_art.md`); the explicit constant
comes from T0E′.
-/

namespace OscInt.API

open OscInt.Statements OscInt.HypercubicAux

/-- **TdF** (`HypercubicKernelFactorStatement`): `K_d(t, x) = ∏_j I(t, x_j)` on `ℤ^d`, every `d`. Fubini over `Fin d`. -/
theorem hypercubicKernelFactor : HypercubicKernelFactorStatement := tdF_of hcFubiniFacts

/-- **TdE′** (`HypercubicCubeRootStatement`): `|K_d(t, x)| ≤ (8(1 + √7)/3)^d t^{−d/3}` for every `d`, `t > 0`,
`x ∈ ℤ^d`: the free lattice Schrödinger group on `ℤ^d` with an explicit dispersive constant (TdF and T0E′). -/
theorem hypercubicCubeRoot : HypercubicCubeRootStatement := tdEp_of hypercubicKernelFactor

end OscInt.API
