/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.FiniteRingAssembly
import OscInt.Front.FiniteRingKernel
import OscInt.Front.FiniteRingCoset
import OscInt.Front.FiniteRingImages
import OscInt.Front.FiniteRingEnergy
import OscInt.Front.FiniteRingChainEnergy
import OscInt.Front.PeriodicAnalyticFinal

/-!
# Batch FR: the final theorems

Route `docs/proof-FR.md` (refereed; "Parts as integrated"); assembly `OscInt/Front/FiniteRingAssembly.lean`; parts
`OscInt/Front/FiniteRingKernel.lean` (FR-K and the evenness of the ring kernel), `OscInt/Front/FiniteRingCoset.lean`
(FR-S, from the Fourier series and the aliasing lemma of batch PA), `OscInt/Front/FiniteRingImages.lean` (the bound
for a sum over images), `OscInt/Front/FiniteRingEnergy.lean` and `OscInt/Front/FiniteRingChainEnergy.lean` (the two
uniqueness arguments, by conservation of the sum of squared moduli). The mathematics is classical: the propagator
of a ring by periodisation of the propagator of the line (method of images), the propagator of an open chain with
identical sites as the odd part of the propagator of a ring of `2(M + 1)` sites, and explicit finite-size bounds
from the light-cone bound LC-1. Nothing here is claimed as new mathematics (`docs/prior_art.md`, batch FR).
-/

namespace OscInt.API

open OscInt.Statements OscInt.FiniteRingAux

/-- **FR-K** (`RingKernelStatement`): for `N ≥ 1` the ring kernel `R_N(t, r)` solves `i ∂_t R + ΔR = 0` in the site
variable, is the unit datum of the ring at `t = 0` and has period `N`. A finite sum of modes. -/
theorem ringKernelSolves : RingKernelStatement := ringKernelStatement_part

/-- **FR-S** (`RingCosetSumStatement`): the ring kernel is the line kernel summed over the coset `r + Nℤ`, with
unconditional convergence (method of images). The Fourier series of `z ↦ e^{i(2t(cos z − 1) + rz)}` at the `N` nodes. -/
theorem ringCosetSum : RingCosetSumStatement := ringCosetSumStatement_part

/-- **FR-P** (`RingFiniteSizeStatement`): `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every
`η > 0`: the ring differs from the line by the images, which LC-1 bounds one by one. -/
theorem ringFiniteSize : RingFiniteSizeStatement :=
  ringFiniteSize_of ringCosetSum latticeKernel1LightCone imageSumFacts

/-- **FR-U** (`RingUniqueStatement`): every solution of period `N` is the ring-kernel sum of its datum over one
period: the kernel is the propagator of the ring. FR-K and conservation of the sum of squared moduli. -/
theorem ringUnique : RingUniqueStatement := ringUnique_of ringKernelSolves ringDatumFacts ringEnergyFacts

/-- **FC-K** (`ChainKernelStatement`): the chain kernel `C_M(t; x, y) = R_{2(M+1)}(t, x − y) − R_{2(M+1)}(t, x + y)`
solves the equation, vanishes at the walls `0` and `M + 1` and is the unit datum on the sites `1, …, M`. -/
theorem chainKernelSolves : ChainKernelStatement := chainKernel_of ringKernelSolves ringEvenFacts

/-- **FC-U** (`ChainUniqueStatement`): every solution on the open chain with Dirichlet walls is the chain-kernel sum
of its datum: the kernel is the propagator of the chain of `M` identical sites. -/
theorem chainUnique : ChainUniqueStatement := chainUnique_of chainKernelSolves chainEnergyFacts

/-- **FC-P** (`ChainFiniteSizeStatement`): the chain kernel differs from the line kernel `G(t, x − y)` by at most
`e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`, for every `η > 0`. -/
theorem chainFiniteSize : ChainFiniteSizeStatement := chainFiniteSize_of ringFiniteSize latticeKernel1LightCone

end OscInt.API
