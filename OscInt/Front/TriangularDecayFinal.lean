/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriangularDecayAssembly
import OscInt.Front.TriangularDecayMonomial
import OscInt.Front.TriangularDecayLocal
import OscInt.Front.TriangularDecayCore
import OscInt.Front.TriangularDecayNormalized
import OscInt.Front.TriangularDecayChart
import OscInt.Front.TriangularDecayFourier
import OscInt.Front.TriangularDecayTorus
import OscInt.Cusp.Transverse

/-!
# Batch K2: the final theorems under the challenge names

`docs/proof-K2.md`. Each theorem is an assembly of `OscInt/Front/TriangularDecayAssembly.lean` or
`OscInt/Front/TriangularDecayLocal.lean` applied to the proved parts. The statement-type checks are in
`StatementTypes.lean`; the comparator is `comparator-K2.json`.
-/

namespace OscInt.API

open OscInt.Statements

/-- **K2-MA** Monomial asymptotics with an explicit remainder. -/
theorem monomialAsymptotic : MonomialAsymptoticStatement :=
  OscInt.K2.monomialAsymptotic_of OscInt.K2.monomialPositivity OscInt.K2.monomialTail

/-- **K2-ML** The monomial lower bound. -/
theorem monomialLower : MonomialLowerStatement := OscInt.K2.monomialLower_of monomialAsymptotic

/-- **K2-L** The local bound of order m, uniform over every linear term. -/
theorem reducedOrderBound : ReducedOrderBoundStatement :=
  OscInt.K2.reducedOrderBound_of OscInt.K2.coreEstimateM OscInt.K2.normalizedDataM OscInt.K2.chart
    OscInt.Cusp.transverseNonStat

/-- **K2-F** Fourier localisation from a smooth bump to lattice sites. -/
theorem torusLocalization : TorusLocalizationStatement :=
  OscInt.K2.torusLocalization_of OscInt.K2.fourierDecay OscInt.K2.torusExpansion

end OscInt.API
