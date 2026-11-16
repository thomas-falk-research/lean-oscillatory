/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.KusminLandauAssembly
import OscInt.Front.KusminLandauCore
import OscInt.Front.KusminLandauDeriv

/-!
# Batch KL: the final theorems

Route `docs/proof-KL.md` (refereed; revision section); assembly `OscInt/Front/KusminLandauAssembly.lean`; parts
`OscInt/Front/KusminLandauCore.lean` (Landau's inequality on differences with `k = 0`, by summation by parts) and
`OscInt/Front/KusminLandauDeriv.lean` (the derivative form, by the mean value theorem). The inequality is classical
(Kuzmin 1927; Landau 1928, with the sharp bound `cot(πλ/2)`); it was formalised before with the weaker constant
`1/λ` (`docs/prior_art.md`). The constant `2/π` of KL-C is the one a published lemma got wrong (`docs/statements.md`,
batch KL, "Why").
-/

namespace OscInt.API

open OscInt.Statements OscInt.KusminLandauAux

/-- **KL-D** (`KusminLandauStatement`): if the differences of `c_0, …, c_N` are monotone and lie in
`[k + λ, k + 1 − λ]` for an integer `k` and `0 < λ ≤ 1/2`, then `|Σ_{n ≤ N} e^{2πi c_n}| ≤ cot(πλ/2)` (Landau's sharp
form of the Kusmin–Landau inequality). -/
theorem kusminLandau : KusminLandauStatement := kusminLandau_of klCoreFacts

/-- **KL-C** (`KusminLandauTwoOverPiStatement`): under the same hypotheses, `|Σ_{n ≤ N} e^{2πi c_n}| ≤ 2/(πλ)`. -/
theorem kusminLandauTwoOverPi : KusminLandauTwoOverPiStatement := kusminLandauTwoOverPi_of kusminLandau

/-- **KL-F** (`KusminLandauDerivStatement`): the textbook form. For `f` continuous on `[a, b]` with a monotone
derivative on `(a, b)` taking values in `[k + λ, k + 1 − λ]`, `|Σ_{a ≤ n ≤ b} e^{2πi f(n)}| ≤ cot(πλ/2)`. -/
theorem kusminLandauDeriv : KusminLandauDerivStatement := kusminLandauDeriv_of klDerivFacts kusminLandau

end OscInt.API
