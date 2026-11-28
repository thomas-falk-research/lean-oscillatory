/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.TorusLocalizationC2Assembly
import OscInt.Front.TorusLocalizationC2Ibp
import OscInt.Front.TorusLocalizationC2Fourier

/-!
# Batch LOC2: the final theorem

Route `docs/proof-LOC2.md`; blueprint `Blueprint/TorusLocalizationC2.lean`; the lead's assembly
`OscInt/Front/TorusLocalizationC2Assembly.lean` (as K2's `torusLocalization_of`, with nearest-integer offsets).
Parts by proof agents: `TorusLocalizationC2Ibp.lean` (Q1 integration by parts, Q5 the Laplacian of `χ e^{iδ·k}`) and
`TorusLocalizationC2Fourier.lean` (Q2 Bessel through Mathlib's Parseval on the torus, Q3 the shell sum, Q4 the
combination, Q6 the expansion for a continuous cutoff).
-/

namespace OscInt.API

open OscInt.Statements OscInt.LOC2Aux

/-- **K2-FQ** Fourier localisation for a `C²` cutoff with the explicit constant `locConstC2 χ`. -/
theorem torusLocalizationC2 : TorusLocalizationC2Statement :=
  torusLocalizationC2_of (locCombine locIbp locBessel locShell locLaplace) locExpansion

end OscInt.API
