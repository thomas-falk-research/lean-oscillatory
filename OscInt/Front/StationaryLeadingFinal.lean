/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.StationaryLeadingAssembly
import OscInt.Front.StationaryLeadingBounds
import OscInt.Front.StationaryLeadingFresnelTail
import OscInt.Front.StationaryLeadingFresnelValue
import OscInt.Front.StationaryLeadingFresnel
import OscInt.Front.StationaryLeadingFresnelBound
import OscInt.Front.StationaryLeadingKernel
import OscInt.Front.StationaryLeadingLine
import OscInt.Front.StationaryLeadingBump

/-!
# Batch SPL: the final theorems

Route `docs/proof-SPL.md` (sections 10 and 11; read by one route referee, an AI agent of the lead's model family;
"Parts as integrated"). Assembly `OscInt/Front/StationaryLeadingAssembly.lean` (SPL-I from the identity at `λ = 1`
by scaling) and `OscInt/Front/StationaryLeadingBounds.lean` (SPL-S, SPL-K, SPL-A from SPL-I). Parts:
`OscInt/Front/StationaryLeadingFresnelTail.lean` (the Fresnel primitive has a limit, approached at rate `2/x`),
`OscInt/Front/StationaryLeadingFresnelValue.lean` (the limit is `√π (1 + i)/2`, by Abel summation from the complex
Gaussian integral), `OscInt/Front/StationaryLeadingFresnel.lean` (P-fresnel from the two),
`OscInt/Front/StationaryLeadingFresnelBound.lean` (`|F| ≤ 7/4` from VC2-S and VC2-N),
`OscInt/Front/StationaryLeadingKernel.lean` (the kernel: its primitives, oddness, continuity, `|κ| ≤ 7/8`),
`OscInt/Front/StationaryLeadingLine.lean` (three integrations by parts on a half-line and a reflection) and
`OscInt/Front/StationaryLeadingBump.lean` (mollified point masses for the third derivative).
The identity is classical (the two-sided case of Erdélyi's remainder representation after three integrations by
parts; `docs/prior_art.md`, gate of 2026-11-19). Nothing here is claimed as new mathematics.
-/

namespace OscInt.API

open OscInt.Statements OscInt.Blueprint.StationaryLeading OscInt.StationaryLeadingAux

/-- **SPL-I** (`StationaryLeadingIdentityStatement`): for an amplitude `g` with three derivatives, all integrable, and
`λ > 0`, the remainder `R(g, λ) = ∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}` of the stationary-phase leading term
equals `−i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt`, with the explicit kernel `κ = splKernel` (cf. A. Erdélyi, *Asymptotic
Expansions*, 1956, section 2.8, for one-sided integrals). -/
theorem stationaryLeadingIdentity : StationaryLeadingIdentityStatement :=
  stationaryLeadingIdentity_of (splLineFacts_of (splKernelFacts_of
    (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)
    (splFresnelBoundFacts_of (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts))))

/-- **SPL-S** (`StationaryLeadingStatement`): `|R(g, λ)| ≤ |κ(τ)| ‖g‴‖₁ λ^{−3/2}` for some `τ ≥ 0`. -/
theorem stationaryLeading : StationaryLeadingStatement :=
  stationaryLeading_of stationaryLeadingIdentity (splKernelFacts_of
    (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)
    (splFresnelBoundFacts_of (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)))

/-- **SPL-K** (`StationaryLeadingSevenEighthsStatement`): `|R(g, λ)| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}` for every `λ > 0`: the
leading term of the method of stationary phase for the phase `u²/2`, with an explicit bound of the remainder. -/
theorem stationaryLeadingSevenEighths : StationaryLeadingSevenEighthsStatement :=
  stationaryLeadingSevenEighths_of stationaryLeadingIdentity (splKernelFacts_of
    (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)
    (splFresnelBoundFacts_of (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)))

/-- **SPL-A** (`StationaryLeadingAttainedStatement`): for every `τ ≥ 0` and `ε > 0` a smooth compactly supported
amplitude, not identically zero, has `|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g‴‖₁`; so no constant below `sup |κ|` is true in
SPL-K. -/
theorem stationaryLeadingAttained : StationaryLeadingAttainedStatement :=
  stationaryLeadingAttained_of stationaryLeadingIdentity (splKernelFacts_of
    (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts)
    (splFresnelBoundFacts_of (splFresnelFacts_of splFresnelTailFacts splFresnelValueFacts))) splBumpFacts

end OscInt.API
