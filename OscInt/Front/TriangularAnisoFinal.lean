/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import OscInt.Front.TriAssembly
import OscInt.Front.TriQuartic
import OscInt.Front.TriAlg
import OscInt.Front.ReducedBridge
import OscInt.Front.TriWitness

/-!
# Batch TRI: the final theorems

Route `docs/proof-TRI.md` (sections 0 to 9; read by one route referee, an AI agent of the lead's model family,
`review/2026-11-27-TRI-route-referee-answers.md`). Assembly `OscInt/Front/TriAssembly.lean`. Parts:
- `OscInt/Front/TriDeriv.lean`: explicit derivatives of `triPhase`;
- `OscInt/Front/TriQuartic.lean`: TRI-Q;
- `OscInt/Front/TriAlg.lean`: the algebraic classification, with the lemma that no A4 point lies off the symmetry
  line;
- `OscInt/Front/ReducedBridge.lean`: the bridge from a reduced curve to the cubic and the quartic invariant, for any
  smooth phase;
- `OscInt/Front/TriWitness.lean`: the A5 points and their sextic.

The mathematics is an external derivation (another model family), checked by the lead and by referees of the lead's
family (`review/2026-11-26-A5-handoff-answers.md`). The classification for general `α` and the exceptional coupling
were not found in the literature searched (`review/2026-11-26-A5-handoff-answers.md`, section 5). Nothing here is
claimed as new mathematics.
-/

namespace OscInt.API

open OscInt.Statements

/-- **TRI-K** (`TriClassificationStatement`): for `α ≠ 0`, every point of `cos k₁ + cos k₂ + α cos(k₁ + k₂)` is of
type A1 or A2, A3 or A5. -/
theorem triClassification : TriClassificationStatement :=
  TriAssembly.triClassification_of TriAlg.algClassify TriWitness.witA5

/-- **TRI-X** (`TriA5LocusStatement`): A5 points occur only for `|α| = 1/(2√2)`, at `(θ, −θ)` and `(−θ, θ)` modulo
`2π`, `θ = arccos(−2α)`. -/
theorem triA5Locus : TriA5LocusStatement :=
  TriAssembly.triA5Locus_of ReducedBridge.bridge TriAlg.algA5 TriAlg.algZero TriDeriv.triPhase_smooth

/-- **TRI-W** (`TriA5WitnessStatement`): for `|α| = 1/(2√2)` both points are A5, and every reduced curve at
`(θ, −θ)` gives the reduced sixth derivative `−60√2 · sign α`. -/
theorem triA5Witness : TriA5WitnessStatement :=
  TriAssembly.triA5Witness_of TriWitness.witA5 TriWitness.witSextic

/-- **TRI-Q** (`TriQuarticStatement`): the reduced quartics `−12` at `(π/2, π/2)` and `12(8α² − 1)` at `(θ, −θ)`. -/
theorem triQuartic : TriQuarticStatement := TriQuartic.triQuartic_proof

/-- The bite owed by the answers to the blind reviews (`review/2026-11-27-TRI-preproof-answers.md`, A2): the A3 point
`(π/2, π/2)` of `triPhase (1/4)` is not an A5 point. -/
theorem triQuarter_halfPi_not_isA5 : ¬ IsA5Point (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) :=
  TriAssembly.quarter_halfPi_not_isA5_of triA5Locus

end OscInt.API
