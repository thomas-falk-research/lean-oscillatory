/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/


import OscInt.Cusp.Assembly
import OscInt.Cusp.VdCk
import OscInt.Cusp.Core4
import OscInt.Cusp.Implicit4
import OscInt.Cusp.Transverse
import OscInt.Cusp.Normalize

/-!
# Batch A3: the frozen public conclusions

The part proofs provide the exact interfaces consumed by the existing assembly.
Syntactic statement-type assertions are appended to `StatementTypes.lean`, which owns
the existing assertion command and imports this module through `OscInt`.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`.
-/

namespace OscInt

open OscInt.Statements

/-- The explicit derivative-chain bound, with its frozen coefficient and arbitrary linear term. -/
theorem vdCk : VdCkStatement := Cusp.vdcK

/-- The uniform cusp estimate obtained by supplying the four assembly interfaces. -/
theorem cuspBoundGen : CuspBoundGenStatement :=
  Cusp.cuspBoundGen_of Cusp.coreEstimate4 Cusp.normalizedData4
    Cusp.transverseNonStat Cusp.a3Normalize

/-- The stable case follows by forgetting the extra coupling condition. -/
theorem cuspBound : CuspBoundStatement := Cusp.cuspBound_of_gen cuspBoundGen

end OscInt

namespace OscInt.API

open OscInt.Statements

/-- The exact S1.k name and statement expected by the A3 comparator. -/
theorem vdCk : VdCkStatement := OscInt.vdCk

/-- The exact S5.1′ name and statement expected by the A3 comparator. -/
theorem cuspBoundGen : CuspBoundGenStatement := OscInt.cuspBoundGen

/-- The exact S5.1 name and statement expected by the A3 comparator. -/
theorem cuspBound : CuspBoundStatement := OscInt.cuspBound

end OscInt.API
