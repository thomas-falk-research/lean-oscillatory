/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeGroupAssembly
import OscInt.Front.LatticeGroupOp
import OscInt.Front.LatticeGroupExp
import OscInt.Front.LatticeGroupUnique
import OscInt.Front.LatticeGroupConv
import OscInt.Front.LatticeGroupBound
import OscInt.Front.LatticeGroupEnvelope

/-!
# Batch LS: the final theorems

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. LS-E, LS-K, LS-D and LS-D′ at their frozen statement types, from the nine parts and the compiled assembly
`OscInt/Front/LatticeGroupAssembly.lean`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.API

open OscInt.Statements OscInt.LatticeGroupAux OscInt.LatticeConvAux
open OscInt.LatticeKernelBoundAux OscInt.LatticeEnvelopeAux

theorem latticeSchrodingerExists : LatticeSchrodingerExistsStatement :=
  lsE_of lapOpFacts expSolutionFacts

theorem latticeSchrodingerKernel : LatticeSchrodingerKernelStatement :=
  lsK_of lapOpFacts expSolutionFacts uniqueFacts kernelConvFacts

theorem latticeSchrodingerDispersive : LatticeSchrodingerDispersiveStatement :=
  lsD_of latticeSchrodingerKernel kernelBoundFacts

theorem latticeSchrodingerDecay : LatticeSchrodingerDecayStatement :=
  lsDp_of latticeSchrodingerDispersive envelopeFacts

end OscInt.API
