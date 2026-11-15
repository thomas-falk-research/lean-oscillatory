/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.D4UniformParts
import OscInt.Front.D4UniformModulation

/-!
# Batch D4U: the final theorems

Route `docs/proof-D4U.md`; interfaces `Blueprint/D4Uniform.lean`. S4.2U and S4.2O at their frozen statement types, from
the three parts (`OscInt/Front/D4UniformParts.lean`: P-radius, P-linear, by the lead;
`OscInt/Front/D4UniformModulation.lean`: P-mod, by a proof agent of the lead) and the assembly
`OscInt/Front/D4UniformAssembly.lean`, which uses the proved S4.1′ (`OscInt.d4BoundNe`) and S4.2 (`OscInt.d4Limit`).

Provenance: the question, a hand proof of the same shape and unelaborated Lean drafts with the same decomposition came
from an external research packet (AI-use disclosure in `docs/statements.md`, batch D4U; record
`review/2026-11-15-D4U-packet-answers.md`). The statements were written fresh by the lead; the route follows the
packet's decomposition; the Lean proofs in this repository are the lead's (assembly, P-radius, P-linear) and the lead's
proof agent's (P-mod).
-/

namespace OscInt.API

open OscInt.Statements OscInt.D4UniformAux

/-- **S4.2U** (`D4LimitUniformStatement`): at a D4 critical point (C⁴ phase, `φ(0) = 0`, `Dφ(0) = 0`, `D²φ(0) = 0`,
`disc ≠ 0`) the limit `t^{2/3} ∫ e^{itφ} A → c_C A(0)` of S4.2 holds uniformly over every family of amplitudes that
is C²-totally bounded on `B̄(0, δ)`, `δ` depending on `φ` only. The classical compact-family form of the stationary
phase limit (uniform estimate on differences plus a finite net). -/
theorem d4LimitUniform : D4LimitUniformStatement :=
  d4LimitUniform_of commonRadius linear

/-- **S4.2O** (`D4LimitOffsetStatement`): the D4 limit with a bounded linear term,
`t^{2/3} ∫ e^{i(tφ + y·κ)} A → c_C A(0)` uniformly for `‖y‖ ≤ R` (max norm), for each fixed `R` (the threshold depends
on `R`), for every C² amplitude supported in `B̄(0, δ)`. -/
theorem d4LimitOffset : D4LimitOffsetStatement :=
  d4LimitOffset_of d4LimitUniform modulation

end OscInt.API
