/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Hypercubic

/-! # Blueprint for batch HC (TdF, TdE′): intermediate propositions, definitions only

Route: `docs/proof-HC.md`. One part; the assembly `OscInt/Front/HypercubicAssembly.lean` proves the statements from it
and from the proved T0E′. -/

namespace OscInt.Blueprint.Hypercubic

open OscInt.Statements

/-- **P-fubini** The integral over the box `[−π, π]^d` of a product of one-variable continuous functions is the
product of their integrals over `[−π, π]`. -/
def HCFubiniFacts : Prop :=
  ∀ (d : ℕ) (f : Fin d → ℝ → ℂ), (∀ j, Continuous (f j)) →
    ∫ k in hypercubeBox d, ∏ j, f j (k j) = ∏ j, ∫ x in (-Real.pi)..Real.pi, f j x

end OscInt.Blueprint.Hypercubic
