/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.KusminLandau

/-! # Blueprint for batch KL (KL-D, KL-C, KL-F): intermediate propositions, definitions only

Route: `docs/proof-KL.md`. Two parts; the assembly `OscInt/Front/KusminLandauAssembly.lean` proves the three
statements from them. -/

namespace OscInt.Blueprint.KusminLandau

open OscInt.Statements

/-- **K-core** Landau's inequality on differences when the integer `k` is `0`: differences in `[λ, 1 − λ]`,
monotone, give `|Σ_{n ≤ N} e(c_n)| ≤ cot(πλ/2)` (summation by parts with the weights `1/(e(d_n) − 1)`). -/
def KLCoreFacts : Prop :=
  ∀ (c : ℕ → ℝ) (N : ℕ) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 → DiffsMonotoneIn c N 0 lam →
    ‖expSum c N‖ ≤ Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2)

/-- **K-deriv** The derivative form follows from the form on differences (mean value theorem on each unit
interval). -/
def KLDerivFacts : Prop := KusminLandauStatement → KusminLandauDerivStatement

end OscInt.Blueprint.KusminLandau
