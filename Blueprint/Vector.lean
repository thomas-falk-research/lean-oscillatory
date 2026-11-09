/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Vector

/-! # Blueprint for batch VT (route `docs/proof-VT.md`): the duality transfer. Definitions only. -/

namespace OscInt.Blueprint

/-- **P-transfer** A bound `B M` for every scalar amplitude `(2, K, M)` against the phase `e^{iθ}` (`θ` continuous on an
open `U ⊇ K`, `K` compact) holds for every `E`-valued amplitude `(2, K, M)`, `E` a complex Banach space. -/
def VecTransferFacts : Prop :=
  ∀ (K U : Set (ℝ × ℝ)) (θ : ℝ × ℝ → ℝ) (B : ℝ → ℝ), IsCompact K → IsOpen U → K ⊆ U → ContinuousOn θ U →
    (∀ (A : ℝ × ℝ → ℂ) (M : ℝ), ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(θ k) * Complex.I) * A k‖ ≤ B M) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (A : ℝ × ℝ → E) (M : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(θ k) * Complex.I) • A k‖ ≤ B M

end OscInt.Blueprint
