/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.D4Limit
import OscInt.D4.Sanity

/-!
# S4.1′, S4.2 sanity checks (generic witnesses, lesson 17)

* `cubicForm_cubicCoeffs_genCubic`: for every binary cubic, `cubicForm (cubicCoeffs φ)` is `φ` itself, so the
  constant `d4Constant (cubicCoeffs φ)` is built from the true cubic part (all four coefficients, any values).
* `sanity_D4Limit_hyps_elliptic`: the elliptic umbilic `x³ − 3xy²` (`disc = 108 > 0`) meets the hypotheses of S4.1′
  and S4.2, which the `disc < 0` statement S4.1 excludes (`sanity_D4_elliptic_excluded`); so the widening has
  content.
-/

namespace OscInt.D4

open OscInt.Statements

theorem cubicForm_cubicCoeffs_genCubic (a b c d : ℝ) :
    cubicForm (cubicCoeffs (genCubic a b c d)) = genCubic a b c d := by
  rw [cubicCoeffs_genCubic]; funext z; simp only [cubicForm, genCubic]

theorem sanity_D4Limit_hyps_elliptic :
    ContDiff ℝ 4 (genCubic 1 0 (-3) 0) ∧ genCubic 1 0 (-3) 0 0 = 0 ∧ fderiv ℝ (genCubic 1 0 (-3) 0) 0 = 0 ∧
      (∀ v w, dd (genCubic 1 0 (-3) 0) 0 v w = 0) ∧ disc (cubicCoeffs (genCubic 1 0 (-3) 0)) = 108 ∧
      disc (cubicCoeffs (genCubic 1 0 (-3) 0)) ≠ 0 := by
  have hd : disc (cubicCoeffs (genCubic 1 0 (-3) 0)) = 108 := by
    rw [cubicCoeffs_genCubic]; simp only [disc]; norm_num
  refine ⟨genCubic_contDiff _ _ _ _, by simp [genCubic], ?_, dd_genCubic_zero _ _ _ _, hd, by rw [hd]; norm_num⟩
  ext <;> simp [fd_genCubic]

end OscInt.D4
