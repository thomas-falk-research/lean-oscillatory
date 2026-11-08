/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.D4.CubicComp

/-!
# S4.4 assembly against the blueprint interfaces

`D4ConstantClosedFormStatement` from E1, E2, E3, E5, E6c, E7 (`Blueprint/D4ClosedForm.lean`; route
`docs/proof-S44.md`). E4 (`OscInt/D4/CubicComp.lean`) is proved by `ring`.
For `disc q < 0` (resp. `> 0`) E5 gives `g` with `C ∘ g = N` for the normal form `N = x(x² + y²)` (resp.
`xy(x + y)`); E3 gives `J(C) = |det g| J(N)`, E2 and E6c give `J(N)`, E4 gives `|disc C|^{1/6} = |disc N|^{1/6}/|det g|`,
and E1 (with E7 for `disc < 0`) finishes.
-/

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- **S4.4** from the interfaces. -/
theorem d4ConstantClosedForm_of (h1 : CosMomentValueFacts) (h2 : AngularLineFacts) (h3 : CovarianceFacts)
    (h5 : CubicNormalFormFacts) (h6 : LineMomentValuesFacts) (h7 : GammaSixthFacts) :
    D4ConstantClosedFormStatement := by
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  -- `J(C) = |det g| · J(N)` whenever `C ∘ g = N`
  have hJ : ∀ q g N : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 → det2 g ≠ 0 → cubicComp q g = N →
      angularMoment q = |det2 g| * angularMoment N := by
    intro q g N hq hg hN
    have := h3 q g hq hg
    rw [hN] at this
    rw [this]; field_simp [abs_ne_zero.mpr hg]
  refine ⟨h1, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hN⟩ := h5.1 q hq
    have hdN : disc ((1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) = -4 := by norm_num [disc]
    have hJq := hJ q g _ hq.ne hg hN
    rw [h2 (1, 0, 1, 0) (by rw [hdN]; norm_num), h6.1] at hJq
    have hD := abs_disc_rpow_mul q g
    rw [hN, hdN] at hD
    have h4 : |(-4 : ℝ)| ^ ((1 : ℝ) / 6) = 2 ^ ((1 : ℝ) / 3) := by
      rw [show |(-4 : ℝ)| = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h4] at hD
    have h2pos : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hdet : 0 < |det2 g| := abs_pos.mpr hg
    have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hs3p : 0 < Real.sqrt 3 := by positivity
    have hDq : 0 < |disc q| ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (abs_pos.mpr hq.ne) _
    unfold d4Constant
    rw [h1, hJq]
    rw [eq_div_iff (by positivity)]
    have h7' : Real.sqrt Real.pi * Real.Gamma (1 / 6) * 2 ^ ((1 : ℝ) / 3) =
        Real.sqrt 3 * Real.Gamma (1 / 3) ^ 2 := by
      rw [h7]; field_simp
    calc Real.Gamma (2 / 3) / 2 *
          (|det2 g| * (2 * (Real.sqrt Real.pi * Real.Gamma (1 / 6) / Real.Gamma (2 / 3)))) / 3 *
          (Real.sqrt 3 * |disc q| ^ ((1 : ℝ) / 6))
        = Real.sqrt Real.pi * Real.Gamma (1 / 6) * (|disc q| ^ ((1 : ℝ) / 6) * |det2 g|) *
            Real.sqrt 3 / 3 := by field_simp
      _ = Real.sqrt Real.pi * Real.Gamma (1 / 6) * 2 ^ ((1 : ℝ) / 3) * Real.sqrt 3 / 3 := by rw [hD]
      _ = Real.Gamma (1 / 3) ^ 2 := by
        rw [h7']; linear_combination (Real.Gamma (1 / 3) ^ 2 / 3) * hs3
  · obtain ⟨g, hg, hN⟩ := h5.2 q hq
    have hdN : disc ((0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ)) = 1 := by norm_num [disc]
    have hJq := hJ q g _ hq.ne' hg hN
    rw [h2 (0, 1, 1, 0) (by rw [hdN]; norm_num), h6.2] at hJq
    have hD := abs_disc_rpow_mul q g
    rw [hN, hdN, abs_one, Real.one_rpow, abs_of_pos hq] at hD
    have hDq : 0 < disc q ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hq _
    unfold d4Constant
    rw [h1, hJq, eq_div_iff hDq.ne']
    calc Real.Gamma (2 / 3) / 2 *
          (|det2 g| * (2 * (3 * Real.Gamma (1 / 3) ^ 2 / Real.Gamma (2 / 3)))) / 3 * disc q ^ ((1 : ℝ) / 6)
        = Real.Gamma (1 / 3) ^ 2 * (disc q ^ ((1 : ℝ) / 6) * |det2 g|) := by field_simp
      _ = Real.Gamma (1 / 3) ^ 2 := by rw [hD, mul_one]

end OscInt.D4
