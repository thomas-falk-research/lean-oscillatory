/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: the D4 limit along a bounded moving offset, and the lower bound it gives (batch D4U)

Only `import OscInt.API` and Mathlib. The use the batch was made for: a lattice kernel evaluated at sites x_t whose
offset from the moving D4 point, y(t) = x_t − t v, stays bounded but changes with t (rounding to the lattice). Here,
for the generic cubic φ = x³ + 2x²y + 3xy² + 5y³ (disc = −367), a bump amplitude `bumpC δ` (value 1 at 0) and the
offsets y(t) = (fract t, −fract 2t), which jump at every integer and half-integer and stay in the max-norm unit ball:
* `offset_path_limit`: t^{2/3} ∫ e^{i(tφ + y(t)·κ)} A → Γ(1/3)²/(√3 · 367^{1/6}), unconditionally (S4.2O through the
  sanity layer's `offset_sanity`, and the closed form S4.4);
* `offset_path_lower`: hence, for all large t, |∫ e^{i(tφ + y(t)·κ)} A| ≥ (c_C/2) t^{−2/3}, via the sharpness lemma SH;
  this is the shape of a lower bound for the kernel along lattice sites.
-/

open Filter Topology OscInt.Statements OscInt.API OscInt.API.D4UniformSanity OscInt.D4

/-- The offsets `y(t) = (fract t, −fract 2t)` lie in the max-norm unit ball. -/
theorem offsetPath_bound (t : ℝ) : ‖((Int.fract t, -Int.fract (2 * t)) : ℝ × ℝ)‖ ≤ 1 := by
  rw [Prod.norm_def, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _),
    abs_of_nonneg (Int.fract_nonneg _)]
  exact max_le (Int.fract_lt_one _).le (Int.fract_lt_one _).le

/-- The closed form of c_C for the generic cubic (S4.4, `Disc = −367 < 0`). -/
theorem d4Constant_generic :
    d4Constant (1, 2, 3, 5) = Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * (367 : ℝ) ^ ((1 : ℝ) / 6)) := by
  rw [OscInt.d4ConstantClosedForm.2.1 (1, 2, 3, 5) (by norm_num [disc])]
  norm_num [disc]

/-- **Unconditional**: the D4 limit along the moving offsets, with the closed-form constant. -/
theorem offset_path_limit : ∃ δ, ∃ hδ : 0 < δ,
    Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
      oscInt2 (fun κ => t * genCubic 1 2 3 5 κ + lin (Int.fract t, -Int.fract (2 * t)) κ) (bumpC δ hδ)) atTop
      (𝓝 ((Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * (367 : ℝ) ^ ((1 : ℝ) / 6)) : ℝ) : ℂ)) := by
  obtain ⟨δ, hδ, h⟩ := offset_sanity d4LimitOffset
  refine ⟨δ, hδ, ?_⟩
  rw [← d4Constant_generic]
  exact h 1 (fun t => (Int.fract t, -Int.fract (2 * t))) offsetPath_bound

/-- **Unconditional**: the lower bound along the moving offsets, for all large `t`. -/
theorem offset_path_lower : ∃ δ, ∃ hδ : 0 < δ, ∀ᶠ t : ℝ in atTop,
    d4Constant (1, 2, 3, 5) / 2 * t ^ (-((2 : ℝ) / 3)) ≤
      ‖oscInt2 (fun κ => t * genCubic 1 2 3 5 κ + lin (Int.fract t, -Int.fract (2 * t)) κ) (bumpC δ hδ)‖ := by
  obtain ⟨δ, hδ, h⟩ := offset_path_limit
  refine ⟨δ, hδ, ?_⟩
  rw [← d4Constant_generic] at h
  have hpos := (OscInt.d4ConstantPos.2.2 (1, 2, 3, 5) (by norm_num [disc])).2
  have hne : ((d4Constant (1, 2, 3, 5) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have := (sharpness.1 _ ((2 : ℝ) / 3) _ h hne).1
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] using this
