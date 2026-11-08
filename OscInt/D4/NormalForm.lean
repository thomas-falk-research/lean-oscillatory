/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.D4.CubicComp

/-!
# S4.4, part E5: normal forms of binary cubics

`normalForm : OscInt.Blueprint.CubicNormalFormFacts`: a binary cubic `C` with `disc C < 0` becomes
`x(x² + y²) = (1, 0, 1, 0)` and one with `disc C > 0` becomes `xy(x + y) = (0, 1, 1, 0)` after an invertible
linear change of variables. Route `docs/proof-S44.md`, E5 (and its revision, item 7):
1. `C(−z) = −C(z)` and the intermediate value theorem on `[0, π]` give a zero `(cos θ₀, sin θ₀)` of `C`; the rotation
   `(sin θ₀, cos θ₀, −cos θ₀, sin θ₀)` (det 1) kills the `y³` coefficient.
2. `disc (a, b, c, 0) = c²(b² − 4ac) ≠ 0`, so `c ≠ 0`; a shear (det 1) gives `(A, 0, C, 0)`, `disc = −4AC³`.
3. Diagonal scaling with a real cube root `α³ = 1/A` (built from `|·|^{1/3}` of a nonnegative base, sign by hand)
   and `β = (±Cα)^{−1/2}` gives `(1, 0, ±1, 0)` with `± = sign(AC) = −sign(disc)`.
4. `x(x² − y²) ∘ (x + y, x − y) = 4xy(x + y)`, then the scaling `γ³ = 1/4`.
Changes of variables are chained by `cubicComp_cubicComp` (`cubicComp` respects the matrix product `mul`) and
`det2_mul`, both by `ring`; the discriminant invariance is `OscInt.D4.disc_cubicComp` (E4).
-/

namespace OscInt.D4.NormalFormAux

open Set OscInt.Statements OscInt.Blueprint

/-- The matrix product: `lin2 (mul g h) = lin2 g ∘ lin2 h`. -/
def mul (g h : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (g.1 * h.1 + g.2.1 * h.2.2.1, g.1 * h.2.1 + g.2.1 * h.2.2.2,
    g.2.2.1 * h.1 + g.2.2.2 * h.2.2.1, g.2.2.1 * h.2.1 + g.2.2.2 * h.2.2.2)

theorem lin2_mul (g h : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : lin2 (mul g h) z = lin2 g (lin2 h z) := by
  simp only [lin2, mul, Prod.mk.injEq]
  constructor <;> ring

/-- `cubicComp` respects composition: `(C ∘ g) ∘ h = C ∘ (g h)`. -/
theorem cubicComp_cubicComp (q g h : ℝ × ℝ × ℝ × ℝ) :
    cubicComp (cubicComp q g) h = cubicComp q (mul g h) := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨g₁, g₂, g₃, g₄⟩ := g
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [cubicComp, cubicForm, lin2, mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `det2` is multiplicative. -/
theorem det2_mul (g h : ℝ × ℝ × ℝ × ℝ) : det2 (mul g h) = det2 g * det2 h := by
  obtain ⟨g₁, g₂, g₃, g₄⟩ := g
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [det2, mul]
  ring

/-- Every binary cubic vanishes somewhere on the unit circle (`C(−z) = −C(z)` and the IVT on `[0, π]`). -/
theorem exists_circle_zero (q : ℝ × ℝ × ℝ × ℝ) :
    ∃ θ : ℝ, cubicForm q (Real.cos θ, Real.sin θ) = 0 := by
  set f : ℝ → ℝ := fun θ => cubicForm q (Real.cos θ, Real.sin θ) with hf
  have hcont : ContinuousOn f (Icc 0 Real.pi) := by
    apply Continuous.continuousOn
    simp only [hf, cubicForm]
    fun_prop
  have h0 : f 0 = q.1 := by simp [hf, cubicForm]
  have hπ : f Real.pi = -q.1 := by simp [hf, cubicForm]; ring
  rcases le_total 0 q.1 with h | h
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' Real.pi_pos.le hcont
      (show (0 : ℝ) ∈ Icc (f Real.pi) (f 0) by rw [h0, hπ]; constructor <;> linarith)
    exact ⟨θ, hθ⟩
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc Real.pi_pos.le hcont
      (show (0 : ℝ) ∈ Icc (f 0) (f Real.pi) by rw [h0, hπ]; constructor <;> linarith)
    exact ⟨θ, hθ⟩

/-- Rotation taking `(0, 1)` to a zero `(cos θ, sin θ)` of `C`: the `y³` coefficient becomes `0`. -/
theorem rotate (q : ℝ × ℝ × ℝ × ℝ) (θ : ℝ) (hθ : cubicForm q (Real.cos θ, Real.sin θ) = 0) :
    (cubicComp q (Real.sin θ, Real.cos θ, -Real.cos θ, Real.sin θ)).2.2.2 = 0 ∧
      det2 (Real.sin θ, Real.cos θ, -Real.cos θ, Real.sin θ) = 1 := by
  refine ⟨?_, ?_⟩
  · simp only [cubicComp, lin2, mul_zero, mul_one, zero_add]
    exact hθ
  · simp only [det2]
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The shear `(x, y) ↦ (x, y − (b/2c) x)` removes the `x²y` term of `(a, b, c, 0)`. -/
theorem shear (a b c : ℝ) (hc : c ≠ 0) :
    cubicComp (a, b, c, 0) (1, 0, -b / (2 * c), 1) = (a - b ^ 2 / (4 * c), 0, c, 0) ∧
      det2 (1, 0, -b / (2 * c), 1) = 1 := by
  refine ⟨?_, by simp [det2]⟩
  simp only [cubicComp, cubicForm, lin2, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The diagonal scaling `(x, y) ↦ (αx, βy)` on `(A, 0, C, 0)`. -/
theorem scale (A C α β : ℝ) :
    cubicComp (A, 0, C, 0) (α, 0, 0, β) = (A * α ^ 3, 0, C * α * β ^ 2, 0) ∧
      det2 (α, 0, 0, β) = α * β := by
  refine ⟨?_, by simp [det2]⟩
  simp only [cubicComp, cubicForm, lin2, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `x(x² − y²) ∘ (x + y, x − y) = 4xy(x + y)`. -/
theorem hyperbolic : cubicComp (1, 0, -1, 0) (1, 1, 1, -1) = (0, 4, 4, 0) ∧
    det2 (1, 1, 1, -1) = -2 := by
  refine ⟨?_, by simp [det2]; norm_num⟩
  simp only [cubicComp, cubicForm, lin2, Prod.mk.injEq]
  norm_num

/-- Real cube roots. -/
theorem exists_cube_eq (x : ℝ) : ∃ α : ℝ, α ^ 3 = x := by
  have key : ∀ y : ℝ, 0 ≤ y → (y ^ ((1 : ℝ) / 3)) ^ 3 = y := fun y hy => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  rcases le_total 0 x with h | h
  · exact ⟨_, key x h⟩
  · refine ⟨-((-x) ^ ((1 : ℝ) / 3)), ?_⟩
    rw [neg_pow, key (-x) (by linarith)]; ring


/-- After a rotation and a shear (both of determinant `1`), `C` becomes `(A, 0, C, 0)` with `C ≠ 0`;
the discriminant is `−4AC³`. -/
theorem reduce (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    ∃ g A C, det2 g = 1 ∧ cubicComp q g = (A, 0, C, 0) ∧ C ≠ 0 ∧ disc q = -4 * A * C ^ 3 := by
  obtain ⟨θ, hθ⟩ := exists_circle_zero q
  obtain ⟨h1, hd1⟩ := rotate q θ hθ
  set g₁ : ℝ × ℝ × ℝ × ℝ := (Real.sin θ, Real.cos θ, -Real.cos θ, Real.sin θ)
  have hdisc1 : disc (cubicComp q g₁) = disc q := by rw [disc_cubicComp, hd1]; ring
  rcases hq1 : cubicComp q g₁ with ⟨a, b, c, d⟩
  rw [hq1] at h1
  simp only at h1
  subst h1
  have hc : c ≠ 0 := by
    rintro rfl
    apply hq
    rw [← hdisc1, hq1]
    simp [disc]
  obtain ⟨h2, hd2⟩ := shear a b c hc
  refine ⟨mul g₁ (1, 0, -b / (2 * c), 1), a - b ^ 2 / (4 * c), c, ?_, ?_, hc, ?_⟩
  · rw [det2_mul, hd1, hd2]; ring
  · rw [← cubicComp_cubicComp, hq1, h2]
  · rw [← hdisc1, hq1]
    simp only [disc]
    field_simp
    ring

/-- Scaling `(A, 0, C, 0)` to `(1, 0, ε, 0)` when `ε = ±1` has the sign of `AC`. -/
theorem scale_to (A C ε : ℝ) (hA : A ≠ 0) (hε : 0 < ε * (A * C)) (hε2 : ε ^ 2 = 1) :
    ∃ k, det2 k ≠ 0 ∧ cubicComp (A, 0, C, 0) k = (1, 0, ε, 0) := by
  obtain ⟨α, hα⟩ := exists_cube_eq (1 / A)
  have hα' : A * α ^ 3 = 1 := by rw [hα]; field_simp
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα'
  have hCα : ε * (C * α) = ε * (A * C) * α ^ 4 := by linear_combination (-(ε * C * α)) * hα'
  have hpos : 0 < ε * (C * α) := by rw [hCα]; positivity
  set β := 1 / Real.sqrt (ε * (C * α))
  have hsq : Real.sqrt (ε * (C * α)) ^ 2 = ε * (C * α) := Real.sq_sqrt hpos.le
  have hs0 : Real.sqrt (ε * (C * α)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hβ0 : β ≠ 0 := by simp [β, hs0]
  have hβ : C * α * β ^ 2 = ε := by
    have hCa0 : ε * (C * α) ≠ 0 := hpos.ne'
    simp only [β, div_pow, one_pow, hsq]
    rw [mul_one_div, div_eq_iff hCa0]
    linear_combination (-(C * α)) * hε2
  obtain ⟨hk, hdk⟩ := scale A C α β
  exact ⟨(α, 0, 0, β), by rw [hdk]; exact mul_ne_zero hα0 hβ0, by rw [hk, hα', hβ]⟩

/-- The scaling `γ³ = 1/4` takes `4xy(x + y)` to `xy(x + y)`. -/
theorem scale_four : ∃ k, det2 k ≠ 0 ∧ cubicComp (0, 4, 4, 0) k = (0, 1, 1, 0) := by
  obtain ⟨γ, hγ⟩ := exists_cube_eq (1 / 4)
  have hγ0 : γ ≠ 0 := by rintro rfl; norm_num at hγ
  refine ⟨(γ, 0, 0, γ), by simp [det2, hγ0], ?_⟩
  simp only [cubicComp, cubicForm, lin2, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ring
  · linear_combination (4 : ℝ) * hγ
  · linear_combination (4 : ℝ) * hγ
  · ring

end OscInt.D4.NormalFormAux

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint NormalFormAux

/-- **E5** Normal forms of binary cubics with `disc ≠ 0`. -/
theorem normalForm : CubicNormalFormFacts := by
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, A, C, hg, hgq, hC, hd⟩ := reduce q hq.ne
    have hAC : 0 < A * C := by
      have : 0 < A * C * C ^ 2 := by nlinarith
      exact pos_of_mul_pos_left this (by positivity)
    have hA : A ≠ 0 := by rintro rfl; simp at hAC
    obtain ⟨k, hk, hkq⟩ := scale_to A C 1 hA (by linarith) (by norm_num)
    exact ⟨mul g k, by rw [det2_mul, hg]; simpa using hk,
      by rw [← cubicComp_cubicComp, hgq, hkq]⟩
  · obtain ⟨g, A, C, hg, hgq, hC, hd⟩ := reduce q hq.ne'
    have hAC : A * C < 0 := by
      have : A * C * C ^ 2 < 0 := by nlinarith
      exact neg_of_mul_neg_left this (by positivity)
    have hA : A ≠ 0 := by rintro rfl; simp at hAC
    obtain ⟨k, hk, hkq⟩ := scale_to A C (-1) hA (by linarith) (by norm_num)
    obtain ⟨hH, hdH⟩ := hyperbolic
    obtain ⟨k', hk', hk'q⟩ := scale_four
    refine ⟨mul (mul (mul g k) (1, 1, 1, -1)) k', ?_, ?_⟩
    · rw [det2_mul, det2_mul, det2_mul, hg, hdH]
      exact mul_ne_zero (mul_ne_zero (by simpa using hk) (by norm_num)) hk'
    · rw [← cubicComp_cubicComp, ← cubicComp_cubicComp, ← cubicComp_cubicComp, hgq, hkq, hH, hk'q]

end OscInt.D4
