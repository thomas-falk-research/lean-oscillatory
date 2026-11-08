/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Convert

/-!
# C5, C6: the discriminant of a binary cubic (route `docs/proof-API2.md`, P-Disc)
-/

namespace OscInt.API

open Filter Topology OscInt.Statements

/-- **C5** -/
theorem disc_eq_cubic_discr : DiscEqCubicDiscrStatement := by
  intro a b c d
  simp [disc, Cubic.discr]

namespace DiscAux

/-- `∂ₓ` of the cubic form (up to the variable names). -/
def cx (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  3 * q.1 * z.1 ^ 2 + 2 * q.2.1 * z.1 * z.2 + q.2.2.1 * z.2 ^ 2

/-- `∂ᵧ` of the cubic form. -/
def cy (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  q.2.1 * z.1 ^ 2 + 2 * q.2.2.1 * z.1 * z.2 + 3 * q.2.2.2 * z.2 ^ 2

theorem hasFDerivAt_cubicForm (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (cubicForm q)
      (cx q z • ContinuousLinearMap.fst ℝ ℝ ℝ + cy q z • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have h := ((((h1.pow 3).const_mul q.1).add (((h1.pow 2).mul h2).const_mul q.2.1)).add
    ((h1.mul (h2.pow 2)).const_mul q.2.2.1)).add ((h2.pow 3).const_mul q.2.2.2)
  convert h using 1
  · funext w; simp only [cubicForm, Pi.add_apply, Pi.mul_apply]; ring
  · ext <;> simp [cx, cy] <;> ring

theorem fderiv_cubicForm_eq_zero_iff (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (cubicForm q) z = 0 ↔ cx q z = 0 ∧ cy q z = 0 := by
  rw [(hasFDerivAt_cubicForm q z).fderiv]
  constructor
  · intro h
    have h1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) h
    have h2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) h
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; simp

/-- Certificates: a common zero of `cx`, `cy` gives `disc · y³ = 0` and `disc · x³ = 0`. -/
theorem disc_mul_eq_zero (q : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) (h1 : cx q z = 0) (h2 : cy q z = 0) :
    disc q * z.2 ^ 3 = 0 ∧ disc q * z.1 ^ 3 = 0 := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨x, y⟩ := z
  simp only [cx, cy] at h1 h2
  simp only [disc]
  constructor
  · linear_combination ((3*a*b*d - 4*a*c^2 + b^2*c)*y + (-2*a*b*c + 2*b^3/3)*x) * h1 +
      ((-9*a^2*d + 5*a*b*c - 4*b^3/3)*y + (6*a^2*c - 2*a*b^2)*x) * h2
  · linear_combination ((6*b*d^2 - 2*c^2*d)*y + (-9*a*d^2 + 5*b*c*d - 4*c^3/3)*x) * h1 +
      ((-2*b*c*d + 2*c^3/3)*y + (3*a*c*d - 4*b^2*d + b*c^2)*x) * h2

/-- Witness: `disc = 0` gives a nonzero common zero of `cx`, `cy`. -/
theorem exists_crit (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q = 0) :
    ∃ z : ℝ × ℝ, z ≠ 0 ∧ cx q z = 0 ∧ cy q z = 0 := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [disc] at hq
  by_cases hg : b ^ 2 - 3 * a * c = 0
  · by_cases ha : a = 0
    · have hb : b = 0 := by subst ha; simpa using hg
      refine ⟨(1, 0), by simp, ?_, ?_⟩ <;> simp [cx, cy, ha, hb]
    · have h3a : (3 * a) ≠ 0 := mul_ne_zero three_ne_zero ha
      have hsq : (27 * a ^ 2 * d - b ^ 3) ^ 2 = 0 := by
        linear_combination (-27 * a ^ 2) * hq +
          (-162 * a ^ 2 * b * d + 36 * a ^ 2 * c ^ 2 + 3 * a * b ^ 2 * c + b ^ 4) * hg
      have hd : 27 * a ^ 2 * d - b ^ 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      set x := -b / (3 * a) with hxdef
      have hx : x * (3 * a) = -b := by rw [hxdef]; field_simp
      refine ⟨(x, 1), by simp, ?_, ?_⟩
      · have key : (3 * a) * cx (a, b, c, d) (x, 1) = 0 := by
          simp only [cx]; linear_combination (3 * a * x + b) * hx - hg
        exact (mul_eq_zero.mp key).resolve_left h3a
      · have key : (3 * a) ^ 2 * cy (a, b, c, d) (x, 1) = 0 := by
          simp only [cy]
          linear_combination (b * (3 * a * x - b) + 6 * a * c) * hx + 2 * b * hg + hd
        exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 h3a)
  · have h2g : 2 * (b ^ 2 - 3 * a * c) ≠ 0 := mul_ne_zero two_ne_zero hg
    set x := (9 * a * d - b * c) / (2 * (b ^ 2 - 3 * a * c)) with hxdef
    have hx : x * (2 * (b ^ 2 - 3 * a * c)) = 9 * a * d - b * c := by
      rw [hxdef]; exact div_mul_cancel₀ _ h2g
    refine ⟨(x, 1), by simp, ?_, ?_⟩
    · have key : (2 * (b ^ 2 - 3 * a * c)) ^ 2 * cx (a, b, c, d) (x, 1) = 0 := by
        simp only [cx]
        linear_combination (3 * a * (x * (2 * (b ^ 2 - 3 * a * c)) + (9 * a * d - b * c)) +
          4 * b * (b ^ 2 - 3 * a * c)) * hx + (-9 * a) * hq
      exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 h2g)
    · have key : (2 * (b ^ 2 - 3 * a * c)) ^ 2 * cy (a, b, c, d) (x, 1) = 0 := by
        simp only [cy]
        linear_combination (b * (x * (2 * (b ^ 2 - 3 * a * c)) + (9 * a * d - b * c)) +
          4 * c * (b ^ 2 - 3 * a * c)) * hx + (-3 * b) * hq
      exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 h2g)

theorem cx_smul (q : ℝ × ℝ × ℝ × ℝ) (t : ℝ) (z : ℝ × ℝ) : cx q (t • z) = t ^ 2 * cx q z := by
  simp only [cx, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem cy_smul (q : ℝ × ℝ × ℝ × ℝ) (t : ℝ) (z : ℝ × ℝ) : cy q (t • z) = t ^ 2 * cy q z := by
  simp only [cy, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

end DiscAux

open DiscAux in
/-- **C6** -/
theorem disc_ne_zero_iff_isolated : DiscNeZeroIffIsolatedStatement := by
  intro q
  constructor
  · intro hq
    apply eventually_nhdsWithin_of_forall
    intro z hz h0
    rw [fderiv_cubicForm_eq_zero_iff] at h0
    obtain ⟨h1, h2⟩ := disc_mul_eq_zero q z h0.1 h0.2
    have hy : z.2 = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h1).resolve_left hq)
    have hx : z.1 = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h2).resolve_left hq)
    exact hz (Prod.ext hx hy)
  · intro hev hq
    obtain ⟨z₀, hz₀, h1, h2⟩ := exists_crit q hq
    have ht : Tendsto (fun t : ℝ => t • z₀) (𝓝[≠] 0) (𝓝[≠] (0 : ℝ × ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t : ℝ => t • z₀) (𝓝 0) (𝓝 ((0 : ℝ) • z₀)) :=
          (continuous_id.smul continuous_const).tendsto 0
        rw [zero_smul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact smul_ne_zero ht hz₀
    obtain ⟨t, ht'⟩ := (ht.eventually hev).exists
    apply ht'
    rw [fderiv_cubicForm_eq_zero_iff, cx_smul, cy_smul, h1, h2]
    simp

end OscInt.API
