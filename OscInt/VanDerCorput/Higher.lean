/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen, Thomas Falk III
Modified 2026 by Thomas Falk III: derived from roos-j/lean-oscillatory and adapted to OscInt's frozen
statements; the changes are described in this file's module docstring.
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.VanDerCorput

/-!
# P3, P4: second- and third-derivative van der Corput bounds (no amplitude)

`vdc2Plain : SplitFacts → VdC1PlainFacts → VdC2PlainFacts` and
`vdc3Plain : SplitFacts → VdC2PlainFacts → VdC3PlainFacts`.

Proof: P0 (`SplitFacts`) applied to the lower-order derivative gives a point `d` with
`μ |x - d| ≤ |g x|`. The generic lemma `HigherAux.split_bound` cuts `[a, b]` at `d ∓ r`: the middle piece
has length `≤ 2r` and integrand of modulus 1; on each outer piece `|x - d| ≥ r`, so the lower-order bound
applies there. For k = 2 take `r = 1/√μ` (P1 with `ν = √μ`), total `2/√μ + 6/√μ`; for k = 3 take
`r = μ^(-1/3)` (P3 with `μ r = μ^(2/3)`), total `2μ^(-1/3) + 16μ^(-1/3)`.

Route adapted from J. Roos and M. Praveen, `roos-j/lean-oscillatory`, `LeanOscillatory/VanDerCorput.lean`
(`norm_integral_exp_mul_I_le_of_order_ge_two'`, Apache-2.0), after Stein, *Harmonic Analysis*, VIII §1.2.
-/

namespace OscInt.VanDerCorput.HigherAux

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint

/-- `HasDerivOn` restricts to subintervals. -/
lemma hasDerivOn_mono {f f' : ℝ → ℝ} {a b s t : ℝ} (h : HasDerivOn f f' a b) (has : a ≤ s) (htb : t ≤ b) :
    HasDerivOn f f' s t :=
  ⟨h.1.mono (Icc_subset_Icc has htb), fun x hx => h.2 x (Ioo_subset_Ioo has htb hx)⟩

/-- Splitting at `d ∓ r`: if every subinterval `[s, t] ⊆ [a, b]` whose interior stays at distance `≥ r` from
`d` has `‖∫_s^t e^{iφ}‖ ≤ B`, then `‖∫_a^b e^{iφ}‖ ≤ 2r + 2B`. -/
lemma split_bound (φ : ℝ → ℝ) (a b d r B : ℝ) (hab : a ≤ b) (hd : d ∈ Icc a b) (hr : 0 ≤ r)
    (hφ : ContinuousOn φ (Icc a b))
    (hB : ∀ s t, a ≤ s → s ≤ t → t ≤ b → (∀ x ∈ Ioo s t, r ≤ |x - d|) →
      ‖∫ x in s..t, Complex.exp (↑(φ x) * Complex.I)‖ ≤ B) :
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 2 * r + 2 * B := by
  set c₁ := max a (d - r)
  set c₂ := min b (d + r)
  have h1 : a ≤ c₁ := le_max_left _ _
  have h12 : c₁ ≤ c₂ :=
    le_min (max_le hab (by linarith [hd.2])) (max_le (by linarith [hd.1]) (by linarith))
  have h2 : c₂ ≤ b := min_le_left _ _
  have hint : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      IntervalIntegrable (fun x => Complex.exp (↑(φ x) * Complex.I)) volume s t := by
    intro s t has hst htb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hst]
    exact Complex.continuous_exp.comp_continuousOn
      (((continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const).mono (Icc_subset_Icc has htb))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a c₁ le_rfl h1 (h12.trans h2))
    (hint c₁ b h1 (h12.trans h2) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hint c₁ c₂ h1 h12 h2) (hint c₂ b (h1.trans h12) h2 le_rfl)]
  have hA : ‖∫ x in a..c₁, Complex.exp (↑(φ x) * Complex.I)‖ ≤ B := by
    refine hB a c₁ le_rfl h1 (h12.trans h2) fun x hx => ?_
    have : x < d - r := by
      rcases lt_max_iff.1 hx.2 with h | h
      · exact absurd hx.1 (not_lt.2 h.le)
      · exact h
    rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
  have hC : ‖∫ x in c₂..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤ B := by
    refine hB c₂ b (h1.trans h12) h2 le_rfl fun x hx => ?_
    have : d + r < x := by
      rcases min_lt_iff.1 hx.1 with h | h
      · exact absurd hx.2 (not_lt.2 h.le)
      · exact h
    exact le_trans (by linarith) (le_abs_self _)
  have hM : ‖∫ x in c₁..c₂, Complex.exp (↑(φ x) * Complex.I)‖ ≤ 2 * r := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      fun x _ => (Complex.norm_exp_ofReal_mul_I (φ x)).le).trans ?_
    rw [one_mul, abs_of_nonneg (sub_nonneg.2 h12)]
    have : c₂ ≤ d + r := min_le_right _ _
    have : d - r ≤ c₁ := le_max_right _ _
    linarith
  calc _ ≤ ‖∫ x in a..c₁, Complex.exp (↑(φ x) * Complex.I)‖
        + (‖∫ x in c₁..c₂, Complex.exp (↑(φ x) * Complex.I)‖
        + ‖∫ x in c₂..b, Complex.exp (↑(φ x) * Complex.I)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 2 * r + 2 * B := by linarith

lemma const2 (μ : ℝ) : 2 * (1 / √μ) + 2 * (3 / √μ) = 8 / √μ := by ring

lemma sqrt_mul_inv (μ : ℝ) (hμ : 0 < μ) : μ * (1 / √μ) = √μ := by
  have h := Real.mul_self_sqrt hμ.le
  have hs : 0 < √μ := Real.sqrt_pos.2 hμ
  field_simp
  linarith

/-- `2 μ^(-1/3) + 2 · 8/√(μ · μ^(-1/3)) = 18 μ^(-1/3)`. -/
lemma const3 {μ : ℝ} (hμ : 0 < μ) :
    2 * μ ^ (-(1 : ℝ) / 3) + 2 * (8 / √(μ * μ ^ (-(1 : ℝ) / 3))) = 18 * μ ^ (-(1 : ℝ) / 3) := by
  set t := μ ^ ((1 : ℝ) / 3) with ht
  have htp : 0 < t := Real.rpow_pos_of_pos hμ _
  have hneg : μ ^ (-(1 : ℝ) / 3) = t⁻¹ := by
    rw [ht, ← Real.rpow_neg hμ.le, neg_div]
  have hcube : μ = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]; norm_num
  have hsq : √(μ * μ ^ (-(1 : ℝ) / 3)) = t := by
    rw [hneg, hcube, show t ^ 3 * t⁻¹ = t ^ 2 by field_simp]
    exact Real.sqrt_sq htp.le
  rw [hsq, hneg]
  field_simp
  ring

end OscInt.VanDerCorput.HigherAux

namespace OscInt.VanDerCorput

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint HigherAux

/-- **P3** from P0 and P1. -/
theorem vdc2Plain (hS : SplitFacts) (h1 : VdC1PlainFacts) : VdC2PlainFacts := by
  intro φ φ' φ'' a b μ hab hμ hφ hφ' hlow
  obtain ⟨hmono, d, hd, hdist⟩ := hS φ' φ'' a b μ hab hμ hφ' hlow
  have hs : 0 < √μ := Real.sqrt_pos.2 hμ
  rw [← const2 μ]
  refine split_bound φ a b d (1 / √μ) (3 / √μ) hab hd (by positivity) hφ.1 ?_
  intro s t has hst htb hfar
  refine h1 φ φ' φ'' s t √μ hst hs (hasDerivOn_mono hφ has htb) (hasDerivOn_mono hφ' has htb) ?_ ?_
  · have hsub : Ioo s t ⊆ Icc a b := Ioo_subset_Icc_self.trans (Icc_subset_Icc has htb)
    exact hmono.imp (fun h => h.mono hsub) (fun h => h.mono hsub)
  · intro x hx
    have hxI : x ∈ Icc a b := ⟨has.trans hx.1.le, hx.2.le.trans htb⟩
    rw [← sqrt_mul_inv μ hμ]
    exact (mul_le_mul_of_nonneg_left (hfar x hx) hμ.le).trans (hdist x hxI)

/-- **P4** from P0 and P3. -/
theorem vdc3Plain (hS : SplitFacts) (h2 : VdC2PlainFacts) : VdC3PlainFacts := by
  intro φ φ' φ'' φ''' a b μ hab hμ hφ hφ' hφ'' hlow
  obtain ⟨-, d, hd, hdist⟩ := hS φ'' φ''' a b μ hab hμ hφ'' hlow
  have hr : 0 < μ ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hμ _
  rw [← const3 hμ]
  refine split_bound φ a b d _ _ hab hd hr.le hφ.1 ?_
  intro s t has hst htb hfar
  refine h2 φ φ' φ'' s t _ hst (mul_pos hμ hr) (hasDerivOn_mono hφ has htb) (hasDerivOn_mono hφ' has htb) ?_
  intro x hx
  have hxI : x ∈ Icc a b := ⟨has.trans hx.1.le, hx.2.le.trans htb⟩
  exact (mul_le_mul_of_nonneg_left (hfar x hx) hμ.le).trans (hdist x hxI)

end OscInt.VanDerCorput
