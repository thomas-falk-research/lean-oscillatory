/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TriangularCrossover
import OscInt.Front.TriangularDecaySanity
import OscInt.Front.TriangularDecayFinal

/-! # Sanity theorems for batch A5U (`TriCrossoverUpperStatement`, `crossEnvelope`)

Draft, written before the statement is stamped; no proof of A5U exists in this file or is used by it, and no lemma
of a planned proof of A5U is proved here. The proved batch-K2 theorems (`OscInt.API.triDecayLower`, from
`OscInt.Front.TriangularDecayFinal`) are used only as data, in the corollary `a5u_window_excludes_zero_proved`.
Two forms (`docs/lessons.md`, rules 8 and 9).

A. Unconditional, through the definitions of `OscInt/Statements/TriangularCrossover.lean`:
* `crossEnvelope`: `1` on `(−∞, 1]` (`a5u_env_of_le`, values at `0` and `1`) and `s^{−1/4}` beyond
  (`a5u_env_of_gt`); exact values `E(16) = 1/2` and `E(81) = 1/3` (a datum that separates the exponent `−1/4` from
  `−1/3` and `−1/5`); positive, at most `1`, antitone on `ℝ`, at most `s^{−1/4}` for `s > 0`, and `min(1, s^{−1/4})`
  for `s > 0`.
* The scaling identity `t^{−2/3} (ε t^{1/3})^{−1/4} = ε^{−1/4} t^{−3/4}` and the prose's equivalent form
  `t^{−2/3} E(ε t^{1/3}) = min(t^{−2/3}, ε^{−1/4} t^{−3/4})` for `ε, t > 0` (`a5u_envelope_min`); the argument
  exceeds `1` once `t > δ^{−3}` (`a5u_scale_gt_one`).
* The hypothesis `|a₀| = a*`: holds at `a*` and `−a*` (both branches), fails at `1/4`; `triRate a₀ = 2/3` at the
  centre and `triRate (a₀ + δ) = 3/4` for `0 < δ < a*` (the punctured window, both signs of `a₀`).
* Bite of `1 ≤ t`, exact: at `t = 0` the right side is `0` for every `C`, `α`, `a₀`, while `‖triKernel α 0 (0, 0)‖ =
  (2π)²` (`a5u_time_zero_bite`).
* Helpers: a bound of this shape forces `C ≥ 0` (`a5u_const_nonneg`); a rate faster than `triRate α` from some time
  on contradicts K2-D (`a5u_rate_clash`, K2-D as hypothesis).

B. Conditional, the statement constant as the only statement hypothesis (two use K2-D as well): the centre
(`envelope argument 0`, K2-U's rate `2/3` at `±a*`); the punctured window with one constant
(`C |α − a₀|^{−1/4} t^{−3/4}`, and the `min` form); every fixed coupling of the punctured window off `{0, ±a*}` at
K2-U's rate `triRate α = 3/4`; a datum in the branch `s > 1` with the exact value `E(16) = 1/2`; a datum in the
branch `s ≤ 1` off the centre; with K2-D, the window radius is below `a*` (the window cannot contain `0`), also with
the proved K2-D.

Planted copies: `plants-a5u/README.md` of the scratch work directory of the sanity agent (not in the repository).
-/

namespace OscInt.API.TriangularCrossoverSanity

open OscInt.Statements OscInt.API.TriangularDecaySanity OscInt.API.TriangularAnisoSanity

/-! ## A. The envelope -/

theorem a5u_env_of_le {s : ℝ} (hs : s ≤ 1) : crossEnvelope s = 1 := by
  simp [crossEnvelope, hs]

theorem a5u_env_of_gt {s : ℝ} (hs : 1 < s) : crossEnvelope s = s ^ (-(1 : ℝ) / 4) := by
  simp [crossEnvelope, not_le.mpr hs]

theorem a5u_env_zero : crossEnvelope 0 = 1 := a5u_env_of_le zero_le_one

theorem a5u_env_one : crossEnvelope 1 = 1 := a5u_env_of_le le_rfl

/-- `E(16) = 16^{−1/4} = 1/2`. -/
theorem a5u_env_sixteen : crossEnvelope 16 = 1 / 2 := by
  rw [a5u_env_of_gt (by norm_num),
    show (16 : ℝ) = 2 ^ (4 : ℝ) by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num), show (4 : ℝ) * (-(1 : ℝ) / 4) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- `E(81) = 81^{−1/4} = 1/3`. -/
theorem a5u_env_eightyone : crossEnvelope 81 = 1 / 3 := by
  rw [a5u_env_of_gt (by norm_num),
    show (81 : ℝ) = 3 ^ (4 : ℝ) by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num), show (4 : ℝ) * (-(1 : ℝ) / 4) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

theorem a5u_env_pos (s : ℝ) : 0 < crossEnvelope s := by
  unfold crossEnvelope
  split_ifs with h
  · exact one_pos
  · exact Real.rpow_pos_of_pos (by linarith [not_le.mp h]) _

theorem a5u_env_le_one (s : ℝ) : crossEnvelope s ≤ 1 := by
  unfold crossEnvelope
  split_ifs with h
  · exact le_rfl
  · exact Real.rpow_le_one_of_one_le_of_nonpos (not_le.mp h).le (by norm_num)

/-- The envelope is antitone on all of `ℝ`. -/
theorem a5u_env_antitone : Antitone crossEnvelope := by
  intro a b hab
  by_cases hb : b ≤ 1
  · rw [a5u_env_of_le hb, a5u_env_of_le (hab.trans hb)]
  · by_cases ha : a ≤ 1
    · rw [a5u_env_of_le ha]
      exact a5u_env_le_one b
    · rw [a5u_env_of_gt (not_le.mp hb), a5u_env_of_gt (not_le.mp ha)]
      exact Real.rpow_le_rpow_of_nonpos (by linarith [not_le.mp ha]) hab (by norm_num)

theorem a5u_env_le_rpow {s : ℝ} (hs : 0 < s) : crossEnvelope s ≤ s ^ (-(1 : ℝ) / 4) := by
  by_cases h : s ≤ 1
  · rw [a5u_env_of_le h]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs h (by norm_num)
  · rw [a5u_env_of_gt (not_le.mp h)]

/-- For `s > 0`, `E(s) = min(1, s^{−1/4})`. -/
theorem a5u_env_eq_min {s : ℝ} (hs : 0 < s) : crossEnvelope s = min 1 (s ^ (-(1 : ℝ) / 4)) := by
  by_cases h : s ≤ 1
  · rw [a5u_env_of_le h, min_eq_left (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs h (by norm_num))]
  · rw [a5u_env_of_gt (not_le.mp h),
      min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos (not_le.mp h).le (by norm_num))]

/-- The scaling identity `t^{−2/3} (ε t^{1/3})^{−1/4} = ε^{−1/4} t^{−3/4}`. -/
theorem a5u_scaling {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    t ^ (-(2 : ℝ) / 3) * (ε * t ^ ((1 : ℝ) / 3)) ^ (-(1 : ℝ) / 4) = ε ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  rw [Real.mul_rpow hε (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le, mul_left_comm, ← Real.rpow_add ht]
  norm_num

/-- The prose's equivalent form: `t^{−2/3} E(ε t^{1/3}) = min(t^{−2/3}, ε^{−1/4} t^{−3/4})` for `ε, t > 0`. -/
theorem a5u_envelope_min {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) =
      min (t ^ (-(2 : ℝ) / 3)) (ε ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4)) := by
  rw [a5u_env_eq_min (mul_pos hε (Real.rpow_pos_of_pos ht _)),
    mul_min_of_nonneg _ _ (Real.rpow_nonneg ht.le _), mul_one, a5u_scaling hε.le ht]

theorem a5u_envelope_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) ≤ ε ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  rw [a5u_envelope_min hε ht]
  exact min_le_right _ _

/-- Beyond the crossover the envelope bound is exactly `ε^{−1/4} t^{−3/4}`. -/
theorem a5u_envelope_beyond {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (hs : 1 < ε * t ^ ((1 : ℝ) / 3)) :
    t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) = ε ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  rw [a5u_env_of_gt hs, a5u_scaling hε.le ht]

/-- The argument `δ t^{1/3}` exceeds `1` once `t > δ^{−3}`. -/
theorem a5u_scale_gt_one {δ t : ℝ} (hδ : 0 < δ) (ht : δ⁻¹ ^ 3 < t) : 1 < δ * t ^ ((1 : ℝ) / 3) := by
  have h1 : δ⁻¹ = (δ⁻¹ ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h2 : δ⁻¹ < t ^ ((1 : ℝ) / 3) := by
    rw [h1]
    exact Real.rpow_lt_rpow (by positivity) ht (by norm_num)
  calc (1 : ℝ) = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
    _ < δ * t ^ ((1 : ℝ) / 3) := mul_lt_mul_of_pos_left h2 hδ

/-! ## A. The couplings and the bite of `1 ≤ t` -/

theorem a5u_abs_exceptional : |triExceptional| = triExceptional := abs_of_pos triExceptional_pos

theorem a5u_abs_neg_exceptional : |-triExceptional| = triExceptional := by
  rw [abs_neg]
  exact abs_of_pos triExceptional_pos

/-- **Bite**: `1/4` is not an exceptional coupling. -/
theorem a5u_quarter_not_exceptional : |(1 / 4 : ℝ)| ≠ triExceptional := by
  rw [abs_of_pos (by norm_num)]
  exact quarter_ne_exceptional

/-- The exceptional couplings are `±a*`. -/
theorem a5u_exceptional_cases {a₀ : ℝ} (ha : |a₀| = triExceptional) :
    a₀ = triExceptional ∨ a₀ = -triExceptional :=
  (abs_eq triExceptional_pos.le).mp ha

theorem a5u_triRate_center {a₀ : ℝ} (ha : |a₀| = triExceptional) : triRate a₀ = 2 / 3 := by
  simp [triRate, ha]

/-- In the punctured window `a₀ + δ`, `0 < δ < a*`, the fixed-coupling rate is `3/4` (both signs of `a₀`). -/
theorem a5u_triRate_window {a₀ δ : ℝ} (ha : |a₀| = triExceptional) (hδ : 0 < δ) (hδa : δ < triExceptional) :
    triRate (a₀ + δ) = 3 / 4 := by
  have hp := triExceptional_pos
  rcases a5u_exceptional_cases ha with rfl | rfl
  · exact triRate_generic _ (by linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  · exact triRate_generic _ (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)

/-- **Bite of `1 ≤ t`** (unconditional): at `t = 0` the right side is `0` for every `C`, `α`, `a₀`, while
`‖triKernel α 0 (0, 0)‖ = (2π)²`. -/
theorem a5u_time_zero_bite (α a₀ C : ℝ) :
    ¬ ‖triKernel α 0 (0, 0)‖ ≤
      C * (0 : ℝ) ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * (0 : ℝ) ^ ((1 : ℝ) / 3)) := by
  rw [Real.zero_rpow (by norm_num), mul_zero, zero_mul, triKernel_time_zero, Complex.norm_real, Real.norm_eq_abs]
  intro h
  have : 0 < (2 * Real.pi) ^ 2 := by positivity
  linarith [le_abs_self ((2 * Real.pi) ^ 2)]

/-! ## A. Helpers -/

/-- A bound `‖x‖ ≤ C t^{−2/3} E(s)` with `t > 0` forces `C ≥ 0`. -/
theorem a5u_const_nonneg {x : ℂ} {C t s : ℝ} (ht : 0 < t)
    (h : ‖x‖ ≤ C * t ^ (-(2 : ℝ) / 3) * crossEnvelope s) : 0 ≤ C := by
  have hp : 0 < t ^ (-(2 : ℝ) / 3) * crossEnvelope s := mul_pos (Real.rpow_pos_of_pos ht _) (a5u_env_pos s)
  rw [mul_assoc] at h
  by_contra hC
  have : C * (t ^ (-(2 : ℝ) / 3) * crossEnvelope s) < 0 := mul_neg_of_neg_of_pos (not_le.mp hC) hp
  linarith [norm_nonneg x]

/-- A rate `b > triRate α` holding from some time on contradicts K2-D at `α`. -/
theorem a5u_rate_clash (hD : TriDecayLowerStatement) (α b C T₀ : ℝ) (hb : triRate α < b)
    (hup : ∀ (t : ℝ) (n : ℤ × ℤ), T₀ ≤ t → ‖triKernel α t n‖ ≤ C * t ^ (-b)) : False := by
  obtain ⟨c, hc, T, hT⟩ := hD α
  obtain ⟨t, htT, -, hlt⟩ := rate_separation (triRate α) b c C (max T T₀) hb hc
  obtain ⟨n, hn⟩ := hT t (le_of_max_le_left htT)
  have := hup t n (le_of_max_le_right htT)
  linarith

/-- With K2-D, a window radius `r` for which the A5U bound holds at `a₀` is below `a*`: at `α = 0` the bound would
give `C a*^{−1/4} t^{−3/4}`, against K2-D's `c t^{−2/3}`. -/
theorem a5u_window_lt (hD : TriDecayLowerStatement) {a₀ r C : ℝ} (ha : |a₀| = triExceptional)
    (hC : ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → 1 ≤ t →
      ‖triKernel α t n‖ ≤ C * t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3))) :
    r < triExceptional := by
  by_contra hr'
  have hr : triExceptional ≤ r := not_lt.mp hr'
  have h0 : |(0 : ℝ) - a₀| = triExceptional := by rw [zero_sub, abs_neg, ha]
  have hC0 : 0 ≤ C := a5u_const_nonneg one_pos (hC 0 1 (0, 0) (by rw [h0]; exact hr) le_rfl)
  refine a5u_rate_clash hD 0 (3 / 4) (C * triExceptional ^ (-(1 : ℝ) / 4)) 1 (by rw [triRate_zero]; norm_num)
    fun t n ht => ?_
  have h1 := hC 0 t n (by rw [h0]; exact hr) ht
  rw [h0, mul_assoc] at h1
  calc ‖triKernel 0 t n‖ ≤ C * (t ^ (-(2 : ℝ) / 3) * crossEnvelope (triExceptional * t ^ ((1 : ℝ) / 3))) := h1
    _ ≤ C * (triExceptional ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (a5u_envelope_le triExceptional_pos (by linarith)) hC0
    _ = C * triExceptional ^ (-(1 : ℝ) / 4) * t ^ (-(3 / 4 : ℝ)) := by
        rw [show (-(3 : ℝ) / 4) = -(3 / 4) by ring]
        ring

/-! ## B. Conditional: A5U as the hypothesis -/

/-- **A5U at the centre** (envelope argument `0`): K2-U's rate `triRate a₀ = 2/3` at `a₀ = ±a*`. -/
theorem a5u_center (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel a₀ t n‖ ≤ C * t ^ (-triRate a₀) := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  refine ⟨C, fun t n ht => ?_⟩
  have := hC a₀ t n (by rw [sub_self, abs_zero]; exact hr.le) ht
  rw [sub_self, abs_zero, zero_mul, a5u_env_zero, mul_one] at this
  rw [a5u_triRate_center ha, show -(2 / 3 : ℝ) = -(2 : ℝ) / 3 by ring]
  exact this

/-- **A5U at both centres** `a*` and `−a*`: rate `2/3`. -/
theorem a5u_center_pm (h : TriCrossoverUpperStatement) :
    (∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel triExceptional t n‖ ≤ C * t ^ (-(2 / 3 : ℝ))) ∧
      ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel (-triExceptional) t n‖ ≤ C * t ^ (-(2 / 3 : ℝ)) := by
  have h1 := a5u_center h _ a5u_abs_exceptional
  have h2 := a5u_center h _ a5u_abs_neg_exceptional
  rw [triRate_exceptional] at h1
  rw [triRate_neg_exceptional] at h2
  exact ⟨h1, h2⟩

/-- **A5U on the punctured window, one constant**: `‖triKernel α t n‖ ≤ C |α − a₀|^{−1/4} t^{−3/4}`. -/
theorem a5u_off_center (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ r > 0, ∃ C : ℝ, ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → α ≠ a₀ → 1 ≤ t →
      ‖triKernel α t n‖ ≤ C * (|α - a₀| ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4)) := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  refine ⟨r, hr, C, fun α t n hα hne ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hε : 0 < |α - a₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h1 := hC α t n hα ht
  have hC0 := a5u_const_nonneg ht0 h1
  rw [mul_assoc] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (a5u_envelope_le hε ht0) hC0)

/-- **A5U in the `min` form** of the prose: `C min(t^{−2/3}, |α − a₀|^{−1/4} t^{−3/4})` on the punctured window. -/
theorem a5u_min_form (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ r > 0, ∃ C : ℝ, ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → α ≠ a₀ → 1 ≤ t →
      ‖triKernel α t n‖ ≤ C * min (t ^ (-(2 : ℝ) / 3)) (|α - a₀| ^ (-(1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4)) := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  refine ⟨r, hr, C, fun α t n hα hne ht => ?_⟩
  have h1 := hC α t n hα ht
  rwa [mul_assoc, a5u_envelope_min (abs_pos.mpr (sub_ne_zero.mpr hne)) (by linarith)] at h1

/-- **A5U at a fixed coupling of the window off `{0, ±a*}`**: K2-U's rate `triRate α = 3/4` (consistency). -/
theorem a5u_fixed (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ r > 0, ∀ α : ℝ, |α - a₀| ≤ r → α ≠ 0 → |α| ≠ triExceptional →
      ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel α t n‖ ≤ C * t ^ (-triRate α) := by
  obtain ⟨r, hr, C, hC⟩ := a5u_off_center h a₀ ha
  refine ⟨r, hr, fun α hα h0 h1 => ⟨C * |α - a₀| ^ (-(1 : ℝ) / 4), fun t n ht => ?_⟩⟩
  have hne : α ≠ a₀ := fun e => h1 (by rw [e]; exact ha)
  rw [triRate_generic α h0 h1, show -(3 / 4 : ℝ) = -(3 : ℝ) / 4 by ring, mul_assoc]
  exact hC α t n hα hne ht

/-- **A5U in the branch `s > 1`, exact envelope value**: at `α = a₀ + δ`, `δ = min(r, 1)`, `t = (16/δ)³` the
argument is `16` and the envelope is `1/2`. -/
theorem a5u_datum_sixteen (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ δ > 0, ∃ C : ℝ, ∀ n : ℤ × ℤ,
      ‖triKernel (a₀ + δ) ((16 / δ) ^ 3) n‖ ≤ C * ((16 / δ) ^ 3) ^ (-(2 : ℝ) / 3) * (1 / 2) := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  have hδ0 : 0 < min r 1 := lt_min hr one_pos
  refine ⟨min r 1, hδ0, C, fun n => ?_⟩
  have hroot : ((16 / min r 1) ^ 3) ^ ((1 : ℝ) / 3) = 16 / min r 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have ht : 1 ≤ (16 / min r 1) ^ 3 :=
    one_le_pow₀ (by rw [le_div_iff₀ hδ0]; linarith [min_le_right r 1])
  have e : min r 1 * (16 / min r 1) = 16 := by field_simp
  have := hC (a₀ + min r 1) ((16 / min r 1) ^ 3) n
    (by rw [add_sub_cancel_left, abs_of_pos hδ0]; exact min_le_left r 1) ht
  rwa [add_sub_cancel_left, abs_of_pos hδ0, hroot, e, a5u_env_sixteen] at this

/-- **A5U in the branch `s ≤ 1` off the centre**: at `α = a₀ + δ`, `δ = min(r, 1)`, `t = 1` the envelope is `1`. -/
theorem a5u_datum_plateau (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ δ > 0, ∃ C : ℝ, ∀ n : ℤ × ℤ, ‖triKernel (a₀ + δ) 1 n‖ ≤ C := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  have hδ0 : 0 < min r 1 := lt_min hr one_pos
  refine ⟨min r 1, hδ0, C, fun n => ?_⟩
  have := hC (a₀ + min r 1) 1 n (by rw [add_sub_cancel_left, abs_of_pos hδ0]; exact min_le_left r 1) le_rfl
  rwa [add_sub_cancel_left, abs_of_pos hδ0, Real.one_rpow, Real.one_rpow, mul_one, mul_one,
    a5u_env_of_le (min_le_right r 1), mul_one] at this

/-- **A5U with K2-D**: the window radius is below `a*`, so the window does not contain `0` (prose, item 2). -/
theorem a5u_window_excludes_zero (h : TriCrossoverUpperStatement) (hD : TriDecayLowerStatement) (a₀ : ℝ)
    (ha : |a₀| = triExceptional) :
    ∃ r > 0, r < triExceptional ∧ ∃ C : ℝ, ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → 1 ≤ t →
      ‖triKernel α t n‖ ≤ C * t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3)) := by
  obtain ⟨r, hr, C, hC⟩ := h a₀ ha
  exact ⟨r, hr, a5u_window_lt hD ha hC, C, hC⟩

/-- **A5U with the proved K2-D** (`OscInt.API.triDecayLower`): the window radius is below `a*`. -/
theorem a5u_window_excludes_zero_proved (h : TriCrossoverUpperStatement) (a₀ : ℝ) (ha : |a₀| = triExceptional) :
    ∃ r > 0, r < triExceptional ∧ ∃ C : ℝ, ∀ (α t : ℝ) (n : ℤ × ℤ), |α - a₀| ≤ r → 1 ≤ t →
      ‖triKernel α t n‖ ≤ C * t ^ (-(2 : ℝ) / 3) * crossEnvelope (|α - a₀| * t ^ ((1 : ℝ) / 3)) :=
  a5u_window_excludes_zero h OscInt.API.triDecayLower a₀ ha

end OscInt.API.TriangularCrossoverSanity
