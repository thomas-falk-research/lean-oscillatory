/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.HadamardWalk
import OscInt.VanDerCorput.Final
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Batch HW, part HW3: the kernel bound HW-K (route `docs/proof-HW.md`, H6)

`HadamardKernelBoundStatement` from `HadamardPhaseFacts` and `HadamardAmplitudeFacts` (hypotheses) and the proved
S1.2 (`OscInt.vanDerCorput_two`) and S1.3 (`OscInt.vanDerCorput_three`): the kernel is `(2π)⁻¹ (I₋ − (−1)^t I₊)`,
each `I_σ` is moved to the window `[−π/4, 7π/4]` by periodicity and cut into four arcs; S1.2 on the two arcs where
`|sin k| ≥ 1/√2`, S1.3 on the two arcs where `|cos k| ≥ 1/√2`; two numerical inequalities.
-/

namespace OscInt.HadamardWalkAux

open OscInt.Statements OscInt.Blueprint.HadamardWalk

/-! ## Trigonometric facts on the four arcs -/

/-- `cos x ≥ 1/√2` for `|x| ≤ π/4`. -/
theorem hwKB_cos_ge (x : ℝ) (hx : |x| ≤ Real.pi / 4) : 1 / Real.sqrt 2 ≤ Real.cos x := by
  have h1 : Real.cos (Real.pi / 4) ≤ Real.cos |x| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) hx
  rw [Real.cos_abs, Real.cos_pi_div_four] at h1
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have e : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff h0.ne' (by norm_num)]
    linarith
  rw [e]
  exact h1

/-- `|cos k| ≥ 1/√2` on `(−π/4, π/4)`. -/
theorem hwKB_abs_cos_arc0 (k : ℝ) (hk : k ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    1 / Real.sqrt 2 ≤ |Real.cos k| :=
  (hwKB_cos_ge k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)).trans (le_abs_self _)

/-- `|sin k| ≥ 1/√2` on `(π/4, 3π/4)`. -/
theorem hwKB_abs_sin_arc1 (k : ℝ) (hk : k ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 4)) :
    1 / Real.sqrt 2 ≤ |Real.sin k| := by
  have h := hwKB_cos_ge (k - Real.pi / 2) (abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩)
  rw [Real.cos_sub_pi_div_two] at h
  exact h.trans (le_abs_self _)

/-- `|cos k| ≥ 1/√2` on `(3π/4, 5π/4)`. -/
theorem hwKB_abs_cos_arc2 (k : ℝ) (hk : k ∈ Set.Ioo (3 * Real.pi / 4) (5 * Real.pi / 4)) :
    1 / Real.sqrt 2 ≤ |Real.cos k| := by
  have h := hwKB_cos_ge (k - Real.pi) (abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩)
  rw [Real.cos_sub_pi] at h
  exact h.trans (neg_le_abs _)

/-- `|sin k| ≥ 1/√2` on `(5π/4, 7π/4)`. -/
theorem hwKB_abs_sin_arc3 (k : ℝ) (hk : k ∈ Set.Ioo (5 * Real.pi / 4) (7 * Real.pi / 4)) :
    1 / Real.sqrt 2 ≤ |Real.sin k| := by
  have h := hwKB_cos_ge (k - Real.pi / 2 - Real.pi) (abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩)
  rw [Real.cos_sub_pi, Real.cos_sub_pi_div_two] at h
  exact h.trans (neg_le_abs _)

/-! ## Continuity, the hypotheses of S1 -/

/-- The dispersion relation is continuous. -/
theorem hwKB_continuous_disp (hP : HadamardPhaseFacts) : Continuous hadamardDispersion :=
  continuous_iff_continuousAt.mpr fun k => (hP.1 k).continuousAt

/-- The amplitude is continuous. -/
theorem hwKB_continuous_amp (hA : HadamardAmplitudeFacts) : Continuous hwAmp :=
  continuous_iff_continuousAt.mpr fun k => (hA.1 k).continuousAt

/-- The derivative of the amplitude is continuous. -/
theorem hwKB_continuous_amp' : Continuous hwAmp' := by
  unfold hwAmp'
  refine Complex.continuous_ofReal.comp (Continuous.div (by fun_prop) (by fun_prop) fun k => ?_)
  positivity

/-- The amplitude hypothesis of S1 on every interval. -/
theorem hwKB_amplitudeOn (hA : HadamardAmplitudeFacts) (a b : ℝ) : AmplitudeOn hwAmp hwAmp' a b :=
  ⟨(hwKB_continuous_amp hA).continuousOn, fun k _ => hA.1 k, hwKB_continuous_amp'.intervalIntegrable a b⟩

/-- A constant multiple of a function with a derivative at every point has a derivative on every interval. -/
theorem hwKB_hasDerivOn (f f' : ℝ → ℝ) (c a b : ℝ) (h : ∀ k : ℝ, HasDerivAt f (f' k) k) :
    HasDerivOn (fun k => c * f k) (fun k => c * f' k) a b :=
  ⟨fun k _ => ((h k).const_mul c).continuousAt.continuousWithinAt, fun k _ => (h k).const_mul c⟩

/-- The oscillatory integral of S1 with phase `c ω(k) + p k` and the amplitude, written out. -/
theorem hwKB_oscInt_eq (c p a b : ℝ) :
    oscInt (fun k => c * hadamardDispersion k + p * k) hwAmp a b =
      ∫ k in a..b, Complex.exp (↑(c * hadamardDispersion k + p * k) * Complex.I) * hwAmp k := rfl

/-- The integrand `e^{i(c ω(k) + p k)} g(k)` is continuous. -/
theorem hwKB_continuous_integrand (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (c p : ℝ) :
    Continuous fun k : ℝ => Complex.exp (↑(c * hadamardDispersion k + p * k) * Complex.I) * hwAmp k := by
  have h1 : Continuous fun k : ℝ => c * hadamardDispersion k + p * k :=
    ((hwKB_continuous_disp hP).const_mul c).add (continuous_id.const_mul p)
  exact ((Complex.continuous_ofReal.comp h1).mul continuous_const).cexp.mul (hwKB_continuous_amp hA)

/-! ## One arc: S1.2 where `|sin k| ≥ 1/√2`, S1.3 where `|cos k| ≥ 1/√2` -/

/-- S1.2 on an arc where `|sin k| ≥ 1/√2`, with `μ = |c| · 2/(3√3)`. -/
theorem hwKB_sin_arc (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (c p a b : ℝ) (hc : c ≠ 0)
    (hab : a ≤ b) (hsin : ∀ k ∈ Set.Ioo a b, 1 / Real.sqrt 2 ≤ |Real.sin k|) :
    ‖oscInt (fun k => c * hadamardDispersion k + p * k) hwAmp a b‖ ≤
      8 / Real.sqrt (|c| * (2 / (3 * Real.sqrt 3))) * ampNorm hwAmp hwAmp' a b := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hq : (0 : ℝ) < 2 / (3 * Real.sqrt 3) := by positivity
  exact OscInt.vanDerCorput_two (fun k => c * hadamardDispersion k) (fun k => c * hwD1 k) (fun k => c * hwD2 k)
    hwAmp hwAmp' a b _ p hab (mul_pos hc' hq) (hwKB_hasDerivOn _ _ c a b hP.1) (hwKB_hasDerivOn _ _ c a b hP.2.1)
    (fun k hk => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hP.2.2.2.1 k (hsin k hk)) hc'.le)
    (hwKB_amplitudeOn hA a b)

/-- S1.3 on an arc where `|cos k| ≥ 1/√2`, with `μ = |c| · 1/(2√2)`. -/
theorem hwKB_cos_arc (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (c p a b : ℝ) (hc : c ≠ 0)
    (hab : a ≤ b) (hcos : ∀ k ∈ Set.Ioo a b, 1 / Real.sqrt 2 ≤ |Real.cos k|) :
    ‖oscInt (fun k => c * hadamardDispersion k + p * k) hwAmp a b‖ ≤
      18 * (|c| * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) * ampNorm hwAmp hwAmp' a b := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hq : (0 : ℝ) < 1 / (2 * Real.sqrt 2) := by positivity
  exact OscInt.vanDerCorput_three (fun k => c * hadamardDispersion k) (fun k => c * hwD1 k)
    (fun k => c * hwD2 k) (fun k => c * hwD3 k) hwAmp hwAmp' a b _ p hab (mul_pos hc' hq)
    (hwKB_hasDerivOn _ _ c a b hP.1) (hwKB_hasDerivOn _ _ c a b hP.2.1) (hwKB_hasDerivOn _ _ c a b hP.2.2.1)
    (fun k hk => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hP.2.2.2.2 k (hcos k hk)) hc'.le)
    (hwKB_amplitudeOn hA a b)

/-! ## Periodicity and the four arcs -/

/-- The integrand is `2π`-periodic when the linear term is an integer multiple of `k`. -/
theorem hwKB_periodic (c : ℝ) (x : ℤ) :
    Function.Periodic
      (fun k : ℝ => Complex.exp (↑(c * hadamardDispersion k + -(x : ℝ) * k) * Complex.I) * hwAmp k)
      (2 * Real.pi) := by
  intro k
  have h1 : hadamardDispersion (k + 2 * Real.pi) = hadamardDispersion k := by
    unfold hadamardDispersion
    rw [Real.sin_add_two_pi]
  have h2 : hwAmp (k + 2 * Real.pi) = hwAmp k := by
    unfold hwAmp
    rw [Real.cos_add_two_pi]
  have e : (↑(c * hadamardDispersion k + -(x : ℝ) * (k + 2 * Real.pi)) : ℂ) * Complex.I =
      ↑(c * hadamardDispersion k + -(x : ℝ) * k) * Complex.I +
        ((-x : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  show Complex.exp (↑(c * hadamardDispersion (k + 2 * Real.pi) + -(x : ℝ) * (k + 2 * Real.pi)) * Complex.I) *
      hwAmp (k + 2 * Real.pi) = _
  rw [h1, h2, e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The integral over a period is the sum of the integrals over the four arcs of `[−π/4, 7π/4]`. -/
theorem hwKB_four_arcs (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (c : ℝ) (x : ℤ) :
    oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (-Real.pi) Real.pi =
      oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (-(Real.pi / 4)) (Real.pi / 4) +
        oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (Real.pi / 4) (3 * Real.pi / 4) +
        oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (3 * Real.pi / 4) (5 * Real.pi / 4) +
        oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (5 * Real.pi / 4) (7 * Real.pi / 4) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun k : ℝ => Complex.exp (↑(c * hadamardDispersion k + -(x : ℝ) * k) * Complex.I) * hwAmp k)
      MeasureTheory.volume a b := fun a b => (hwKB_continuous_integrand hP hA c (-(x : ℝ))).intervalIntegrable a b
  have hper := (hwKB_periodic c x).intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 4))
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    show -(Real.pi / 4) + 2 * Real.pi = 7 * Real.pi / 4 by ring] at hper
  simp only [hwKB_oscInt_eq]
  rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  exact hper

/-- The integral over a period: twice the bound of S1.2 plus twice the bound of S1.3. -/
theorem hwKB_period_bound (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (c : ℝ) (x : ℤ) (hc : c ≠ 0) :
    ‖oscInt (fun k => c * hadamardDispersion k + -(x : ℝ) * k) hwAmp (-Real.pi) Real.pi‖ ≤
      2 * (8 / Real.sqrt (|c| * (2 / (3 * Real.sqrt 3))) * (Real.sqrt 2 - 1 / Real.sqrt 3)) +
        2 * (18 * (|c| * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) * (Real.sqrt 3 - 1)) := by
  have hpi := Real.pi_pos
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hC2 : 0 ≤ 8 / Real.sqrt (|c| * (2 / (3 * Real.sqrt 3))) := by positivity
  have hC3 : 0 ≤ 18 * (|c| * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) := by positivity
  have b0 := (hwKB_cos_arc hP hA c (-(x : ℝ)) (-(Real.pi / 4)) (Real.pi / 4) hc (by linarith)
    hwKB_abs_cos_arc0).trans (mul_le_mul_of_nonneg_left hA.2.1 hC3)
  have b1 := (hwKB_sin_arc hP hA c (-(x : ℝ)) (Real.pi / 4) (3 * Real.pi / 4) hc (by linarith)
    hwKB_abs_sin_arc1).trans (mul_le_mul_of_nonneg_left hA.2.2.1 hC2)
  have b2 := (hwKB_cos_arc hP hA c (-(x : ℝ)) (3 * Real.pi / 4) (5 * Real.pi / 4) hc (by linarith)
    hwKB_abs_cos_arc2).trans (mul_le_mul_of_nonneg_left hA.2.2.2.1 hC3)
  have b3 := (hwKB_sin_arc hP hA c (-(x : ℝ)) (5 * Real.pi / 4) (7 * Real.pi / 4) hc (by linarith)
    hwKB_abs_sin_arc3).trans (mul_le_mul_of_nonneg_left hA.2.2.2.2 hC2)
  rw [hwKB_four_arcs hP hA c x]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add b0 b1)) b2))
    b3).trans (le_of_eq ?_)
  ring

/-! ## The split of the kernel -/

/-- The integrand of the kernel is the difference of the two oscillatory integrands. -/
theorem hwKB_integrand (t : ℕ) (x : ℤ) (k : ℝ) :
    (Complex.exp (↑(-((t : ℝ) * hadamardDispersion k)) * Complex.I) -
          (-1 : ℂ) ^ t * Complex.exp (↑((t : ℝ) * hadamardDispersion k) * Complex.I)) /
        ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) *
      Complex.exp (↑(-((x : ℝ) * k)) * Complex.I) =
      Complex.exp (↑(-(t : ℝ) * hadamardDispersion k + -(x : ℝ) * k) * Complex.I) * hwAmp k -
        (-1 : ℂ) ^ t * (Complex.exp (↑((t : ℝ) * hadamardDispersion k + -(x : ℝ) * k) * Complex.I) * hwAmp k) := by
  have e1 : ∀ A B : ℝ, Complex.exp (↑(A + B) * Complex.I) =
      Complex.exp (↑A * Complex.I) * Complex.exp (↑B * Complex.I) := by
    intro A B
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have e2 : hwAmp k = 1 / ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) := by
    unfold hwAmp
    rw [Complex.ofReal_div, Complex.ofReal_one]
  rw [e1, e1, e2, neg_mul, neg_mul]
  ring

/-- The kernel is `(2π)⁻¹ (I₋ − (−1)^t I₊)`. -/
theorem hwKB_kernel_split (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) (t : ℕ) (x : ℤ) :
    hadamardKernel t x = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (oscInt (fun k => -(t : ℝ) * hadamardDispersion k + -(x : ℝ) * k) hwAmp (-Real.pi) Real.pi -
        (-1 : ℂ) ^ t *
          oscInt (fun k => (t : ℝ) * hadamardDispersion k + -(x : ℝ) * k) hwAmp (-Real.pi) Real.pi) := by
  have hi : ∀ c : ℝ, IntervalIntegrable
      (fun k : ℝ => Complex.exp (↑(c * hadamardDispersion k + -(x : ℝ) * k) * Complex.I) * hwAmp k)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    fun c => (hwKB_continuous_integrand hP hA c (-(x : ℝ))).intervalIntegrable _ _
  unfold hadamardKernel
  simp only [hwKB_oscInt_eq]
  congr 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hi _) ((hi _).const_mul _)]
  exact intervalIntegral.integral_congr fun k _ => hwKB_integrand t x k

/-! ## Real powers and the two numerical inequalities -/

/-- `√2 ≤ 1.4143`. -/
theorem hwKB_sqrt_two_le : Real.sqrt 2 ≤ 14143 / 10000 :=
  (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)

/-- `√3 ≤ 1.7321`. -/
theorem hwKB_sqrt_three_le : Real.sqrt 3 ≤ 17321 / 10000 :=
  (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)

/-- `1 ≤ √3`. -/
theorem hwKB_one_le_sqrt_three : 1 ≤ Real.sqrt 3 :=
  Real.one_le_sqrt.mpr (by norm_num)

/-- `0.577 ≤ 1/√3`. -/
theorem hwKB_inv_sqrt_three_ge : (577 : ℝ) / 1000 ≤ 1 / Real.sqrt 3 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [le_div_iff₀ h3]
  linarith [hwKB_sqrt_three_le]

/-- `0.62 ≤ √(2/(3√3))`. -/
theorem hwKB_sqrt_q_ge : (31 : ℝ) / 50 ≤ Real.sqrt (2 / (3 * Real.sqrt 3)) := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.le_sqrt' (by norm_num), le_div_iff₀ (by positivity)]
  linarith [hwKB_sqrt_three_le]

/-- `t^{−1/2} = (√t)⁻¹`. -/
theorem hwKB_rpow_neg_half (T : ℝ) (hT : 0 < T) : T ^ (-(1 : ℝ) / 2) = (Real.sqrt T)⁻¹ := by
  rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hT.le, ← Real.sqrt_eq_rpow]

/-- The coefficient of S1.2: `8/√(t · 2/(3√3)) ≤ (400/31) t^{−1/2}`. -/
theorem hwKB_coeff_sin (T : ℝ) (hT : 0 < T) :
    8 / Real.sqrt (T * (2 / (3 * Real.sqrt 3))) ≤ 400 / 31 * T ^ (-(1 : ℝ) / 2) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hq := hwKB_sqrt_q_ge
  have hq0 : 0 < Real.sqrt (2 / (3 * Real.sqrt 3)) := by linarith
  rw [hwKB_rpow_neg_half T hT, Real.sqrt_mul hT.le, div_le_iff₀ (mul_pos hs hq0)]
  have e : 400 / 31 * (Real.sqrt T)⁻¹ * (Real.sqrt T * Real.sqrt (2 / (3 * Real.sqrt 3))) =
      400 / 31 * Real.sqrt (2 / (3 * Real.sqrt 3)) := by
    field_simp
  rw [e]
  linarith

/-- `(1/(2√2))^{−1/3} = √2`. -/
theorem hwKB_q_rpow : (1 / (2 * Real.sqrt 2)) ^ (-(1 : ℝ) / 3) = Real.sqrt 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have e : 1 / (2 * Real.sqrt 2) = Real.sqrt 2 ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg h0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
    congr 1
    linear_combination (-Real.sqrt 2) * h
  rw [e, ← Real.rpow_mul h0.le, show -(3 : ℝ) * (-(1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]

/-- The coefficient of S1.3: `18 (t · 1/(2√2))^{−1/3} = 18 √2 · t^{−1/3}`. -/
theorem hwKB_coeff_cos (T : ℝ) (hT : 0 < T) :
    18 * (T * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) = 18 * Real.sqrt 2 * T ^ (-(1 : ℝ) / 3) := by
  rw [Real.mul_rpow hT.le (by positivity), hwKB_q_rpow]
  ring

/-- First numerical inequality: `(1600/31)(√2 − 1/√3) ≤ 14π` (this is `(16/π)(3√3/2)^{1/2}(√2 − 1/√3) ≤ 7`). -/
theorem hwKB_num_one : 1600 / 31 * (Real.sqrt 2 - 1 / Real.sqrt 3) ≤ 14 * Real.pi := by
  linarith [hwKB_sqrt_two_le, hwKB_inv_sqrt_three_ge, Real.pi_gt_d2]

/-- Second numerical inequality: `72 √2 (√3 − 1) ≤ 24π` (this is `(36/π) √2 (√3 − 1) ≤ 12`). -/
theorem hwKB_num_two : 72 * (Real.sqrt 2 * (Real.sqrt 3 - 1)) ≤ 24 * Real.pi := by
  have h : Real.sqrt 2 * (Real.sqrt 3 - 1) ≤ 14143 / 10000 * (7321 / 10000) :=
    mul_le_mul hwKB_sqrt_two_le (by linarith [hwKB_sqrt_three_le]) (by linarith [hwKB_one_le_sqrt_three])
      (by norm_num)
  linarith [Real.pi_gt_d2]

/-- The arithmetic of H6: `(2π)⁻¹` times twice the bound for a period is at most `7 t^{−1/2} + 12 t^{−1/3}`. -/
theorem hwKB_arith (T : ℝ) (hT : 0 < T) :
    (2 * Real.pi)⁻¹ *
        ((2 * (8 / Real.sqrt (T * (2 / (3 * Real.sqrt 3))) * (Real.sqrt 2 - 1 / Real.sqrt 3)) +
            2 * (18 * (T * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) * (Real.sqrt 3 - 1))) +
          (2 * (8 / Real.sqrt (T * (2 / (3 * Real.sqrt 3))) * (Real.sqrt 2 - 1 / Real.sqrt 3)) +
            2 * (18 * (T * (1 / (2 * Real.sqrt 2))) ^ (-(1 : ℝ) / 3) * (Real.sqrt 3 - 1)))) ≤
      7 * T ^ (-(1 : ℝ) / 2) + 12 * T ^ (-(1 : ℝ) / 3) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hu : 0 < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hv : 0 < T ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hT _
  have hs2 : 0 ≤ Real.sqrt 2 - 1 / Real.sqrt 3 := by
    have h3 : (1 : ℝ) / Real.sqrt 3 ≤ 1 := by
      rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]
      exact hwKB_one_le_sqrt_three
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    linarith
  have h1 := mul_le_mul_of_nonneg_right (hwKB_coeff_sin T hT) hs2
  have n1 := mul_le_mul_of_nonneg_left hwKB_num_one hu.le
  have n2 := mul_le_mul_of_nonneg_left hwKB_num_two hv.le
  rw [hwKB_coeff_cos T hT, inv_mul_le_iff₀ hpi]
  nlinarith [h1, n1, n2]

/-! ## HW-K -/

/-- **HW-K** from the phase facts, the amplitude facts and the proved S1.2 and S1.3. -/
theorem hadamardKernelBound_of (hP : HadamardPhaseFacts) (hA : HadamardAmplitudeFacts) :
    HadamardKernelBoundStatement := by
  intro t x ht
  have hT : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hm := hwKB_period_bound hP hA (-(t : ℝ)) x (neg_ne_zero.mpr hT.ne')
  have hp := hwKB_period_bound hP hA (t : ℝ) x hT.ne'
  rw [abs_neg, abs_of_pos hT] at hm
  rw [abs_of_pos hT] at hp
  rw [hwKB_kernel_split hP hA t x, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  refine (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hpi.le)).trans (hwKB_arith (t : ℝ) hT)
  refine (norm_sub_le _ _).trans (add_le_add hm ?_)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hp

end OscInt.HadamardWalkAux
