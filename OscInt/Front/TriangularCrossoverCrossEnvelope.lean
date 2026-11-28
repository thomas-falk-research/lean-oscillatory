/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# Batch A5U, part A7: `CrossEnvelopeFacts`

Route: `docs/proof-A5U.md`, section 4. All powers have positive bases, so each `x ^ r` is written as
`exp (log x * r)` and the inequalities become linear inequalities between the exponents in `log t`, `log ε`,
`log η`:
* (i) for `ε t^{1/3} ≤ 1` it is `t^{−3/4} ≤ t^{−2/3}`; otherwise it is `log ε ≤ 0`;
* (ii) `(ε t^{1/3})³ = t ε³ ≤ 1`;
* (iii) for `t ε³ ≥ 1` the envelope is `(ε t^{1/3})^{−1/4}` and the three terms are at most
  `η^{−1/2}`, `η^{−1/3}`, `η^{−1/4}` times the weight, because `log t + 3 log ε ≥ 0`.
  The constant is `C = 8 η^{−1/2} + 18 η^{−1/3} + 38 η^{−1/4}`.
-/

namespace OscInt.A5UAux

open Real OscInt.Statements

/-- `(t^{1/3})³ = t` for `t ≥ 0`. -/
theorem a5uG2_cube_rpow_third {t : ℝ} (ht : 0 ≤ t) : (t ^ ((1 : ℝ) / 3)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- `log (ε t^{1/3}) = log ε + log t / 3` for `ε, t > 0`. -/
theorem a5uG2_log_scale {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    Real.log (ε * t ^ ((1 : ℝ) / 3)) = Real.log ε + Real.log t * (1 / 3) := by
  rw [Real.log_mul hε.ne' (Real.rpow_pos_of_pos ht _).ne', Real.log_rpow ht]
  ring

/-- A7(i): the complement bound `t^{−3/4} ≤ W`. -/
theorem a5uG2_env_i (ε t : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 1 ≤ t) :
    t ^ (-(3 : ℝ) / 4) ≤ t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  unfold crossEnvelope
  split_ifs with h
  · rw [mul_one]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  · have hεp : 0 < ε := by
      rcases hε0.lt_or_eq with h' | h'
      · exact h'
      · exfalso; apply h; rw [← h', zero_mul]; exact zero_le_one
    have hs : 0 < ε * t ^ ((1 : ℝ) / 3) := mul_pos hεp (Real.rpow_pos_of_pos ht0 _)
    rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos hs,
      a5uG2_log_scale hεp ht0, ← Real.exp_add, Real.exp_le_exp]
    have h1 : Real.log ε ≤ 0 := Real.log_nonpos hε0 hε1
    have h2 : 0 ≤ Real.log t := Real.log_nonneg ht
    nlinarith

/-- A7(ii): `E = 1` on the order-6 branch `t ε³ ≤ 1`. -/
theorem a5uG2_env_ii (ε t : ℝ) (hε0 : 0 ≤ ε) (ht : 0 < t) (h : t * ε ^ 3 ≤ 1) :
    crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) = 1 := by
  have hs : 0 ≤ ε * t ^ ((1 : ℝ) / 3) := mul_nonneg hε0 (Real.rpow_nonneg ht.le _)
  have h3 : (ε * t ^ ((1 : ℝ) / 3)) ^ 3 ≤ 1 := by
    rw [mul_pow, a5uG2_cube_rpow_third ht.le]
    linarith
  have h1 := (pow_le_one_iff_of_nonneg hs (by norm_num)).1 h3
  unfold crossEnvelope
  split_ifs with h2
  · rfl
  · exact absurd h1 h2

/-- On `t ε³ ≥ 1` the envelope is `(ε t^{1/3})^{−1/4}`. -/
theorem a5uG2_env_eq (ε t : ℝ) (hε : 0 < ε) (ht : 0 < t) (h : 1 ≤ t * ε ^ 3) :
    crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) = (ε * t ^ ((1 : ℝ) / 3)) ^ (-(1 : ℝ) / 4) := by
  have hs : 0 ≤ ε * t ^ ((1 : ℝ) / 3) := mul_nonneg hε.le (Real.rpow_nonneg ht.le _)
  have h1 : 1 ≤ ε * t ^ ((1 : ℝ) / 3) := by
    have h3 : 1 ≤ (ε * t ^ ((1 : ℝ) / 3)) ^ 3 := by
      rw [mul_pow, a5uG2_cube_rpow_third ht.le]
      linarith
    exact (one_le_pow_iff_of_nonneg hs (by norm_num)).1 h3
  unfold crossEnvelope
  split_ifs with h2
  · rw [le_antisymm h2 h1, Real.one_rpow]
  · rfl

/-- The exponential form of the weight on `t ε³ ≥ 1`. -/
theorem a5uG2_weight_exp (ε t : ℝ) (hε : 0 < ε) (ht : 0 < t) (h : 1 ≤ t * ε ^ 3) :
    t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3)) =
      Real.exp (Real.log t * (-(3 : ℝ) / 4) + Real.log ε * (-(1 : ℝ) / 4)) := by
  have hs : 0 < ε * t ^ ((1 : ℝ) / 3) := mul_pos hε (Real.rpow_pos_of_pos ht _)
  rw [a5uG2_env_eq ε t hε ht h, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hs,
    a5uG2_log_scale hε ht, ← Real.exp_add]
  congr 1
  ring

/-- `x^r = exp (log x * r)` with the logarithm of a product of positive factors split. -/
theorem a5uG2_rpow_mul3 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (r : ℝ) :
    (x * (y * z)) ^ r = Real.exp ((Real.log x + Real.log y + Real.log z) * r) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hx.ne' (by positivity), Real.log_mul hy.ne' hz.ne',
    add_assoc]

/-- `exp a * exp b ≤ exp c * exp d` from `a + b ≤ c + d`. -/
theorem a5uG2_exp_mul_le {a b c d : ℝ} (h : a + b ≤ c + d) :
    Real.exp a * Real.exp b ≤ Real.exp c * Real.exp d := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  exact h

/-- A7(iii): the three van der Corput terms are at most `C W`. -/
theorem a5uG2_env_iii (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, ∀ ε t : ℝ, 0 < ε → 1 ≤ t → 1 ≤ t * ε ^ 3 →
    t ^ (-(1 : ℝ) / 2) * (8 * (t * (η * ε ^ 2)) ^ (-(1 : ℝ) / 2) +
        18 * (t * (η * (ε * √ε))) ^ (-(1 : ℝ) / 3) + 38 * (t * (η * ε)) ^ (-(1 : ℝ) / 4)) ≤
      C * (t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3))) := by
  set n := Real.log η
  refine ⟨8 * Real.exp (n * (-(1 : ℝ) / 2)) + 18 * Real.exp (n * (-(1 : ℝ) / 3)) +
    38 * Real.exp (n * (-(1 : ℝ) / 4)), fun ε t hε ht h => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hsq : 0 < √ε := Real.sqrt_pos.2 hε
  have hl : 0 ≤ Real.log t + 3 * Real.log ε := by
    have := Real.log_nonneg h
    rwa [Real.log_mul ht0.ne' (by positivity), Real.log_pow] at this
  rw [a5uG2_weight_exp ε t hε ht0 h, Real.rpow_def_of_pos ht0, a5uG2_rpow_mul3 ht0 hη (by positivity),
    a5uG2_rpow_mul3 ht0 hη (by positivity), a5uG2_rpow_mul3 ht0 hη hε, Real.log_pow,
    Real.log_mul hε.ne' hsq.ne', Real.log_sqrt hε.le]
  set l := Real.log t
  set m := Real.log ε
  set w := l * (-(3 : ℝ) / 4) + m * (-(1 : ℝ) / 4)
  have e1 : Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + ((2 : ℕ) : ℝ) * m) * (-(1 : ℝ) / 2)) ≤
      Real.exp (n * (-(1 : ℝ) / 2)) * Real.exp w := a5uG2_exp_mul_le (by simp only [w]; push_cast; linarith)
  have e2 : Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + (m + m / 2)) * (-(1 : ℝ) / 3)) ≤
      Real.exp (n * (-(1 : ℝ) / 3)) * Real.exp w := a5uG2_exp_mul_le (by simp only [w]; linarith)
  have e3 : Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + m) * (-(1 : ℝ) / 4)) ≤
      Real.exp (n * (-(1 : ℝ) / 4)) * Real.exp w := a5uG2_exp_mul_le (by simp only [w]; linarith)
  calc _ = 8 * (Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + ((2 : ℕ) : ℝ) * m) * (-(1 : ℝ) / 2))) +
        18 * (Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + (m + m / 2)) * (-(1 : ℝ) / 3))) +
        38 * (Real.exp (l * (-(1 : ℝ) / 2)) * Real.exp ((l + n + m) * (-(1 : ℝ) / 4))) := by ring
    _ ≤ 8 * (Real.exp (n * (-(1 : ℝ) / 2)) * Real.exp w) + 18 * (Real.exp (n * (-(1 : ℝ) / 3)) * Real.exp w) +
        38 * (Real.exp (n * (-(1 : ℝ) / 4)) * Real.exp w) := by linarith
    _ = _ := by ring

/-- **A7** `CrossEnvelopeFacts`. -/
theorem crossEnvelopeFacts : OscInt.Blueprint.A5U.CrossEnvelopeFacts :=
  ⟨a5uG2_env_i, a5uG2_env_ii, a5uG2_env_iii⟩

end OscInt.A5UAux
