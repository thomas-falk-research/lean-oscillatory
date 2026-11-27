/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TriangularAniso
import OscInt.Front.Poly
import OscInt.Front.ConvertDeriv

/-! # Batch TRI, part P-deriv: explicit derivatives of `triPhase` (proof module)

`docs/proof-TRI.md`, section 0. The derivative lemmas of the sanity layer (`OscInt/Front/TriangularAnisoSanity.lean`,
section A) and the polarisation helpers of `OscInt/Front/CuspSanity.lean`, re-proved here in a proof module so that the
closure of the batch's theorems contains no sanity module (`docs/proof-TRI.md`, section 8). Same proofs, new names.
-/

namespace OscInt.API.TriDeriv

open OscInt.Statements OscInt.API.Poly OscInt.API.DerivAux
open scoped ContDiff

/-! ## Constant families and the polarisation of the third derivative -/

theorem vec2_const (a : ℝ × ℝ) : (![a, a] : Fin 2 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

theorem vec3_const (a : ℝ × ℝ) : (![a, a, a] : Fin 3 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

theorem vec4_const (a : ℝ × ℝ) : (![a, a, a, a] : Fin 4 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

theorem third_polar {f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f k) (v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 f k ![v, v, w] =
      (iteratedFDeriv ℝ 3 f k ![v + w, v + w, v + w] - iteratedFDeriv ℝ 3 f k ![v - w, v - w, v - w] -
        2 * iteratedFDeriv ℝ 3 f k ![w, w, w]) / 6 := by
  simp only [iter3_eq, map_add, map_sub, add_apply, sub_apply]
  set F := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) k
  have s12 := fun a b c => (symm3 hf a b c).1
  have s23 := fun a b c => (symm3 hf a b c).2
  have e1 : F v w v = F v v w := (s23 v v w).symm
  have e2 : F w v v = F v v w := by rw [s12 w v v, e1]
  have e3 : F w w v = F v w w := by rw [s23 w w v, s12 w v w]
  have e4 : F w v w = F v w w := s12 w v w
  linarith [e1, e2, e3, e4]

/-! ## Derivatives along lines -/

/-- `t ↦ b^n cos(c + t b + n π/2)`. -/
noncomputable def cosT (b c : ℝ) (n : ℕ) (t : ℝ) : ℝ := b ^ n * Real.cos (c + t * b + n * (Real.pi / 2))

theorem cosT_hasDerivAt (b c : ℝ) (n : ℕ) (t : ℝ) : HasDerivAt (cosT b c n) (cosT b c (n + 1) t) t := by
  have h1 : HasDerivAt (fun t => c + t * b + n * (Real.pi / 2)) b t := by
    simpa using (((hasDerivAt_id t).mul_const b).const_add c).add_const ((n : ℝ) * (Real.pi / 2))
  have := (h1.cos).const_mul (b ^ n)
  convert this using 1
  · rfl
  simp only [cosT]; push_cast
  rw [show c + t * b + ((n : ℝ) + 1) * (Real.pi / 2) = (c + t * b + n * (Real.pi / 2)) + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two]
  ring

theorem cosT_deriv (b c : ℝ) (n : ℕ) : deriv (cosT b c n) = cosT b c (n + 1) :=
  funext fun t => (cosT_hasDerivAt b c n t).deriv

/-- The line function of `triPhase`. -/
noncomputable def triLine (α : ℝ) (k a : ℝ × ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  cosT a.1 k.1 n t + cosT a.2 k.2 n t + α * cosT (a.1 + a.2) (k.1 + k.2) n t

theorem triLine_deriv (α : ℝ) (k a : ℝ × ℝ) (n : ℕ) : deriv (triLine α k a n) = triLine α k a (n + 1) := by
  funext t
  exact (((cosT_hasDerivAt _ _ n t).add (cosT_hasDerivAt _ _ n t)).add
    ((cosT_hasDerivAt _ _ n t).const_mul α)).deriv

theorem triLine_zero (α : ℝ) (k a : ℝ × ℝ) : (fun t : ℝ => triPhase α (k + t • a)) = triLine α k a 0 := by
  funext t
  simp only [triPhase, triLine, cosT, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
  ring_nf

theorem iteratedDeriv_triLine (α : ℝ) (k a : ℝ × ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => triPhase α (k + t • a)) = triLine α k a n := by
  induction n with
  | zero => simpa using triLine_zero α k a
  | succ n ih => rw [iteratedDeriv_succ, ih, triLine_deriv]

/-! ## Smoothness and the explicit forms -/

theorem triPhase_contDiff (α : ℝ) : ContDiff ℝ ω (triPhase α) := by
  unfold triPhase; fun_prop

theorem triPhase_smooth (α : ℝ) : ContDiff ℝ ∞ (triPhase α) := (triPhase_contDiff α).of_le le_top

theorem triDiag (α : ℝ) (n : ℕ) (k a : ℝ × ℝ) :
    iteratedFDeriv ℝ n (triPhase α) k (fun _ => a) = triLine α k a n 0 := by
  rw [iteratedFDeriv_diag_eq ((triPhase_contDiff α).of_le le_top), iteratedDeriv_triLine]

/-- `DΨ(k) a`. -/
theorem triD1 (α : ℝ) (k a : ℝ × ℝ) : fderiv ℝ (triPhase α) k a =
    -(a.1 * Real.sin k.1) - a.2 * Real.sin k.2 - α * ((a.1 + a.2) * Real.sin (k.1 + k.2)) := by
  have h := triDiag α 1 k a
  rw [iteratedFDeriv_one_apply] at h
  rw [h]
  simp only [triLine, cosT, zero_mul, add_zero, pow_one, Nat.cast_one, one_mul, Real.cos_add_pi_div_two]
  ring

theorem triD2 (α : ℝ) (k a : ℝ × ℝ) : iteratedFDeriv ℝ 2 (triPhase α) k ![a, a] =
    -(a.1 ^ 2 * Real.cos k.1) - a.2 ^ 2 * Real.cos k.2 - α * ((a.1 + a.2) ^ 2 * Real.cos (k.1 + k.2)) := by
  rw [vec2_const, triDiag]
  simp only [triLine, cosT, zero_mul, add_zero]
  push_cast
  simp only [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.cos_add_pi]
  ring

theorem triD3 (α : ℝ) (k a : ℝ × ℝ) : iteratedFDeriv ℝ 3 (triPhase α) k ![a, a, a] =
    a.1 ^ 3 * Real.sin k.1 + a.2 ^ 3 * Real.sin k.2 + α * ((a.1 + a.2) ^ 3 * Real.sin (k.1 + k.2)) := by
  rw [vec3_const, triDiag]
  simp only [triLine, cosT, zero_mul, add_zero]
  push_cast
  have e : ∀ x : ℝ, Real.cos (x + 3 * (Real.pi / 2)) = Real.sin x := by
    intro x
    rw [show x + 3 * (Real.pi / 2) = (x + Real.pi) + Real.pi / 2 by ring, Real.cos_add_pi_div_two, Real.sin_add_pi]
    ring
  simp only [e]

theorem triD4 (α : ℝ) (k a : ℝ × ℝ) : iteratedFDeriv ℝ 4 (triPhase α) k ![a, a, a, a] =
    a.1 ^ 4 * Real.cos k.1 + a.2 ^ 4 * Real.cos k.2 + α * ((a.1 + a.2) ^ 4 * Real.cos (k.1 + k.2)) := by
  rw [vec4_const, triDiag]
  simp only [triLine, cosT, zero_mul, add_zero]
  push_cast
  simp only [show (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi by ring, Real.cos_add_two_pi]

theorem triD2_mixed (α : ℝ) (k u v : ℝ × ℝ) : iteratedFDeriv ℝ 2 (triPhase α) k ![u, v] =
    -(u.1 * v.1 * Real.cos k.1) - u.2 * v.2 * Real.cos k.2 - α * ((u.1 + u.2) * (v.1 + v.2) * Real.cos (k.1 + k.2)) := by
  rw [iteratedFDeriv_two_polar ((triPhase_contDiff α).contDiffAt.of_le le_top), triD2, triD2, triD2]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem triD3_mixed (α : ℝ) (k v w : ℝ × ℝ) : iteratedFDeriv ℝ 3 (triPhase α) k ![v, v, w] =
    v.1 ^ 2 * w.1 * Real.sin k.1 + v.2 ^ 2 * w.2 * Real.sin k.2 +
      α * ((v.1 + v.2) ^ 2 * (w.1 + w.2) * Real.sin (k.1 + k.2)) := by
  rw [third_polar ((triPhase_contDiff α).contDiffAt.of_le le_top), triD3, triD3, triD3]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-! ## The exceptional coupling -/

theorem triExceptional_sq : triExceptional ^ 2 = 1 / 8 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [triExceptional, div_pow, mul_pow, h]; norm_num

theorem triExceptional_eq : triExceptional = Real.sqrt 2 / 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  rw [triExceptional]; field_simp; nlinarith

theorem triExceptional_pos : 0 < triExceptional := by rw [triExceptional]; positivity

theorem triExceptional_lt_half : triExceptional < 1 / 2 := by
  have := triExceptional_sq
  nlinarith [triExceptional_pos]

theorem two_triExceptional : 2 * triExceptional = Real.sqrt 2 / 2 := by rw [triExceptional_eq]; ring

theorem arccos_two_triExceptional : Real.arccos (2 * triExceptional) = Real.pi / 4 := by
  rw [two_triExceptional, ← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem arccos_neg_two_triExceptional : Real.arccos (-2 * triExceptional) = 3 * Real.pi / 4 := by
  rw [neg_mul, Real.arccos_neg, arccos_two_triExceptional]; ring

end OscInt.API.TriDeriv
