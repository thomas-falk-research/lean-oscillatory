/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TriangularAniso
import OscInt.Front.CuspSanity

/-! # Sanity theorems for batch TRI (TRI-K, TRI-X, TRI-W, TRI-Q)

Draft, written before the statements are stamped; no proof of a batch-TRI statement exists in this file or is used
by it. Two forms (`docs/lessons.md`, rules 8 and 9).

A. Unconditional, on closed data, through the definitions of `OscInt/Statements/TriangularAniso.lean`:
* The derivatives of `triPhase α` along a line (`triDiag`: `Dⁿ[aⁿ]` from `t ↦ cos(c + t b)`), and by polarisation
  `D²[u, v]` (`triD2_mixed`), `D³[v, v, w]` (`triD3_mixed`), `D⁴[a⁴]` (`triD4`).
* `triExceptional`: `a*² = 1/8`, `0 < a* < 1/2`, `arccos(−2a*) = 3π/4`, `arccos(2a*) = π/4`; values of `triPhase`.
* `IsA5Point`, `ReducedCurve`, `reducedFn` on the model `k₁² + k₂⁶` at `0` (`v = (0, 1)`, `w = (1, 0)`, `h = 0`,
  reduced sixth derivative `720`); bite: `k₁² + k₂⁴` with the same witness has reduced fourth derivative `24 ≠ 0`.
* One datum in each branch of TRI-K: A1 (`triPhase 1` at `0`, Hessian determinant `3`), A3 (`triPhase (1/4)` at
  `(π/2, π/2)`, reduced quartic `−12`), and, at `α = a*`, the point `(3π/4, −3π/4)`, which is neither A1/A2 nor A3
  (`kA5_not_foldOrNondeg`, `kA5_not_isA3`; the A5 property itself needs a reduced curve and is not proved here).
* Special cases of TRI-Q at `α = 1/4` computed exactly (`quarter_halfPi`, `quarter_theta`: `−12` and `−6`).
* Bites: `(3π/4, 3π/4)` at `a*` (Hessian `(√2/2)·I`) is not A5; `(π/2, π/2)` at `α = 0` (Hessian zero) is of none of
  the three types (the hypothesis `α ≠ 0` of TRI-K is needed).

B. Conditional, each statement constant as the only statement hypothesis (consistency theorems use two).

Planted copies: `plants/README.md` of the scratch work directory of the sanity agent (not in the repository).
-/

namespace OscInt.API.TriangularAnisoSanity

open OscInt.Statements OscInt.API.Poly OscInt.API.CuspSanity
open scoped ContDiff

/-! ## A. Derivatives of `triPhase` along lines -/

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

theorem triPhase_contDiff (α : ℝ) : ContDiff ℝ ω (triPhase α) := by
  unfold triPhase; fun_prop

theorem triDiag (α : ℝ) (n : ℕ) (k a : ℝ × ℝ) :
    iteratedFDeriv ℝ n (triPhase α) k (fun _ => a) = triLine α k a n 0 := by
  rw [iteratedFDeriv_diag_eq ((triPhase_contDiff α).of_le le_top), iteratedDeriv_triLine]

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


theorem cos_three_pi_div_four : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]

theorem sin_three_pi_div_four : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four]

/-- The A5 point of `+a*`. -/
noncomputable def kA5 : ℝ × ℝ := (3 * Real.pi / 4, -(3 * Real.pi / 4))

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem kA5_d2 (u v : ℝ × ℝ) : iteratedFDeriv ℝ 2 (triPhase triExceptional) kA5 ![u, v] =
    Real.sqrt 2 / 4 * (u.1 - u.2) * (v.1 - v.2) := by
  rw [triD2_mixed]
  simp only [kA5, add_neg_cancel, Real.cos_zero, Real.cos_neg, cos_three_pi_div_four, triExceptional_eq]
  ring

theorem kA5_d3 (v w : ℝ × ℝ) : iteratedFDeriv ℝ 3 (triPhase triExceptional) kA5 ![v, v, w] =
    Real.sqrt 2 / 2 * (v.1 ^ 2 * w.1 - v.2 ^ 2 * w.2) := by
  rw [triD3_mixed]
  simp only [kA5, add_neg_cancel, Real.sin_zero, Real.sin_neg, sin_three_pi_div_four]
  ring

theorem kA5_d4 (v : ℝ × ℝ) : iteratedFDeriv ℝ 4 (triPhase triExceptional) kA5 ![v, v, v, v] =
    Real.sqrt 2 / 2 * ((v.1 + v.2) ^ 4 / 2 - v.1 ^ 4 - v.2 ^ 4) := by
  rw [triD4]
  simp only [kA5, add_neg_cancel, Real.cos_zero, Real.cos_neg, cos_three_pi_div_four, triExceptional_eq]
  ring

theorem triPhase_c3 (α : ℝ) (k : ℝ × ℝ) : ContDiffAt ℝ 3 (triPhase α) k :=
  (triPhase_contDiff α).contDiffAt.of_le le_top

theorem triPhase_c2 (α : ℝ) (k : ℝ × ℝ) : ContDiffAt ℝ 2 (triPhase α) k :=
  (triPhase_contDiff α).contDiffAt.of_le le_top

/-- At `+a*` the point `(3π/4, −3π/4)` is neither A1/A2 (the Hessian is singular and the cubic vanishes on the
kernel vector `(1, 1)`) ... -/
theorem kA5_not_foldOrNondeg : ¬ FoldOrNondeg (triPhase triExceptional) kA5 := by
  have hd := OscInt.API.dd_iteratedFDeriv (triPhase triExceptional) kA5 (triPhase_c2 _ _)
  rintro (h | ⟨-, h⟩)
  · apply h
    rw [hessDet, hd, hd, hd, kA5_d2, kA5_d2, kA5_d2]
    ring
  · apply h (1, 1) (by simp) (fun w => by rw [hd, kA5_d2]; ring)
    rw [OscInt.API.ddd_iteratedFDeriv _ _ (triPhase_c3 _ _), kA5_d3]
    ring

/-- ... nor A3: on every kernel vector the reduced quartic vanishes. -/
theorem kA5_not_isA3 : ¬ IsA3Point (triPhase triExceptional) kA5 := by
  rintro ⟨v, w, hv, -, -, h4⟩
  have h1 := hv (1, 0)
  rw [kA5_d2] at h1
  have hv12 : v.1 = v.2 := by
    have hs : 0 < Real.sqrt 2 := by positivity
    have : Real.sqrt 2 / 4 * (v.1 - v.2) = 0 := by simpa using h1
    have := (mul_eq_zero.mp this).resolve_left (by positivity)
    linarith
  apply h4
  rw [kA5_d2, kA5_d4, kA5_d3, hv12]
  ring


theorem half_pi_add_half_pi : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring

/-- Values of `triPhase` at three points (generic `α` at the first two). -/
theorem triPhase_values (α : ℝ) :
    triPhase α (0, 0) = 2 + α ∧ triPhase α (Real.pi / 2, Real.pi / 2) = -α ∧
      triPhase triExceptional (3 * Real.pi / 4, -(3 * Real.pi / 4)) = -(3 * Real.sqrt 2 / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [triPhase, add_zero, Real.cos_zero]; ring
  · simp only [triPhase, half_pi_add_half_pi, Real.cos_pi_div_two, Real.cos_pi]; ring
  · simp only [triPhase, add_neg_cancel, Real.cos_zero, Real.cos_neg, cos_three_pi_div_four, triExceptional_eq]
    ring

/-- TRI-Q's first point at `α = 1/4`: kernel, cubic and the reduced quartic `−12`. -/
theorem quarter_halfPi :
    (∀ z, iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), z] = 0) ∧
      iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1)] = 0 ∧
      iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, 1), (1, 1)] = 1 ∧
      iteratedFDeriv ℝ 4 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1), (1, -1)] = 0 ∧
      iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, 1)] = 2 := by
  refine ⟨fun z => ?_, ?_, ?_, ?_, ?_⟩
  · rw [triD2_mixed]; simp only [half_pi_add_half_pi, Real.cos_pi_div_two, Real.cos_pi]; ring
  · rw [triD3_mixed]; simp only [half_pi_add_half_pi, Real.sin_pi_div_two, Real.sin_pi]; ring
  · rw [triD2_mixed]; simp only [half_pi_add_half_pi, Real.cos_pi_div_two, Real.cos_pi]; ring
  · rw [triD4]; simp only [half_pi_add_half_pi, Real.cos_pi_div_two, Real.cos_pi]; ring
  · rw [triD3_mixed]; simp only [half_pi_add_half_pi, Real.sin_pi_div_two, Real.sin_pi]; ring

theorem quarter_halfPi_quartic :
    iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, 1), (1, 1)] *
          iteratedFDeriv ℝ 4 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1), (1, -1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, 1)] ^ 2 = -12 := by
  obtain ⟨-, -, h2, h4, h3⟩ := quarter_halfPi
  rw [h2, h4, h3]; norm_num

/-- An A3 point (unconditional datum in the A3 branch of TRI-K). -/
theorem quarter_halfPi_isA3 : IsA3Point (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) := by
  obtain ⟨hk, h3, h2, -, -⟩ := quarter_halfPi
  exact ⟨(1, -1), (1, 1), hk, by rw [h2]; norm_num, h3, by rw [quarter_halfPi_quartic]; norm_num⟩

theorem cos_arccos_neg_half : Real.cos (Real.arccos (-2 * (1 / 4))) = -1 / 2 := by
  rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num

theorem sin_arccos_neg_half_sq : Real.sin (Real.arccos (-2 * (1 / 4))) ^ 2 = 3 / 4 := by
  rw [Real.sin_arccos, Real.sq_sqrt (by norm_num)]; norm_num

/-- TRI-Q's second point at `α = 1/4` (`θ = arccos(−1/2) = 2π/3`): kernel, cubic and the reduced quartic
`12(8/16 − 1) = −6`. -/
theorem quarter_theta :
    (∀ z, iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
        ![(1, 1), z] = 0) ∧
      iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
        ![(1, 1), (1, 1), (1, 1)] = 0 ∧
      iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, -1), (1, -1)] *
        iteratedFDeriv ℝ 4 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, 1), (1, 1), (1, 1), (1, 1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, 1), (1, 1), (1, -1)] ^ 2 = -6 := by
  refine ⟨fun z => ?_, ?_, ?_⟩
  · rw [triD2_mixed]; simp only [add_neg_cancel, Real.cos_zero, Real.cos_neg, cos_arccos_neg_half]; ring
  · rw [triD3_mixed]; simp only [add_neg_cancel, Real.sin_zero, Real.sin_neg]; ring
  · rw [triD2_mixed, triD4, triD3_mixed]
    simp only [add_neg_cancel, Real.cos_zero, Real.cos_neg, cos_arccos_neg_half, Real.sin_zero, Real.sin_neg]
    have := sin_arccos_neg_half_sq
    linear_combination (-12 : ℝ) * this

/-- An A1 datum: `triPhase 1` at `0` has Hessian determinant `3`. -/
theorem one_zero_hessDet : hessDet (triPhase 1) (0, 0) = 3 := by
  have hd := OscInt.API.dd_iteratedFDeriv (triPhase 1) (0, 0) (triPhase_c2 _ _)
  rw [hessDet, hd, hd, hd, triD2_mixed, triD2_mixed, triD2_mixed]
  simp only [add_zero, Real.cos_zero]; norm_num

theorem one_zero_foldOrNondeg : FoldOrNondeg (triPhase 1) (0, 0) :=
  Or.inl (by rw [one_zero_hessDet]; norm_num)

/-- `(3π/4, 3π/4)` at `+a*`: the Hessian is `(√2/2)·I`, so the only kernel vector is `0`; not an A5 point. -/
theorem kDiag_not_isA5 : ¬ IsA5Point (triPhase triExceptional) (3 * Real.pi / 4, 3 * Real.pi / 4) := by
  rintro ⟨v, w, hv0, hv, -⟩
  have e : 3 * Real.pi / 4 + 3 * Real.pi / 4 = Real.pi / 2 + Real.pi := by ring
  have h1 := hv (1, 0)
  have h2 := hv (0, 1)
  rw [triD2_mixed] at h1 h2
  simp only [e, Real.cos_add_pi, Real.cos_pi_div_two, cos_three_pi_div_four] at h1 h2
  have hs : 0 < Real.sqrt 2 := by positivity
  apply hv0
  have a : v.1 = 0 := by
    have : Real.sqrt 2 / 2 * v.1 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  have b : v.2 = 0 := by
    have : Real.sqrt 2 / 2 * v.2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  exact Prod.ext a b

/-- `(π/2, π/2)` at `α = 0` (a D4 point of `cos k₁ + cos k₂`): the Hessian is zero, so it is of none of the three
types (the bite of the hypothesis `α ≠ 0` of TRI-K). -/
theorem zero_halfPi_d2 (u v : ℝ × ℝ) : iteratedFDeriv ℝ 2 (triPhase 0) (Real.pi / 2, Real.pi / 2) ![u, v] = 0 := by
  rw [triD2_mixed]; simp only [Real.cos_pi_div_two]; ring

theorem zero_halfPi_none : ¬ (FoldOrNondeg (triPhase 0) (Real.pi / 2, Real.pi / 2) ∨
    IsA3Point (triPhase 0) (Real.pi / 2, Real.pi / 2) ∨ IsA5Point (triPhase 0) (Real.pi / 2, Real.pi / 2)) := by
  have hd := OscInt.API.dd_iteratedFDeriv (triPhase 0) (Real.pi / 2, Real.pi / 2) (triPhase_c2 _ _)
  rintro (h | ⟨v, w, -, h, -⟩ | ⟨v, w, -, -, h, -⟩)
  · rcases h with h | ⟨⟨v, w, h⟩, -⟩
    · apply h; rw [hessDet, hd, hd, hd, zero_halfPi_d2, zero_halfPi_d2, zero_halfPi_d2]; ring
    · exact h (by rw [hd, zero_halfPi_d2])
  · exact h (zero_halfPi_d2 _ _)
  · exact h (zero_halfPi_d2 _ _)


/-! ## The model A5 phase `k₁² + k₂⁶` and the bite `k₁² + k₂⁴` -/

/-- `k₁² + k₂^m`. -/
noncomputable def model (m : ℕ) (k : ℝ × ℝ) : ℝ := k.1 ^ 2 + k.2 ^ m

theorem model_hasFDerivAt (m : ℕ) (x : ℝ × ℝ) :
    HasFDerivAt (model m) ((2 • x.1 ^ (2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (m • x.2 ^ (m - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
  ((hasFDerivAt_fst).pow 2).add ((hasFDerivAt_snd).pow m)

theorem model_fderiv (m : ℕ) (x w : ℝ × ℝ) :
    fderiv ℝ (model m) x w = 2 * x.1 * w.1 + m * x.2 ^ (m - 1) * w.2 := by
  rw [(model_hasFDerivAt m x).fderiv]
  simp [nsmul_eq_mul]

theorem model_contDiff (m : ℕ) : ContDiff ℝ ω (model m) := by unfold model; fun_prop

theorem model_d2 (m : ℕ) (hm : 3 ≤ m) (a : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (model m) 0 ![a, a] = 2 * a.1 ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  rw [vec2_const, iteratedFDeriv_diag_eq ((model_contDiff _).of_le le_top)]
  have e : (fun t : ℝ => model (j + 3) (0 + t • a)) = fun t => a.1 ^ 2 * t ^ 2 + a.2 ^ (j + 3) * t ^ (j + 3) := by
    funext t; simp only [model, zero_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [e, iteratedDeriv_fun_add (by fun_prop) (by fun_prop), iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, iteratedDeriv_fun_pow_zero]
  simp; ring

/-- The model's Hessian kernel at `0` contains `(0, 1)` (and `model_d2` gives `D²[(1, 0), (1, 0)] = 2`). -/
theorem model_kernel (m : ℕ) (hm : 3 ≤ m) (z : ℝ × ℝ) : iteratedFDeriv ℝ 2 (model m) 0 ![(0, 1), z] = 0 := by
  rw [iteratedFDeriv_two_polar ((model_contDiff m).contDiffAt.of_le le_top), model_d2 m hm, model_d2 m hm,
    model_d2 m hm]
  simp

/-- The reduced function of the model along `h = 0`: `u ↦ u^m`. -/
theorem model_reducedFn (m : ℕ) (hm : 3 ≤ m) :
    reducedFn (model m) 0 (0, 1) (1, 0) (fun _ => 0) = fun u => u ^ m := by
  funext u
  rw [reducedFn, model_fderiv]
  simp [model]
  omega

theorem model_reducedCurve (m : ℕ) : ReducedCurve (model m) 0 (0, 1) (1, 0) 1 (fun _ => 0) := by
  refine ⟨contDiff_const, rfl, fun u _ => ?_⟩
  rw [model_fderiv, model_fderiv]
  simp

theorem model6_isA5 : IsA5Point (model 6) 0 := by
  refine ⟨(0, 1), (1, 0), by simp, model_kernel 6 (by norm_num), ?_, 1, one_pos, fun _ => 0,
    model_reducedCurve 6, fun j hj => ?_, ?_⟩
  · rw [model_d2 6 (by norm_num)]; norm_num
  · rw [model_reducedFn 6 (by norm_num), iteratedDeriv_fun_pow_zero]
    simp only [Finset.mem_Icc] at hj
    simp [show j ≠ 6 by omega]
  · rw [model_reducedFn 6 (by norm_num), iteratedDeriv_fun_pow_zero]
    norm_num [Nat.factorial]

theorem model6_sextic : iteratedDeriv 6 (reducedFn (model 6) 0 (0, 1) (1, 0) (fun _ => 0)) 0 = 720 := by
  rw [model_reducedFn 6 (by norm_num), iteratedDeriv_fun_pow_zero]
  norm_num [Nat.factorial]

/-- **Bite.** For `k₁² + k₂⁴` with the same `v`, `w`, `h`: the reduced fourth derivative is `24 ≠ 0`, so the
conditions of orders 1 to 5 fail for this witness. -/
theorem model4_quartic : iteratedDeriv 4 (reducedFn (model 4) 0 (0, 1) (1, 0) (fun _ => 0)) 0 = 24 := by
  rw [model_reducedFn 4 (by norm_num), iteratedDeriv_fun_pow_zero]
  norm_num [Nat.factorial]

theorem model4_fails : ¬ ∀ j ∈ Finset.Icc 1 5, iteratedDeriv j (reducedFn (model 4) 0 (0, 1) (1, 0) (fun _ => 0)) 0 = 0 :=
  fun h => by have := h 4 (by simp); rw [model4_quartic] at this; norm_num at this


/-! ## B. Through the statement constants (each the only statement hypothesis) -/

/-- **TRI-Q** at `α = 1/4`: the values `−12` (at `(π/2, π/2)`) and `12(8α² − 1) = −6` (at `(θ, −θ)`,
`θ = arccos(−1/2)`). -/
theorem triQ_quarter (h : TriQuarticStatement) :
    iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, 1), (1, 1)] *
          iteratedFDeriv ℝ 4 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1), (1, -1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, 1)] ^ 2 = -12 ∧
    iteratedFDeriv ℝ 2 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, -1), (1, -1)] *
        iteratedFDeriv ℝ 4 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, 1), (1, 1), (1, 1), (1, 1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (1 / 4)) (Real.arccos (-2 * (1 / 4)), -Real.arccos (-2 * (1 / 4)))
          ![(1, 1), (1, 1), (1, -1)] ^ 2 = -6 := by
  have h1 := h (1 / 4) (by norm_num)
  have h2 := h1.2 (by rw [abs_of_pos (by norm_num)]; norm_num)
  dsimp only at h2
  refine ⟨h1.1.2.2, ?_⟩
  rw [h2.2.2]; norm_num

/-- **TRI-Q** at `α = −1/3` (negative coupling): the values `−12` and `12(8/9 − 1) = −4/3`. -/
theorem triQ_neg_third (h : TriQuarticStatement) :
    iteratedFDeriv ℝ 2 (triPhase (-1 / 3)) (Real.pi / 2, Real.pi / 2) ![(1, 1), (1, 1)] *
          iteratedFDeriv ℝ 4 (triPhase (-1 / 3)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, -1), (1, -1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (-1 / 3)) (Real.pi / 2, Real.pi / 2) ![(1, -1), (1, -1), (1, 1)] ^ 2 = -12 ∧
    iteratedFDeriv ℝ 2 (triPhase (-1 / 3)) (Real.arccos (-2 * (-1 / 3)), -Real.arccos (-2 * (-1 / 3)))
          ![(1, -1), (1, -1)] *
        iteratedFDeriv ℝ 4 (triPhase (-1 / 3)) (Real.arccos (-2 * (-1 / 3)), -Real.arccos (-2 * (-1 / 3)))
          ![(1, 1), (1, 1), (1, 1), (1, 1)] -
        3 * iteratedFDeriv ℝ 3 (triPhase (-1 / 3)) (Real.arccos (-2 * (-1 / 3)), -Real.arccos (-2 * (-1 / 3)))
          ![(1, 1), (1, 1), (1, -1)] ^ 2 = -4 / 3 := by
  have h1 := h (-1 / 3) (by norm_num)
  have h2 := h1.2 (by rw [abs_of_neg (by norm_num)]; norm_num)
  dsimp only at h2
  refine ⟨h1.1.2.2, ?_⟩
  rw [h2.2.2]; norm_num

/-- **TRI-Q** at `α = a*`: the anti-diagonal reduced quartic at the A5 point is `0` (consistency with TRI-W). -/
theorem triQ_exceptional (h : TriQuarticStatement) :
    iteratedFDeriv ℝ 2 (triPhase triExceptional) kA5 ![(1, -1), (1, -1)] *
        iteratedFDeriv ℝ 4 (triPhase triExceptional) kA5 ![(1, 1), (1, 1), (1, 1), (1, 1)] -
      3 * iteratedFDeriv ℝ 3 (triPhase triExceptional) kA5 ![(1, 1), (1, 1), (1, -1)] ^ 2 = 0 := by
  have h2 := (h triExceptional triExceptional_pos.ne').2
    (by rw [abs_of_pos triExceptional_pos]; exact triExceptional_lt_half.le)
  dsimp only at h2
  rw [arccos_neg_two_triExceptional] at h2
  rw [kA5, h2.2.2, triExceptional_sq]; norm_num

/-- **TRI-X**, bite at `α = 1/2 ≠ a*`: `(π, π)` is not an A5 point. -/
theorem triX_half (h : TriA5LocusStatement) : ¬ IsA5Point (triPhase (1 / 2)) (Real.pi, Real.pi) := by
  intro hA
  have := (h _ _ hA).1
  rw [abs_of_pos (by norm_num)] at this
  exact absurd this triExceptional_lt_half.ne'

/-- **TRI-X**, bite: the isotropic phase `α = 1` has no A5 point at all. -/
theorem triX_one (h : TriA5LocusStatement) (k : ℝ × ℝ) : ¬ IsA5Point (triPhase 1) k := by
  intro hA
  have := (h _ _ hA).1
  rw [abs_one] at this
  linarith [triExceptional_lt_half]

/-- **TRI-X**, bite with a negative coupling: `α = −1/3` has no A5 point. -/
theorem triX_neg_third (h : TriA5LocusStatement) (k : ℝ × ℝ) : ¬ IsA5Point (triPhase (-1 / 3)) k := by
  intro hA
  have := (h _ _ hA).1
  rw [abs_of_neg (by norm_num)] at this
  have h8 := triExceptional_sq
  rw [← this] at h8
  norm_num at h8

/-- **TRI-W** at `α = +a*`: both points `(3π/4, −3π/4)` and `(−3π/4, 3π/4)` are A5 points. -/
theorem triW_pos (h : TriA5WitnessStatement) :
    IsA5Point (triPhase triExceptional) (3 * Real.pi / 4, -(3 * Real.pi / 4)) ∧
      IsA5Point (triPhase triExceptional) (-(3 * Real.pi / 4), 3 * Real.pi / 4) := by
  have := h triExceptional (abs_of_pos triExceptional_pos)
  rw [arccos_neg_two_triExceptional] at this
  exact ⟨this.1, this.2.1⟩

/-- **TRI-W** at `α = −a*`: both points `(π/4, −π/4)` and `(−π/4, π/4)` are A5 points. -/
theorem triW_neg (h : TriA5WitnessStatement) :
    IsA5Point (triPhase (-triExceptional)) (Real.pi / 4, -(Real.pi / 4)) ∧
      IsA5Point (triPhase (-triExceptional)) (-(Real.pi / 4), Real.pi / 4) := by
  have := h (-triExceptional) (by rw [abs_neg, abs_of_pos triExceptional_pos])
  rw [show -2 * -triExceptional = 2 * triExceptional by ring, arccos_two_triExceptional] at this
  exact ⟨this.1, this.2.1⟩

/-- **TRI-W**, the sextic at `+a*`: every reduced curve at `(3π/4, −3π/4)` gives `−60√2`. -/
theorem triW_sextic_pos (h : TriA5WitnessStatement) (ε : ℝ) (c : ℝ → ℝ) (hε : 0 < ε)
    (hc : ReducedCurve (triPhase triExceptional) (3 * Real.pi / 4, -(3 * Real.pi / 4)) (1, 1) (1, -1) ε c) :
    iteratedDeriv 6 (reducedFn (triPhase triExceptional) (3 * Real.pi / 4, -(3 * Real.pi / 4)) (1, 1) (1, -1) c) 0
      = -60 * Real.sqrt 2 := by
  have := (h triExceptional (abs_of_pos triExceptional_pos)).2.2 ε c hε
  rw [arccos_neg_two_triExceptional, sign_pos triExceptional_pos] at this
  simpa using this hc

/-- **TRI-W**, the sextic at `−a*`: every reduced curve at `(π/4, −π/4)` gives `+60√2` (the sign flips). -/
theorem triW_sextic_neg (h : TriA5WitnessStatement) (ε : ℝ) (c : ℝ → ℝ) (hε : 0 < ε)
    (hc : ReducedCurve (triPhase (-triExceptional)) (Real.pi / 4, -(Real.pi / 4)) (1, 1) (1, -1) ε c) :
    iteratedDeriv 6 (reducedFn (triPhase (-triExceptional)) (Real.pi / 4, -(Real.pi / 4)) (1, 1) (1, -1) c) 0
      = 60 * Real.sqrt 2 := by
  have := (h (-triExceptional) (by rw [abs_neg, abs_of_pos triExceptional_pos])).2.2 ε c hε
  rw [show -2 * -triExceptional = 2 * triExceptional by ring, arccos_two_triExceptional,
    sign_neg (neg_neg_of_pos triExceptional_pos)] at this
  simpa using this hc

/-- **TRI-K** at `α = 2` and `α = −1/3`, at two generic points: one of the three types. -/
theorem triK_generic (h : TriClassificationStatement) :
    (FoldOrNondeg (triPhase 2) (1 / 3, 2 / 5) ∨ IsA3Point (triPhase 2) (1 / 3, 2 / 5) ∨
        IsA5Point (triPhase 2) (1 / 3, 2 / 5)) ∧
      (FoldOrNondeg (triPhase (-1 / 3)) (2, -5 / 7) ∨ IsA3Point (triPhase (-1 / 3)) (2, -5 / 7) ∨
        IsA5Point (triPhase (-1 / 3)) (2, -5 / 7)) :=
  ⟨h 2 (by norm_num) _, h (-1 / 3) (by norm_num) _⟩

/-- **TRI-K** at `α = a*`: the point `(3π/4, −3π/4)`, neither A1/A2 nor A3 (unconditional), is an A5 point (a datum in
the A5 branch of the classification). -/
theorem triK_kA5 (h : TriClassificationStatement) : IsA5Point (triPhase triExceptional) kA5 := by
  rcases h _ triExceptional_pos.ne' kA5 with h1 | h1 | h1
  · exact absurd h1 kA5_not_foldOrNondeg
  · exact absurd h1 kA5_not_isA3
  · exact h1

/-- **TRI-K** with **TRI-X**: away from `|α| = a*` only A1/A2 or A3 remain, at `α = 2` and `α = −1/3`. -/
theorem triK_triX_generic (hK : TriClassificationStatement) (hX : TriA5LocusStatement) :
    (FoldOrNondeg (triPhase 2) (1 / 3, 2 / 5) ∨ IsA3Point (triPhase 2) (1 / 3, 2 / 5)) ∧
      (FoldOrNondeg (triPhase (-1 / 3)) (2, -5 / 7) ∨ IsA3Point (triPhase (-1 / 3)) (2, -5 / 7)) := by
  obtain ⟨h1, h2⟩ := triK_generic hK
  refine ⟨h1.elim Or.inl (fun h => h.elim Or.inr fun h5 => ?_), h2.elim Or.inl (fun h => h.elim Or.inr fun h5 => ?_)⟩
  · have := (hX _ _ h5).1
    rw [abs_of_pos (by norm_num)] at this
    linarith [triExceptional_lt_half]
  · exact absurd h5 (triX_neg_third hX _)

/-- **Consistency TRI-X with TRI-W**: the witness point of TRI-W lies on the locus of TRI-X, for both signs. -/
theorem triX_triW_consistent (hX : TriA5LocusStatement) (hW : TriA5WitnessStatement) (α : ℝ)
    (hα : |α| = triExceptional) :
    ∃ j₁ j₂ : ℤ,
      (Real.arccos (-2 * α), -Real.arccos (-2 * α)) =
          (Real.arccos (-2 * α) + 2 * Real.pi * j₁, -Real.arccos (-2 * α) + 2 * Real.pi * j₂) ∨
        (Real.arccos (-2 * α), -Real.arccos (-2 * α)) =
          (-Real.arccos (-2 * α) + 2 * Real.pi * j₁, Real.arccos (-2 * α) + 2 * Real.pi * j₂) :=
  (hX _ _ (hW α hα).1).2

/-- **Consistency TRI-K with TRI-X**: the A5 point that TRI-K forces at `(3π/4, −3π/4)` passes TRI-X's test
`|α| = a*`, and lies on its locus. -/
theorem triK_triX_consistent (hK : TriClassificationStatement) (hX : TriA5LocusStatement) :
    |triExceptional| = triExceptional ∧
      ∃ j₁ j₂ : ℤ,
        kA5 = (Real.arccos (-2 * triExceptional) + 2 * Real.pi * j₁,
            -Real.arccos (-2 * triExceptional) + 2 * Real.pi * j₂) ∨
          kA5 = (-Real.arccos (-2 * triExceptional) + 2 * Real.pi * j₁,
            Real.arccos (-2 * triExceptional) + 2 * Real.pi * j₂) :=
  hX _ _ (triK_kA5 hK)

end OscInt.API.TriangularAnisoSanity
