/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriBlueprint
import OscInt.Front.TriDeriv
import OscInt.Front.ConvertDeriv
import Mathlib

/-! # Batch TRI, part P-alg (with P-EG): the algebraic classification of `triPhase α`

`docs/proof-TRI.md`, sections 1, 2, 3 and 9 (items 4, 5). Lemma P-EG (section 3) is `eg_false`. The point `k = (x, y)`
is written in half-angle variables `c = cos s`, `l = sin s`, `d = cos σ`, `m = sin σ` with `s = (x + y)/2`,
`σ = (x − y)/2` (`HalfAngle`), so that every derivative of section 0 is a polynomial in `c, l, d, m, α`; the identities
(I1)–(I5) of section 1 are `linear_combination`s modulo the two circle relations, with cofactors computed by SymPy
Gröbner reduction. The kernel vector is `V = (cd + lm, cd − lm) = (cos y, cos x)` and `W = (1, −1)`.
-/

namespace OscInt.API.TriAlg

open OscInt.Statements OscInt.API.TriDeriv OscInt.API.TriBlueprint
open scoped ContDiff

/-! ## P-EG (section 3) -/

/-- `E = 0`, `G = 0`, `0 < P < 1`, `0 < Q ≤ 1` is impossible (`docs/proof-TRI.md`, section 3). -/
theorem eg_false (P Q : ℝ) (hP0 : 0 < P) (hP1 : P < 1) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (hE : 2 * P ^ 2 + 8 * P * Q ^ 2 - 4 * P * Q - 3 * P - 2 * Q ^ 2 + Q + 1 = 0)
    (hG : 2 * P ^ 2 * Q - P ^ 2 - 2 * P * Q + 2 * P + 2 * Q ^ 3 - Q ^ 2 - 1 = 0) : False := by
  rcases eq_or_lt_of_le hQ1 with rfl | hQ1'
  · nlinarith
  rcases lt_trichotomy Q (1 / 2) with hQh | rfl | hQh
  · -- 0 < Q < 1/2
    have hBN : (16 * Q ^ 2 * (1 - Q) + 1 - 2 * Q) * P = (1 - Q) * (8 * Q ^ 2 + 2 * Q + 1) := by
      linear_combination 2 * hG - (2 * Q - 1) * hE
    have hN : 0 < (1 - Q) * (8 * Q ^ 2 + 2 * Q + 1) := by
      apply mul_pos <;> nlinarith
    have hB : 0 < 16 * Q ^ 2 * (1 - Q) + 1 - 2 * Q := by
      by_contra hB
      have hB' := not_lt.mp hB
      nlinarith
    have hNB : 0 < Q * (3 - 4 * Q) * (1 - 2 * Q) := by
      apply mul_pos
      · apply mul_pos <;> linarith
      · linarith
    nlinarith
  · nlinarith
  · have hBN : (16 * Q ^ 2 * (1 - Q) + 1 - 2 * Q) * P = (1 - Q) * (8 * Q ^ 2 + 2 * Q + 1) := by
      linear_combination 2 * hG - (2 * Q - 1) * hE
    have hN : 0 < (1 - Q) * (8 * Q ^ 2 + 2 * Q + 1) := by
      apply mul_pos <;> nlinarith
    have hB : 0 < 16 * Q ^ 2 * (1 - Q) + 1 - 2 * Q := by
      by_contra hB
      have hB' := not_lt.mp hB
      nlinarith
    have hF0 : 8 * Q ^ 2 * (Q - 1) * (2 * Q - 1) * (32 * Q ^ 4 - 16 * Q ^ 3 - 8 * Q ^ 2 - 8 * Q + 1) = 0 := by
      linear_combination (16 * Q ^ 2 * (1 - Q) + 1 - 2 * Q) ^ 2 * hE -
        (-32 * P * Q ^ 3 + 32 * P * Q ^ 2 - 4 * P * Q + 2 * P - 128 * Q ^ 5 + 192 * Q ^ 4 - 48 * Q ^ 3 -
          20 * Q ^ 2 + 4 * Q - 1) * hBN
    have hF : 32 * Q ^ 4 - 16 * Q ^ 3 - 8 * Q ^ 2 - 8 * Q + 1 = 0 := by
      have h1 : 8 * Q ^ 2 * (Q - 1) * (2 * Q - 1) ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) (by linarith)
      exact (mul_eq_zero.mp hF0).resolve_left h1
    rcases lt_or_ge Q (19 / 20) with hQ2 | hQ2
    · -- the rational certificate (I7)
      have hcert : (9 / 20 : ℝ) ^ 4 * (32 * Q ^ 4 - 16 * Q ^ 3 - 8 * Q ^ 2 - 8 * Q + 1) =
          -(5 * (19 / 20 - Q) ^ 4 + 127 / 5 * (19 / 20 - Q) ^ 3 * (Q - 1 / 2) +
            1074 / 25 * (19 / 20 - Q) ^ 2 * (Q - 1 / 2) ^ 2 + 12673 / 500 * (19 / 20 - Q) * (Q - 1 / 2) ^ 3 +
            7369 / 5000 * (Q - 1 / 2) ^ 4) := by ring
      have hh : 0 < 19 / 20 - Q := by linarith
      have hk : 0 < Q - 1 / 2 := by linarith
      have hpos : 0 < 5 * (19 / 20 - Q) ^ 4 + 127 / 5 * (19 / 20 - Q) ^ 3 * (Q - 1 / 2) +
            1074 / 25 * (19 / 20 - Q) ^ 2 * (Q - 1 / 2) ^ 2 + 12673 / 500 * (19 / 20 - Q) * (Q - 1 / 2) ^ 3 +
            7369 / 5000 * (Q - 1 / 2) ^ 4 := by positivity
      rw [hF, mul_zero] at hcert
      linarith
    · nlinarith

/-! ## Half-angle variables -/

/-- The half-angle data of a point `k`: `c = cos s`, `l = sin s`, `d = cos σ`, `m = sin σ`. -/
structure HalfAngle (k : ℝ × ℝ) (c l d m : ℝ) : Prop where
  hcl : c ^ 2 + l ^ 2 = 1
  hdm : d ^ 2 + m ^ 2 = 1
  cx : Real.cos k.1 = c * d - l * m
  sx : Real.sin k.1 = l * d + c * m
  cy : Real.cos k.2 = c * d + l * m
  sy : Real.sin k.2 = l * d - c * m
  cxy : Real.cos (k.1 + k.2) = 2 * c ^ 2 - 1
  sxy : Real.sin (k.1 + k.2) = 2 * l * c
  per : l = 0 → ∃ n : ℤ, k.1 + k.2 = 2 * Real.pi * n

theorem halfAngle_aux (s σ : ℝ) :
    HalfAngle (s + σ, s - σ) (Real.cos s) (Real.sin s) (Real.cos σ) (Real.sin σ) where
  hcl := Real.cos_sq_add_sin_sq s
  hdm := Real.cos_sq_add_sin_sq σ
  cx := by simp only [Real.cos_add]
  sx := by simp only [Real.sin_add]
  cy := by simp only [Real.cos_sub]
  sy := by simp only [Real.sin_sub]
  cxy := by
    simp only [show s + σ + (s - σ) = 2 * s by ring, Real.cos_two_mul]
  sxy := by
    simp only [show s + σ + (s - σ) = 2 * s by ring, Real.sin_two_mul]
  per := by
    intro hl
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hl
    exact ⟨n, by simp only; rw [← hn]; ring⟩

theorem halfAngle (k : ℝ × ℝ) : ∃ c l d m : ℝ, HalfAngle k c l d m := by
  have h := halfAngle_aux ((k.1 + k.2) / 2) ((k.1 - k.2) / 2)
  have e : ((k.1 + k.2) / 2 + (k.1 - k.2) / 2, (k.1 + k.2) / 2 - (k.1 - k.2) / 2) = k := by
    ext <;> simp only <;> ring
  rw [e] at h
  exact ⟨_, _, _, _, h⟩

/-! ## The polynomials of section 0 -/

/-- `D = P + Q − 1 + 2αcd(2P − 1)`. -/
noncomputable def Dp (α c d : ℝ) : ℝ := c ^ 2 + d ^ 2 - 1 + 2 * α * c * d * (2 * c ^ 2 - 1)

/-- `R = 8αc³d³ + 2PQ − P − 2Q² + Q + 1`. -/
noncomputable def Rp (α c d : ℝ) : ℝ :=
  8 * α * c ^ 3 * d ^ 3 + 2 * c ^ 2 * d ^ 2 - c ^ 2 - 2 * (d ^ 2) ^ 2 + d ^ 2 + 1

/-- `E = 2P² + 8PQ² − 4PQ − 3P − 2Q² + Q + 1`. -/
noncomputable def Ep (c d : ℝ) : ℝ :=
  2 * (c ^ 2) ^ 2 + 8 * c ^ 2 * (d ^ 2) ^ 2 - 4 * c ^ 2 * d ^ 2 - 3 * c ^ 2 - 2 * (d ^ 2) ^ 2 + d ^ 2 + 1

/-- `G = 2P²Q − P² − 2PQ + 2P + 2Q³ − Q² − 1`. -/
noncomputable def Gp (c d : ℝ) : ℝ :=
  2 * (c ^ 2) ^ 2 * d ^ 2 - (c ^ 2) ^ 2 - 2 * c ^ 2 * d ^ 2 + 2 * c ^ 2 + 2 * (d ^ 2) ^ 3 - (d ^ 2) ^ 2 - 1

/-- (I4) `(2P − 1)R − 4PQ·D + E = 0`. -/
theorem I4 (α c d : ℝ) : (2 * c ^ 2 - 1) * Rp α c d - 4 * c ^ 2 * d ^ 2 * Dp α c d + Ep c d = 0 := by
  unfold Rp Dp Ep; ring

/-! ## Multilinearity of the explicit forms (no half-angle variables) -/

section Lin

variable (α : ℝ) (k : ℝ × ℝ)

theorem lin2 (a b : ℝ × ℝ) (μ ν : ℝ) :
    iteratedFDeriv ℝ 2 (triPhase α) k ![μ • a + ν • b, μ • a + ν • b] =
      μ ^ 2 * iteratedFDeriv ℝ 2 (triPhase α) k ![a, a] +
        2 * μ * ν * iteratedFDeriv ℝ 2 (triPhase α) k ![b, a] +
        ν ^ 2 * iteratedFDeriv ℝ 2 (triPhase α) k ![b, b] := by
  simp only [triD2_mixed, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem lin3 (a b : ℝ × ℝ) (t μ ν : ℝ) :
    iteratedFDeriv ℝ 3 (triPhase α) k ![t • a, t • a, μ • b + ν • a] =
      t ^ 2 * (μ * iteratedFDeriv ℝ 3 (triPhase α) k ![a, a, b] +
        ν * iteratedFDeriv ℝ 3 (triPhase α) k ![a, a, a]) := by
  simp only [triD3_mixed, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem lin3d (a : ℝ × ℝ) (t : ℝ) :
    iteratedFDeriv ℝ 3 (triPhase α) k ![t • a, t • a, t • a] =
      t ^ 3 * iteratedFDeriv ℝ 3 (triPhase α) k ![a, a, a] := by
  simp only [triD3_mixed, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem lin4 (a : ℝ × ℝ) (t : ℝ) :
    iteratedFDeriv ℝ 4 (triPhase α) k ![t • a, t • a, t • a, t • a] =
      t ^ 4 * iteratedFDeriv ℝ 4 (triPhase α) k ![a, a, a, a] := by
  simp only [triD4, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

end Lin

/-! ## The identities of section 1 in half-angle variables -/

section Ids

variable {α : ℝ} {k : ℝ × ℝ} {c l d m : ℝ}

theorem d2h (H : HalfAngle k c l d m) (a b : ℝ × ℝ) : iteratedFDeriv ℝ 2 (triPhase α) k ![a, b] =
    -(a.1 * b.1 * (c * d - l * m)) - a.2 * b.2 * (c * d + l * m) -
      α * ((a.1 + a.2) * (b.1 + b.2) * (2 * c ^ 2 - 1)) := by
  rw [triD2_mixed, H.cx, H.cy, H.cxy]

theorem d3h (H : HalfAngle k c l d m) (a b : ℝ × ℝ) : iteratedFDeriv ℝ 3 (triPhase α) k ![a, a, b] =
    a.1 ^ 2 * b.1 * (l * d + c * m) + a.2 ^ 2 * b.2 * (l * d - c * m) +
      α * ((a.1 + a.2) ^ 2 * (b.1 + b.2) * (2 * l * c)) := by
  rw [triD3_mixed, H.sx, H.sy, H.sxy]

theorem d4h (H : HalfAngle k c l d m) (a : ℝ × ℝ) : iteratedFDeriv ℝ 4 (triPhase α) k ![a, a, a, a] =
    a.1 ^ 4 * (c * d - l * m) + a.2 ^ 4 * (c * d + l * m) + α * ((a.1 + a.2) ^ 4 * (2 * c ^ 2 - 1)) := by
  rw [triD4, H.cx, H.cy, H.cxy]

/-- (I1) `hessDet = D`, in the `iteratedFDeriv` form. -/
theorem vHess (H : HalfAngle k c l d m) :
    iteratedFDeriv ℝ 2 (triPhase α) k ![(1, 0), (1, 0)] * iteratedFDeriv ℝ 2 (triPhase α) k ![(0, 1), (0, 1)] -
      iteratedFDeriv ℝ 2 (triPhase α) k ![(1, 0), (0, 1)] ^ 2 = Dp α c d := by
  simp only [d2h H, Dp]
  linear_combination (-m ^ 2) * H.hcl + ((c - 1) * (c + 1)) * H.hdm

/-- `D²[W, W] = −2cd`. -/
theorem vW (H : HalfAngle k c l d m) :
    iteratedFDeriv ℝ 2 (triPhase α) k ![(1, -1), (1, -1)] = -2 * c * d := by
  simp only [d2h H]; ring

/-- (I2) `D²[V, z] = −D (z₁ + z₂)`. -/
theorem vVz (H : HalfAngle k c l d m) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (triPhase α) k ![(c * d + l * m, c * d - l * m), z] = -Dp α c d * (z.1 + z.2) := by
  simp only [d2h H, Dp]
  linear_combination (m ^ 2 * (z.1 + z.2)) * H.hcl + (-(c - 1) * (c + 1) * (z.1 + z.2)) * H.hdm

/-- (I3) `D³[V, V, V] = 2lc R`. -/
theorem vT (H : HalfAngle k c l d m) :
    iteratedFDeriv ℝ 3 (triPhase α) k
        ![(c * d + l * m, c * d - l * m), (c * d + l * m, c * d - l * m), (c * d + l * m, c * d - l * m)] =
      2 * l * c * Rp α c d := by
  simp only [d3h H, Rp]
  linear_combination (2 * c * l * m ^ 2 * (3 * d ^ 2 + m ^ 2)) * H.hcl +
    (2 * c * l * (c ^ 2 * d ^ 2 - c ^ 2 * m ^ 2 - c ^ 2 + 2 * d ^ 2 + m ^ 2 + 1)) * H.hdm

/-- (I5) `2cd D⁴[V⁴] + 3 (D³[V, V, W])² = −12P G + 16P²Q² D`. -/
theorem vQ (H : HalfAngle k c l d m) :
    2 * c * d * iteratedFDeriv ℝ 4 (triPhase α) k
        ![(c * d + l * m, c * d - l * m), (c * d + l * m, c * d - l * m), (c * d + l * m, c * d - l * m),
          (c * d + l * m, c * d - l * m)] +
      3 * iteratedFDeriv ℝ 3 (triPhase α) k
        ![(c * d + l * m, c * d - l * m), (c * d + l * m, c * d - l * m), (1, -1)] ^ 2 =
      -12 * c ^ 2 * Gp c d + 16 * c ^ 4 * d ^ 4 * Dp α c d := by
  simp only [d3h H, d4h H, Gp, Dp]
  linear_combination (4 * c ^ 2 * m ^ 2 * (2 * c ^ 2 * d ^ 4 - 3 * c ^ 2 * d ^ 2 * m ^ 2 - 3 * c ^ 2 * m ^ 4 +
      12 * d ^ 4 * l ^ 2 + 12 * d ^ 4 + 9 * d ^ 2 * l ^ 2 * m ^ 2 + 9 * d ^ 2 * m ^ 2 + 3 * l ^ 2 * m ^ 4 +
      3 * m ^ 4)) * H.hcl +
    (4 * c ^ 2 * (c ^ 4 * d ^ 4 - 3 * c ^ 4 * d ^ 2 + 3 * c ^ 4 * m ^ 4 + 3 * c ^ 4 * m ^ 2 + 3 * c ^ 4 -
      4 * c ^ 2 * d ^ 4 - 6 * c ^ 2 * d ^ 2 * m ^ 2 - 6 * c ^ 2 * m ^ 4 - 6 * c ^ 2 * m ^ 2 - 6 * c ^ 2 +
      6 * d ^ 4 + 6 * d ^ 2 * m ^ 2 + 3 * d ^ 2 + 3 * m ^ 4 + 3 * m ^ 2 + 3)) * H.hdm

end Ids

/-! ## The locus (section 2, case 5(c) with `2Q = 1`) -/

section Cases

variable {α : ℝ} {k : ℝ × ℝ} {c l d m : ℝ}

theorem locus_of (H : HalfAngle k c l d m) (hD : Dp α c d = 0) (hd : d ≠ 0) (hl : l = 0)
    (hQ : 2 * d ^ 2 = 1) : |α| = triExceptional ∧ InLocus α k := by
  have hc2 : c ^ 2 = 1 := by have := H.hcl; rw [hl] at this; linarith
  have hdd : d = -2 * α * c := by
    have h : d * (d + 2 * α * c) = 0 := by
      unfold Dp at hD; linear_combination hD - (1 + 4 * α * c * d) * hc2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hd
    · linarith
  have hα2 : α ^ 2 = 1 / 8 := by
    linear_combination (-α ^ 2) * hc2 + (-1 / 4) * (d - 2 * α * c) * hdd + (1 / 8) * hQ
  have habs : |α| = triExceptional := by
    rw [← abs_of_pos triExceptional_pos]
    exact (sq_eq_sq_iff_abs_eq_abs _ _).mp (by rw [hα2, triExceptional_sq])
  refine ⟨habs, ?_⟩
  have hcos : Real.cos k.1 = -2 * α := by
    rw [H.cx, hl, hdd]; linear_combination (-2 * α) * hc2
  obtain ⟨n, hn⟩ := H.per hl
  have hθ : Real.cos (Real.arccos (-2 * α)) = -2 * α := Real.cos_arccos (by nlinarith) (by nlinarith)
  obtain ⟨j, hj | hj⟩ := Real.cos_eq_cos_iff.mp (hθ.trans hcos.symm)
  · refine ⟨j, n - j, Or.inl (Prod.ext ?_ ?_)⟩
    · dsimp only; rw [hj]; ring
    · dsimp only; push_cast; linarith
  · refine ⟨j, n - j, Or.inr (Prod.ext ?_ ?_)⟩
    · dsimp only; rw [hj]; ring
    · dsimp only; push_cast; linarith

/-- Section 2, case 5 with vanishing cubic and `G = 0`: case (b) is impossible (P-EG), case (c) is the locus. -/
theorem locus_of_G (H : HalfAngle k c l d m) (hD : Dp α c d = 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hT : l * Rp α c d = 0) (hG : Gp c d = 0) : |α| = triExceptional ∧ InLocus α k := by
  by_cases hl : l = 0
  · apply locus_of H hD hd hl
    have hc2 : c ^ 2 = 1 := by have := H.hcl; rw [hl] at this; linarith
    have h : (d ^ 2) ^ 2 * (2 * d ^ 2 - 1) = 0 := by
      unfold Gp at hG; rw [hc2] at hG; linear_combination hG
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp (pow_eq_zero_iff two_ne_zero |>.mp h)) hd
    · linarith
  · exfalso
    have hR : Rp α c d = 0 := (mul_eq_zero.mp hT).resolve_left hl
    have hE : Ep c d = 0 := by have := I4 α c d; rw [hR, hD] at this; linarith
    have hl2 : 0 < l ^ 2 := lt_of_le_of_ne (sq_nonneg l) (Ne.symm (pow_ne_zero 2 hl))
    have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))
    have hd2 : 0 < d ^ 2 := lt_of_le_of_ne (sq_nonneg d) (Ne.symm (pow_ne_zero 2 hd))
    unfold Ep at hE
    unfold Gp at hG
    exact eg_false (c ^ 2) (d ^ 2) hc2 (by linarith [H.hcl]) hd2 (by nlinarith [H.hdm, sq_nonneg m]) hE hG

/-! ## Kernel vectors (section 2, case 5) -/

theorem ker_param (H : HalfAngle k c l d m) (hc : c ≠ 0) (hd : d ≠ 0) (v : ℝ × ℝ)
    (hW : iteratedFDeriv ℝ 2 (triPhase α) k ![v, (1, -1)] = 0) (hv : v ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ v = t • (c * d + l * m, c * d - l * m) := by
  rw [d2h H] at hW
  have key : v.2 * (c * d + l * m) = v.1 * (c * d - l * m) := by linear_combination hW
  have hcd : 2 * c * d ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hd
  have e1 : v.1 * (2 * c * d) = (v.1 + v.2) * (c * d + l * m) := by linear_combination (-1 : ℝ) * key
  have e2 : v.2 * (2 * c * d) = (v.1 + v.2) * (c * d - l * m) := by linear_combination key
  refine ⟨(v.1 + v.2) / (2 * c * d), ?_, ?_⟩
  · intro h0
    have hs : v.1 + v.2 = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · exact absurd h hcd
    rw [hs, zero_mul] at e1 e2
    apply hv
    exact Prod.ext ((mul_eq_zero.mp e1).resolve_right hcd) ((mul_eq_zero.mp e2).resolve_right hcd)
  · refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hcd]; exact e1
    · simp only [Prod.smul_snd, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hcd]; exact e2

theorem w_param (hc : c ≠ 0) (hd : d ≠ 0) (w : ℝ × ℝ) :
    ∃ μ ν : ℝ, w = μ • ((1 : ℝ), (-1 : ℝ)) + ν • (c * d + l * m, c * d - l * m) := by
  have hcd : 2 * c * d ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hd
  refine ⟨(w.1 * (c * d - l * m) - w.2 * (c * d + l * m)) / (2 * c * d), (w.1 + w.2) / (2 * c * d), ?_⟩
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring

end Cases

/-! ## The classification and the A5 conditions (section 2) -/

theorem c2 (α : ℝ) (k : ℝ × ℝ) : ContDiffAt ℝ 2 (triPhase α) k :=
  (triPhase_contDiff α).contDiffAt.of_le le_top

theorem c3 (α : ℝ) (k : ℝ × ℝ) : ContDiffAt ℝ 3 (triPhase α) k :=
  (triPhase_contDiff α).contDiffAt.of_le le_top

section Main

variable {α : ℝ} {k : ℝ × ℝ} {c l d m : ℝ}

/-- Case 3: `D = 0`, `d = 0`. -/
theorem fold_d0 (hα : α ≠ 0) (H : HalfAngle k c l d m) (hD : Dp α c d = 0) (hd : d = 0) :
    FoldOrNondeg (triPhase α) k := by
  subst hd
  have hc2 : c ^ 2 = 1 := by unfold Dp at hD; linear_combination hD
  have hl : l = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination H.hcl - hc2)
  subst hl
  have hm2 : m ^ 2 = 1 := by linear_combination H.hdm
  have hdd := OscInt.API.dd_iteratedFDeriv (triPhase α) k (c2 α k)
  right
  refine ⟨⟨(1, 0), (1, 0), ?_⟩, fun v hv hker => ?_⟩
  · rw [hdd, d2h H]
    intro h; apply hα
    linear_combination (-1 : ℝ) * h + (-2 * α) * hc2
  · have h1 := hker (1, 0)
    rw [hdd, d2h H] at h1
    obtain ⟨a, b⟩ := v
    have hs : α * (a + b) = 0 := by
      dsimp only at h1; linear_combination (-1 : ℝ) * h1 + (-2 * α * (a + b)) * hc2
    have hb : b = -a := by have := (mul_eq_zero.mp hs).resolve_left hα; linarith
    subst hb
    have ha : a ≠ 0 := by
      intro ha; apply hv; subst ha; simp
    rw [OscInt.API.ddd_iteratedFDeriv _ _ (c3 α k), d3h H]
    dsimp only
    have hc : c ≠ 0 := by intro h; rw [h] at hc2; norm_num at hc2
    have hm : m ≠ 0 := by intro h; rw [h] at hm2; norm_num at hm2
    have : a ^ 2 * a * (0 * 0 + c * m) + (-a) ^ 2 * (-a) * (0 * 0 - c * m) +
        α * ((a + -a) ^ 2 * (a + -a) * (2 * 0 * c)) = 2 * c * m * a ^ 3 := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hm) (pow_ne_zero 3 ha)

/-- Case 4: `D = 0`, `c = 0`. -/
theorem a3_c0 (hα : α ≠ 0) (H : HalfAngle k c l d m) (hD : Dp α c d = 0) (hc : c = 0) :
    IsA3Point (triPhase α) k := by
  subst hc
  have hd2 : d ^ 2 = 1 := by unfold Dp at hD; linear_combination hD
  have hm : m = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination H.hdm - hd2)
  subst hm
  refine ⟨(1, -1), (1, 1), fun z => ?_, ?_, ?_, ?_⟩
  · rw [d2h H]; ring
  · rw [d2h H]
    intro h; apply hα
    linear_combination h / 4
  · rw [OscInt.API.TriDeriv.triD3, H.sx, H.sy, H.sxy]; ring
  · rw [d2h H, d4h H, d3h H]
    intro h
    have : (-12 : ℝ) = 0 := by linear_combination h + (12 * l ^ 2) * hd2 + 12 * H.hcl
    norm_num at this

/-- Section 2, case 5(a). -/
theorem fold_generic (H : HalfAngle k c l d m) (hc : c ≠ 0) (hd : d ≠ 0)
    (hT : l * Rp α c d ≠ 0) : FoldOrNondeg (triPhase α) k := by
  have hdd := OscInt.API.dd_iteratedFDeriv (triPhase α) k (c2 α k)
  right
  refine ⟨⟨(1, -1), (1, -1), ?_⟩, fun v hv hker => ?_⟩
  · rw [hdd, vW H]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc) hd
  · have hkW := hker (1, -1)
    rw [hdd] at hkW
    obtain ⟨t, ht, rfl⟩ := ker_param H hc hd v hkW hv
    rw [OscInt.API.ddd_iteratedFDeriv _ _ (c3 α k), lin3d, vT H]
    have : 2 * l * c * Rp α c d = (2 * c) * (l * Rp α c d) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero 3 ht) (mul_ne_zero (mul_ne_zero two_ne_zero hc) hT)

/-- Section 2, cases 5(b) and 5(c) with `G ≠ 0`. -/
theorem a3_generic (H : HalfAngle k c l d m) (hD : Dp α c d = 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hT : l * Rp α c d = 0) (hG : Gp c d ≠ 0) : IsA3Point (triPhase α) k := by
  refine ⟨(c * d + l * m, c * d - l * m), (1, -1), fun z => by rw [vVz H, hD]; ring, ?_, ?_, ?_⟩
  · rw [vW H]; exact mul_ne_zero (mul_ne_zero (by norm_num) hc) hd
  · rw [vT H]; linear_combination 2 * c * hT
  · rw [vW H]
    have hQ := vQ (α := α) H
    rw [hD] at hQ
    intro h
    have h12 : 12 * c ^ 2 * Gp c d = 0 := by linear_combination h + hQ
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)) hG h12

end Main

/-- **P-alg, classification** (`docs/proof-TRI.md`, section 2). -/
theorem algClassify : AlgClassify := by
  intro α hα k
  obtain ⟨c, l, d, m, H⟩ := halfAngle k
  by_cases hD : Dp α c d = 0
  swap
  · left; left
    have hdd := OscInt.API.dd_iteratedFDeriv (triPhase α) k (c2 α k)
    rw [hessDet, hdd, hdd, hdd, vHess H]
    exact hD
  by_cases hd : d = 0
  · exact Or.inl (fold_d0 hα H hD hd)
  by_cases hc : c = 0
  · exact Or.inr (Or.inl (a3_c0 hα H hD hc))
  by_cases hT : l * Rp α c d = 0
  · by_cases hG : Gp c d = 0
    · exact Or.inr (Or.inr (locus_of_G H hD hc hd hT hG))
    · exact Or.inr (Or.inl (a3_generic H hD hc hd hT hG))
  · exact Or.inl (fold_generic H hc hd hT)

/-- **P-alg, the A5 conditions force the locus** (section 2, with the invariance step). -/
theorem algA5 : AlgA5 := by
  intro α hα k v w hv hker hcub hww hq
  obtain ⟨c, l, d, m, H⟩ := halfAngle k
  by_cases hD : Dp α c d = 0
  swap
  · exfalso
    have h1 := hker (1, 0)
    have h2 := hker (0, 1)
    rw [d2h H] at h1 h2
    dsimp only at h1 h2
    have e1 : v.1 * Dp α c d = 0 := by
      unfold Dp
      linear_combination (-(c * d + l * m) - α * (2 * c ^ 2 - 1)) * h1 - (-α * (2 * c ^ 2 - 1)) * h2 +
        v.1 * m ^ 2 * H.hcl - v.1 * (c ^ 2 - 1) * H.hdm
    have e2 : v.2 * Dp α c d = 0 := by
      unfold Dp
      linear_combination (-(c * d - l * m) - α * (2 * c ^ 2 - 1)) * h2 - (-α * (2 * c ^ 2 - 1)) * h1 +
        v.2 * m ^ 2 * H.hcl - v.2 * (c ^ 2 - 1) * H.hdm
    exact hv (Prod.ext ((mul_eq_zero.mp e1).resolve_right hD) ((mul_eq_zero.mp e2).resolve_right hD))
  by_cases hd : d = 0
  · exfalso
    subst hd
    have hc2 : c ^ 2 = 1 := by unfold Dp at hD; linear_combination hD
    have hl : l = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination H.hcl - hc2)
    subst hl
    have hm2 : m ^ 2 = 1 := by linear_combination H.hdm
    have h1 := hker (1, 0)
    rw [d2h H] at h1
    obtain ⟨a, b⟩ := v
    have hs : α * (a + b) = 0 := by
      dsimp only at h1; linear_combination (-1 : ℝ) * h1 + (-2 * α * (a + b)) * hc2
    have hb : b = -a := by have := (mul_eq_zero.mp hs).resolve_left hα; linarith
    subst hb
    rw [d3h H] at hcub
    dsimp only at hcub
    have h0 : 2 * c * m * a ^ 3 = 0 := by linear_combination hcub
    have h4 : 4 * a ^ 6 = 0 := by
      linear_combination (2 * c * m * a ^ 3) * h0 - 4 * a ^ 6 * m ^ 2 * hc2 - 4 * a ^ 6 * hm2
    have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.mp (by linarith : a ^ 6 = 0)
    subst ha
    exact hv (by simp)
  by_cases hc : c = 0
  · exfalso
    subst hc
    have hd2 : d ^ 2 = 1 := by unfold Dp at hD; linear_combination hD
    have hm : m = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination H.hdm - hd2)
    subst hm
    have h1 := hker (1, 0)
    rw [d2h H] at h1
    obtain ⟨a, b⟩ := v
    have hs : α * (a + b) = 0 := by dsimp only at h1; linear_combination h1
    have hb : b = -a := by have := (mul_eq_zero.mp hs).resolve_left hα; linarith
    subst hb
    have ha : a ≠ 0 := by intro ha; apply hv; subst ha; simp
    rw [d2h H] at hww
    unfold qinv at hq
    rw [d2h H, d4h H, d3h H] at hq
    dsimp only at hww hq
    have hq' : a ^ 4 * (w.1 + w.2) ^ 2 = 0 := by
      linear_combination (-1 / 3 : ℝ) * hq + (-a ^ 4 * (w.1 + w.2) ^ 2 * l ^ 2) * hd2 +
        (-a ^ 4 * (w.1 + w.2) ^ 2) * H.hcl
    rcases mul_eq_zero.mp hq' with h | h
    · exact ha (pow_eq_zero_iff (by norm_num) |>.mp h)
    · apply hww
      have : w.1 + w.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
      have hw2 : w.2 = -w.1 := by linarith
      rw [hw2]; ring
  -- the generic case `D = 0`, `cd ≠ 0`
  obtain ⟨t, ht, rfl⟩ := ker_param H hc hd v (hker (1, -1)) hv
  obtain ⟨μ, ν, rfl⟩ := w_param (l := l) (m := m) hc hd w
  rw [lin3d, vT H] at hcub
  have hT : l * Rp α c d = 0 := by
    have h := (mul_eq_zero.mp hcub).resolve_left (pow_ne_zero 3 ht)
    have : (2 * c) * (l * Rp α c d) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hc)
  have hT' : 2 * l * c * Rp α c d = 0 := by linear_combination 2 * c * hT
  rw [lin2, vW H, vVz H, vVz H, hD] at hww
  have hμ : μ ≠ 0 := by intro hμ; apply hww; rw [hμ]; ring
  unfold qinv at hq
  rw [lin2, lin4, lin3, vW H, vVz H, vVz H, hD, vT H, hT'] at hq
  have hQ := vQ (α := α) H
  rw [hD] at hQ
  have h12 : t ^ 4 * μ ^ 2 * (12 * c ^ 2 * Gp c d) = 0 := by linear_combination hq + t ^ 4 * μ ^ 2 * hQ
  have hG : Gp c d = 0 := by
    rcases mul_eq_zero.mp h12 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ht
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hμ
    · exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc))
  exact locus_of_G H hD hc hd hT hG

/-- **P-alg, the case `α = 0`** (section 4, last paragraph). -/
theorem algZero : AlgZero := by
  intro k v w hv hker hww
  have h1 := hker (1, 0)
  have h2 := hker (0, 1)
  simp only [triD2_mixed] at h1 h2 hww
  rw [triD3]
  obtain ⟨a, b⟩ := v
  obtain ⟨p, q⟩ := w
  dsimp only at h1 h2 hww ⊢
  have ha : a * Real.cos k.1 = 0 := by linear_combination -h1
  have hb : b * Real.cos k.2 = 0 := by linear_combination -h2
  have hs1 := Real.sin_sq_add_cos_sq k.1
  have hs2 := Real.sin_sq_add_cos_sq k.2
  by_cases hx : Real.cos k.1 = 0
  · have hy : Real.cos k.2 ≠ 0 := by
      intro hy; apply hww; rw [hx, hy]; ring
    have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hy
    subst hb0
    have ha0 : a ≠ 0 := by intro h; apply hv; rw [h]; rfl
    have hsx : Real.sin k.1 ≠ 0 := by intro h; rw [h, hx] at hs1; norm_num at hs1
    have : a ^ 3 * Real.sin k.1 + 0 ^ 3 * Real.sin k.2 + 0 * ((a + 0) ^ 3 * Real.sin (k.1 + k.2)) =
        a ^ 3 * Real.sin k.1 := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero 3 ha0) hsx
  · have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_right hx
    subst ha0
    have hb0 : b ≠ 0 := by intro h; apply hv; rw [h]; rfl
    have hy : Real.cos k.2 = 0 := (mul_eq_zero.mp hb).resolve_left hb0
    have hsy : Real.sin k.2 ≠ 0 := by intro h; rw [h, hy] at hs2; norm_num at hs2
    have : 0 ^ 3 * Real.sin k.1 + b ^ 3 * Real.sin k.2 + 0 * ((0 + b) ^ 3 * Real.sin (k.1 + k.2)) =
        b ^ 3 * Real.sin k.2 := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero 3 hb0) hsy

end OscInt.API.TriAlg
