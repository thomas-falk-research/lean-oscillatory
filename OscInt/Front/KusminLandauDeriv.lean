/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.KusminLandau
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Interval

/-!
# Batch KL, part K-deriv: the derivative form of Kusmin–Landau from the form on differences

Route `docs/proof-KL.md`, "Part K-deriv". With `m = ⌈a⌉`, `M = ⌊b⌋` and `c j = f (m + j)`, the mean value
theorem on each unit interval `[m + j, m + j + 1] ⊆ [a, b]` writes the differences of `c` as values of `f′` at
points of the open interval `(a, b)`; the sum over `Finset.Icc m M` is `expSum c (M − m)`. The empty sum is
bounded directly.
-/

namespace OscInt.KusminLandauAux

open OscInt.Statements OscInt.Blueprint.KusminLandau Set

/-- Mean value theorem on a unit interval `[x, x + 1] ⊆ [a, b]`: `f (x + 1) − f x = f′ ξ`, `x < ξ < x + 1`. -/
theorem klDeriv_mvt (f f' : ℝ → ℝ) (a b : ℝ) (hf : HasDerivOn f f' a b) (x : ℝ) (hax : a ≤ x)
    (hxb : x + 1 ≤ b) : ∃ ξ, x < ξ ∧ ξ < x + 1 ∧ f (x + 1) - f x = f' ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope f f' (lt_add_one x)
    (hf.1.mono (Icc_subset_Icc hax hxb))
    (fun y hy => hf.2 y ⟨lt_of_le_of_lt hax hy.1, lt_of_lt_of_le hy.2 hxb⟩)
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  rw [h, add_sub_cancel_left, div_one]

/-- Each difference of `j ↦ f (m + j)`, `j < N`, is `f′ ξ` for some `ξ ∈ (m + j, m + j + 1) ⊆ (a, b)`. -/
theorem klDeriv_step (f f' : ℝ → ℝ) (a b : ℝ) (hf : HasDerivOn f f' a b) (m : ℤ) (N : ℕ)
    (ham : a ≤ (m : ℝ)) (hmb : (m : ℝ) + (N : ℝ) ≤ b) (j : ℕ) (hj : j < N) :
    ∃ ξ ∈ Ioo a b, (m : ℝ) + (j : ℝ) < ξ ∧ ξ < (m : ℝ) + (j : ℝ) + 1 ∧
      f ((m : ℝ) + ((j + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (j : ℝ)) = f' ξ := by
  have hj' : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have h1 : a ≤ (m : ℝ) + (j : ℝ) := by linarith
  have h2 : (m : ℝ) + (j : ℝ) + 1 ≤ b := by linarith
  obtain ⟨ξ, h3, h4, h5⟩ := klDeriv_mvt f f' a b hf _ h1 h2
  refine ⟨ξ, ⟨lt_of_le_of_lt h1 h3, lt_of_lt_of_le h4 h2⟩, h3, h4, ?_⟩
  rw [← h5, Nat.cast_add, Nat.cast_one, add_assoc]

/-- The differences of `j ↦ f (m + j)`, `j < N`, are monotone and lie in `[k + λ, k + 1 − λ]`. -/
theorem klDeriv_diffs (f f' : ℝ → ℝ) (a b : ℝ) (k : ℤ) (lam : ℝ) (hf : HasDerivOn f f' a b)
    (hmono : MonotoneOn f' (Ioo a b) ∨ AntitoneOn f' (Ioo a b))
    (hb : ∀ x ∈ Ioo a b, (k : ℝ) + lam ≤ f' x ∧ f' x ≤ (k : ℝ) + 1 - lam) (m : ℤ) (N : ℕ)
    (ham : a ≤ (m : ℝ)) (hmb : (m : ℝ) + (N : ℝ) ≤ b) :
    DiffsMonotoneIn (fun j : ℕ => f ((m : ℝ) + (j : ℝ))) N k lam := by
  have hstep := klDeriv_step f f' a b hf m N ham hmb
  have hle : ∀ n : ℕ, n + 1 < N → ∃ ξ0 ∈ Ioo a b, ∃ ξ1 ∈ Ioo a b, ξ0 ≤ ξ1 ∧
      f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (n : ℝ)) = f' ξ0 ∧
      f ((m : ℝ) + ((n + 1 + 1 : ℕ) : ℝ)) - f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) = f' ξ1 := by
    intro n hn
    obtain ⟨ξ0, hξ0, -, h0, e0⟩ := hstep n (Nat.lt_of_succ_lt hn)
    obtain ⟨ξ1, hξ1, h1, -, e1⟩ := hstep (n + 1) hn
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at h1
    exact ⟨ξ0, hξ0, ξ1, hξ1, (h0.trans h1).le, e0, e1⟩
  refine ⟨?_, ?_⟩
  · rcases hmono with hm | hm
    · left
      intro n hn
      obtain ⟨ξ0, hξ0, ξ1, hξ1, h01, e0, e1⟩ := hle n hn
      show f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (n : ℝ)) ≤
        f ((m : ℝ) + ((n + 1 + 1 : ℕ) : ℝ)) - f ((m : ℝ) + ((n + 1 : ℕ) : ℝ))
      rw [e0, e1]
      exact hm hξ0 hξ1 h01
    · right
      intro n hn
      obtain ⟨ξ0, hξ0, ξ1, hξ1, h01, e0, e1⟩ := hle n hn
      show f ((m : ℝ) + ((n + 1 + 1 : ℕ) : ℝ)) - f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) ≤
        f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (n : ℝ))
      rw [e0, e1]
      exact hm hξ0 hξ1 h01
  · intro n hn
    obtain ⟨ξ, hξ, -, -, e⟩ := hstep n hn
    show (k : ℝ) + lam ≤ f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (n : ℝ)) ∧
      f ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) - f ((m : ℝ) + (n : ℝ)) ≤ (k : ℝ) + 1 - lam
    rw [e]
    exact hb ξ hξ

/-- For `0 < λ ≤ 1/2` the bound `cos(πλ/2)/sin(πλ/2)` is nonnegative (the case of the empty sum). -/
theorem klDeriv_bound_nonneg (lam : ℝ) (hl : 0 < lam) (hl2 : lam ≤ 1 / 2) :
    0 ≤ Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2) := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ Real.pi * lam / 2 := by positivity
  have h1 : Real.pi * lam / 2 ≤ Real.pi / 2 := by nlinarith
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩)
    (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith))

/-- For `m ≤ M` the sum over the integers of `[m, M]` is `expSum (j ↦ f (m + j)) (M − m).toNat`. -/
theorem klDeriv_reindex (f : ℝ → ℝ) (m M : ℤ) (h : m ≤ M) :
    ∑ n ∈ Finset.Icc m M, Complex.exp (↑(2 * Real.pi * f (n : ℝ)) * Complex.I) =
      expSum (fun j : ℕ => f ((m : ℝ) + (j : ℝ))) (M - m).toNat := by
  have hN : (M + 1 - m).toNat = (M - m).toNat + 1 := by omega
  rw [Int.Icc_eq_finset_map, Finset.sum_map, hN]
  unfold expSum
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (((Nat.castEmbedding.trans (addLeftEmbedding m)) j : ℤ) : ℝ) = (m : ℝ) + (j : ℝ) := by
    show ((m + (j : ℤ) : ℤ) : ℝ) = (m : ℝ) + (j : ℝ)
    push_cast
    rfl
  rw [e]

/-- **K-deriv** The derivative form of Kusmin–Landau follows from the form on differences. -/
theorem klDerivFacts : KLDerivFacts := by
  intro hKL f f' a b k lam hl hl2 hf hmono hb
  by_cases h : ⌈a⌉ ≤ ⌊b⌋
  · have hc : (((⌊b⌋ - ⌈a⌉).toNat : ℤ) : ℝ) = ((⌊b⌋ - ⌈a⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr h)]
    rw [Int.cast_natCast, Int.cast_sub] at hc
    have hmb : ((⌈a⌉ : ℤ) : ℝ) + (((⌊b⌋ - ⌈a⌉).toNat : ℕ) : ℝ) ≤ b := by
      rw [hc, add_sub_cancel]
      exact Int.floor_le b
    rw [klDeriv_reindex f ⌈a⌉ ⌊b⌋ h]
    exact hKL _ _ k lam hl hl2
      (klDeriv_diffs f f' a b k lam hf hmono hb ⌈a⌉ (⌊b⌋ - ⌈a⌉).toNat (Int.le_ceil a) hmb)
  · rw [Finset.Icc_eq_empty h, Finset.sum_empty, norm_zero]
    exact klDeriv_bound_nonneg lam hl hl2

end OscInt.KusminLandauAux
