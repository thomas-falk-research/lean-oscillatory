/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# A5U part A1: level crossings of a derivative chain (Rolle count)

If `D 0, …, D n` is a derivative chain on `[a, b]` with `n ≥ 1` and `D n ≠ 0` on `(a, b)`, then `D 0` takes any
value at most `n` times on `[a, b]`. Proof: Rolle's theorem between consecutive level points
(`a5uG1_rolle_finset`) turns `k + 1` level points of `D 0` into `k` zeros of `D 1` in `(a, b)`; induction on `n`.
-/

namespace OscInt.A5UAux

open Set OscInt.Statements OscInt.Blueprint.A5U

/-- Rolle step: `s` level points of `f` on `[a, b]` give a finset `T ⊆ (a, b)` of zeros of `f'` with
`|s| ≤ |T| + 1`, every point of `T` lying below some point of `s`. -/
theorem a5uG1_rolle_finset {f f' : ℝ → ℝ} {a b c : ℝ} (hf : HasDerivOn f f' a b) (s : Finset ℝ) :
    (∀ x ∈ s, x ∈ Icc a b ∧ f x = c) →
      ∃ T : Finset ℝ, (∀ t ∈ T, t ∈ Ioo a b ∧ f' t = 0) ∧ s.card ≤ T.card + 1 ∧
        ∀ t ∈ T, ∃ x ∈ s, t < x := by
  classical
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    exact ⟨∅, by simp, by simp, by simp⟩
  · intro m s hlt ih hs
    obtain ⟨T, hT, hcard, hTlt⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    have hm := hs m (Finset.mem_insert_self m s)
    have hms : m ∉ s := fun h => lt_irrefl m (hlt m h)
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    have hx₀ : s.max' hne ∈ s := s.max'_mem hne
    have hx₀m : s.max' hne < m := hlt _ hx₀
    have h0 := hs _ (Finset.mem_insert_of_mem hx₀)
    obtain ⟨z, hz, hz0⟩ := exists_hasDerivAt_eq_zero hx₀m
      (hf.1.mono (Icc_subset_Icc h0.1.1 hm.1.2)) (h0.2.trans hm.2.symm)
      (fun x hx => hf.2 x ⟨lt_of_le_of_lt h0.1.1 hx.1, lt_of_lt_of_le hx.2 hm.1.2⟩)
    have hzT : z ∉ T := by
      intro hzT
      obtain ⟨x, hx, hzx⟩ := hTlt z hzT
      have := s.le_max' x hx
      linarith [hz.1]
    refine ⟨insert z T, ?_, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨⟨lt_of_le_of_lt h0.1.1 hz.1, lt_of_lt_of_le hz.2 hm.1.2⟩, hz0⟩
      · exact hT t ht
    · rw [Finset.card_insert_of_notMem hms, Finset.card_insert_of_notMem hzT]
      omega
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨m, Finset.mem_insert_self m s, hz.2⟩
      · obtain ⟨x, hx, htx⟩ := hTlt t ht
        exact ⟨x, Finset.mem_insert_of_mem hx, htx⟩

/-- The level-crossing count for a chain of length `n + 1`. -/
theorem a5uG1_levelCrossing_succ (n : ℕ) : ∀ (D : ℕ → ℝ → ℝ) (a b c : ℝ) (S : Finset ℝ),
    DerivChain D (n + 1) a b → (∀ x ∈ Ioo a b, D (n + 1) x ≠ 0) →
      (∀ x ∈ S, x ∈ Icc a b ∧ D 0 x = c) → S.card ≤ n + 1 := by
  induction n with
  | zero =>
    intro D a b c S hch hne hS
    obtain ⟨T, hT, hcard, -⟩ := a5uG1_rolle_finset (hch 0 (by omega)) S hS
    have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => hne t (hT t ht).1 (hT t ht).2
    rw [hT0, Finset.card_empty] at hcard
    exact hcard
  | succ n ih =>
    intro D a b c S hch hne hS
    obtain ⟨T, hT, hcard, -⟩ := a5uG1_rolle_finset (hch 0 (by omega)) S hS
    have hT' := ih (fun j => D (j + 1)) a b 0 T (fun j hj => hch (j + 1) (by omega))
      (fun x hx => hne x hx) (fun t ht => ⟨Ioo_subset_Icc_self (hT t ht).1, (hT t ht).2⟩)
    omega

/-- **A1** Level crossings (Rolle count). -/
theorem levelCrossing : LevelCrossingFacts := by
  intro D n a b c S hn hch hne hS
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact a5uG1_levelCrossing_succ m D a b c S hch hne hS

end OscInt.A5UAux
