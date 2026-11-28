/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Cusp.Final

/-!
# A5U part A3: piecewise van der Corput with three thresholds

From A1 (`LevelCrossingFacts`) and A2 (`AmpNormRestrictFacts`). The level sets `|D j| = l_j` (`j = 2, 3, 4`) are
finite with at most `2 (6 − j)` points (A1 applied to the shifted chain `D j, …, D 6`), at most 18 in all. On an
interval free of such points one alternative `l_j < |D j|` holds throughout (intermediate values), and the frozen
`OscInt.API.vdCk` of order `j` applies with the restricted amplitude (A2). Splitting at the cut points
(`a5uG1_induct`, induction on their number) gives at most 19 pieces.
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.A5U

/-- The sum of the three van der Corput coefficients. -/
noncomputable def a5uG1_K (l₂ l₃ l₄ : ℝ) : ℝ :=
  8 * l₂ ^ (-(1 : ℝ) / 2) + 18 * l₃ ^ (-(1 : ℝ) / 3) + 38 * l₄ ^ (-(1 : ℝ) / 4)

/-- A cut point: one of the three levels is attained. -/
def a5uG1_bad (D : ℕ → ℝ → ℝ) (l₂ l₃ l₄ x : ℝ) : Prop :=
  |D 2 x| = l₂ ∨ |D 3 x| = l₃ ∨ |D 4 x| = l₄

theorem a5uG1_K_nonneg (l₂ l₃ l₄ : ℝ) (h₂ : 0 ≤ l₂) (h₃ : 0 ≤ l₃) (h₄ : 0 ≤ l₄) : 0 ≤ a5uG1_K l₂ l₃ l₄ := by
  unfold a5uG1_K
  have := Real.rpow_nonneg h₂ (-(1 : ℝ) / 2)
  have := Real.rpow_nonneg h₃ (-(1 : ℝ) / 3)
  have := Real.rpow_nonneg h₄ (-(1 : ℝ) / 4)
  positivity

theorem a5uG1_ampNorm_nonneg {ψ ψ' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) : 0 ≤ ampNorm ψ ψ' a b :=
  add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _)

/-- Restriction of a derivative chain to a shorter chain on a subinterval. -/
theorem a5uG1_chain_restrict {D : ℕ → ℝ → ℝ} {k m : ℕ} {a b l r : ℝ} (h : DerivChain D k a b) (hm : m ≤ k)
    (hal : a ≤ l) (hrb : r ≤ b) : DerivChain D m l r := fun j hj =>
  ⟨(h j (by omega)).1.mono (Icc_subset_Icc hal hrb),
    fun x hx => (h j (by omega)).2 x ⟨hal.trans_lt hx.1, hx.2.trans_le hrb⟩⟩

/-- A level set of `D j`, `j < 6`, on `[a, b]` lies in a finset with at most `6 − j` points (A1). -/
theorem a5uG1_level_finset (hA1 : LevelCrossingFacts) {D : ℕ → ℝ → ℝ} {a b : ℝ} {j : ℕ} (hj : j < 6)
    (hch : DerivChain D 6 a b) (h6 : ∀ x ∈ Ioo a b, D 6 x ≠ 0) (c : ℝ) :
    ∃ F : Finset ℝ, F.card ≤ 6 - j ∧ ∀ x ∈ Icc a b, D j x = c → x ∈ F := by
  have hch' : DerivChain (fun i => D (i + j)) (6 - j) a b := fun i hi => by
    show HasDerivOn (D (i + j)) (D (i + 1 + j)) a b
    rw [show i + 1 + j = i + j + 1 by omega]
    exact hch (i + j) (by omega)
  have h6' : ∀ x ∈ Ioo a b, (fun i => D (i + j)) (6 - j) x ≠ 0 := by
    intro x hx
    show D (6 - j + j) x ≠ 0
    rw [show 6 - j + j = 6 by omega]
    exact h6 x hx
  have key : ∀ S : Finset ℝ, (∀ x ∈ S, x ∈ Icc a b ∧ D j x = c) → S.card ≤ 6 - j := fun S hS =>
    hA1 _ (6 - j) a b c S (by omega) hch' h6' (fun x hx => by simpa using hS x hx)
  have hfin : {x | x ∈ Icc a b ∧ D j x = c}.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (7 - j)
    have := key S (fun x hx => hS hx)
    omega
  exact ⟨hfin.toFinset, key _ (fun x hx => hfin.mem_toFinset.1 hx),
    fun x hx hD => hfin.mem_toFinset.2 ⟨hx, hD⟩⟩

/-- Intermediate values: a strict lower bound for `|f|` at one point of `(l, r)` persists on `(l, r)` when the
level `|f| = λ` is never attained there. -/
theorem a5uG1_persist {f : ℝ → ℝ} {l r lam m : ℝ} (hf : ContinuousOn f (Ioo l r)) (hm : m ∈ Ioo l r)
    (hlm : lam < |f m|) (hno : ∀ x ∈ Ioo l r, |f x| ≠ lam) : ∀ x ∈ Ioo l r, lam < |f x| := by
  intro x hx
  by_contra hle
  obtain ⟨y, hy, hyv⟩ := isPreconnected_Ioo.intermediate_value hx hm hf.abs ⟨not_lt.1 hle, hlm.le⟩
  exact hno y hy hyv

/-- `vdCk` of order `j` on a subinterval, with the amplitude norm of the whole interval. -/
theorem a5uG1_vdc_piece (hA2 : AmpNormRestrictFacts) {D : ℕ → ℝ → ℝ} {ψ ψ' : ℝ → ℂ} {a b p lam l r : ℝ}
    {j : ℕ} (hj2 : 2 ≤ j) (hj6 : j ≤ 6) (hlam : 0 < lam) (hch : DerivChain D 6 a b)
    (hψ : AmplitudeOn ψ ψ' a b) (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b)
    (hlow : ∀ x ∈ Ioo l r, lam < |D j x|) :
    ‖oscInt (fun x => D 0 x + p * x) ψ l r‖ ≤
      ((5 : ℝ) * 2 ^ (j - 1) - 2) * lam ^ (-(1 : ℝ) / (j : ℝ)) * ampNorm ψ ψ' a b := by
  obtain ⟨hψ', hN⟩ := hA2 ψ ψ' a b l r hal hlr hrb hψ
  have h := OscInt.API.vdCk j D ψ ψ' l r lam p hj2 hlr hlam (a5uG1_chain_restrict hch hj6 hal hrb)
    (fun x hx => (hlow x hx).le) hψ'
  have hpow : (1 : ℝ) ≤ 2 ^ (j - 1) := one_le_pow₀ (by norm_num)
  have hc : 0 ≤ ((5 : ℝ) * 2 ^ (j - 1) - 2) * lam ^ (-(1 : ℝ) / (j : ℝ)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hlam.le _)
  exact h.trans (mul_le_mul_of_nonneg_left hN hc)

/-- A piece free of cut points: one alternative holds throughout, and `vdCk` gives `K · ampNorm`. -/
theorem a5uG1_piece (hA2 : AmpNormRestrictFacts) {D : ℕ → ℝ → ℝ} {ψ ψ' : ℝ → ℂ} {a b p l₂ l₃ l₄ l r : ℝ}
    (hl₂ : 0 < l₂) (hl₃ : 0 < l₃) (hl₄ : 0 < l₄) (hch : DerivChain D 6 a b)
    (halt : ∀ x ∈ Ioo a b, l₂ < |D 2 x| ∨ l₃ < |D 3 x| ∨ l₄ < |D 4 x|) (hψ : AmplitudeOn ψ ψ' a b)
    (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) (hgood : ∀ x ∈ Ioo l r, ¬ a5uG1_bad D l₂ l₃ l₄ x) :
    ‖oscInt (fun x => D 0 x + p * x) ψ l r‖ ≤ a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b := by
  have hK := a5uG1_K_nonneg l₂ l₃ l₄ hl₂.le hl₃.le hl₄.le
  have hN : 0 ≤ ampNorm ψ ψ' a b := a5uG1_ampNorm_nonneg (hal.trans (hlr.trans hrb))
  rcases hlr.eq_or_lt with rfl | hlt
  · simp only [oscInt, intervalIntegral.integral_same, norm_zero]
    exact mul_nonneg hK hN
  have hm : (l + r) / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hsub : Ioo l r ⊆ Icc a b := fun x hx => ⟨hal.trans hx.1.le, hx.2.le.trans hrb⟩
  have hcont : ∀ j < 6, ContinuousOn (D j) (Ioo l r) := fun j hj => (hch j hj).1.mono hsub
  have h₂ := Real.rpow_nonneg hl₂.le (-(1 : ℝ) / 2)
  have h₃ := Real.rpow_nonneg hl₃.le (-(1 : ℝ) / 3)
  have h₄ := Real.rpow_nonneg hl₄.le (-(1 : ℝ) / 4)
  rcases halt _ ⟨hal.trans_lt hm.1, hm.2.trans_le hrb⟩ with h | h | h
  · have hlow := a5uG1_persist (hcont 2 (by norm_num)) hm h (fun x hx he => hgood x hx (Or.inl he))
    have := a5uG1_vdc_piece (p := p) (j := 2) hA2 le_rfl (by norm_num) hl₂ hch hψ hal hlr hrb hlow
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hN)
    norm_num [a5uG1_K]
    linarith
  · have hlow := a5uG1_persist (hcont 3 (by norm_num)) hm h
      (fun x hx he => hgood x hx (Or.inr (Or.inl he)))
    have := a5uG1_vdc_piece (p := p) (j := 3) hA2 (by norm_num) (by norm_num) hl₃ hch hψ hal hlr hrb hlow
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hN)
    norm_num [a5uG1_K]
    linarith
  · have hlow := a5uG1_persist (hcont 4 (by norm_num)) hm h
      (fun x hx he => hgood x hx (Or.inr (Or.inr he)))
    have := a5uG1_vdc_piece (p := p) (j := 4) hA2 (by norm_num) (by norm_num) hl₄ hch hψ hal hlr hrb hlow
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hN)
    norm_num [a5uG1_K]
    linarith

/-- The integrand of `oscInt` is interval integrable on every subinterval of `[a, b]`. -/
theorem a5uG1_integrable {D : ℕ → ℝ → ℝ} {ψ ψ' : ℝ → ℂ} {a b p u v : ℝ} (hch : DerivChain D 6 a b)
    (hψ : AmplitudeOn ψ ψ' a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    IntervalIntegrable (fun x => Complex.exp (↑(D 0 x + p * x) * Complex.I) * ψ x) volume u v := by
  have hφ : ContinuousOn (fun x => D 0 x + p * x) (Icc a b) :=
    (hch 0 (by norm_num)).1.add (continuousOn_const.mul continuousOn_id)
  have hc : ContinuousOn (fun x => Complex.exp (↑(D 0 x + p * x) * Complex.I) * ψ x) (Icc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const).cexp.mul hψ.1
  exact (hc.mono (Icc_subset_Icc hau hvb)).intervalIntegrable_of_Icc huv

/-- Splitting at the cut points: if every cut point in `(l, r)` lies in `F ⊆ (l, r)`, the integral over `[l, r]`
is at most `(|F| + 1) K · ampNorm` (induction on a bound `n` for `|F|`). -/
theorem a5uG1_induct (hA2 : AmpNormRestrictFacts) {D : ℕ → ℝ → ℝ} {ψ ψ' : ℝ → ℂ} {a b p l₂ l₃ l₄ : ℝ}
    (hl₂ : 0 < l₂) (hl₃ : 0 < l₃) (hl₄ : 0 < l₄) (hch : DerivChain D 6 a b)
    (halt : ∀ x ∈ Ioo a b, l₂ < |D 2 x| ∨ l₃ < |D 3 x| ∨ l₄ < |D 4 x|) (hψ : AmplitudeOn ψ ψ' a b)
    (hab : a ≤ b) (n : ℕ) :
    ∀ (F : Finset ℝ) (l r : ℝ), F.card ≤ n → a ≤ l → l ≤ r → r ≤ b → (∀ x ∈ F, x ∈ Ioo l r) →
      (∀ x ∈ Ioo l r, a5uG1_bad D l₂ l₃ l₄ x → x ∈ F) →
      ‖oscInt (fun x => D 0 x + p * x) ψ l r‖ ≤ ((F.card : ℝ) + 1) * (a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b) := by
  classical
  have hKN : 0 ≤ a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b :=
    mul_nonneg (a5uG1_K_nonneg l₂ l₃ l₄ hl₂.le hl₃.le hl₄.le) (a5uG1_ampNorm_nonneg hab)
  have base : ∀ l r : ℝ, a ≤ l → l ≤ r → r ≤ b → (∀ x ∈ Ioo l r, a5uG1_bad D l₂ l₃ l₄ x → x ∈ (∅ : Finset ℝ)) →
      ‖oscInt (fun x => D 0 x + p * x) ψ l r‖ ≤
        (((∅ : Finset ℝ).card : ℝ) + 1) * (a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b) := by
    intro l r hal hlr hrb hbad
    rw [Finset.card_empty, Nat.cast_zero, zero_add, one_mul]
    exact a5uG1_piece hA2 hl₂ hl₃ hl₄ hch halt hψ hal hlr hrb
      (fun x hx hb => Finset.notMem_empty x (hbad x hx hb))
  induction n with
  | zero =>
    intro F l r hF hal hlr hrb _ hbad
    obtain rfl : F = ∅ := Finset.card_eq_zero.1 (by omega)
    exact base l r hal hlr hrb hbad
  | succ n ih =>
    intro F l r hF hal hlr hrb hFin hbad
    rcases F.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · exact base l r hal hlr hrb hbad
    have hzI := hFin z hz
    have hcardR : (F.filter (fun x => z < x)).card + 1 ≤ (F.filter (fun x => ¬ x < z)).card := by
      rw [← Finset.card_insert_of_notMem (fun h => lt_irrefl z (Finset.mem_filter.1 h).2)]
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_filter.2 ⟨hz, lt_irrefl _⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨h1, not_lt.2 h2.le⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun x => x < z)
    have hL := ih (F.filter (fun x => x < z)) l z (by omega) hal hzI.1.le (hzI.2.le.trans hrb)
      (fun x hx => ⟨(hFin x (Finset.mem_filter.1 hx).1).1, (Finset.mem_filter.1 hx).2⟩)
      (fun x hx hb => Finset.mem_filter.2 ⟨hbad x ⟨hx.1, hx.2.trans hzI.2⟩ hb, hx.2⟩)
    have hR := ih (F.filter (fun x => z < x)) z r (by omega) (hal.trans hzI.1.le) hzI.2.le hrb
      (fun x hx => ⟨(Finset.mem_filter.1 hx).2, (hFin x (Finset.mem_filter.1 hx).1).2⟩)
      (fun x hx hb => Finset.mem_filter.2 ⟨hbad x ⟨hzI.1.trans hx.1, hx.2⟩ hb, hx.1⟩)
    have hsum : oscInt (fun x => D 0 x + p * x) ψ l r =
        oscInt (fun x => D 0 x + p * x) ψ l z + oscInt (fun x => D 0 x + p * x) ψ z r := by
      unfold oscInt
      exact (intervalIntegral.integral_add_adjacent_intervals
        (a5uG1_integrable hch hψ hal hzI.1.le (hzI.2.le.trans hrb))
        (a5uG1_integrable hch hψ (hal.trans hzI.1.le) hzI.2.le hrb)).symm
    have hc : (((F.filter (fun x => x < z)).card : ℝ) + 1) + (((F.filter (fun x => z < x)).card : ℝ) + 1) ≤
        (F.card : ℝ) + 1 := by
      have : (F.filter (fun x => x < z)).card + 1 + ((F.filter (fun x => z < x)).card + 1) ≤ F.card + 1 := by
        omega
      exact_mod_cast this
    rw [hsum]
    calc _ ≤ ‖oscInt (fun x => D 0 x + p * x) ψ l z‖ + ‖oscInt (fun x => D 0 x + p * x) ψ z r‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add hL hR
      _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hKN

/-- The cut points in `(a, b)` lie in the union of the six level finsets, of total size at most `18`. -/
theorem a5uG1_cuts (hA1 : LevelCrossingFacts) {D : ℕ → ℝ → ℝ} {a b l₂ l₃ l₄ : ℝ} (hl₂ : 0 < l₂)
    (hl₃ : 0 < l₃) (hl₄ : 0 < l₄) (hch : DerivChain D 6 a b) (h6 : ∀ x ∈ Ioo a b, D 6 x ≠ 0) :
    ∃ F : Finset ℝ, F.card ≤ 18 ∧ (∀ x ∈ F, x ∈ Ioo a b) ∧
      ∀ x ∈ Ioo a b, a5uG1_bad D l₂ l₃ l₄ x → x ∈ F := by
  classical
  obtain ⟨F₁, hc₁, hF₁⟩ := a5uG1_level_finset hA1 (j := 2) (by norm_num) hch h6 l₂
  obtain ⟨F₂, hc₂, hF₂⟩ := a5uG1_level_finset hA1 (j := 2) (by norm_num) hch h6 (-l₂)
  obtain ⟨F₃, hc₃, hF₃⟩ := a5uG1_level_finset hA1 (j := 3) (by norm_num) hch h6 l₃
  obtain ⟨F₄, hc₄, hF₄⟩ := a5uG1_level_finset hA1 (j := 3) (by norm_num) hch h6 (-l₃)
  obtain ⟨F₅, hc₅, hF₅⟩ := a5uG1_level_finset hA1 (j := 4) (by norm_num) hch h6 l₄
  obtain ⟨F₆, hc₆, hF₆⟩ := a5uG1_level_finset hA1 (j := 4) (by norm_num) hch h6 (-l₄)
  refine ⟨(F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅ ∪ F₆).filter (fun x => x ∈ Ioo a b), ?_,
    fun x hx => (Finset.mem_filter.1 hx).2, ?_⟩
  · have := Finset.card_filter_le (F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅ ∪ F₆) (fun x => x ∈ Ioo a b)
    have := Finset.card_union_le (F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅) F₆
    have := Finset.card_union_le (F₁ ∪ F₂ ∪ F₃ ∪ F₄) F₅
    have := Finset.card_union_le (F₁ ∪ F₂ ∪ F₃) F₄
    have := Finset.card_union_le (F₁ ∪ F₂) F₃
    have := Finset.card_union_le F₁ F₂
    omega
  · intro x hx hb
    refine Finset.mem_filter.2 ⟨?_, hx⟩
    have hxI := Ioo_subset_Icc_self hx
    rcases hb with h | h | h
    · rcases (abs_eq hl₂.le).1 h with h' | h'
      · simp [hF₁ x hxI h']
      · simp [hF₂ x hxI h']
    · rcases (abs_eq hl₃.le).1 h with h' | h'
      · simp [hF₃ x hxI h']
      · simp [hF₄ x hxI h']
    · rcases (abs_eq hl₄.le).1 h with h' | h'
      · simp [hF₅ x hxI h']
      · simp [hF₆ x hxI h']

/-- **A3** Piecewise van der Corput with three thresholds, from A1 and A2. -/
theorem piecewiseVdC : PiecewiseVdCFacts := by
  intro hA1 hA2 D ψ ψ' a b p l₂ l₃ l₄ hab hl₂ hl₃ hl₄ hch h6 halt hψ
  obtain ⟨F, hcard, hFin, hbad⟩ := a5uG1_cuts hA1 hl₂ hl₃ hl₄ hch h6
  have h := a5uG1_induct (p := p) hA2 hl₂ hl₃ hl₄ hch halt hψ hab 18 F a b hcard le_rfl hab le_rfl hFin hbad
  have hKN : 0 ≤ a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b :=
    mul_nonneg (a5uG1_K_nonneg l₂ l₃ l₄ hl₂.le hl₃.le hl₄.le) (a5uG1_ampNorm_nonneg hab)
  have hc : (F.card : ℝ) + 1 ≤ 19 := by
    have : F.card + 1 ≤ 19 := by omega
    exact_mod_cast this
  calc _ ≤ _ := h
    _ ≤ 19 * (a5uG1_K l₂ l₃ l₄ * ampNorm ψ ψ' a b) := mul_le_mul_of_nonneg_right hc hKN
    _ = _ := by unfold a5uG1_K; ring

end OscInt.A5UAux
