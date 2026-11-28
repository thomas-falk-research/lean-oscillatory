/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Front.TriangularAnisoFinal
import OscInt.Front.ReducedBridge
import OscInt.Front.LatticeCubeRootFinal
import OscInt.Front.TriangularDecaySanity
import OscInt.Front.ConvertDeriv
import OscInt.Front.TriDeriv

/-!
# Batch K2, assembly AU: the global upper bound K2-U from the parts

Route `docs/proof-K2.md`, section 2, and section 8, items 4 (m5, m6, N1). At `α = 0` the bound is T6E′ through
`triKernel 0 = latticeKernel`. For `α ≠ 0`, P7 (`TorusPatchFacts`) is applied to `triPhase α` with `β = triRate α`;
the local bound at each point comes from K2-L, with the order chosen by TRI-K's case:
* nondegenerate point: `w ∈ {e₁, e₂, e₁ + e₂}`, P5 and P6 give `g″(0) ≠ 0`, order 2;
* fold: a kernel vector `v`, P5 and `ReducedBridge.bridge` give `g‴(0) = D³Ψ[v³] ≠ 0`, order 3;
* A3 point: P5 and the bridge give `g⁗(0) = qinv / D²Ψ[w, w] ≠ 0`, order 4;
* A5 point (only at `|α| = a*`, TRI-X): its own reduced curve, order 6.
-/

namespace OscInt.K2.TriDecayUpperAux

open OscInt.Statements OscInt.Blueprint.K2
open scoped ContDiff

/-- A local bound of order `m` from K2-L, weakened to any exponent `β ≤ 1/2 + 1/m` (route N1: `max C 0`). -/
theorem local_bound (hL : ReducedOrderBoundStatement) {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {k₀ v w : ℝ × ℝ}
    {ε : ℝ} {h : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m) (hw : iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0) (hε : 0 < ε)
    (hred : ReducedCurve Ψ k₀ v w ε h) (hd : iteratedDeriv m (reducedFn Ψ k₀ v w h) 0 ≠ 0) {β : ℝ}
    (hβ : β ≤ 1 / 2 + 1 / (m : ℝ)) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t → ‖oscInt2 (fun κ => t * Ψ κ + lin y κ) A‖ ≤ C * M * t ^ (-β) := by
  have hspan := OscInt.API.TriangularDecaySanity.span_of_hyps Ψ k₀ v w ε h m hΨ (by omega) hw hε hred hd
  obtain ⟨δ, hδ, C, hC⟩ := hL Ψ k₀ v w ε h m hΨ hm hspan hw hε hred hd
  refine ⟨δ, hδ, max C 0, fun A M y t hA ht => ?_⟩
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hA.2.2 0 (by norm_num) k₀)
  have hpow : t ^ (-(1 / 2 + 1 / (m : ℝ))) ≤ t ^ (-β) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hp0 : 0 ≤ t ^ (-(1 / 2 + 1 / (m : ℝ))) := Real.rpow_nonneg (by linarith) _
  calc ‖oscInt2 (fun κ => t * Ψ κ + lin y κ) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ))) := hC A M y t hA ht
    _ ≤ max C 0 * M * t ^ (-(1 / 2 + 1 / (m : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) hp0
    _ ≤ max C 0 * M * t ^ (-β) := mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) hM)

/-- Expansion of a bilinear form on `ℝ²` in the standard basis. -/
theorem expand2 (D : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (x y : ℝ × ℝ) :
    D x y = x.1 * y.1 * D (1, 0) (1, 0) + x.1 * y.2 * D (1, 0) (0, 1) + x.2 * y.1 * D (0, 1) (1, 0) +
      x.2 * y.2 * D (0, 1) (0, 1) := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  have hy : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hx, hy]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

theorem triRate_le (α : ℝ) : triRate α ≤ 3 / 4 := by
  unfold triRate; split_ifs <;> norm_num

theorem triRate_nonneg (α : ℝ) : 0 ≤ triRate α := by
  unfold triRate; split_ifs <;> norm_num

theorem triRate_exc {α : ℝ} (h : |α| = triExceptional) : triRate α = 2 / 3 := by
  unfold triRate; simp [h]

theorem triPhase_per₁ (α : ℝ) (k : ℝ × ℝ) : triPhase α (k.1 + 2 * Real.pi, k.2) = triPhase α k := by
  simp only [triPhase]
  rw [show k.1 + 2 * Real.pi + k.2 = (k.1 + k.2) + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.cos_add_two_pi]

theorem triPhase_per₂ (α : ℝ) (k : ℝ × ℝ) : triPhase α (k.1, k.2 + 2 * Real.pi) = triPhase α k := by
  simp only [triPhase]
  rw [show k.1 + (k.2 + 2 * Real.pi) = (k.1 + k.2) + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.cos_add_two_pi]

/-- The local hypothesis of P7 at every point of `triPhase α`, `α ≠ 0`, with exponent `triRate α`. -/
theorem local_tri (hL : ReducedOrderBoundStatement) (h5 : ReducedCurveExistsFacts) (h6 : ReducedOrderTwoFacts)
    {α : ℝ} (hα : α ≠ 0) (k₀ : ℝ × ℝ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * t ^ (-triRate α) := by
  have hcls := OscInt.API.triClassification α hα k₀
  set Ψ := triPhase α with hΨdef
  have hΨ : ContDiff ℝ ∞ Ψ := OscInt.API.TriDeriv.triPhase_smooth α
  have hΨ2 : ContDiffAt ℝ 2 Ψ k₀ := (hΨ.of_le (by simp)).contDiffAt
  have hΨ3 : ContDiffAt ℝ 3 Ψ k₀ := (hΨ.of_le (by simp)).contDiffAt
  have hr := triRate_le α
  set D := fderiv ℝ (fderiv ℝ Ψ) k₀ with hD
  have hDi : ∀ a b : ℝ × ℝ, iteratedFDeriv ℝ 2 Ψ k₀ ![a, b] = D a b := fun a b => by
    rw [iteratedFDeriv_two_apply]; rfl
  have hdd : ∀ a b : ℝ × ℝ, dd Ψ k₀ a b = D a b := fun a b => by
    rw [OscInt.API.dd_iteratedFDeriv Ψ k₀ hΨ2, hDi]
  have hsym : D (0, 1) (1, 0) = D (1, 0) (0, 1) := by
    rw [← hDi, ← hDi]; exact OscInt.API.ReducedBridge.iteratedFDeriv_two_swap hΨ k₀ _ _
  rcases hcls with hF | hA3 | hA5
  · -- A1 / A2
    by_cases hdet : hessDet Ψ k₀ ≠ 0
    · -- nondegenerate point: order 2
      have hdet' : D (1, 0) (1, 0) * D (0, 1) (0, 1) - D (1, 0) (0, 1) ^ 2 ≠ 0 := by
        simpa only [hessDet, hdd] using hdet
      suffices H : ∃ v w : ℝ × ℝ, D w w ≠ 0 ∧ D v v - D v w ^ 2 / D w w ≠ 0 by
        obtain ⟨v, w, hw, hg⟩ := H
        have hw' : iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 := by rwa [hDi]
        obtain ⟨ε, hε, h, hred⟩ := h5 Ψ k₀ v w hΨ hw'
        have h2 := h6 Ψ k₀ v w ε h hΨ hw' hε hred
        rw [hDi, hDi, hDi] at h2
        refine local_bound hL hΨ (m := 2) le_rfl hw' hε hred (by rw [h2]; exact hg) ?_
        norm_num; linarith
      by_cases ha : D (1, 0) (1, 0) = 0
      · by_cases hc : D (0, 1) (0, 1) = 0
        · have hb : D (1, 0) (0, 1) ≠ 0 := by
            intro hb; apply hdet'; rw [ha, hb]; ring
          refine ⟨(1, 0), (1, 1), ?_, ?_⟩
          · rw [expand2 D (1, 1) (1, 1), hsym]
            simp only [mul_one]
            rw [ha, hc]; intro h0; apply hb; linarith
          · rw [expand2 D (1, 0) (1, 1), expand2 D (1, 1) (1, 1), hsym]
            simp only [mul_one, zero_mul, add_zero, one_mul]
            rw [ha, hc]
            simp only [zero_add, add_zero]
            rw [show D (1, 0) (0, 1) + D (1, 0) (0, 1) = 2 * D (1, 0) (0, 1) by ring]
            field_simp
            intro h0; apply hb; linarith
        · refine ⟨(1, 0), (0, 1), hc, ?_⟩
          intro h0; apply hdet'
          field_simp at h0
          linear_combination h0
      · refine ⟨(0, 1), (1, 0), ha, ?_⟩
        rw [hsym]
        intro h0; apply hdet'
        field_simp at h0
        linear_combination h0
    · -- fold: order 3
      obtain ⟨⟨v₀, w₀, hne⟩, hfold⟩ := hF.resolve_left hdet
      have hdet0 : D (1, 0) (1, 0) * D (0, 1) (0, 1) - D (1, 0) (0, 1) ^ 2 = 0 := by
        simpa only [hessDet, hdd] using not_not.mp hdet
      have hne' : D v₀ w₀ ≠ 0 := by rwa [hdd] at hne
      suffices H : ∃ v w : ℝ × ℝ, v ≠ 0 ∧ (∀ z, D v z = 0) ∧ D w w ≠ 0 by
        obtain ⟨v, w, hv0, hker, hw⟩ := H
        have hw' : iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0 := by rwa [hDi]
        have hker' : ∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0 := fun z => by rw [hDi]; exact hker z
        have hddd := hfold v hv0 (fun z => by rw [hdd]; exact hker z)
        rw [OscInt.API.ddd_iteratedFDeriv Ψ k₀ hΨ3] at hddd
        obtain ⟨ε, hε, h, hred⟩ := h5 Ψ k₀ v w hΨ hw'
        have hb := (OscInt.API.ReducedBridge.bridge Ψ k₀ v w ε h hΨ hker' hw' hε hred).1
        refine local_bound hL hΨ (m := 3) (by norm_num) hw' hε hred (by rw [hb]; exact hddd) ?_
        norm_num; linarith
      by_cases ha : D (1, 0) (1, 0) = 0
      · have hb : D (1, 0) (0, 1) = 0 := by
          rw [ha, zero_mul, zero_sub, neg_eq_zero] at hdet0; exact pow_eq_zero_iff (by norm_num) |>.mp hdet0
        have hc : D (0, 1) (0, 1) ≠ 0 := by
          intro hc; apply hne'; rw [expand2 D v₀ w₀, hsym, ha, hb, hc]; ring
        refine ⟨(1, 0), (0, 1), by simp, fun z => ?_, hc⟩
        rw [expand2 D (1, 0) z, ha, hb]; ring
      · refine ⟨(D (1, 0) (0, 1), -D (1, 0) (1, 0)), (1, 0), ?_, fun z => ?_, ha⟩
        · intro h0; apply ha; have := congrArg Prod.snd h0; simpa using this
        · rw [expand2 D _ z, hsym]
          simp only
          linear_combination (-z.2) * hdet0
  · -- A3: order 4
    obtain ⟨v, w, hker, hw, -, hq⟩ := hA3
    obtain ⟨ε, hε, h, hred⟩ := h5 Ψ k₀ v w hΨ hw
    have hb := (OscInt.API.ReducedBridge.bridge Ψ k₀ v w ε h hΨ hker hw hε hred).2
    refine local_bound hL hΨ (m := 4) (by norm_num) hw hε hred ?_ ?_
    · rw [hb]; exact div_ne_zero hq hw
    · norm_num; linarith
  · -- A5: order 6, only at `|α| = a*`
    have hexc := (OscInt.API.triA5Locus α k₀ hA5).1
    obtain ⟨v, w, -, -, hw, ε, hε, h, hred, -, h6'⟩ := hA5
    refine local_bound hL hΨ (m := 6) (by norm_num) hw hε hred h6' ?_
    rw [triRate_exc hexc]; norm_num

end OscInt.K2.TriDecayUpperAux

namespace OscInt.K2

open OscInt.Statements OscInt.Blueprint.K2 OscInt.K2.TriDecayUpperAux

/-- **K2-U** from K2-L, P5, P6 and P7 (with TRI-K/X, `ReducedBridge.bridge`, T6E′). -/
theorem triDecayUpper_of (hL : OscInt.Statements.ReducedOrderBoundStatement)
    (h5 : OscInt.Blueprint.K2.ReducedCurveExistsFacts) (h6 : OscInt.Blueprint.K2.ReducedOrderTwoFacts)
    (h7 : OscInt.Blueprint.K2.TorusPatchFacts) : OscInt.Statements.TriDecayUpperStatement := by
  intro α
  by_cases hα : α = 0
  · subst hα
    refine ⟨(8 * (1 + Real.sqrt 7) / 3) ^ 2, fun t n ht => ?_⟩
    have hrate : triRate 0 = 2 / 3 := by unfold triRate; simp
    rw [OscInt.API.TriangularDecaySanity.triKernel_zero, hrate,
      show (-(2 / 3 : ℝ)) = -(2 : ℝ) / 3 by ring]
    exact OscInt.API.latticeLaplacianCubeRoot t n (by linarith)
  · obtain ⟨C, hC⟩ := h7 (triPhase α) (triRate α) (OscInt.API.TriDeriv.triPhase_smooth α) (triRate_nonneg α)
      (triPhase_per₁ α) (triPhase_per₂ α) (local_tri hL h5 h6 hα)
    exact ⟨C, fun t n ht => hC t n ht⟩


end OscInt.K2
