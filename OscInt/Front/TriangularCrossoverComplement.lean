/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayUpper
import OscInt.Front.TriangularDecayNormalized

/-!
# Batch A5U, part B2: the complement of the A5 points (`ComplementLocalFacts`)

Route `stmts/proof-A5U-draft.md`, section 5 (B2). A clone of the case logic of
`OscInt.K2.TriDecayUpperAux.local_tri` at the coupling `a₀ ≠ 0`, with B1 (`ReducedOrderBoundParamFacts`) for the
family `(α, k) ↦ triPhase α k` in place of K2-L. TRI-K (`OscInt.API.triClassification`) at `a₀` gives:
* a nondegenerate point: P5 and P6 (`OscInt.K2.reducedCurveExists`, `OscInt.K2.reducedOrderTwo`), order 2;
* a fold: P5 and `ReducedBridge.bridge`, order 3;
* an A3 point: P5 and the bridge, order 4;
* an A5 point: excluded by hypothesis.
Each order `m ≤ 4` gives `t^{−(1/2 + 1/m)} ≤ t^{−3/4}` for `t ≥ 1`.
-/

namespace OscInt.A5UAux

open OscInt.Statements OscInt.Blueprint.K2 OscInt.Blueprint.A5U OscInt.K2.TriDecayUpperAux
open scoped ContDiff

/-- The conclusion of B2 at one point `k₀` of `triPhase a₀`. -/
def a5uB_Loc (a₀ : ℝ) (k₀ : ℝ × ℝ) : Prop :=
  ∃ δ > 0, ∃ ρ > 0, ∃ C : ℝ, ∀ α : ℝ, |α - a₀| ≤ ρ →
    ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ), AmpBound 2 (Metric.closedBall k₀ δ) A M → 1 ≤ t →
      ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4)

/-- `(α, k) ↦ triPhase α k` is jointly `C^∞`. -/
theorem a5uB_triPhase_joint : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => triPhase p.1 p.2) := by
  unfold triPhase
  fun_prop

/-- B1 at a point of reduced order `m ≤ 4` of `triPhase a₀`, weakened to the exponent `3/4`. -/
theorem a5uB_local (hB1 : ReducedOrderBoundParamFacts) {a₀ : ℝ} {k₀ v w : ℝ × ℝ} {ε : ℝ} {h : ℝ → ℝ}
    {m : ℕ} (hm : 2 ≤ m) (hm4 : m ≤ 4) (hw : iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![w, w] ≠ 0) (hε : 0 < ε)
    (hred : ReducedCurve (triPhase a₀) k₀ v w ε h) (hd : iteratedDeriv m (reducedFn (triPhase a₀) k₀ v w h) 0 ≠ 0) :
    a5uB_Loc a₀ k₀ := by
  have hspan := OscInt.API.TriangularDecaySanity.span_of_hyps (triPhase a₀) k₀ v w ε h m
    (OscInt.API.TriDeriv.triPhase_smooth a₀) (by omega) hw hε hred hd
  obtain ⟨δ, hδ, ρ, hρ, C, hC⟩ := hB1 triPhase a₀ k₀ v w ε h m a5uB_triPhase_joint hm hspan hw hε hred hd
  refine ⟨δ, hδ, ρ, hρ, max C 0, fun α hα A M y t hA ht => ?_⟩
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hA.2.2 0 (by norm_num) k₀)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm4' : (m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hexp : -(1 / 2 + 1 / (m : ℝ)) ≤ -(3 : ℝ) / 4 := by
    have : 1 / 4 ≤ 1 / (m : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hm0]; linarith
    linarith
  have hpow : t ^ (-(1 / 2 + 1 / (m : ℝ))) ≤ t ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le ht hexp
  have hp0 : 0 ≤ t ^ (-(1 / 2 + 1 / (m : ℝ))) := Real.rpow_nonneg (by linarith) _
  calc ‖oscInt2 (fun κ => t * triPhase α κ + lin y κ) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ))) :=
        hC α hα A M y t hA ht
    _ ≤ max C 0 * M * t ^ (-(1 / 2 + 1 / (m : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) hp0
    _ ≤ max C 0 * M * t ^ (-(3 : ℝ) / 4) := mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) hM)

/-- The Hessian of `triPhase a₀` at `k₀` as a bilinear form, with its three readings. -/
theorem a5uB_hess (a₀ : ℝ) (k₀ : ℝ × ℝ) :
    (∀ a b : ℝ × ℝ, iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![a, b] = fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ a b) ∧
    (∀ a b : ℝ × ℝ, dd (triPhase a₀) k₀ a b = fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ a b) ∧
    fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ (0, 1) (1, 0) = fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ (1, 0) (0, 1) := by
  have hΨ : ContDiff ℝ ∞ (triPhase a₀) := OscInt.API.TriDeriv.triPhase_smooth a₀
  have hΨ2 : ContDiffAt ℝ 2 (triPhase a₀) k₀ := (hΨ.of_le (by simp)).contDiffAt
  have hDi : ∀ a b : ℝ × ℝ, iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![a, b] =
      fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ a b := fun a b => by
    rw [iteratedFDeriv_two_apply]; rfl
  refine ⟨hDi, fun a b => by rw [OscInt.API.dd_iteratedFDeriv (triPhase a₀) k₀ hΨ2, hDi], ?_⟩
  rw [← hDi, ← hDi]; exact OscInt.API.ReducedBridge.iteratedFDeriv_two_swap hΨ k₀ _ _

/-- A nondegenerate point of `triPhase a₀`: order 2 (P5, P6). -/
theorem a5uB_nondeg (hB1 : ReducedOrderBoundParamFacts) {a₀ : ℝ} {k₀ : ℝ × ℝ}
    (hdet : hessDet (triPhase a₀) k₀ ≠ 0) : a5uB_Loc a₀ k₀ := by
  obtain ⟨hDi, hdd, hsym⟩ := a5uB_hess a₀ k₀
  set D := fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ with hD
  have hdet' : D (1, 0) (1, 0) * D (0, 1) (0, 1) - D (1, 0) (0, 1) ^ 2 ≠ 0 := by
    simpa only [hessDet, hdd] using hdet
  suffices H : ∃ v w : ℝ × ℝ, D w w ≠ 0 ∧ D v v - D v w ^ 2 / D w w ≠ 0 by
    obtain ⟨v, w, hw, hg⟩ := H
    have hw' : iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![w, w] ≠ 0 := by rwa [hDi]
    obtain ⟨ε, hε, h, hred⟩ :=
      OscInt.K2.reducedCurveExists (triPhase a₀) k₀ v w (OscInt.API.TriDeriv.triPhase_smooth a₀) hw'
    have h2 := OscInt.K2.reducedOrderTwo (triPhase a₀) k₀ v w ε h (OscInt.API.TriDeriv.triPhase_smooth a₀)
      hw' hε hred
    rw [hDi, hDi, hDi] at h2
    exact a5uB_local hB1 (m := 2) le_rfl (by norm_num) hw' hε hred (by rw [h2]; exact hg)
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

/-- A fold of `triPhase a₀`: order 3 (P5 and the bridge). -/
theorem a5uB_fold (hB1 : ReducedOrderBoundParamFacts) {a₀ : ℝ} {k₀ : ℝ × ℝ}
    (hF : FoldOrNondeg (triPhase a₀) k₀) (hdet : ¬ hessDet (triPhase a₀) k₀ ≠ 0) : a5uB_Loc a₀ k₀ := by
  obtain ⟨hDi, hdd, hsym⟩ := a5uB_hess a₀ k₀
  have hΨ : ContDiff ℝ ∞ (triPhase a₀) := OscInt.API.TriDeriv.triPhase_smooth a₀
  have hΨ3 : ContDiffAt ℝ 3 (triPhase a₀) k₀ := (hΨ.of_le (by simp)).contDiffAt
  set D := fderiv ℝ (fderiv ℝ (triPhase a₀)) k₀ with hD
  obtain ⟨⟨v₀, w₀, hne⟩, hfold⟩ := hF.resolve_left hdet
  have hdet0 : D (1, 0) (1, 0) * D (0, 1) (0, 1) - D (1, 0) (0, 1) ^ 2 = 0 := by
    simpa only [hessDet, hdd] using not_not.mp hdet
  have hne' : D v₀ w₀ ≠ 0 := by rwa [hdd] at hne
  suffices H : ∃ v w : ℝ × ℝ, v ≠ 0 ∧ (∀ z, D v z = 0) ∧ D w w ≠ 0 by
    obtain ⟨v, w, hv0, hker, hw⟩ := H
    have hw' : iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![w, w] ≠ 0 := by rwa [hDi]
    have hker' : ∀ z, iteratedFDeriv ℝ 2 (triPhase a₀) k₀ ![v, z] = 0 := fun z => by rw [hDi]; exact hker z
    have hddd := hfold v hv0 (fun z => by rw [hdd]; exact hker z)
    rw [OscInt.API.ddd_iteratedFDeriv (triPhase a₀) k₀ hΨ3] at hddd
    obtain ⟨ε, hε, h, hred⟩ := OscInt.K2.reducedCurveExists (triPhase a₀) k₀ v w hΨ hw'
    have hb := (OscInt.API.ReducedBridge.bridge (triPhase a₀) k₀ v w ε h hΨ hker' hw' hε hred).1
    exact a5uB_local hB1 (m := 3) (by norm_num) (by norm_num) hw' hε hred (by rw [hb]; exact hddd)
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

/-- An A3 point of `triPhase a₀`: order 4 (P5 and the bridge). -/
theorem a5uB_a3 (hB1 : ReducedOrderBoundParamFacts) {a₀ : ℝ} {k₀ : ℝ × ℝ}
    (hA3 : IsA3Point (triPhase a₀) k₀) : a5uB_Loc a₀ k₀ := by
  have hΨ : ContDiff ℝ ∞ (triPhase a₀) := OscInt.API.TriDeriv.triPhase_smooth a₀
  obtain ⟨v, w, hker, hw, -, hq⟩ := hA3
  obtain ⟨ε, hε, h, hred⟩ := OscInt.K2.reducedCurveExists (triPhase a₀) k₀ v w hΨ hw
  have hb := (OscInt.API.ReducedBridge.bridge (triPhase a₀) k₀ v w ε h hΨ hker hw hε hred).2
  exact a5uB_local hB1 (m := 4) (by norm_num) le_rfl hw hε hred (by rw [hb]; exact div_ne_zero hq hw)

/-- **B2** The complement of the A5 points, from B1. -/
theorem complementLocal : OscInt.Blueprint.A5U.ComplementLocalFacts := by
  intro hB1 a₀ ha₀ k₀ hk
  rcases OscInt.API.triClassification a₀ ha₀ k₀ with hF | hA3 | hA5
  · by_cases hdet : hessDet (triPhase a₀) k₀ ≠ 0
    · exact a5uB_nondeg hB1 hdet
    · exact a5uB_fold hB1 hF hdet
  · exact a5uB_a3 hB1 hA3
  · exact absurd hA5 hk

end OscInt.A5UAux
