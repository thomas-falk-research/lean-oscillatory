/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayCore

/-!
# Batch A5U, part A4: `CoreEstimateMultiFacts`

Route: `docs/proof-A5U.md`, section 4 (packet X4). A clone of `OscInt.K2.coreEstimateM`
(`OscInt/Front/TriangularDecayCore.lean`) of order 6: the amplitude from `CoreAux.amplitude_facts`, the outer
integral from `Core4Aux.oscInt2_eq_outer_linear`, the derivative chain `t g^{(j)}` of length 6
(`CoreEstimateMAux.hasDerivOn_iter`), and the piecewise van der Corput bound `PiecewiseVdCBound` (A3's conclusion)
with thresholds `t l_j` in place of `OscInt.API.vdCk`. The constant is
`P = 19 · 8 (1 + 4b)(1 + 2a(1 + 24 β(D, μ)⁶))/√μ`.
-/

namespace OscInt.A5UAux

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open OscInt.StationaryPhase.CoreAux OscInt.Cusp.Core4Aux OscInt.K2.CoreEstimateMAux
open scoped ContDiff

/-- The constant algebra: `8/√(tμ) = (8/√μ) t^{−1/2}`, with the other factors kept explicit. -/
theorem a5uG3_arith {t μ : ℝ} (ht : 0 < t) (hμ : 0 < μ) (S b M Y : ℝ) :
    19 * S * (8 / √(t * μ) * ((1 + 4 * b) * M * Y)) =
      19 * 8 * ((1 + 4 * b) * Y) / √μ * M * t ^ (-(1 : ℝ) / 2) * S := by
  rw [Real.sqrt_mul ht.le, Real.sqrt_eq_rpow t, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg ht.le]
  have hst : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsμ : 0 < √μ := Real.sqrt_pos.2 hμ
  field_simp

/-- **A4** The multi-order core estimate, from A3's bound. -/
theorem coreEstimateMulti : CoreEstimateMultiFacts := by
  intro hpw a b μ D ha hb hμ
  let Y : ℝ := (1 + 4 * b) * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))
  refine ⟨19 * 8 * Y / √μ, ?_⟩
  intro Q ys A M t p ν l₂ l₃ l₄ hν hl₂ hl₃ hl₄ hC halt hA ht
  obtain ⟨hQ, hys, hcrit, hlow, hD, hνm⟩ := hC
  obtain ⟨hA2, hsupp, hM⟩ := hA
  have hQ4 : ContDiff ℝ 4 Q := hQ.of_le (by simp)
  have hys3 : ContDiffOn ℝ 3 ys (Ioo (-2 * a) (2 * a)) := hys.of_le (by simp)
  have ht0 : 0 < t := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  have e2b : -2 * b = -(2 * b) := by ring
  rw [e2b] at hlow hD
  have hcrit' : ∀ x ∈ Icc (-a) a, pd e₂ Q (x, ys x) = 0 := fun x hx => (hcrit x hx).2
  obtain ⟨cys, hγ, h1, -, -⟩ := phase_facts (m := t) hQ4 hys3 ha hcrit'
  have hA2' : ContDiff ℝ 2 A := by exact_mod_cast hA2
  obtain ⟨hamp, hnorm⟩ := amplitude_facts (D := D) hQ4 hA2' ha hb ht0 hμ hM0 cys hγ
    (fun x hx => by
      rw [clamp_eq hx]
      exact ⟨⟨by linarith [(hcrit x hx).1.1], by linarith [(hcrit x hx).1.2]⟩, hcrit' x hx⟩)
    hlow (fun i hi x hx s hs => hD i hi x hx s hs) hM hsupp
  have hg : ContDiffOn ℝ ∞ (fun x => Q (x, ys x)) (Ioo (-2 * a) (2 * a)) :=
    hQ.comp_contDiffOn (contDiffOn_id.prodMk hys)
  let chain : ℕ → ℝ → ℝ := fun j => if j = 0 then fun x => t * Q (x, clamp a ys x)
    else fun x => t * iteratedDeriv j (fun s => Q (s, ys s)) x
  have hchain : DerivChain chain 6 (-a) a := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa [chain] using h1
    · have hj0 : j ≠ 0 := by omega
      simpa [chain, hj0] using hasDerivOn_iter (c := t) ha hg j
  have hc : ∀ j, j ≠ 0 → ∀ x, |chain j x| = t * |iteratedDeriv j (fun s => Q (s, ys s)) x| := by
    intro j hj x
    simp only [chain, hj, ite_false, abs_mul, abs_of_pos ht0]
  have h6 : ∀ x ∈ Ioo (-a) a, chain 6 x ≠ 0 := by
    intro x hx h0
    have := hc 6 (by norm_num) x
    rw [h0, abs_zero] at this
    have hpos : 0 < t * |iteratedDeriv 6 (fun s => Q (s, ys s)) x| :=
      mul_pos ht0 (hν.trans_le (hνm x (Ioo_subset_Icc_self hx)))
    linarith
  have halt' : ∀ x ∈ Ioo (-a) a, t * l₂ < |chain 2 x| ∨ t * l₃ < |chain 3 x| ∨ t * l₄ < |chain 4 x| := by
    intro x hx
    rw [hc 2 (by norm_num), hc 3 (by norm_num), hc 4 (by norm_num)]
    rcases halt x hx with h | h | h
    · exact Or.inl (mul_lt_mul_of_pos_left h ht0)
    · exact Or.inr (Or.inl (mul_lt_mul_of_pos_left h ht0))
    · exact Or.inr (Or.inr (mul_lt_mul_of_pos_left h ht0))
  rw [oscInt2_eq_outer_linear hQ.continuous hA2'.continuous hsupp ha hb]
  have hv := hpw chain (innerF t b Q A (clamp a ys)) (innerF' t b Q A (clamp a ys)) (-a) a (t * p)
    (t * l₂) (t * l₃) (t * l₄) (by linarith) (by positivity) (by positivity) (by positivity) hchain h6 halt' hamp
  change ‖oscInt (fun x => t * Q (x, clamp a ys x) + t * p * x)
    (innerF t b Q A (clamp a ys)) (-a) a‖ ≤ _ at hv
  refine hv.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_))
  rw [a5uG3_arith ht0 hμ]
