/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.Cusp.Core4
import OscInt.Cusp.Final

/-! Batch K2, part P1: `CoreEstimateMFacts`, the order-m core estimate with an outer linear term.

Route: `docs/proof-K2.md`, section 1 ("P1") and section 8. A clone of `OscInt.Cusp.coreEstimate4` with the order
4 replaced by any `m ≥ 2`: the amplitude from `CoreAux.amplitude_facts`, the outer integral from
`Core4Aux.oscInt2_eq_outer_linear`, a derivative chain of length m, and `OscInt.API.vdCk` of order m. -/

namespace OscInt.K2.CoreEstimateMAux

open Set Filter Topology MeasureTheory Complex OscInt.Statements OscInt.Blueprint
open OscInt.StationaryPhase.CoreAux
open scoped ContDiff

/-- For `j ≥ 1`, the j-th reduced derivative has derivative the (j+1)-th on `[-a, a]`. -/
theorem hasDerivOn_iter {g : ℝ → ℝ} {a c : ℝ} (ha : 0 < a) (hg : ContDiffOn ℝ ∞ g (Ioo (-2 * a) (2 * a)))
    (j : ℕ) :
    HasDerivOn (fun x => c * iteratedDeriv j g x) (fun x => c * iteratedDeriv (j + 1) g x) (-a) a := by
  have hsub : Icc (-a) a ⊆ Ioo (-2 * a) (2 * a) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgn : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g (Ioo (-2 * a) (2 * a)) :=
    hg.of_le (by exact_mod_cast le_top)
  have hd : ∀ x ∈ Ioo (-2 * a) (2 * a), HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g x) x :=
    fun x hx => hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hgn (i := j) (by omega) hx
  refine ⟨?_, fun x hx => ((hd x (hsub (Ioo_subset_Icc_self hx))).const_mul c)⟩
  intro x hx
  exact ((hd x (hsub hx)).continuousAt.const_mul c).continuousWithinAt

/-- The exponent algebra: add `-1/2` and `-1/m`, keeping the parameter factors explicit. -/
theorem arithM {m t μ ν : ℝ} (_hm : 0 < m) (ht : 0 < t) (hμ : 0 < μ) (hν : 0 < ν) (P : ℝ) :
    (t * ν) ^ (-(1 : ℝ) / m) * (8 / √(t * μ) * P) =
      8 * ν ^ (-(1 : ℝ) / m) / √μ * P * t ^ (-(1 / 2 + 1 / m)) := by
  have he : -(1 / 2 + 1 / m) = -(1 / 2 : ℝ) + -(1 : ℝ) / m := by ring
  rw [he, Real.rpow_add ht, Real.mul_rpow ht.le hν.le, Real.sqrt_mul ht.le, Real.sqrt_eq_rpow t,
    Real.rpow_neg ht.le]
  have hst : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsμ : 0 < √μ := Real.sqrt_pos.2 hμ
  field_simp

end OscInt.K2.CoreEstimateMAux

namespace OscInt.K2

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2
open OscInt.StationaryPhase.CoreAux OscInt.Cusp.Core4Aux CoreEstimateMAux
open scoped ContDiff

/-- **K2-P1.** The order-m core estimate with an outer linear term. -/
theorem coreEstimateM : CoreEstimateMFacts := by
  intro m hm2 a b μ ν D ha hb hμ hν
  let K : ℝ := (5 : ℝ) * 2 ^ (m - 1) - 2
  let Y : ℝ := (1 + 4 * b) * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))
  refine ⟨K * (8 * ν ^ (-(1 : ℝ) / (m : ℝ)) / √μ) * Y, ?_⟩
  intro Q ys A M t p hC hA ht
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
  have hchain : DerivChain chain m (-a) a := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa [chain] using h1
    · have hj0 : j ≠ 0 := by omega
      simpa [chain, hj0] using hasDerivOn_iter (c := t) ha hg j
  have hm0 : m ≠ 0 := by omega
  have hν' : ∀ x ∈ Ioo (-a) a, t * ν ≤ |chain m x| := by
    intro x hx
    change t * ν ≤ |(if m = 0 then fun x => t * Q (x, clamp a ys x)
      else fun x => t * iteratedDeriv m (fun s => Q (s, ys s)) x) x|
    rw [ite_eq_right_iff.mpr (fun h => absurd h hm0), abs_mul, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (hνm x (Ioo_subset_Icc_self hx)) ht0.le
  rw [oscInt2_eq_outer_linear hQ.continuous hA2'.continuous hsupp ha hb]
  have hv := OscInt.API.vdCk m chain (innerF t b Q A (clamp a ys)) (innerF' t b Q A (clamp a ys))
    (-a) a (t * ν) (t * p) hm2 (by linarith) (by positivity) hchain hν' hamp
  change ‖oscInt (fun x => t * Q (x, clamp a ys x) + t * p * x)
    (innerF t b Q A (clamp a ys)) (-a) a‖ ≤ _ at hv
  have hK : 0 ≤ K := by
    have : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
    simp only [K]; linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine hv.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_))
  rw [mul_assoc, arithM hmR ht0 hμ hν]
  simp only [K, Y]
  ring

end OscInt.K2

