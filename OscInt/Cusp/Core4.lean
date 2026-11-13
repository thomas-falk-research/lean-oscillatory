/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Cusp.VdC4
import OscInt.StationaryPhase.Core

/-! Batch A3, P2. The unbounded outer linear coefficient is never inserted into CoreHyps.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`. -/

namespace OscInt.Cusp.Core4Aux

open Set Filter Topology MeasureTheory Complex OscInt.Statements OscInt.Blueprint
open OscInt.StationaryPhase.CoreAux

/-- On the smaller open interval the reduced derivative is the x partial derivative along the graph. -/
theorem reduced_deriv_eventually {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {a x : ℝ}
    (hQ : ContDiff ℝ 4 Q) (hys : ContDiffOn ℝ 3 ys (Ioo (-2 * a) (2 * a))) (ha : 0 < a)
    (hcrit : ∀ t ∈ Icc (-a) a, pd e₂ Q (t, ys t) = 0) (hx : x ∈ Ioo (-a) a) :
    deriv (fun t => Q (t, ys t)) =ᶠ[𝓝 x] fun t => pd e₁ Q (t, ys t) := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  have ht' : t ∈ Ioo (-2 * a) (2 * a) := by
    constructor <;> linarith [ht.1, ht.2]
  have hd : DifferentiableAt ℝ ys t :=
    (hys.differentiableOn (by norm_num) t ht').differentiableAt (isOpen_Ioo.mem_nhds ht')
  exact (hasDerivAt_reduced (hQ.differentiable (by norm_num)) hd
    (hcrit t (Ioo_subset_Icc_self ht))).deriv

/-- The cubic reduced derivative is continuous at the endpoints and differentiable in the interior. -/
theorem phase_four_last {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ} {a m : ℝ}
    (hQ : ContDiff ℝ 4 Q) (hys : ContDiffOn ℝ 3 ys (Ioo (-2 * a) (2 * a))) (ha : 0 < a)
    (hcrit : ∀ x ∈ Icc (-a) a, pd e₂ Q (x, ys x) = 0) :
    HasDerivOn (fun x => m * iteratedDeriv 3 (fun t => Q (t, ys t)) x)
      (fun x => m * iteratedDeriv 4 (fun t => Q (t, ys t)) x) (-a) a := by
  let g : ℝ → ℝ := fun t => Q (t, ys t)
  let R : ℝ → ℝ := fun t => pd e₁ Q (t, ys t)
  have hsub : Icc (-a) a ⊆ Ioo (-2 * a) (2 * a) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hg : ContDiffOn ℝ 3 g (Ioo (-2 * a) (2 * a)) :=
    (hQ.of_le (by norm_num)).comp_contDiffOn (contDiffOn_id.prodMk hys)
  have hR : ContDiffOn ℝ 3 R (Ioo (-2 * a) (2 * a)) :=
    (contDiff_pd (n := 3) hQ e₁).comp_contDiffOn (contDiffOn_id.prodMk hys)
  have hc : ContinuousOn (iteratedDeriv 3 g) (Ioo (-2 * a) (2 * a)) :=
    (hg.continuousOn_iteratedDerivWithin (m := 3) (by norm_num) isOpen_Ioo.uniqueDiffOn).congr
      (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)
  refine ⟨continuousOn_const.mul (hc.mono hsub), fun x hx => ?_⟩
  have he : deriv g =ᶠ[𝓝 x] R := reduced_deriv_eventually hQ hys ha hcrit hx
  have h4 : iteratedDeriv 4 g x = iteratedDeriv 3 R x := by
    rw [iteratedDeriv_succ']
    exact Filter.EventuallyEq.iteratedDeriv_eq 3 he
  have h3 : iteratedDeriv 3 g =ᶠ[𝓝 x] iteratedDeriv 2 R := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    rw [iteratedDeriv_succ']
    exact Filter.EventuallyEq.iteratedDeriv_eq 2 (reduced_deriv_eventually hQ hys ha hcrit ht)
  have hd := hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hR (i := 2) (by norm_num)
    (hsub (Ioo_subset_Icc_self hx))
  show HasDerivAt (fun x => m * iteratedDeriv 3 g x) (m * iteratedDeriv 4 g x) x
  rw [h4]
  exact (hd.congr_of_eventuallyEq h3).const_mul m

/-- Fubini with the outer phase `Q(x,clamp ys x)+p*x`; the two linear terms cancel in the inner phase. -/
theorem oscInt2_eq_outer_linear {Q : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {ys : ℝ → ℝ}
    {a b m p : ℝ} (hQ : Continuous Q) (hA : Continuous A)
    (hsupp : tsupport A ⊆ Icc (-a) a ×ˢ Icc (-b) b) (ha : 0 < a) (hb : 0 < b) :
    oscInt2 (fun k => m * (Q k + p * k.1)) A =
      oscInt (fun x => m * Q (x, clamp a ys x) + (m * p) * x)
        (innerF m b Q A (clamp a ys)) (-a) a := by
  rw [oscInt2_eq_iterated (Q := fun k => Q k + p * k.1) (fun x => Q (x, clamp a ys x) + p * x)
    (hQ.add (continuous_const.mul continuous_fst)) hA hsupp ha hb]
  have hi : ∀ x t, (Q (x, t) + p * x) - (Q (x, clamp a ys x) + p * x) =
      Q (x, t) - Q (x, clamp a ys x) := fun x t => by ring
  have ho : ∀ x, m * (Q (x, clamp a ys x) + p * x) = m * Q (x, clamp a ys x) + (m * p) * x :=
    fun x => by ring
  simp only [oscInt, innerF, hi, ho]

/-- Add the exponents `-1/2` and `-1/4`, keeping the parameter factors explicit. -/
theorem arith4 {m μ ν : ℝ} (hm : 0 < m) (hμ : 0 < μ) (hν : 0 < ν) (P : ℝ) :
    38 * (m * ν) ^ (-(1 : ℝ) / 4) * (8 / √(m * μ) * P) =
      304 * ν ^ (-(1 : ℝ) / 4) / √μ * P * m ^ (-(3 / 4 : ℝ)) := by
  have he : -(3 / 4 : ℝ) = -(1 / 2) + -(1 : ℝ) / 4 := by norm_num
  rw [he, Real.rpow_add hm, Real.mul_rpow hm.le hν.le, Real.sqrt_mul hm.le, Real.sqrt_eq_rpow m,
    Real.rpow_neg hm.le]
  have hsm : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm _
  have hsμ : 0 < √μ := Real.sqrt_pos.2 hμ
  field_simp
  ring

end OscInt.Cusp.Core4Aux

namespace OscInt.Cusp

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint
open OscInt.StationaryPhase.CoreAux Core4Aux

/-- **A3-P2.** The existing transverse amplitude bound and P1 give the order-four core estimate. -/
theorem coreEstimate4 : CoreEstimate4Facts := by
  intro a b μ ν D ha hb hμ hν
  let Y : ℝ := (1 + 4 * b) * (1 + 2 * a * (1 + 24 * beta D μ ^ 6))
  refine ⟨304 * ν ^ (-(1 : ℝ) / 4) / √μ * Y, ?_⟩
  intro Q ys A M m p hC hA hm
  obtain ⟨hQ, hys, hcrit, hlow, hD, _hysbound, hν4⟩ := hC
  obtain ⟨hA2, hsupp, hM⟩ := hA
  have hm0 : 0 < m := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  have e2b : -2 * b = -(2 * b) := by ring
  rw [e2b] at hlow hD
  have hcrit' : ∀ x ∈ Icc (-a) a, pd e₂ Q (x, ys x) = 0 := fun x hx => (hcrit x hx).2
  obtain ⟨cys, hγ, h1, h2, h3⟩ := phase_facts (m := m) hQ hys ha hcrit'
  have h4 := phase_four_last (m := m) hQ hys ha hcrit'
  have hA2' : ContDiff ℝ 2 A := by exact_mod_cast hA2
  obtain ⟨hamp, hnorm⟩ := amplitude_facts (D := D) hQ hA2' ha hb hm0 hμ hM0 cys hγ
    (fun x hx => by
      rw [clamp_eq hx]
      exact ⟨⟨by linarith [(hcrit x hx).1.1], by linarith [(hcrit x hx).1.2]⟩, hcrit' x hx⟩)
    hlow (fun i hi x hx t ht => hD i hi x hx t ht) hM hsupp
  let chain : ℕ → ℝ → ℝ := fun j => if j = 0 then fun x => m * Q (x, clamp a ys x)
    else fun x => m * iteratedDeriv j (fun t => Q (t, ys t)) x
  have hchain : DerivChain chain 4 (-a) a := by
    intro j hj
    interval_cases j
    · simpa [chain] using h1
    · simpa [chain] using h2
    · simpa [chain] using h3
    · simpa [chain] using h4
  have hν' : ∀ x ∈ Ioo (-a) a, m * ν ≤ |chain 4 x| := by
    intro x hx
    change m * ν ≤ |m * iteratedDeriv 4 (fun t => Q (t, ys t)) x|
    rw [abs_mul, abs_of_pos hm0]
    exact mul_le_mul_of_nonneg_left (hν4 x (Ioo_subset_Icc_self hx)) hm0.le
  rw [oscInt2_eq_outer_linear hQ.continuous hA2'.continuous hsupp ha hb]
  have hv := vdc4 chain (innerF m b Q A (clamp a ys)) (innerF' m b Q A (clamp a ys))
    (-a) a (m * ν) (m * p) (by linarith) (by positivity) hchain hν' hamp
  change ‖oscInt (fun x => m * Q (x, clamp a ys x) + m * p * x)
    (innerF m b Q A (clamp a ys)) (-a) a‖ ≤ _ at hv
  refine hv.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (le_of_eq ?_))
  rw [arith4 hm0 hμ hν]
  simp only [Y]
  ring

end OscInt.Cusp
