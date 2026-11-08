/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Global

/-!
# SH: the sharpness lemma (lead)

Route `docs/proof-GD.md` R5. One lemma over a filter `l` and a map `x : α → ℝ` tending to `+∞`, specialised to the
real variable (`x = id`) and to sequences (`x = Nat.cast`).
-/

namespace OscInt.API.SharpnessAux

open Filter Topology

variable {α : Type*} {l : Filter α} {x : α → ℝ} {I : α → ℂ} {σ : ℝ} {c : ℂ}

theorem eventually_lower (hx : Tendsto x l atTop)
    (h : Tendsto (fun a => (((x a) ^ σ : ℝ) : ℂ) * I a) l (𝓝 c)) (hc : c ≠ 0) :
    ∀ᶠ a in l, ‖c‖ / 2 * x a ^ (-σ) ≤ ‖I a‖ := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 : ∀ᶠ a in l, ‖(((x a) ^ σ : ℝ) : ℂ) * I a - c‖ < ‖c‖ / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp h).eventually (gt_mem_nhds (half_pos hpos))
  filter_upwards [h1, hx.eventually_gt_atTop 0] with a ha hxa
  have hn : ‖(((x a) ^ σ : ℝ) : ℂ) * I a‖ = x a ^ σ * ‖I a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxa _)]
  have hge : ‖c‖ / 2 ≤ x a ^ σ * ‖I a‖ := by
    have := norm_sub_norm_le c ((((x a) ^ σ : ℝ) : ℂ) * I a)
    rw [norm_sub_rev] at this; linarith
  have hp : 0 < x a ^ σ := Real.rpow_pos_of_pos hxa _
  rw [Real.rpow_neg hxa.le, ← div_eq_mul_inv, div_le_iff₀ hp]
  linarith [mul_comm (x a ^ σ) ‖I a‖]

theorem not_faster (hx : Tendsto x l atTop) [l.NeBot]
    (h : Tendsto (fun a => (((x a) ^ σ : ℝ) : ℂ) * I a) l (𝓝 c)) (hc : c ≠ 0) (σ' : ℝ) (hσ : σ < σ') :
    ¬ ∃ C : ℝ, ∀ᶠ a in l, ‖I a‖ ≤ C * x a ^ (-σ') := by
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have ht : Tendsto (fun a => C * x a ^ (-(σ' - σ))) l (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hσ)).comp hx).const_mul C
  have h2 : ∀ᶠ a in l, C * x a ^ (-(σ' - σ)) < ‖c‖ / 2 := ht.eventually (gt_mem_nhds (half_pos hpos))
  obtain ⟨a, ha1, ha2, ha3, hxa⟩ :=
    (h2.and ((eventually_lower hx h hc).and (hC.and (hx.eventually_gt_atTop 0)))).exists
  have hp : 0 < x a ^ σ := Real.rpow_pos_of_pos hxa _
  have key : x a ^ σ * x a ^ (-σ') = x a ^ (-(σ' - σ)) := by
    rw [← Real.rpow_add hxa]; ring_nf
  have e1 : ‖c‖ / 2 ≤ x a ^ σ * ‖I a‖ := by
    have := mul_le_mul_of_nonneg_left ha2 hp.le
    rwa [show x a ^ σ * (‖c‖ / 2 * x a ^ (-σ)) = ‖c‖ / 2 by
      rw [mul_left_comm, ← Real.rpow_add hxa, add_neg_cancel, Real.rpow_zero, mul_one]] at this
  have e2 : x a ^ σ * ‖I a‖ ≤ C * x a ^ (-(σ' - σ)) := by
    have := mul_le_mul_of_nonneg_left ha3 hp.le
    rwa [mul_left_comm, key] at this
  linarith

end OscInt.API.SharpnessAux

namespace OscInt.API

open OscInt.Statements OscInt.API.SharpnessAux Filter Topology

/-- **SH** (`SharpnessStatement`). -/
theorem sharpness : SharpnessStatement := by
  refine ⟨fun I σ c h hc => ⟨eventually_lower tendsto_id h hc, fun σ' hσ => not_faster tendsto_id h hc σ' hσ⟩,
    fun I σ c h hc => ⟨eventually_lower tendsto_natCast_atTop_atTop h hc,
      fun σ' hσ => not_faster tendsto_natCast_atTop_atTop h hc σ' hσ⟩⟩

end OscInt.API
