/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover

/-!
# A5U part A2: restriction of the amplitude hypothesis and of `ampNorm`

On `[l, r] ⊆ [a, b]` the amplitude hypothesis restricts, and `ampNorm ψ ψ' l r ≤ ampNorm ψ ψ' a b`: the endpoint
value satisfies `‖ψ r‖ ≤ ‖ψ b‖ + ∫_r^b ‖ψ'‖` by the fundamental theorem of calculus, and the integral of `‖ψ'‖`
over `[a, b]` splits as `[a, l] + [l, r] + [r, b]` with a nonnegative first piece.
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.A5U

/-- **A2** Restriction of the amplitude hypothesis and of `ampNorm` to a subinterval. -/
theorem ampNormRestrict : AmpNormRestrictFacts := by
  intro ψ ψ' a b l r hal hlr hrb hψ
  obtain ⟨hc, hd, hi⟩ := hψ
  have hab : a ≤ b := hal.trans (hlr.trans hrb)
  have hsub : ∀ u v : ℝ, a ≤ u → v ≤ b → u ≤ v → IntervalIntegrable ψ' volume u v := fun u v hu hv huv =>
    hi.mono_set (by rw [uIcc_of_le huv, uIcc_of_le hab]; exact Icc_subset_Icc hu hv)
  have hn : ∀ u v : ℝ, a ≤ u → v ≤ b → u ≤ v → IntervalIntegrable (fun x => ‖ψ' x‖) volume u v :=
    fun u v hu hv huv => (hsub u v hu hv huv).norm
  refine ⟨⟨hc.mono (Icc_subset_Icc hal hrb), fun x hx => hd x ⟨hal.trans_lt hx.1, hx.2.trans_le hrb⟩,
    hsub l r hal hrb hlr⟩, ?_⟩
  have har : a ≤ r := hal.trans hlr
  have hftc : ∫ x in r..b, ψ' x = ψ b - ψ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrb (hc.mono (Icc_subset_Icc har le_rfl))
      (fun x hx => hd x ⟨har.trans_lt hx.1, hx.2⟩) (hsub r b har le_rfl hrb)
  have h1 : ‖ψ r‖ - ‖ψ b‖ ≤ ∫ x in r..b, ‖ψ' x‖ := by
    calc ‖ψ r‖ - ‖ψ b‖ ≤ ‖ψ r - ψ b‖ := norm_sub_norm_le _ _
      _ = ‖∫ x in r..b, ψ' x‖ := by rw [hftc, norm_sub_rev]
      _ ≤ ∫ x in r..b, ‖ψ' x‖ := intervalIntegral.norm_integral_le_integral_norm hrb
  have h2 : (∫ x in a..l, ‖ψ' x‖) + (∫ x in l..r, ‖ψ' x‖) + ∫ x in r..b, ‖ψ' x‖ = ∫ x in a..b, ‖ψ' x‖ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hn a l le_rfl (hlr.trans hrb) hal)
        (hn l r hal hrb hlr),
      intervalIntegral.integral_add_adjacent_intervals (hn a r le_rfl hrb har) (hn r b har le_rfl hrb)]
  have h3 : 0 ≤ ∫ x in a..l, ‖ψ' x‖ := intervalIntegral.integral_nonneg hal (fun _ _ => norm_nonneg _)
  unfold ampNorm
  linarith

end OscInt.A5UAux
