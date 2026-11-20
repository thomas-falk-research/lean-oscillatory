/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.SecondDerivSharp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Batch VC2, part VC1: the turning point and the root inequality (route `docs/proof-VC2.md`, V1 and V2)

* `vdc2TurningPointFacts`: a derivative that increases at a positive rate on `(a, b)` is negative before
  `x₀ = sup {x ∈ (a, b) | f′ x ≤ 0}` (or `x₀ = a` if that set is empty) and positive after it.
* `vdc2RootFacts`: on a side, `2 lam (f(x) − f(c)) ≤ f′(x)²`, by monotone comparison of
  `G(y) = f(y) + f′(x) (x − y) − lam (x − y)² / 2` on `[c, x]`.
-/

namespace OscInt.SecondDerivSharpAux

open Set OscInt.Statements OscInt.Blueprint.SecondDerivSharp

/-- The turning point when the derivative is nonpositive somewhere: `x₀` is the supremum of those points. -/
theorem vdc2T_turn_of_nonempty (f' : ℝ → ℝ) (a b lam : ℝ) (hlam : 0 < lam)
    (hrate : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y → lam * (y - x) ≤ f' y - f' x)
    (hne : {x | x ∈ Ioo a b ∧ f' x ≤ 0}.Nonempty) :
    ∃ x₀ ∈ Icc a b, (∀ x ∈ Ioo a x₀, f' x < 0) ∧ ∀ x ∈ Ioo x₀ b, 0 < f' x := by
  have hbdd : BddAbove {x | x ∈ Ioo a b ∧ f' x ≤ 0} := ⟨b, fun x hx => hx.1.2.le⟩
  have hle : a ≤ sSup {x | x ∈ Ioo a b ∧ f' x ≤ 0} := by
    obtain ⟨z, hz⟩ := hne
    exact hz.1.1.le.trans (le_csSup hbdd hz)
  refine ⟨sSup {x | x ∈ Ioo a b ∧ f' x ≤ 0}, ⟨hle, csSup_le hne fun x hx => hx.1.2.le⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hne hx.2
    have h1 := hrate x ⟨hx.1, hxz.trans hz.1.2⟩ z hz.1 hxz.le
    have h2 : 0 < lam * (z - x) := mul_pos hlam (sub_pos.2 hxz)
    have h3 : f' z ≤ 0 := hz.2
    linarith
  · intro x hx
    by_contra hneg
    have hxZ : x ∈ {x | x ∈ Ioo a b ∧ f' x ≤ 0} := ⟨⟨hle.trans_lt hx.1, hx.2⟩, not_lt.1 hneg⟩
    exact absurd (le_csSup hbdd hxZ) (not_le.2 hx.1)

/-- **V-turn** (route V1): the turning point of a derivative that increases at a positive rate. -/
theorem vdc2TurningPointFacts : Vdc2TurningPointFacts := by
  intro f' a b lam hab hlam hrate
  by_cases hne : {x | x ∈ Ioo a b ∧ f' x ≤ 0}.Nonempty
  · exact vdc2T_turn_of_nonempty f' a b lam hlam hrate hne
  · refine ⟨a, left_mem_Icc.2 hab, fun x hx => absurd (hx.1.trans hx.2) (lt_irrefl a), fun x hx => ?_⟩
    by_contra hneg
    exact hne ⟨x, hx, not_lt.1 hneg⟩

/-- The comparison function `y ↦ f y + h (x − y) − lam (x − y)² / 2` has derivative `m − h + lam (x − y)`. -/
theorem vdc2T_hasDerivAt_compare (f : ℝ → ℝ) (h lam x y m : ℝ) (hf : HasDerivAt f m y) :
    HasDerivAt (fun y => f y + h * (x - y) - lam * (x - y) ^ 2 / 2) (m - h + lam * (x - y)) y := by
  have h2 : HasDerivAt (fun y : ℝ => x - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub x
  have h3 := (hf.add (h2.const_mul h)).sub (((h2.pow 2).const_mul lam).div_const 2)
  refine h3.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- **V-root** (route V2): on a side, `2 lam (f(x) − f(c)) ≤ f′(x)²`. -/
theorem vdc2RootFacts : Vdc2RootFacts := by
  intro f f' c d lam hS x hx
  obtain ⟨-, hlam, hcont, hder, hrate, -⟩ := hS
  have hG : AntitoneOn (fun y => f y + f' x * (x - y) - lam * (x - y) ^ 2 / 2) (Icc c x) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => f' y - f' x + lam * (x - y))
      (convex_Icc c x) ?_ ?_ ?_
    · have hc : ContinuousOn f (Icc c x) := hcont.mono (Icc_subset_Icc le_rfl hx.2.le)
      exact (hc.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))).sub
        ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)).div_const 2)
    · intro y hy
      rw [interior_Icc] at hy
      exact (vdc2T_hasDerivAt_compare f (f' x) lam x y (f' y) (hder y ⟨hy.1, hy.2.trans hx.2⟩)).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have h1 := hrate y ⟨hy.1, hy.2.trans hx.2⟩ x hx hy.2.le
      linarith
  have h1 := hG (left_mem_Icc.2 hx.1.le) (right_mem_Icc.2 hx.1.le) hx.1.le
  simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    sub_zero] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
  nlinarith [sq_nonneg (f' x - lam * (x - c))]

end OscInt.SecondDerivSharpAux
