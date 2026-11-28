/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.StationaryLeadingSharp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Batch SPL-N, part N10: a nonzero smooth compactly supported amplitude has `‖g₃‖₁ > 0` (helper of agent C)

Route `docs/proof-SPLN.md`, section 2, **Assembly** (SPL-NC): `g₃ = g‴` is continuous because `g` is `C^∞` and
derivatives are unique; `∫ ‖g₃‖ = 0` with `‖g₃‖` continuous, integrable and nonnegative gives `g₃ = 0`; then `g₂`,
`g₁`, `g` in turn have zero derivative and compact support, so each vanishes. Proves
`splnC_thirdPos : SplnThirdPosFacts`.
-/

namespace OscInt.SPLNAux

open OscInt.Statements OscInt.Blueprint.SPLN MeasureTheory
open scoped ContDiff

/-- A constant function on `ℝ` with compact support is zero. -/
theorem splnC_const_zero (c : ℂ) (h : HasCompactSupport (fun _ : ℝ => c)) : c = 0 := by
  by_contra hc
  have hs : tsupport (fun _ : ℝ => c) = Set.univ := by
    simp [tsupport, Function.support, hc]
  have hcomp : IsCompact (tsupport (fun _ : ℝ => c)) := h
  rw [hs] at hcomp
  exact noncompact_univ ℝ hcomp

/-- A function with compact support and zero derivative everywhere vanishes. -/
theorem splnC_zero_of_deriv (f f' : ℝ → ℂ) (hd : ∀ x, HasDerivAt f (f' x) x) (h0 : ∀ x, f' x = 0)
    (hs : HasCompactSupport f) : ∀ x, f x = 0 := by
  have hc : ∀ x, f x = f 0 := fun x =>
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => by rw [(hd t).deriv, h0]) x 0
  have hf : f = fun _ => f 0 := funext hc
  have hz : f 0 = 0 := splnC_const_zero (f 0) (hf ▸ hs)
  exact fun x => (hc x).trans hz

/-- **N10** A smooth compactly supported amplitude that is not identically zero has `‖g₃‖₁ > 0`. -/
theorem splnC_thirdPos : SplnThirdPosFacts := by
  intro g g₁ g₂ g₃ hg hsm hcs hne
  obtain ⟨d1, d2, d3, -, -, -, hi3⟩ := hg
  have e1 : deriv g = g₁ := funext fun x => (d1 x).deriv
  have e2 : deriv g₁ = g₂ := funext fun x => (d2 x).deriv
  have e3 : deriv g₂ = g₃ := funext fun x => (d3 x).deriv
  have h3 : iteratedDeriv 3 g = g₃ := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, e1, e2, e3]
  have hcont : Continuous g₃ := h3 ▸ hsm.continuous_iteratedDeriv 3 (WithTop.coe_le_coe.mpr le_top)
  refine lt_of_le_of_ne (integral_nonneg fun _ => norm_nonneg _) (Ne.symm ?_)
  intro h0
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hi3.norm).mp h0
  have hz : (fun t => ‖g₃ t‖) = 0 := (hcont.norm.ae_eq_iff_eq volume continuous_zero).mp hae
  have hg3 : ∀ t, g₃ t = 0 := fun t => norm_eq_zero.mp (congrFun hz t)
  have s1 : HasCompactSupport g₁ := e1 ▸ hcs.deriv
  have s2 : HasCompactSupport g₂ := e2 ▸ s1.deriv
  have z2 := splnC_zero_of_deriv g₂ g₃ d3 hg3 s2
  have z1 := splnC_zero_of_deriv g₁ g₂ d2 z2 s1
  have z0 := splnC_zero_of_deriv g g₁ d1 z1 hcs
  obtain ⟨x, hx⟩ := hne
  exact hx (z0 x)

end OscInt.SPLNAux
