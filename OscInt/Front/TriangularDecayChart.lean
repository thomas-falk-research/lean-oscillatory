/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.StationaryPhase.Local
import OscInt.Front.ConvertDeriv

/-!
# Batch K2, part P3: the chart (`ChartFacts`)

Route: `docs/proof-K2.md`, section 1 ("P3"). With `L (u, s) = u v + s w` (invertible by the spanning hypothesis,
`exists_equiv_cols`) and `F k = Ψ (k₀ + L k) − Ψ k₀ − DΨ(k₀)(L k)`:
* `DF(y) z = DΨ(k₀ + L y)(L z) − DΨ(k₀)(L z)` (`fderiv_F_apply`), so `∂_s F(u, h u) = 0` on `|u| < ε` by
  `ReducedCurve`, and `∂_s F(0) = 0`;
* `∂²_s F(0) = dd Ψ k₀ w w = D²Ψ(k₀)[w, w] ≠ 0` (`dd_F`, `OscInt.API.dd_iteratedFDeriv`);
* `F (u, h u) = reducedFn Ψ k₀ v w h u − Ψ k₀`, so the m-th derivatives agree for `m ≥ 1`.
-/

namespace OscInt.K2.ChartAux

open OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.StationaryPhase.LocalAux
open scoped ContDiff

/-- The derivative of the chart phase. -/
theorem fderiv_F_apply {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) (k₀ : ℝ × ℝ)
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y z : ℝ × ℝ) :
    fderiv ℝ (fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k)) y z =
      fderiv ℝ Ψ (k₀ + L y) (L z) - fderiv ℝ Ψ k₀ (L z) := by
  have hA : HasFDerivAt (fun k => k₀ + L k) L y := L.hasFDerivAt.const_add k₀
  have h1 : HasFDerivAt (fun k => Ψ (k₀ + L k)) ((fderiv ℝ Ψ (k₀ + L y)).comp L) y :=
    (hΨ (k₀ + L y)).hasFDerivAt.comp y hA
  have h2 : HasFDerivAt (fun k => fderiv ℝ Ψ k₀ (L k)) ((fderiv ℝ Ψ k₀).comp L) y :=
    ((fderiv ℝ Ψ k₀).comp L).hasFDerivAt
  have h3 : HasFDerivAt (fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k))
      ((fderiv ℝ Ψ (k₀ + L y)).comp L - (fderiv ℝ Ψ k₀).comp L) y :=
    (h1.sub_const (Ψ k₀)).sub h2
  rw [h3.fderiv]
  rfl

/-- `iteratedDeriv` of order `m ≥ 1` ignores an additive constant. -/
theorem iteratedDeriv_sub_const' (f : ℝ → ℝ) (c : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    iteratedDeriv m (fun u => f u - c) = iteratedDeriv m f := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  congr 1
  funext x
  exact deriv_sub_const c

end OscInt.K2.ChartAux

namespace OscInt.K2

open OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.StationaryPhase.LocalAux OscInt.K2.ChartAux
open scoped ContDiff

theorem chart : ChartFacts := by
  intro Ψ k₀ v w ε h m hΨ hm hdet hww hε hcurve hred
  obtain ⟨L, hL1, hL2⟩ := exists_equiv_cols v w hdet
  have hLk : ∀ k : ℝ × ℝ, L k = k.1 • v + k.2 • w := by
    intro k
    have hk : k = k.1 • ((1 : ℝ), (0 : ℝ)) + k.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hk]
    rw [map_add, map_smul, map_smul, hL1, hL2]
  refine ⟨L, hLk, ?_⟩
  obtain ⟨hhs, hh0, hcrv⟩ := hcurve
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  set Lc : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) with hLc
  have hLc_apply : ∀ k, Lc k = L k := fun _ => rfl
  have hDF := fderiv_F_apply hΨd k₀ Lc
  simp only [hLc_apply] at hDF
  have hL0 : L ((0 : ℝ), (1 : ℝ)) = w := hL2
  -- the transverse derivative as a function
  have hpd : (fun y => fderiv ℝ (fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k)) y (0, 1)) =
      fun y => fderiv ℝ Ψ (k₀ + L y) w - fderiv ℝ Ψ k₀ w := by
    funext y
    rw [hDF, hL0]
  refine ⟨?_, ?_, ?_, hε, hhs, hh0, ?_, ?_⟩
  · -- smoothness
    have hA : ContDiff ℝ ∞ (fun k : ℝ × ℝ => k₀ + L k) := contDiff_const.add L.contDiff
    exact ((hΨ.comp hA).sub contDiff_const).sub ((fderiv ℝ Ψ k₀).contDiff.comp L.contDiff)
  · rw [hDF, hL0, map_zero, add_zero, sub_self]
  · -- second transverse derivative
    have hdd : dd (fun k => Ψ (k₀ + L k) - Ψ k₀ - fderiv ℝ Ψ k₀ (L k)) 0 (0, 1) (0, 1) = dd Ψ k₀ w w := by
      unfold dd
      rw [hpd, fderiv_sub_const]
      have hdiff : DifferentiableAt ℝ (fun z => fderiv ℝ Ψ z w) (k₀ + Lc 0) :=
        (contDiff_fderiv_apply (n := 1) (hΨ.of_le (by simp)) w).differentiable (by simp) _
      have := fderiv_comp_affine_apply (f := fun z => fderiv ℝ Ψ z w) k₀ Lc 0 (0, 1) hdiff
      simp only [hLc_apply, map_zero, add_zero, hL0] at this
      exact this
    rw [hdd, OscInt.API.dd_iteratedFDeriv Ψ k₀ (hΨ.contDiffAt.of_le (by simp))]
    exact hww
  · intro u hu
    rw [hDF, hL0, hLk, ← add_assoc]
    exact sub_eq_zero.mpr (hcrv u hu)
  · have hfun : (fun u => Ψ (k₀ + L (u, h u)) - Ψ k₀ - fderiv ℝ Ψ k₀ (L (u, h u))) =
        fun u => reducedFn Ψ k₀ v w h u - Ψ k₀ := by
      funext u
      simp only [hLk, reducedFn, add_assoc]
      ring
    rw [hfun, iteratedDeriv_sub_const' _ _ hm]
    exact hred

end OscInt.K2

