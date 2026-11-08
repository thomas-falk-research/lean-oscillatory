/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Convert

/-!
# Front-end batch 2, P-Deriv: `dd`, `ddd`, `hessDet`, `cubicCoeffs` through `iteratedFDeriv` (C1–C4)

Route: `docs/proof-API2.md`, P-Deriv. Everything is reduced to the curried derivatives `fderiv (fderiv Ψ)` and
`fderiv (fderiv (fderiv Ψ))` at `k`. Smoothness is only local (`ContDiffAt`), so the identities at nearby points
are transported with `ContDiffAt.eventually` and `Filter.EventuallyEq.fderiv_eq`. The symmetry of `D³Ψ(k)` comes
from two transpositions: the first two arguments (symmetry of the second derivative of `DΨ`, which is `C²` near
`k`) and the last two (symmetry of `D²Ψ(y)` for `y` near `k`).
-/

open Filter Topology OscInt.Statements
open scoped ContDiff

namespace OscInt.API.DerivAux

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Directional derivative of `y ↦ G y v`. -/
theorem fderiv_apply_const {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] F} {k : ℝ × ℝ} (hG : DifferentiableAt ℝ G k)
    (v w : ℝ × ℝ) : fderiv ℝ (fun y => G y v) k w = fderiv ℝ G k w v := by
  rw [fderiv_clm_apply hG (differentiableAt_const v)]
  simp

/-- Symmetry of the second derivative of a `C²`-near-`k` function, in curried form. -/
theorem symm2 {f : ℝ × ℝ → F} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f k) (v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ f) k v w = fderiv ℝ (fderiv ℝ f) k w v :=
  hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w

theorem diff_fderiv {f : ℝ × ℝ → F} {k : ℝ × ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f k) (hn : 2 ≤ n) :
    DifferentiableAt ℝ (fderiv ℝ f) k :=
  (hf.fderiv_right (m := 1) (by exact_mod_cast hn)).differentiableAt one_ne_zero

/-- `dd Ψ y v w = D(DΨ)(y) w v` (no symmetry). -/
theorem dd_eq_fderiv2 {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hΨ : ContDiffAt ℝ 2 Ψ k) (v w : ℝ × ℝ) :
    dd Ψ k v w = fderiv ℝ (fderiv ℝ Ψ) k w v :=
  fderiv_apply_const (diff_fderiv (n := 2) hΨ le_rfl) v w

theorem iter3_eq (f : ℝ × ℝ → ℝ) (k u v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 f k ![u, v, w] = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) k u v w := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl


/-- `y ↦ D²Ψ(y)[b, c]` has derivative `D³Ψ(k)[a, b, c]` in direction `a`. -/
theorem fderiv_fderiv2_apply {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hΨ : ContDiffAt ℝ 3 Ψ k) (a b c : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ Ψ) y b c) k a =
      fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k a b c := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ Ψ) k := hΨ.fderiv_right (m := 2) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ Ψ)) k := diff_fderiv (n := 2) h2 le_rfl
  have hd' : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ Ψ) y b) k :=
    hd.clm_apply (differentiableAt_const b)
  rw [fderiv_apply_const hd' c a, fderiv_apply_const hd b a]

/-- Full symmetry data for `D³Ψ(k)`: swaps of the first two and of the last two arguments. -/
theorem symm3 {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hΨ : ContDiffAt ℝ 3 Ψ k) (a b c : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k b a c ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k a c b := by
  refine ⟨?_, ?_⟩
  · have h2 : ContDiffAt ℝ 2 (fderiv ℝ Ψ) k := hΨ.fderiv_right (m := 2) (by norm_num)
    rw [symm2 h2 a b]
  · rw [← fderiv_fderiv2_apply hΨ, ← fderiv_fderiv2_apply hΨ]
    have hev : ∀ᶠ y in 𝓝 k, ContDiffAt ℝ 3 Ψ y := hΨ.eventually (by simp)
    have : (fun y => fderiv ℝ (fderiv ℝ Ψ) y b c) =ᶠ[𝓝 k] fun y => fderiv ℝ (fderiv ℝ Ψ) y c b :=
      hev.mono fun y hy => symm2 (hy.of_le (by norm_num)) b c
    rw [this.fderiv_eq]

/-- `ddd Ψ k u v w = D³Ψ(k)[w, v, u]` in curried form (before symmetrisation). -/
theorem ddd_eq_fderiv3 {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hΨ : ContDiffAt ℝ 3 Ψ k) (u v w : ℝ × ℝ) :
    ddd Ψ k u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ Ψ)) k w v u := by
  have hev : ∀ᶠ y in 𝓝 k, ContDiffAt ℝ 3 Ψ y := hΨ.eventually (by simp)
  have : (fun y => dd Ψ y u v) =ᶠ[𝓝 k] fun y => fderiv ℝ (fderiv ℝ Ψ) y v u :=
    hev.mono fun y hy => dd_eq_fderiv2 (hy.of_le (by norm_num)) u v
  rw [ddd, this.fderiv_eq, fderiv_fderiv2_apply hΨ]

end OscInt.API.DerivAux

namespace OscInt.API

open OscInt.API.DerivAux

theorem dd_iteratedFDeriv : DdEqIteratedStatement := by
  intro Ψ k hΨ v w
  rw [dd_eq_fderiv2 hΨ, symm2 hΨ, iteratedFDeriv_two_apply]
  rfl

theorem ddd_iteratedFDeriv : DddEqIteratedStatement := by
  intro Ψ k hΨ u v w
  rw [ddd_eq_fderiv3 hΨ, iter3_eq, (symm3 hΨ w v u).2, (symm3 hΨ w u v).1, (symm3 hΨ u w v).2]

theorem hessDet_eq_det : HessDetEqDetStatement := by
  intro Ψ k hΨ
  have h := dd_iteratedFDeriv Ψ k hΨ
  rw [hessDet, Matrix.det_fin_two, h, h, h]
  have hs : iteratedFDeriv ℝ 2 Ψ k ![(0, 1), (1, 0)] = iteratedFDeriv ℝ 2 Ψ k ![(1, 0), (0, 1)] := by
    rw [← h, ← h, dd_eq_fderiv2 hΨ, dd_eq_fderiv2 hΨ, symm2 hΨ]
  simp only [hessianMatrix, coordVec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hs]
  ring


theorem cubicCoeffs_eq : CubicCoeffsEqStatement := by
  intro φ hφ κ
  set T := fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) 0 with hT
  have hκ : κ = κ.1 • ((1, 0) : ℝ × ℝ) + κ.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have s1 := symm3 hφ (1, 0) (1, 0) (0, 1)
  have s2 := symm3 hφ (1, 0) (0, 1) (1, 0)
  have s4 := symm3 hφ (0, 1) (1, 0) (0, 1)
  rw [← hT] at s1 s2 s4
  rw [iter3_eq, ← hT, cubicForm, cubicCoeffs, ddd_eq_fderiv3 hφ, ddd_eq_fderiv3 hφ, ddd_eq_fderiv3 hφ,
    ddd_eq_fderiv3 hφ, ← hT, hκ]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  linear_combination (-(1 / 3) * κ.1 ^ 2 * κ.2) * s2.1 + (-(1 / 6) * κ.1 ^ 2 * κ.2) * s1.2 +
    (-(1 / 3) * κ.1 * κ.2 ^ 2) * s4.2 + ((1 / 6) * κ.1 * κ.2 ^ 2) * s4.1

end OscInt.API
