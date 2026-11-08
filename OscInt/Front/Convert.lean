/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.Core
import OscInt.Front.ConvertDeriv
import OscInt.Front.ConvertDisc
import OscInt.Front.ConvertFold
import OscInt.Front.ConvertNorm

/-!
# Front-end batch 2: the lead's assembly (C7) and the front ends (FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′)

Statements: `OscInt/Statements/Convert.lean` (stamped `stamps/20261107T101640Z-4acb308f54f4`, blind-reviewed
FAITHFUL ×2 before any proof). Route: `docs/proof-API2.md`. Parts: `ConvertDeriv` (C1–C4), `ConvertDisc` (C5, C6),
`ConvertFold` (fold core, C7′), `ConvertNorm` (C8, C9). Each front end is proved from the frozen statement it fronts
(`OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold`, `OscInt.d4BoundNe`) and the conversions.
-/

namespace OscInt.API.ConvertAux

open OscInt.Statements

/-- The vector `p` of a linear term: `L k = p · k`. -/
def vecOf (L : (ℝ × ℝ) →L[ℝ] ℝ) : ℝ × ℝ := (L (1, 0), L (0, 1))

theorem continuous_vecOf : Continuous vecOf := by
  unfold vecOf
  exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).continuous).prodMk
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous

/-- A functional on `ℝ × ℝ` vanishes iff it vanishes on the standard basis. -/
theorem functional_eq_zero_iff (G : (ℝ × ℝ) →L[ℝ] ℝ) : G = 0 ↔ G (1, 0) = 0 ∧ G (0, 1) = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩
    ext
    · simpa using h1
    · simpa using h2

theorem isCritical_iff {Ψ : ℝ × ℝ → ℝ} (L : (ℝ × ℝ) →L[ℝ] ℝ) (k : ℝ × ℝ) :
    IsCritical Ψ (vecOf L) k ↔ fderiv ℝ Ψ k + L = 0 := by
  rw [functional_eq_zero_iff]; simp [IsCritical, vecOf]

/-- The written-out integral is `oscInt2` with `p = vecOf L`. -/
theorem integral_eq_oscInt2 (Ψ : ℝ × ℝ → ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (A : ℝ × ℝ → ℂ) (m : ℝ) :
    ∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k =
      oscInt2 (fun k => m * (Ψ k + lin (vecOf L) k)) A := by
  simp only [oscInt2, vecOf, NormAux.lin_apply_functional]

theorem integral_eq_oscInt2' (φ : ℝ × ℝ → ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (A : ℝ × ℝ → ℂ) (t : ℝ) :
    ∫ κ : ℝ × ℝ, Complex.exp (↑(t * φ κ + L κ) * Complex.I) * A κ =
      oscInt2 (fun κ => t * φ κ + lin (vecOf L) κ) A := by
  simp only [oscInt2, vecOf, NormAux.lin_apply_functional]

/-- `D²Ψ(k)` as a bilinear map is `fderiv (fderiv Ψ) k`, and `dd` reads it in the stated order. -/
theorem dd_eq_B {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hΨ : ContDiffAt ℝ 3 Ψ k) (v w : ℝ × ℝ) :
    dd Ψ k v w = fderiv ℝ (fderiv ℝ Ψ) k v w := by
  rw [dd_iteratedFDeriv Ψ k (hΨ.of_le (by norm_num)), iteratedFDeriv_two_apply]; rfl

theorem third_smul (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) (c : ℝ) (v : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 Ψ k ![c • v, c • v, c • v] = c ^ 3 * iteratedFDeriv ℝ 3 Ψ k ![v, v, v] := by
  have : (![c • v, c • v, c • v] : Fin 3 → ℝ × ℝ) = fun i => c • (![v, v, v] : Fin 3 → ℝ × ℝ) i := by
    funext i; fin_cases i <;> rfl
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp [smul_eq_mul]

end OscInt.API.ConvertAux

namespace OscInt.API

open OscInt.Statements ConvertAux

/-- **C7** `FoldOrNondeg` in matrix form (span and rank forms), from the fold core with `B = D²Ψ(k)`,
`T v = D³Ψ(k)[v, v, v]` (C1, C2). -/
theorem foldOrNondeg_iff : FoldOrNondegIffStatement := by
  intro Ψ k hΨ
  set B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ Ψ) k with hBdef
  set T : ℝ × ℝ → ℝ := fun v => iteratedFDeriv ℝ 3 Ψ k ![v, v, v] with hTdef
  have hB : ∀ v w, B v w = B w v := DerivAux.symm2 (hΨ.of_le (by norm_num))
  have hT : ∀ (c : ℝ) v, T (c • v) = c ^ 3 * T v := fun c v => third_smul Ψ k c v
  have hdd : ∀ v w, dd Ψ k v w = B v w := dd_eq_B hΨ
  have hddd : ∀ v, ddd Ψ k v v v = T v := fun v => ddd_iteratedFDeriv Ψ k hΨ v v v
  have hH : hessianMatrix Ψ k = Matrix.of fun i j => B (coordVec i) (coordVec j) := by
    ext i j; simp [hessianMatrix, iteratedFDeriv_two_apply, hBdef]
  have hL : FoldOrNondeg Ψ k ↔
      (B (1, 0) (1, 0) * B (0, 1) (0, 1) - B (1, 0) (0, 1) ^ 2 ≠ 0 ∨
        ((∃ v w, B v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0)) := by
    simp only [FoldOrNondeg, hessDet, hdd, hddd]
  obtain ⟨h1, h2⟩ := FoldAux.foldCore B T hB hT
  refine ⟨hL.trans ?_, hL.trans ?_⟩
  · rw [h1]; unfold FoldOrNondegMatrix; rw [hH]
  · rw [h2, hH]

/-- **FE-S2.1** Non-stationary phase in Mathlib's idiom, from S2.1 (one-point family) and C8 (iii). -/
theorem nonStationaryFE : NonStationaryFEStatement := by
  intro N Ψ K c hΨ hK hc
  have hΨ' : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) Ψ := by exact_mod_cast hΨ
  obtain ⟨C, hC⟩ := OscInt.nonStationary Unit N (fun _ => Ψ) K (c / Real.sqrt 2)
    (sanity_familyCk_const _ _ hΨ') hK (by positivity)
  refine ⟨C, fun A M L m hA hsupp hbd hgrad hm => ?_⟩
  have hdiff : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hG : ∀ k ∈ K, GradLower Ψ (vecOf L) k (c / Real.sqrt 2) := by
    intro k hk
    refine ((gradLower_iff Ψ (vecOf L) k c (hdiff k) hc.le).2.2) ?_
    rw [vecOf, NormAux.fderiv_add_lin (hdiff k)]; exact hgrad k hk
  rw [integral_eq_oscInt2]
  exact hC A M () (vecOf L) m ⟨hA, hsupp, hbd⟩ hG hm

/-- **FE-S2.2** Nondegenerate stationary phase in Mathlib's idiom, from S2.2 and C3. -/
theorem stationaryPhaseFE : StationaryPhaseFEStatement := by
  intro Ψ K K' hΨ hK hK' hcrit
  obtain ⟨C, hC⟩ := OscInt.stationaryPhase Ψ K (vecOf '' K') hΨ hK (hK'.image continuous_vecOf) (by
    rintro _ ⟨L, hL, rfl⟩ k hk hk'
    rw [hessDet_eq_det Ψ k (hΨ.contDiffAt.of_le (by norm_num))]
    exact hcrit L hL k hk ((isCritical_iff L k).1 hk'))
  refine ⟨C, fun A M L m hA hsupp hbd hL hm => ?_⟩
  rw [integral_eq_oscInt2]
  exact hC A M (vecOf L) m ⟨hA, hsupp, hbd⟩ ⟨L, hL, rfl⟩ hm

/-- **FE-S3** Uniform fold estimate in Mathlib's idiom, from S3 (one-point family) and C7. -/
theorem foldFE : FoldFEStatement := by
  intro Ψ K K' hΨ hK hK' hfold
  have hΨ' : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) Ψ := by exact_mod_cast hΨ
  obtain ⟨C, hC⟩ := OscInt.fold Unit (fun _ => Ψ) K (vecOf '' K') (sanity_familyCk_const _ _ hΨ') hK
    (hK'.image continuous_vecOf) (fun _ k hk =>
      ((foldOrNondeg_iff Ψ k (hΨ.contDiffAt.of_le (by norm_num))).1).2 (hfold k hk))
  refine ⟨C, fun A M L m hA hsupp hbd hL hm => ?_⟩
  rw [integral_eq_oscInt2]
  exact hC A M () (vecOf L) m ⟨hA, hsupp, hbd⟩ ⟨L, hL, rfl⟩ hm

/-- A binary cubic is determined by its values: equal forms have equal coefficients. -/
theorem ConvertAux.coeffs_eq_of_forms {q q' : ℝ × ℝ × ℝ × ℝ} (h : ∀ κ, cubicForm q κ = cubicForm q' κ) :
    q = q' := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨a', b', c', d'⟩ := q'
  have h1 := h (1, 0); have h2 := h (0, 1); have h3 := h (1, 1); have h4 := h (1, -1)
  simp only [cubicForm] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  have hb : b = b' := by linarith
  have hc : c = c' := by linarith
  subst h1 h2 hb hc; rfl

/-- **FE-S4.1′** Uniform D4 bound in Mathlib's idiom, from S4.1′, C1, C4 and C5. -/
theorem d4BoundFE : D4BoundFEStatement := by
  intro φ a b c d hφ h2 h3 hdisc
  have hφ3 : ContDiffAt ℝ 3 φ 0 := hφ.contDiffAt.of_le (by norm_num)
  have hdd : ∀ v w, dd φ 0 v w = 0 := fun v w => by
    rw [dd_iteratedFDeriv φ 0 (hφ3.of_le (by norm_num)), h2]; rfl
  have hq : cubicCoeffs φ = (a, b, c, d) := ConvertAux.coeffs_eq_of_forms fun κ => by
    rw [cubicCoeffs_eq φ hφ3 κ, show κ = (κ.1, κ.2) from rfl, h3]; simp only [cubicForm]; ring
  have hD : disc (cubicCoeffs φ) ≠ 0 := by rw [hq, disc_eq_cubic_discr]; exact hdisc
  obtain ⟨δ, hδ, C, hC⟩ := OscInt.d4BoundNe φ hφ hdd hD
  refine ⟨δ, hδ, C, fun A M L t hA hsupp hbd ht => ?_⟩
  rw [integral_eq_oscInt2']
  exact hC A M (vecOf L) t ⟨hA, hsupp, hbd⟩ ht

end OscInt.API
