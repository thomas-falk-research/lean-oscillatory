/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: local smoothness (front-end batch 3, acceptance of ROADMAP P2)

Two phases a downstream user meets in lattice and photonic dispersion problems, used only through `import OscInt.API`
and Mathlib:

1. The arccos-type dispersion relation `Ψ_{a,b}(x, y) = arccos(a cos x + b cos y)`, smooth wherever `|a| + |b| < 1`;
   Mathlib gives its smoothness only through `Real.contDiffOn_arccos` on `{−1, 1}ᶜ`, so the user proves `ContDiffOn`
   of the uncurried family on `V ×ˢ univ` with `V = {(a, b) | |a| + |b| < 1}` and applies FE-S2.1L uniformly over a
   compact parameter set `S ⊆ V` (and FE-S2.1l for one phase).
2. A phase that is genuinely singular outside the amplitude's support, `k₁⁴ + 4|k₁ + 3| − 12 + k₂²` (not `C¹` on ℝ²):
   FE-S2.2l and FE-S3l give `m^{-1}` and `m^{-5/6}` bounds for the linear term `4k₁` (the derivative data are
   discharged in `OscInt/Front/FamilySanity.lean`; here the proved theorems are plugged in).
-/

open OscInt.Statements

namespace ConsumerLocal

/-- The arccos dispersion relation as a family in `σ = (a, b)`. -/
noncomputable def disp (σ : ℝ × ℝ) (k : ℝ × ℝ) : ℝ := Real.arccos (σ.1 * Real.cos k.1 + σ.2 * Real.cos k.2)

/-- The parameter region `|a| + |b| < 1`. -/
def region : Set (ℝ × ℝ) := {σ | |σ.1| + |σ.2| < 1}

theorem region_isOpen : IsOpen region :=
  isOpen_lt ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)) continuous_const

/-- On `region × ℝ²` the argument of `arccos` stays in `(−1, 1)`. -/
theorem arg_mem (σ : ℝ × ℝ) (hσ : σ ∈ region) (k : ℝ × ℝ) :
    σ.1 * Real.cos k.1 + σ.2 * Real.cos k.2 ∈ ({-1, 1}ᶜ : Set ℝ) := by
  have hσ' : |σ.1| + |σ.2| < 1 := hσ
  have h1 : |σ.1 * Real.cos k.1| ≤ |σ.1| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |σ.2 * Real.cos k.2| ≤ |σ.2| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h : |σ.1 * Real.cos k.1 + σ.2 * Real.cos k.2| < 1 :=
    lt_of_le_of_lt ((abs_add_le _ _).trans (add_le_add h1 h2)) hσ'
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor <;> intro he <;> rw [he] at h <;> norm_num at h

/-- The family is `Cⁿ` jointly in `(σ, k)` on `region ×ˢ univ`, via `Real.contDiffOn_arccos` only. -/
theorem disp_contDiffOn (n : ℕ) : ContDiffOn ℝ n (Function.uncurry disp) (region ×ˢ Set.univ) := by
  have hin : ContDiff ℝ n (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1.1 * Real.cos q.2.1 + q.1.2 * Real.cos q.2.2) := by
    fun_prop
  exact Real.contDiffOn_arccos.comp hin.contDiffOn fun q hq => arg_mem q.1 hq.1 q.2

/-- **FE-S2.1L for the arccos family**: decay `m^{-N}` uniformly over `σ` in a compact `S ⊆ region`, over amplitudes
supported in a compact `K`, and over linear terms keeping the gradient `≥ c` on `K`. -/
theorem disp_nonStationary (N : ℕ) (S : Set (ℝ × ℝ)) (hS : IsCompact S) (hSr : S ⊆ region)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      σ ∈ S → ContDiff ℝ N A → tsupport A ⊆ K → (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      (∀ k ∈ K, c ≤ ‖fderiv ℝ (disp σ) k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (disp σ k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N :=
  OscInt.API.nonStationaryLocal (ℝ × ℝ) N disp S region K Set.univ c hS region_isOpen hSr hK isOpen_univ
    (Set.subset_univ K) (by exact_mod_cast disp_contDiffOn (N + 1)) hc

/-- **FE-S2.2l for the kink phase** (singular on `k₁ = −3`, outside `K = B̄(0, 2)`; linear term `4k₁`). -/
theorem kink_stationaryPhase : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (OscInt.API.FamilySanity.kinkPhase k +
      OscInt.API.FamilySanity.L₀ k)) * Complex.I) * A k‖ ≤ C * M / m :=
  OscInt.API.FamilySanity.stationaryPhaseOn_kink OscInt.API.stationaryPhaseOn

/-- **FE-S3l for the kink phase**: the fold bound with the classical hypothesis. -/
theorem kink_fold : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (OscInt.API.FamilySanity.kinkPhase k +
      OscInt.API.FamilySanity.L₀ k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6) :=
  OscInt.API.FamilySanity.foldOn_kink OscInt.API.foldOn

/-- The kink phase is not `C¹` on ℝ², so the batch-2 front ends do not apply without a hand-made cut-off. -/
example : ¬ ContDiff ℝ 1 OscInt.API.FamilySanity.kinkPhase := OscInt.API.FamilySanity.kinkPhase_not_contDiff

/-- The classical fold bite, now unconditional: x³ + y³ with `p = (0, −3)` (fold critical points `(0, ±1)`,
`0 ∈ K` degenerate but not critical), where neither S2.2 nor S3 applies. -/
example := OscInt.API.FamilySanity.foldCrit_fold_bite OscInt.API.foldCrit

/-- Why S2.2 does not give the fold bite: `(0, 1) ∈ B̄(0, 2)` is a critical point of `x³ + y³ + (0, −3)·` with a
degenerate Hessian (post-proof referee B, MINOR 3). -/
example : IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (0, -3) (0, 1) ∧
    hessDet (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (0, 1) = 0 ∧ ((0 : ℝ), (1 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [IsCritical, sanity_fd_cubes]; norm_num
  · simp only [hessDet, sanity_dd_cubes]; norm_num
  · simp [Metric.mem_closedBall, Prod.norm_def]

/-- The infinite-family bites, unconditional (S2.2F and S3c on `σ (k₁⁴ + 4k₁) + k₂²`, `σ ∈ [1, 2]`). -/
example := OscInt.API.FamilySanity.stationaryPhaseFamily_sign_bite OscInt.API.familyCk_of_uncurry
  OscInt.API.stationaryPhaseFamily
example := OscInt.API.FamilySanity.foldCrit_sign_bite OscInt.API.familyCk_of_uncurry OscInt.API.foldCrit

end ConsumerLocal
