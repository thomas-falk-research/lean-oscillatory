/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Family
import OscInt.Front.Convert
namespace OscInt.API.FamilySanity
open OscInt.Statements OscInt.API.ConvertAux

/-! # Sanity theorems through the batch-3 statement constants

Every theorem below about a frozen statement of `OscInt/Statements/Family.lean` takes that statement as a hypothesis
and only applies it to concrete data, discharging its hypotheses there. Nothing here proves a frozen statement. If a
statement body were changed by one of the plants named in the docstrings, the discharge for these data would become
impossible and this file would stop compiling. -/

/-! ## Bite 1: `x³ + y³` with a fold critical point, through S3c -/

/-- The fold condition holds at the critical points of `x³ + y³ + (0, −3)·k` (namely `(0, ±1)`): the Hessian
`diag(0, 6k₂)` has rank one with kernel spanned by `(1, 0)` and `D³[(1, 0), (1, 0), (1, 0)] = 6`. -/
theorem cubes_fold_at_crit : ∀ p ∈ ({((0 : ℝ), (-3 : ℝ))} : Set (ℝ × ℝ)), ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
    IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) p k →
      FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) k := by
  intro p hp k _ hk
  rw [Set.mem_singleton_iff] at hp; subst hp
  simp only [IsCritical, sanity_fd_cubes] at hk
  obtain ⟨h1, h2⟩ := hk
  have hx : k.1 = 0 := by nlinarith [sq_nonneg k.1]
  have hy : k.2 ≠ 0 := by rintro h; rw [h] at h2; norm_num at h2
  right
  refine ⟨⟨(0, 1), (0, 1), ?_⟩, fun v hv hw => ?_⟩
  · rw [sanity_dd_cubes]; simpa using hy
  · have h0 := hw (0, 1)
    rw [sanity_dd_cubes] at h0
    have hv2 : v.2 = 0 := by
      simp only [mul_zero, mul_one, zero_add] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exfalso; rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact hy h'
      · exact h
    have hv1 : v.1 ≠ 0 := fun h => hv (Prod.ext h hv2)
    rw [sanity_ddd_cubes, hv2]
    simpa using hv1

/-- **Bite of S3c through the statement constant.** One-point family `Unit`, `Ψ = x³ + y³`, `K = closedBall 0 2`,
`K' = {(0, −3)}`. The critical points of `Ψ + (0, −3)·` are `(0, ±1)`, both folds (Hessian `diag(0, 6k₂)`, kernel
spanned by `(1, 0)`, third derivative `6` along it), so S3c yields the rate `m^{-5/6}`.

Plants caught: `p ↦ 0` in the critical-point condition (then `0 ∈ K` is critical and the Hessian vanishes there, so
`FoldOrNondeg` fails), and "fold condition at every `k ∈ K`" (`0 ∈ K`, same failure). Neither S2.2 nor S3 applies to
these data: the critical points are degenerate (S2.2), and `FoldOrNondeg` fails at `0 ∈ K` (S3). -/
theorem foldCrit_fold_bite (h : FoldCritStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    AmpBound 2 (Metric.closedBall 0 2) A M → 1 ≤ m →
    ‖oscInt2 (fun k => m * ((k.1 ^ 3 + k.2 ^ 3) + lin (0, -3) k)) A‖ ≤ C * M * m ^ (-(5 : ℝ) / 6) := by
  obtain ⟨C, hC⟩ := h Unit (fun _ => fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (Metric.closedBall 0 2)
    {((0 : ℝ), (-3 : ℝ))} (sanity_familyCk_const 4 _ (by fun_prop)) (isCompact_closedBall _ _)
    isCompact_singleton (fun _ => cubes_fold_at_crit)
  exact ⟨C, fun A M m hA hm => hC A M () (0, -3) m hA (Set.mem_singleton _) hm⟩

/-! ## Bite 2: the sign family `σ (k₁⁴ + 4k₁) + k₂²`, `σ ∈ [1, 2]` -/

/-- The phase family `Ψσ(k) = σ (k₁⁴ + 4k₁) + k₂²`. -/
def signFamily (σ : ℝ) (k : ℝ × ℝ) : ℝ := σ * (k.1 ^ 4 + 4 * k.1) + k.2 ^ 2

/-- `∂_v (a k₁⁴ + b k₁ + c k₂²)(y) = (4a y₁³ + b) v₁ + 2c y₂ v₂`. -/
theorem fd_quartic (a b c : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 4 + b * k.1 + c * k.2 ^ 2) y v =
      (4 * a * y.1 ^ 3 + b) * v.1 + 2 * c * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 4 + b * k.1 + c * k.2 ^ 2)
      ((4 * a * y.1 ^ 3 + b) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * c * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 4).const_mul a).add
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul b)).add
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2).const_mul c) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp

/-- `∂_v (a k₁³ + b k₂ + c)(y) = 3a y₁² v₁ + b v₂`. -/
theorem fd_cubic (a b c : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2 + c) y v = 3 * a * y.1 ^ 2 * v.1 + b * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2 + c)
      ((3 * a * y.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul b)).add_const c using 1
    ext
    · simp; ring
    · simp
  rw [h.fderiv]; simp

/-- `signFamily σ` as a polynomial in the form of `fd_quartic`. -/
theorem signFamily_eq (σ : ℝ) :
    signFamily σ = fun k : ℝ × ℝ => σ * k.1 ^ 4 + (4 * σ) * k.1 + 1 * k.2 ^ 2 := by
  funext k; simp only [signFamily]; ring

/-- `∂_v Ψσ(y) = σ (4y₁³ + 4) v₁ + 2y₂ v₂`. -/
theorem signFamily_fd (σ : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (signFamily σ) y v = σ * (4 * y.1 ^ 3 + 4) * v.1 + 2 * y.2 * v.2 := by
  rw [signFamily_eq, fd_quartic]; ring

/-- `∂_w ∂_v Ψσ(y) = 12σ y₁² v₁w₁ + 2 v₂w₂`. -/
theorem signFamily_dd (σ : ℝ) (y v w : ℝ × ℝ) :
    dd (signFamily σ) y v w = 12 * σ * y.1 ^ 2 * v.1 * w.1 + 2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (signFamily σ) y v) =
      fun y => (4 * σ * v.1) * y.1 ^ 3 + (2 * v.2) * y.2 + 4 * σ * v.1 := by
    funext y; rw [signFamily_fd]; ring
  rw [dd, this, fd_cubic]; ring

/-- `hessDet Ψσ(y) = 24σ y₁²`. -/
theorem signFamily_hessDet (σ : ℝ) (y : ℝ × ℝ) : hessDet (signFamily σ) y = 24 * σ * y.1 ^ 2 := by
  simp only [hessDet, signFamily_dd]; ring

/-- The sign family is jointly `C⁴` in `(σ, k)`. -/
theorem signFamily_uncurry_contDiff : ContDiff ℝ 4 (Function.uncurry signFamily) := by
  change ContDiff ℝ 4 (fun q : ℝ × (ℝ × ℝ) => q.1 * (q.2.1 ^ 4 + 4 * q.2.1) + q.2.2 ^ 2)
  fun_prop

/-- C10 applied to the (non-constant) sign family on the compact parameter set `[1, 2]`. -/
theorem familyCkOfUncurry_nonconst (hC10 : FamilyCkOfUncurryStatement) :
    FamilyCk 4 (fun σ : Set.Icc (1 : ℝ) 2 => signFamily σ) :=
  hC10 ℝ 4 signFamily signFamily_uncurry_contDiff (Set.Icc 1 2)

/-- For `σ ∈ [1, 2]` every critical point `k` of `Ψσ + (4, 0)·` has `k₁ ≠ 0` (else `4σ + 4 = 0`). -/
theorem signFamily_crit_ne (σ : Set.Icc (1 : ℝ) 2) (p : ℝ × ℝ) (hp : p ∈ ({((4 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)))
    (k : ℝ × ℝ) (hk : IsCritical (signFamily σ) p k) : k.1 ≠ 0 := by
  rw [Set.mem_singleton_iff] at hp; subst hp
  obtain ⟨h1, -⟩ := hk
  rw [signFamily_fd] at h1
  intro h0
  rw [h0] at h1
  have := σ.2.1
  norm_num at h1
  linarith

/-- For `σ ∈ [1, 2]` the Hessian is nondegenerate at every critical point of `Ψσ + (4, 0)·`. -/
theorem signFamily_nondeg (σ : Set.Icc (1 : ℝ) 2) (p : ℝ × ℝ) (hp : p ∈ ({((4 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)))
    (k : ℝ × ℝ) (hk : IsCritical (signFamily σ) p k) : hessDet (signFamily σ) k ≠ 0 := by
  have hx := signFamily_crit_ne σ p hp k hk
  have hσ : (0 : ℝ) < σ := lt_of_lt_of_le one_pos σ.2.1
  rw [signFamily_hessDet]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hσ.ne') (pow_ne_zero 2 hx)

/-- **Bite of S2.2F through the statement constant.** Family `Ψσ = σ (k₁⁴ + 4k₁) + k₂²` over the infinite compact
`Icc 1 2` (`FamilyCk 4` from C10), `K = closedBall 0 2`, `K' = {(4, 0)}`. A critical point satisfies
`σ (4x³ + 4) + 4 = 0`, so `x ≠ 0` and `hessDet = 24σx² ≠ 0`.

Plants caught: `p ↦ -p` (for `σ = 1` the point `(0, 0) ∈ K` becomes critical with Hessian `diag(0, 2)`, degenerate),
and "nondegenerate at every `k ∈ K`" (`(0, 0) ∈ K`, `hessDet = 0`). Plant NOT caught here: `p ↦ 0` (the critical
points then satisfy `x³ = −1`, still nondegenerate); theorem `foldCrit_fold_bite` catches that plant for S3c. -/
theorem stationaryPhaseFamily_sign_bite (hC10 : FamilyCkOfUncurryStatement) (h : StationaryPhaseFamilyStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Set.Icc (1 : ℝ) 2) (m : ℝ),
      AmpBound 2 (Metric.closedBall 0 2) A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * (signFamily σ k + lin (4, 0) k)) A‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := h (Set.Icc (1 : ℝ) 2) (fun σ => signFamily σ) (Metric.closedBall 0 2)
    {((4 : ℝ), (0 : ℝ))} (familyCkOfUncurry_nonconst hC10) (isCompact_closedBall _ _) isCompact_singleton
    (fun σ p hp k _ hk => signFamily_nondeg σ p hp k hk)
  exact ⟨C, fun A M σ m hA hm => hC A M σ (4, 0) m hA (Set.mem_singleton _) hm⟩

/-- **Bite of S3c through the statement constant**, same data as `stationaryPhaseFamily_sign_bite`, rate
`m^{-5/6}`; the hypothesis holds by the nondegenerate branch of `FoldOrNondeg`.

Plant caught: `p ↦ -p` (for `σ = 1` the point `(0, 0)` becomes critical, Hessian `diag(0, 2)`, kernel spanned by
`(1, 0)`, third derivative `24σ·0 = 0` along it, so it is neither nondegenerate nor a fold); likewise "at every
`k ∈ K`". Plant NOT caught here: `p ↦ 0` (critical points `x³ = −1`, nondegenerate); `foldCrit_fold_bite` catches
it. -/
theorem foldCrit_sign_bite (hC10 : FamilyCkOfUncurryStatement) (h : FoldCritStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Set.Icc (1 : ℝ) 2) (m : ℝ),
      AmpBound 2 (Metric.closedBall 0 2) A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * (signFamily σ k + lin (4, 0) k)) A‖ ≤ C * M * m ^ (-(5 : ℝ) / 6) := by
  obtain ⟨C, hC⟩ := h (Set.Icc (1 : ℝ) 2) (fun σ => signFamily σ) (Metric.closedBall 0 2)
    {((4 : ℝ), (0 : ℝ))} (familyCkOfUncurry_nonconst hC10) (isCompact_closedBall _ _) isCompact_singleton
    (fun σ p hp k _ hk => Or.inl (signFamily_nondeg σ p hp k hk))
  exact ⟨C, fun A M σ m hA hm => hC A M σ (4, 0) m hA (Set.mem_singleton _) hm⟩

/-! ## Bite 3: a phase singular outside `U`, through the Mathlib-idiom single-phase forms -/

/-- `k₁⁴ + 4|k₁ + 3| − 12 + k₂²`: equal to `k₁⁴ + 4k₁ + k₂²` on `{k₁ > −3}`, not differentiable at `(−3, 0)`. -/
noncomputable def kinkPhase (k : ℝ × ℝ) : ℝ := k.1 ^ 4 + 4 * |k.1 + 3| - 12 + k.2 ^ 2

/-- The linear term `L₀ k = 4 k₁`. -/
noncomputable def L₀ : (ℝ × ℝ) →L[ℝ] ℝ := (4 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The open half-plane `U = {k₁ > −3}`. -/
def kinkU : Set (ℝ × ℝ) := {k | -3 < k.1}

theorem kinkU_isOpen : IsOpen kinkU := isOpen_lt continuous_const continuous_fst

/-- `closedBall 0 2 ⊆ U` (max norm). -/
theorem closedBall_subset_kinkU : Metric.closedBall (0 : ℝ × ℝ) 2 ⊆ kinkU := by
  intro k hk
  rw [Metric.mem_closedBall, dist_zero_right] at hk
  have h1 : ‖k.1‖ ≤ 2 := (norm_fst_le k).trans hk
  rw [Real.norm_eq_abs] at h1
  show -3 < k.1
  linarith [neg_abs_le k.1]

/-- On `U` the kink phase is the polynomial `signFamily 1`. -/
theorem kinkPhase_eq_on (k : ℝ × ℝ) (hk : k ∈ kinkU) : kinkPhase k = signFamily 1 k := by
  have : 0 < k.1 + 3 := by have h3 : -3 < k.1 := hk; linarith
  simp only [kinkPhase, signFamily, abs_of_pos this]; ring

/-- Germ equality at points of `U`. -/
theorem kinkPhase_eventuallyEq (k : ℝ × ℝ) (hk : k ∈ kinkU) : kinkPhase =ᶠ[nhds k] signFamily 1 :=
  Filter.eventually_of_mem (kinkU_isOpen.mem_nhds hk) kinkPhase_eq_on

theorem kinkPhase_contDiffOn : ContDiffOn ℝ 4 kinkPhase {k | -3 < k.1} := by
  have hP : ContDiff ℝ 4 (signFamily 1) := by rw [signFamily_eq]; fun_prop
  exact hP.contDiffOn.congr kinkPhase_eq_on

/-- The kink phase is not `C¹` on `ℝ²`: it is not differentiable at `(−3, 0)`. -/
theorem kinkPhase_not_contDiff : ¬ ContDiff ℝ 1 kinkPhase := by
  intro h
  have hd : DifferentiableAt ℝ kinkPhase ((0 : ℝ) - 3, (0 : ℝ)) := h.differentiable (by norm_num) _
  have hl : DifferentiableAt ℝ (fun x : ℝ => ((x - 3, (0 : ℝ)) : ℝ × ℝ)) 0 :=
    (differentiableAt_id.sub_const 3).prodMk (differentiableAt_const _)
  have hc : DifferentiableAt ℝ (fun x : ℝ => kinkPhase (x - 3, 0)) 0 :=
    hd.comp (f := fun x : ℝ => ((x - 3, (0 : ℝ)) : ℝ × ℝ)) (0 : ℝ) hl
  have he : (abs : ℝ → ℝ) = fun x => (kinkPhase (x - 3, 0) - (x - 3) ^ 4 + 12) / 4 := by
    funext x; simp only [kinkPhase, sub_add_cancel]; ring
  apply not_differentiableAt_abs_zero
  rw [he]
  exact ((hc.sub (by fun_prop)).add_const 12).div_const 4

/-- The Hessian matrix of the kink phase at `k ∈ U` is that of the polynomial. -/
theorem kink_hessianMatrix (k : ℝ × ℝ) (hk : k ∈ kinkU) :
    hessianMatrix kinkPhase k = hessianMatrix (signFamily 1) k := by
  have := ((kinkPhase_eventuallyEq k hk).iteratedFDeriv ℝ 2).eq_of_nhds
  simp only [hessianMatrix, this]

/-- At a critical point of `kinkPhase + L₀` in `U`, the Hessian determinant is `24k₁² ≠ 0`. -/
theorem kink_det_ne (k : ℝ × ℝ) (hk : k ∈ kinkU) (hc : fderiv ℝ kinkPhase k + L₀ = 0) :
    (hessianMatrix kinkPhase k).det ≠ 0 := by
  rw [(kinkPhase_eventuallyEq k hk).fderiv_eq, functional_eq_zero_iff] at hc
  obtain ⟨h1, -⟩ := hc
  simp only [add_apply, signFamily_fd, L₀, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul] at h1
  have hx : k.1 ≠ 0 := by intro h0; rw [h0] at h1; norm_num at h1
  have hP : ContDiffAt ℝ 2 (signFamily 1) k := by rw [signFamily_eq]; fun_prop
  rw [kink_hessianMatrix k hk, ← hessDet_eq_det _ _ hP, signFamily_hessDet]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)

/-- **Bite of FE-S2.2l through the statement constant.** `Ψ = kinkPhase` (singular on `k₁ = −3`), `U = {k₁ > −3}`,
`K = closedBall 0 2 ⊆ U`, `K' = {L₀}`, `L₀ = 4·fst`. On `U` the phase is `k₁⁴ + 4k₁ + k₂²`; a critical point of
`Ψ + L₀` has `4x³ + 4 + 4 = 0`, so `x ≠ 0` and `det = 24x² ≠ 0`.

Pinned by these data: the sign `+ L` (with `− L` the critical point is `x = 0`, `(0, 0) ∈ K`, degenerate) and the
order `e₀ = (1, 0)`, `e₁ = (0, 1)` (`L₀ e₀ = 4 ≠ 0 = L₀ e₁`). The phase is not `C¹` on `ℝ²`
(`kinkPhase_not_contDiff`), so front-end batch 2 does not apply without a hand-made cut-off. -/
theorem stationaryPhaseOn_kink (h : StationaryPhaseOnStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L₀ k)) * Complex.I) * A k‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := h kinkPhase (Metric.closedBall 0 2) kinkU {L₀} (isCompact_closedBall _ _) kinkU_isOpen
    closedBall_subset_kinkU isCompact_singleton kinkPhase_contDiffOn
    (fun L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      exact kink_det_ne k (closedBall_subset_kinkU hk) hc)
  exact ⟨C, fun A M m hA hs hM hm => hC A M L₀ m hA hs hM (Set.mem_singleton _) hm⟩

/-- **Bite of FE-S3l through the statement constant**, same data as `stationaryPhaseOn_kink`, rate `m^{-5/6}`;
`FoldOrNondegMatrix` holds by its nondegenerate branch. The same pins apply (`+ L`, order `e₀/e₁`); with `− L` the
critical point `(0, 0)` has Hessian `diag(0, 2)`, kernel spanned by `e₀ = (1, 0)`, third derivative `0` along it,
so the fold condition fails. -/
theorem foldOn_kink (h : FoldOnStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L₀ k)) * Complex.I) * A k‖ ≤
      C * M * m ^ (-(5 : ℝ) / 6) := by
  obtain ⟨C, hC⟩ := h kinkPhase (Metric.closedBall 0 2) kinkU {L₀} (isCompact_closedBall _ _) kinkU_isOpen
    closedBall_subset_kinkU isCompact_singleton kinkPhase_contDiffOn
    (fun L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      exact Or.inl (kink_det_ne k (closedBall_subset_kinkU hk) hc))
  exact ⟨C, fun A M m hA hs hM hm => hC A M L₀ m hA hs hM (Set.mem_singleton _) hm⟩

end OscInt.API.FamilySanity
