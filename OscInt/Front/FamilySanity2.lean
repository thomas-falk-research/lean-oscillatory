/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.FamilySanity
import OscInt.Front.ConvertSanity
namespace OscInt.API.FamilySanity
open OscInt.Statements OscInt.API.ConvertAux

/-! # Sanity theorems through the remaining batch-3 statement constants

Every theorem below about a frozen statement of `OscInt/Statements/Family.lean` takes that statement as a hypothesis
and only applies it to concrete data, discharging its hypotheses there; no proof `OscInt.API.*` of a frozen statement
is used. A plant in a statement body that makes one of these hypotheses impossible to discharge on these data stops
this file from compiling. A plant that only WEAKENS a hypothesis (or strengthens the conclusion) cannot be detected by
a conditional sanity theorem of this kind: the discharge only gets easier. -/

/-! ## FE-S2.1L: the arccos dispersion family -/

/-- The arccos dispersion relation as a family in `σ = (a, b)`. -/
noncomputable def disp (σ : ℝ × ℝ) (k : ℝ × ℝ) : ℝ := Real.arccos (σ.1 * Real.cos k.1 + σ.2 * Real.cos k.2)

/-- The parameter region `|a| + |b| < 1`. -/
def dispRegion : Set (ℝ × ℝ) := {σ | |σ.1| + |σ.2| < 1}

theorem dispRegion_isOpen : IsOpen dispRegion :=
  isOpen_lt ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)) continuous_const

/-- On `dispRegion × ℝ²` the argument of `arccos` stays in `(−1, 1)`. -/
theorem disp_arg_mem (σ : ℝ × ℝ) (hσ : σ ∈ dispRegion) (k : ℝ × ℝ) :
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

/-- The family is `Cⁿ` jointly in `(σ, k)` on `dispRegion ×ˢ univ`, via `Real.contDiffOn_arccos` only. -/
theorem disp_contDiffOn (n : ℕ) : ContDiffOn ℝ n (Function.uncurry disp) (dispRegion ×ˢ Set.univ) := by
  have hin : ContDiff ℝ n (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1.1 * Real.cos q.2.1 + q.1.2 * Real.cos q.2.2) := by
    fun_prop
  exact Real.contDiffOn_arccos.comp hin.contDiffOn fun q hq => disp_arg_mem q.1 hq.1 q.2

/-- `closedBall 0 (1/4) ⊆ dispRegion` (max norm: `|a| + |b| ≤ 1/2 < 1`). -/
theorem closedBall_subset_dispRegion : Metric.closedBall (0 : ℝ × ℝ) (1 / 4) ⊆ dispRegion := by
  intro σ hσ
  rw [Metric.mem_closedBall, dist_zero_right] at hσ
  have h1 : ‖σ.1‖ ≤ 1 / 4 := (norm_fst_le σ).trans hσ
  have h2 : ‖σ.2‖ ≤ 1 / 4 := (norm_snd_le σ).trans hσ
  rw [Real.norm_eq_abs] at h1 h2
  show |σ.1| + |σ.2| < 1
  linarith

/-- `(3/4, 0) ∈ dispRegion \ closedBall 0 (1/4)`: the inclusion `S ⊆ V` is strict. -/
theorem dispRegion_not_subset : ((3 / 4 : ℝ), (0 : ℝ)) ∈ dispRegion ∧
    ((3 / 4 : ℝ), (0 : ℝ)) ∉ Metric.closedBall (0 : ℝ × ℝ) (1 / 4) := by
  refine ⟨by show |(3 / 4 : ℝ)| + |(0 : ℝ)| < 1; norm_num [abs_of_pos], fun h => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h
  have := (le_max_left _ _).trans h
  norm_num at this

/-- **FE-S2.1L through the statement constant, for the arccos family.** `E = ℝ × ℝ`, `Ψ = disp`,
`V = {σ | |σ₁| + |σ₂| < 1}` (open, NOT compact), `S = closedBall 0 (1/4)` (compact; `S ⊆ V` because in the max norm
`|σ₁| + |σ₂| ≤ 1/2`; `S ≠ V` since `(3/4, 0) ∈ V \ S`, `dispRegion_not_subset`), `U = univ`, any compact `K`, any
`c > 0` and `N`. `ContDiffOn` of the uncurried family on `V ×ˢ univ` comes only from `Real.contDiffOn_arccos`.

Plants caught: `S ⊆ V` reversed (`V ⊆ S` fails, `dispRegion_not_subset`); `K ⊆ U` reversed (`univ ⊆ K` is not
derivable for an arbitrary compact `K`, and fails for every bounded `K`); `IsOpen V` replaced by `IsCompact V` (`V`
is not compact, and nothing about `V` beyond openness is available here). Plants NOT caught: any plant that WEAKENS a
hypothesis, e.g. `ContDiffOn … (V ×ˢ U)` replaced by `ContDiffOn … (S ×ˢ K)`, or a dropped hypothesis; a conditional
sanity theorem only detects a hypothesis that became harder to discharge. -/
theorem nonStationaryLocal_family (h : NonStationaryLocalStatement) (N : ℕ) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      σ ∈ Metric.closedBall (0 : ℝ × ℝ) (1 / 4) → ContDiff ℝ N A → tsupport A ⊆ K →
      (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → (∀ k ∈ K, c ≤ ‖fderiv ℝ (disp σ) k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (disp σ k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N :=
  h (ℝ × ℝ) N disp (Metric.closedBall 0 (1 / 4)) dispRegion K Set.univ c (isCompact_closedBall _ _)
    dispRegion_isOpen closedBall_subset_dispRegion hK isOpen_univ (Set.subset_univ K)
    (by exact_mod_cast disp_contDiffOn (N + 1)) hc

/-! ## FE-S2.2L and FE-S3L: the constant kink family -/

/-- The constant kink family is `C⁴` on `Ioo 0 2 ×ˢ kinkU`. -/
theorem kinkFamily_contDiffOn :
    ContDiffOn ℝ 4 (Function.uncurry fun _ : ℝ => kinkPhase) (Set.Ioo (0 : ℝ) 2 ×ˢ kinkU) :=
  kinkPhase_contDiffOn.comp contDiffOn_snd fun _ hq => hq.2

/-- `{1} ⊆ Ioo 0 2`. -/
theorem one_subset_Ioo : ({1} : Set ℝ) ⊆ Set.Ioo 0 2 := by
  rw [Set.singleton_subset_iff]; constructor <;> norm_num

/-- **FE-S2.2L through the statement constant.** `E = ℝ`, the constant family `fun _ => kinkPhase`, `S = {1}`,
`V = Ioo 0 2` (`S ⊊ V`), `U = kinkU = {k₁ > −3}`, `K = closedBall 0 2`, `K' = {L₀}`. The critical-point condition
is `kink_det_ne` (`x ≠ 0`, `det = 24x²`).

Plants caught: `S ⊆ V` reversed (`Ioo 0 2 ⊄ {1}`); `K ⊆ U` reversed (`kinkU ⊄ closedBall 0 2`); `IsOpen V` /
`IsOpen U` replaced by compactness (neither is compact); `+ L` replaced by `− L` (critical point `(0, 0) ∈ K`, Hessian
`diag(0, 2)`); "at every `k ∈ K`" (`(0, 0) ∈ K` is degenerate). Not caught: weakening plants (e.g. smoothness only on
`S ×ˢ K`). -/
theorem stationaryPhaseLocal_kink (h : StationaryPhaseLocalStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L₀ k)) * Complex.I) * A k‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := h ℝ (fun _ => kinkPhase) {1} (Set.Ioo 0 2) (Metric.closedBall 0 2) kinkU {L₀}
    isCompact_singleton isOpen_Ioo one_subset_Ioo (isCompact_closedBall _ _) kinkU_isOpen
    closedBall_subset_kinkU isCompact_singleton kinkFamily_contDiffOn
    (fun _ _ L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      exact kink_det_ne k (closedBall_subset_kinkU hk) hc)
  exact ⟨C, fun A M m hA hs hM hm =>
    hC A M 1 L₀ m (Set.mem_singleton _) hA hs hM (Set.mem_singleton _) hm⟩

/-- **FE-S3L through the statement constant**, same data as `stationaryPhaseLocal_kink`, rate `m^{-5/6}`;
`FoldOrNondegMatrix` by its nondegenerate branch. Plants caught: as for `stationaryPhaseLocal_kink` (with `− L` the
critical point `(0, 0)` has Hessian `diag(0, 2)`, kernel `e₀`, third derivative `0` along it: not a fold). -/
theorem foldLocal_kink (h : FoldLocalStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L₀ k)) * Complex.I) * A k‖ ≤
      C * M * m ^ (-(5 : ℝ) / 6) := by
  obtain ⟨C, hC⟩ := h ℝ (fun _ => kinkPhase) {1} (Set.Ioo 0 2) (Metric.closedBall 0 2) kinkU {L₀}
    isCompact_singleton isOpen_Ioo one_subset_Ioo (isCompact_closedBall _ _) kinkU_isOpen
    closedBall_subset_kinkU isCompact_singleton kinkFamily_contDiffOn
    (fun _ _ L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      exact Or.inl (kink_det_ne k (closedBall_subset_kinkU hk) hc))
  exact ⟨C, fun A M m hA hs hM hm =>
    hC A M 1 L₀ m (Set.mem_singleton _) hA hs hM (Set.mem_singleton _) hm⟩

/-! ## FE-S4.1′L: a generic cubic with a kink outside `U` -/

/-- `x³ + 2x²y + 3xy² + 5y³ + |x − 5| − 5 + x`: the generic cubic on `{x < 5}`, not differentiable on `x = 5`. -/
noncomputable def d4Kink (k : ℝ × ℝ) : ℝ := OscInt.D4.genCubic 1 2 3 5 k + |k.1 - 5| - 5 + k.1

/-- The open half-plane `{x < 5}`. -/
def d4U : Set (ℝ × ℝ) := {k | k.1 < 5}

theorem d4U_isOpen : IsOpen d4U := isOpen_lt continuous_fst continuous_const

theorem d4Kink_eq_on (k : ℝ × ℝ) (hk : k ∈ d4U) : d4Kink k = OscInt.D4.genCubic 1 2 3 5 k := by
  have : k.1 - 5 < 0 := by have h5 : k.1 < 5 := hk; linarith
  simp only [d4Kink, abs_of_neg this]; ring

theorem d4Kink_eventuallyEq : d4Kink =ᶠ[nhds 0] OscInt.D4.genCubic 1 2 3 5 :=
  Filter.eventually_of_mem (d4U_isOpen.mem_nhds (show (0 : ℝ × ℝ).1 < 5 by norm_num)) d4Kink_eq_on

theorem d4Kink_contDiffOn : ContDiffOn ℝ 4 d4Kink d4U :=
  (OscInt.API.ConvertSanity.d4FE_hyps_generic).1.contDiffOn.congr d4Kink_eq_on

/-- `d4Kink` is not `C¹` on `ℝ²`: it is not differentiable at `(5, 0)`. -/
theorem d4Kink_not_contDiff : ¬ ContDiff ℝ 1 d4Kink := by
  intro h
  have hd : DifferentiableAt ℝ d4Kink ((0 : ℝ) + 5, (0 : ℝ)) := h.differentiable (by norm_num) _
  have hl : DifferentiableAt ℝ (fun x : ℝ => ((x + 5, (0 : ℝ)) : ℝ × ℝ)) 0 :=
    (differentiableAt_id.add_const 5).prodMk (differentiableAt_const _)
  have hc : DifferentiableAt ℝ (fun x : ℝ => d4Kink (x + 5, 0)) 0 :=
    hd.comp (f := fun x : ℝ => ((x + 5, (0 : ℝ)) : ℝ × ℝ)) (0 : ℝ) hl
  have he : (abs : ℝ → ℝ) = fun x => d4Kink (x + 5, 0) - (x + 5) ^ 3 - x := by
    funext x; simp only [d4Kink, OscInt.D4.genCubic, add_sub_cancel_right]; ring
  apply not_differentiableAt_abs_zero
  rw [he]
  exact (hc.sub (by fun_prop)).sub (by fun_prop)

/-- **FE-S4.1′L through the statement constant.** `φ = d4Kink` (equal to `x³ + 2x²y + 3xy² + 5y³` on
`U = {x < 5}`, singular on `x = 5`; not `C¹` on `ℝ²`, `d4Kink_not_contDiff`), coefficients `(1, 2, 3, 5)`
(`disc = −367`). The derivative hypotheses at `0` come from germ equality with the generic cubic and
`d4FE_hyps_generic`. The coefficient order `x³, x²y, xy², y³` is pinned by `d4FE_reversed_fails` (the reversed
coefficients `(5, 3, 2, 1)` have the same discriminant but violate the identity). Plants caught: a permuted
coefficient order in the cubic form, a wrong factor (`6`) in front of it, `IsOpen U` replaced by `IsCompact U`
(`U = {x < 5}` is unbounded), `iteratedFDeriv ℝ 2 φ 0 = 0` replaced by a nonzero Hessian. Not caught: weakening
plants (e.g. `ContDiffOn ℝ 4 φ U` lowered to `ContDiffOn ℝ 3 φ U`). -/
theorem d4BoundLocal_kink (h : D4BoundLocalStatement) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ t →
      ‖∫ κ : ℝ × ℝ, Complex.exp (↑(t * d4Kink κ + L κ) * Complex.I) * A κ‖ ≤ C * M * t ^ (-(2 : ℝ) / 3) := by
  have h2 := (d4Kink_eventuallyEq.iteratedFDeriv ℝ 2).eq_of_nhds
  have h3 := (d4Kink_eventuallyEq.iteratedFDeriv ℝ 3).eq_of_nhds
  obtain ⟨-, h2', h3', hdisc⟩ := OscInt.API.ConvertSanity.d4FE_hyps_generic
  exact h d4Kink d4U 1 2 3 5 d4U_isOpen (show (0 : ℝ × ℝ).1 < 5 by norm_num) d4Kink_contDiffOn
    (h2.trans h2') (fun x y => by rw [h3]; exact h3' x y) hdisc

/-! ## FE-S2.1l: the kink phase -/

/-- The kink phase is `C^{N+1}` on `kinkU`, for every `N`. -/
theorem kinkPhase_contDiffOn_N (N : ℕ) : ContDiffOn ℝ (N + 1) kinkPhase kinkU := by
  have hP : ContDiff ℝ (N + 1) (signFamily 1) := by rw [signFamily_eq]; fun_prop
  exact hP.contDiffOn.congr kinkPhase_eq_on

/-- **FE-S2.1l through the statement constant.** `Ψ = kinkPhase`, `K = closedBall 0 2`, `U = kinkU`, `c = 1`, any
`N`. Plants caught: `K ⊆ U` reversed (`kinkU ⊄ closedBall 0 2`); `IsOpen U` replaced by `IsCompact U` (`kinkU` is
unbounded). Not caught: weakening plants (e.g. `ContDiffOn … U` replaced by `ContDiffOn … K`). -/
theorem nonStationaryOn_kink (h : NonStationaryOnStatement) (N : ℕ) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ N A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      (∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2, 1 ≤ ‖fderiv ℝ kinkPhase k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N :=
  h N kinkPhase (Metric.closedBall 0 2) kinkU 1 (isCompact_closedBall _ _) kinkU_isOpen closedBall_subset_kinkU
    (kinkPhase_contDiffOn_N N) one_pos

/-! ## S2.2F: the binder bite (adversarial M2) -/

/-- `Ψ(k) = k₁⁴/4 − 2k₁³ + 9/2 k₁² + k₂²`: `∂₁Ψ = x(x − 3)²`, `∂₁₁Ψ = 3(x − 1)(x − 3)`. -/
noncomputable def binderPhase (k : ℝ × ℝ) : ℝ := k.1 ^ 4 / 4 - 2 * k.1 ^ 3 + 9 / 2 * k.1 ^ 2 + k.2 ^ 2

theorem binderPhase_eq :
    binderPhase = fun k : ℝ × ℝ => (1 / 4) * k.1 ^ 4 + (-2) * k.1 ^ 3 + (9 / 2) * k.1 ^ 2 + 1 * k.2 ^ 2 := by
  funext k; simp only [binderPhase]; ring

/-- `∂_v Ψ(y) = (y₁³ − 6y₁² + 9y₁) v₁ + 2y₂ v₂`. -/
theorem binderPhase_fd (y v : ℝ × ℝ) :
    fderiv ℝ binderPhase y v = (y.1 ^ 3 - 6 * y.1 ^ 2 + 9 * y.1) * v.1 + 2 * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => (1 / 4) * k.1 ^ 4 + (-2) * k.1 ^ 3 + (9 / 2) * k.1 ^ 2 + 1 * k.2 ^ 2)
      ((y.1 ^ 3 - 6 * y.1 ^ 2 + 9 * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 4).const_mul (1 / 4)).add
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).const_mul (-2))).add
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul (9 / 2))).add
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2).const_mul 1) using 1
    ext <;> simp; ring
  rw [binderPhase_eq, h.fderiv]; simp

/-- `∂_w (a k₁³ + b k₁² + c k₁ + d k₂)(y) = (3a y₁² + 2b y₁ + c) w₁ + d w₂`. -/
theorem fd_cubic_lin (a b c d : ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.1 ^ 2 + c * k.1 + d * k.2) y w =
      (3 * a * y.1 ^ 2 + 2 * b * y.1 + c) * w.1 + d * w.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.1 ^ 2 + c * k.1 + d * k.2)
      ((3 * a * y.1 ^ 2 + 2 * b * y.1 + c) • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ)
      y := by
    convert (((((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).const_mul a).add
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul b)).add
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul c)).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul d) using 1
    ext <;> simp; ring
  rw [h.fderiv]; simp

/-- `∂_w ∂_v Ψ(y) = (3y₁² − 12y₁ + 9) v₁w₁ + 2 v₂w₂`. -/
theorem binderPhase_dd (y v w : ℝ × ℝ) :
    dd binderPhase y v w = (3 * y.1 ^ 2 - 12 * y.1 + 9) * v.1 * w.1 + 2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ binderPhase y v) =
      fun y => v.1 * y.1 ^ 3 + (-6 * v.1) * y.1 ^ 2 + (9 * v.1) * y.1 + (2 * v.2) * y.2 := by
    funext y; rw [binderPhase_fd]; ring
  rw [dd, this, fd_cubic_lin]; ring

/-- `hessDet Ψ(y) = 6(y₁ − 1)(y₁ − 3)`. -/
theorem binderPhase_hessDet (y : ℝ × ℝ) : hessDet binderPhase y = 6 * (y.1 - 1) * (y.1 - 3) := by
  simp only [hessDet, binderPhase_dd]; ring

/-- The point `(3, 0)` is a critical point of `Ψ + (0, 0)·` with a degenerate Hessian, and lies outside
`K = closedBall 0 1`: the binder `k ∈ K` is what excludes it. -/
theorem binder_degenerate_outside :
    IsCritical binderPhase (0, 0) (3, 0) ∧ hessDet binderPhase (3, 0) = 0 ∧
      ((3 : ℝ), (0 : ℝ)) ∉ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  refine ⟨?_, ?_, fun h => ?_⟩
  · simp only [IsCritical, binderPhase_fd]; norm_num
  · rw [binderPhase_hessDet]; norm_num
  · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h
    have := (le_max_left _ _).trans h
    norm_num at this

/-- `(1, 0) ∈ K = closedBall 0 1` has a degenerate Hessian, so "nondegenerate at every `k ∈ K`" fails here. -/
theorem binder_everywhere_fails :
    hessDet binderPhase (1, 0) = 0 ∧ ((1 : ℝ), (0 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  refine ⟨by rw [binderPhase_hessDet]; norm_num, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; norm_num

/-- The S2.2F hypothesis for `Ψ = binderPhase`, `K = closedBall 0 1`, `K' = {(0, 0), (3, 0)}`. -/
theorem binder_nondeg : ∀ p ∈ ({((0 : ℝ), (0 : ℝ)), ((3 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)),
    ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1, IsCritical binderPhase p k → hessDet binderPhase k ≠ 0 := by
  intro p hp k hk hc
  have hx : k.1 ≤ 1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hk
    have := (norm_fst_le k).trans hk
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  obtain ⟨h1, -⟩ := hc
  rw [binderPhase_fd] at h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rw [binderPhase_hessDet]
  refine mul_ne_zero (mul_ne_zero (by norm_num) fun h0 => ?_) fun h0 => ?_
  · have : k.1 = 1 := by linarith
    rcases hp with rfl | rfl <;> rw [this] at h1 <;> norm_num at h1
  · have : k.1 = 3 := by linarith
    linarith

/-- **S2.2F through the statement constant: the binder bite (adversarial M2).** One-point family `Unit`,
`Ψ = k₁⁴/4 − 2k₁³ + 9/2 k₁² + k₂²` (`∂₁Ψ = x(x − 3)²`, `∂₁₁Ψ = 3(x − 1)(x − 3)`), `K = closedBall 0 1`,
`K' = {(0, 0), (3, 0)}`. With `p = (0, 0)` the critical points are `(0, 0)` (Hessian `diag(9, 2)`, in `K`) and
`(3, 0)` (degenerate, NOT in `K`, `binder_degenerate_outside`). With `p = (3, 0)` the critical points satisfy
`x³ − 6x² + 9x + 3 = 0`, which is `7` at `x = 1` and `3` at `x = 3`, so the Hessian is nondegenerate there.

Plants caught: the binder `∀ k ∈ K` replaced by `∀ k` (the degenerate critical point `(3, 0)` enters), or by
`∀ k ∈ K'` read as points (`(3, 0) ∈ K'` is then a degenerate critical point for `p = (0, 0)`). Also caught here,
contrary to the expectation in the brief: "nondegenerate at every `k ∈ K`" (dropping the critical-point condition),
because `hessDet = 6(x − 1)(x − 3)` vanishes at `(1, 0) ∈ K` (`binder_everywhere_fails`); the sign bites
(`stationaryPhaseFamily_sign_bite`) catch that plant too. Weakening plants are not caught. -/
theorem stationaryPhaseFamily_binder_bite (h : StationaryPhaseFamilyStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound 2 (Metric.closedBall 0 1) A M → p ∈ ({((0 : ℝ), (0 : ℝ)), ((3 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) →
      1 ≤ m → ‖oscInt2 (fun k => m * (binderPhase k + lin p k)) A‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := h Unit (fun _ => binderPhase) (Metric.closedBall 0 1)
    {((0 : ℝ), (0 : ℝ)), ((3 : ℝ), (0 : ℝ))}
    (sanity_familyCk_const 4 _ (by rw [binderPhase_eq]; fun_prop)) (isCompact_closedBall _ _)
    (Set.toFinite _).isCompact (fun _ => binder_nondeg)
  exact ⟨C, fun A M p m hA hp hm => hC A M () p m hA hp hm⟩

end OscInt.API.FamilySanity
