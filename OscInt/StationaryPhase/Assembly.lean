import Blueprint.StationaryPhase
import OscInt.StationaryPhase.Family

/-!
# S2.2, S3 assembly against the blueprint interfaces

`StationaryPhaseStatement` and `FoldStatement` from the localisation (R2), the non-critical local bound (L1) and
the critical-point local bounds (L2–L6), following `docs/proof-S2S3.md` (R1): the linear term `p·k` becomes part of
the parameter, it changes only first derivatives, so Hessians, third derivatives, `hessDet` and `FoldOrNondeg` are
those of `Ψ_σ`, and `k` is a critical point of `Ψ_σ + p·` exactly when `IsCritical (Ψ_σ) p k`.
-/

namespace OscInt.StationaryPhase

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

theorem hasFDerivAt_lin (p y : ℝ × ℝ) :
    HasFDerivAt (lin p) (p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
  exact ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul p.1).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul p.2)

theorem fderiv_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) (p y v : ℝ × ℝ) :
    fderiv ℝ (fun k => Ψ k + lin p k) y v = fderiv ℝ Ψ y v + (p.1 * v.1 + p.2 * v.2) := by
  rw [((hΨ y).hasFDerivAt.fun_add (hasFDerivAt_lin p y)).fderiv]
  simp

theorem dd_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    dd (fun k => Ψ k + lin p k) = dd Ψ := by
  have h1 : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  funext y v w
  have : (fun y => fderiv ℝ (fun k => Ψ k + lin p k) y v) =
      fun y => fderiv ℝ Ψ y v + (p.1 * v.1 + p.2 * v.2) := by
    funext y; exact fderiv_add_lin h1 p y v
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ Ψ y v) y :=
    ((hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).clm_apply
      (differentiableAt_const v)
  simp only [dd, this]
  rw [fderiv_add_const]

theorem ddd_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    ddd (fun k => Ψ k + lin p k) = ddd Ψ := by
  funext y u v w
  simp only [ddd, dd_add_lin hΨ p]

theorem hessDet_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    hessDet (fun k => Ψ k + lin p k) = hessDet Ψ := by
  funext k; simp only [hessDet, dd_add_lin hΨ p]

theorem foldOrNondeg_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (p k : ℝ × ℝ) :
    FoldOrNondeg (fun k => Ψ k + lin p k) k ↔ FoldOrNondeg Ψ k := by
  simp only [FoldOrNondeg, hessDet_add_lin hΨ p, dd_add_lin hΨ p, ddd_add_lin hΨ p]

theorem isCritical_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) (p k : ℝ × ℝ) :
    IsCritical (fun k => Ψ k + lin p k) 0 k ↔ IsCritical Ψ p k := by
  simp only [IsCritical, fderiv_add_lin hΨ]; norm_num

theorem familyCk_of_le {Λ : Type} [TopologicalSpace Λ] {m n : ℕ} {Ψ : Λ → ℝ × ℝ → ℝ} (hmn : m ≤ n)
    (h : FamilyCk n Ψ) : FamilyCk m Ψ :=
  ⟨fun σ => (h.1 σ).of_le (by exact_mod_cast hmn), fun j hj => h.2 j (hj.trans hmn)⟩

theorem ampBound_nonneg {n : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0 (Nat.zero_le n) 0)

/-- A local bound with rate `1` gives one with any rate `r ≤ 1`. -/
theorem LocalBound.of_one {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {τ₀ : T} {k₀ : ℝ × ℝ}
    {r : ℝ} (hr : r ≤ 1) (h : LocalBound Q τ₀ k₀ 1) : LocalBound Q τ₀ k₀ r := by
  obtain ⟨U, hU, δ, hδ, C, hC⟩ := h
  refine ⟨U, hU, δ, hδ, max C 0, fun A M τ m hτ hA hm => (hC A M τ m hτ hA hm).trans ?_⟩
  have hM := ampBound_nonneg hA
  have h1 : m ^ (-(1 : ℝ)) ≤ m ^ (-r) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
  calc C * M * m ^ (-(1 : ℝ)) ≤ max C 0 * M * m ^ (-(1 : ℝ)) := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * M * m ^ (-r) := by gcongr

/-- The parameter space `Λ × K'` of (R1) is compact. -/
theorem compactSpace_prod_subtype (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] {K' : Set (ℝ × ℝ)}
    (hK' : IsCompact K') : CompactSpace (Λ × K') := by
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  infer_instance

/-- **S3** from the interfaces. -/
theorem fold_of (hFL : FamilyAddLinearFacts) (hLoc : LocalizationFacts) (hNC : LocalNonCritFacts)
    (hC : LocalCritFacts) : FoldStatement := by
  intro Λ _ _ Ψ K K' hΨ hK hK' hfold
  have := compactSpace_prod_subtype Λ hK'
  let Q : Λ × K' → ℝ × ℝ → ℝ := fun q k => Ψ q.1 k + lin q.2.1 k
  have hQ : FamilyCk 4 Q := hFL Λ 4 Ψ K' hΨ
  have h2 : ∀ σ, ContDiff ℝ 2 (Ψ σ) := fun σ => (hΨ.1 σ).of_le (by norm_num)
  obtain ⟨C, hCb⟩ := hLoc (Λ × K') Q K (5 / 6) hK fun q k hk => by
    by_cases hcr : IsCritical (Q q) 0 k
    · exact (hC _ Q q k hQ hcr).2 ((foldOrNondeg_add_lin (h2 q.1) q.2.1 k).mpr (hfold q.1 k hk))
    · exact LocalBound.of_one (by norm_num) (hNC _ Q q k (familyCk_of_le (by norm_num) hQ) hcr)
  refine ⟨C, fun A M σ p m hA hp hm => ?_⟩
  have := hCb A M (σ, ⟨p, hp⟩) m hA hm
  simpa [Q, show (-(5 : ℝ) / 6) = -(5 / 6) by ring] using this

/-- **S2.2** from the interfaces. -/
theorem stationaryPhase_of (hFL : FamilyAddLinearFacts) (hLoc : LocalizationFacts) (hNC : LocalNonCritFacts)
    (hC : LocalCritFacts) : StationaryPhaseStatement := by
  intro Ψ K K' hΨ hK hK' hcrit
  have := compactSpace_prod_subtype Unit hK'
  let Q : Unit × K' → ℝ × ℝ → ℝ := fun q k => Ψ k + lin q.2.1 k
  have hΨ1 : FamilyCk 4 (fun _ : Unit => Ψ) := sanity_familyCk_const 4 Ψ hΨ
  have hQ : FamilyCk 4 Q := hFL Unit 4 _ K' hΨ1
  have h2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
  obtain ⟨C, hCb⟩ := hLoc (Unit × K') Q K 1 hK fun q k hk => by
    by_cases hcr : IsCritical (Q q) 0 k
    · refine (hC _ Q q k hQ hcr).1 ?_
      have hc := (isCritical_add_lin (h2.differentiable (by norm_num)) q.2.1 k).mp hcr
      simpa [Q, hessDet_add_lin h2 q.2.1] using hcrit q.2.1 q.2.2 k hk hc
    · exact hNC _ Q q k (familyCk_of_le (by norm_num) hQ) hcr
  refine ⟨C, fun A M p m hA hp hm => ?_⟩
  have := hCb A M ((), ⟨p, hp⟩) m hA hm
  rw [Real.rpow_neg_one] at this
  simpa [Q, div_eq_mul_inv] using this

end OscInt.StationaryPhase
