import Blueprint.StationaryPhase
import OscInt.StationaryPhase.Family
import OscInt.StationaryPhase.Change

/-!
# S2/S3: local bounds at critical points (L2–L6 assembled) and S2.1 from the non-stationary core

This file proves
* `OscInt.StationaryPhase.localCrit_of : NormalFormFacts → NormalizedDataFacts → CoreEstimateFacts →
  LocalCritFacts`. Route `docs/proof-S2S3.md` (L2)–(L6): at a critical point `k₀` of `Q τ₀`, the normal form
  (L2) gives `L` with `NormalPoint j (Q τ₀ ∘ (k₀ + L·))`; the family `τ ↦ Q τ ∘ (k₀ + L·)` is of class `C⁴`
  (`familyAffine`); the normalized data (L3–L5) and the core estimate (L6) bound `I(m Q_τ ∘ (k₀ + L·), B)` for
  `B` supported in `[-a, a] × [-b, b]`. An amplitude supported in `closedBall k₀ δ`, `δ = min a b / (‖L⁻¹‖ + 1)`,
  is moved there by `affineChange` and `ampBoundAffine` (max norm on `ℝ × ℝ`). Rates: `1/2 + 1/2 = 1` (j = 2),
  `1/2 + 1/3 = 5/6` (j = 3); under `FoldOrNondeg` with `hessDet ≠ 0` the rate-1 bound is used (`m ≥ 1`).
* `OscInt.StationaryPhase.nonStationary_of : NonStatCoreFacts → NonStationaryStatement`. Route (N1) with the
  revision: let `G` bound `|∂ᵢΨ_σ|` on `Λ × K` and `R = 2G + 1`. For `‖p‖ ≤ R` (max norm) the parameter set
  `{(σ, p) : ‖p‖ ≤ R, ∀ k ∈ K, GradLower (Ψ σ) p k c}` is compact (closed in `Λ × closedBall 0 R`) and carries the
  family `Ψ_σ + p·`. For `‖p‖ > R`, `m (Ψ_σ + p·) = (m ‖p‖)(s Ψ_σ + u·)` with `s = ‖p‖⁻¹ ∈ [0, 1/R]`,
  `u = s p` on the unit sphere of the max norm, and the family `(σ, s, u) ↦ s Ψ_σ + u·` over the compact
  `Λ × [0, 1/R] × S` has gradient `≥ 1/2` on `K`; the frequency `m ‖p‖ ≥ m` only improves `m^{-N}`.
-/

namespace OscInt.StationaryPhase.LocalCritAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

/-- Amplitude bounds are monotone in the support set. -/
theorem ampBound_mono {n : ℕ} {K K' : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M)
    (hK : K ⊆ K') : AmpBound n K' A M :=
  ⟨h.1, h.2.1.trans hK, h.2.2⟩

theorem ampBound_nonneg' {n : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M) :
    0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0 (Nat.zero_le n) 0)

/-- Families of class `Cⁿ` pull back along continuous maps of the parameter. -/
theorem familyCk_comp {Λ Λ' : Type} [TopologicalSpace Λ] [TopologicalSpace Λ'] {n : ℕ}
    {Ψ : Λ → ℝ × ℝ → ℝ} (h : FamilyCk n Ψ) {f : Λ' → Λ} (hf : Continuous f) :
    FamilyCk n (fun σ => Ψ (f σ)) :=
  ⟨fun σ => h.1 (f σ), fun j hj => (h.2 j hj).comp (hf.prodMap continuous_id)⟩

/-- The preimage of `closedBall k₀ δ` under `k ↦ k₀ + L k` lies in the box `[-a, a] × [-b, b]` when
`δ (‖L⁻¹‖ + 1) ≤ min a b`. -/
theorem preimage_ball_subset_box (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (k₀ : ℝ × ℝ) {a b δ : ℝ} (hδ : 0 ≤ δ)
    (hab : δ * (‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ + 1) ≤ min a b) :
    (fun k => k₀ + L k) ⁻¹' Metric.closedBall k₀ δ ⊆ Icc (-a) a ×ˢ Icc (-b) b := by
  intro k hk
  simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hk
  have hk' : ‖k‖ ≤ min a b := by
    calc ‖k‖ = ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (L k)‖ := by simp
      _ ≤ ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ * ‖L k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ * δ := by gcongr
      _ ≤ δ * (‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ + 1) := by
          nlinarith [norm_nonneg (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))]
      _ ≤ min a b := hab
  have h1 : |k.1| ≤ min a b := (norm_fst_le k).trans hk'
  have h2 : |k.2| ≤ min a b := (norm_snd_le k).trans hk'
  exact ⟨abs_le.mp (h1.trans (min_le_left _ _)), abs_le.mp (h2.trans (min_le_right _ _))⟩

/-- **Local bound at a normal point.** If `L` puts `Q τ₀` into normal form of order `j` at `k₀`, the
normalized data (L3–L5) and the core estimate (L6) give a local bound with rate `1/2 + 1/j`. -/
theorem localBound_of_normalPoint (hND : NormalizedDataFacts) (hCE : CoreEstimateFacts) (j : ℕ)
    (hj : j = 2 ∨ j = 3) {T : Type} [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (τ₀ : T) (k₀ : ℝ × ℝ)
    (hQ : FamilyCk 4 Q) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (hNP : NormalPoint j (fun k => Q τ₀ (k₀ + L k))) :
    LocalBound Q τ₀ k₀ (1 / 2 + 1 / (j : ℝ)) := by
  set L' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
  have hQ' : FamilyCk 4 (fun τ => fun k => Q τ (k₀ + L k)) := familyAffine T 4 Q k₀ L' hQ
  obtain ⟨U, hU, a, b, μ, ν, D, ha, hb, hμ, hν, ys, hys⟩ := hND j hj T _ τ₀ hQ' hNP
  obtain ⟨C, hC⟩ := hCE j hj a b μ ν D ha hb hμ hν
  set S := ‖(L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ + 1
  have hS : 0 < S := by positivity
  refine ⟨U, hU, min a b / S, div_pos (lt_min ha hb) hS,
    |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| * C * max 1 ‖L'‖ ^ 2,
    fun A M τ m hτ hA hm => ?_⟩
  have hsub := preimage_ball_subset_box L k₀ (div_pos (lt_min ha hb) hS).le
    (le_of_eq (div_mul_cancel₀ _ hS.ne'))
  have hA' := ampBound_mono (ampBoundAffine 2 _ A M k₀ L hA) hsub
  have hcore := hC _ (ys τ) _ _ m (hys τ hτ) hA' hm
  rw [affineChange (fun k => m * Q τ k) A k₀ L, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  calc |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| *
        ‖oscInt2 (fun k => m * Q τ (k₀ + L k)) (fun k => A (k₀ + L k))‖
      ≤ |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| *
        (C * (max 1 ‖L'‖ ^ 2 * M) * m ^ (-(1 / 2 + 1 / (j : ℝ)))) := by gcongr
    _ = _ := by ring

/-- A local bound with rate `r'` gives one with any rate `r ≤ r'` (as `m ≥ 1`). -/
theorem localBound_mono {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {τ₀ : T} {k₀ : ℝ × ℝ}
    {r r' : ℝ} (hr : r ≤ r') (h : LocalBound Q τ₀ k₀ r') : LocalBound Q τ₀ k₀ r := by
  obtain ⟨U, hU, δ, hδ, C, hC⟩ := h
  refine ⟨U, hU, δ, hδ, max C 0, fun A M τ m hτ hA hm => (hC A M τ m hτ hA hm).trans ?_⟩
  have hM := ampBound_nonneg' hA
  have h1 : m ^ (-r') ≤ m ^ (-r) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
  calc C * M * m ^ (-r') ≤ max C 0 * M * m ^ (-r') := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * M * m ^ (-r) := by gcongr

theorem localBound_congr_rate {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {τ₀ : T}
    {k₀ : ℝ × ℝ} {r r' : ℝ} (hr : r = r') (h : LocalBound Q τ₀ k₀ r') : LocalBound Q τ₀ k₀ r :=
  hr ▸ h

end OscInt.StationaryPhase.LocalCritAux

namespace OscInt.StationaryPhase

open Set MeasureTheory OscInt.Statements OscInt.Blueprint LocalCritAux

/-- **L2–L6 assembled**: local bounds at critical points, rate `1` for a nondegenerate Hessian and `5/6` at a
point where `FoldOrNondeg` holds. -/
theorem localCrit_of (hNF : NormalFormFacts) (hND : NormalizedDataFacts) (hCE : CoreEstimateFacts) :
    LocalCritFacts := by
  intro T _ Q τ₀ k₀ hQ hcr
  have hNF' := hNF (Q τ₀) k₀ (hQ.1 τ₀) hcr
  have h2 : hessDet (Q τ₀) k₀ ≠ 0 → LocalBound Q τ₀ k₀ 1 := fun hdet => by
    obtain ⟨L, hL⟩ := hNF'.1 hdet
    exact localBound_congr_rate (by norm_num)
      (localBound_of_normalPoint hND hCE 2 (Or.inl rfl) Q τ₀ k₀ hQ L hL)
  refine ⟨h2, fun hfold => ?_⟩
  by_cases hdet : hessDet (Q τ₀) k₀ = 0
  · obtain ⟨L, hL⟩ := hNF'.2 hdet hfold
    exact localBound_congr_rate (by norm_num)
      (localBound_of_normalPoint hND hCE 3 (Or.inr rfl) Q τ₀ k₀ hQ L hL)
  · exact localBound_mono (by norm_num) (h2 hdet)

end OscInt.StationaryPhase

namespace OscInt.StationaryPhase.LocalCritAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

/-- Directional first derivatives of a family of class `C¹` are jointly continuous. -/
theorem continuous_fderiv_apply {Λ : Type} [TopologicalSpace Λ] {n : ℕ} {Ψ : Λ → ℝ × ℝ → ℝ}
    (h : FamilyCk n Ψ) (hn : 1 ≤ n) (v : ℝ × ℝ) :
    Continuous fun q : Λ × (ℝ × ℝ) => fderiv ℝ (Ψ q.1) q.2 v := by
  have h1 := h.2 1 hn
  have : (fun q : Λ × (ℝ × ℝ) => fderiv ℝ (Ψ q.1) q.2 v) =
      fun q => iteratedFDeriv ℝ 1 (Ψ q.1) q.2 (fun _ => v) := by
    funext q; rw [iteratedFDeriv_one_apply]
  rw [this]
  fun_prop

/-- Multiplying a family by a continuous real parameter `s` keeps class `Cⁿ`. -/
theorem familyCk_smul {Λ : Type} [TopologicalSpace Λ] {n : ℕ} {Ψ : Λ → ℝ × ℝ → ℝ} (h : FamilyCk n Ψ)
    (S : Set ℝ) : FamilyCk n (fun q : Λ × S => fun k => (q.2 : ℝ) * Ψ q.1 k) := by
  refine ⟨fun q => contDiff_const.mul (h.1 q.1), fun j hj => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have : ∀ q : (Λ × S) × (ℝ × ℝ), iteratedFDeriv ℝ j (fun k => (q.1.2 : ℝ) * Ψ q.1.1 k) q.2 =
      (q.1.2 : ℝ) • iteratedFDeriv ℝ j (Ψ q.1.1) q.2 := fun q => by
    have he : (fun k => (q.1.2 : ℝ) * Ψ q.1.1 k) = (q.1.2 : ℝ) • Ψ q.1.1 := by funext k; simp
    rw [he, iteratedFDeriv_const_smul_apply ((h.1 q.1.1).of_le hj').contDiffAt]
  simp_rw [this]
  exact (continuous_subtype_val.comp continuous_fst.snd).smul
    ((h.2 j hj).comp (continuous_fst.fst.prodMk continuous_snd))

theorem fderiv_smul_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) (s : ℝ) (u y v : ℝ × ℝ) :
    fderiv ℝ (fun k => s * Ψ k + lin u k) y v = s * fderiv ℝ Ψ y v + (u.1 * v.1 + u.2 * v.2) := by
  have hl : HasFDerivAt (lin u)
      (u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul u.1).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul u.2)
  rw [(((hΨ y).hasFDerivAt.const_mul s).fun_add hl).fderiv]
  simp

theorem fderiv_add_lin' {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) (p y v : ℝ × ℝ) :
    fderiv ℝ (fun k => Ψ k + lin p k) y v = fderiv ℝ Ψ y v + (p.1 * v.1 + p.2 * v.2) := by
  have h := fderiv_smul_add_lin hΨ 1 p y v
  simp only [one_mul] at h
  exact h

/-- A bound on the partial derivatives of a `C¹` family on `Λ × K` (`Λ` compact, `K` compact). -/
theorem exists_bound_partials {Λ : Type} [TopologicalSpace Λ] [CompactSpace Λ] {n : ℕ}
    {Ψ : Λ → ℝ × ℝ → ℝ} (h : FamilyCk n Ψ) (hn : 1 ≤ n) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ G, 0 ≤ G ∧ ∀ σ, ∀ k ∈ K, |fderiv ℝ (Ψ σ) k (1, 0)| ≤ G ∧ |fderiv ℝ (Ψ σ) k (0, 1)| ≤ G := by
  obtain ⟨G, hG⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn
    (((continuous_fderiv_apply h hn (1, 0)).abs.add (continuous_fderiv_apply h hn (0, 1)).abs).continuousOn)
  refine ⟨max G 0, le_max_right _ _, fun σ k hk => ?_⟩
  have := hG (σ, k) ⟨mem_univ _, hk⟩
  simp only [Pi.add_apply, Real.norm_eq_abs] at this
  rw [abs_of_nonneg (by positivity)] at this
  constructor <;> nlinarith [abs_nonneg (fderiv ℝ (Ψ σ) k (1, 0)), abs_nonneg (fderiv ℝ (Ψ σ) k (0, 1)),
    le_max_left G 0]

/-- Arithmetic for the large-`p` case: if `|t| = 1` and `|s a| ≤ 1/2` then `(s a + t)² ≥ 1/4`. -/
theorem sq_ge_quarter {s a t : ℝ} (ht : |t| = 1) (hsa : |s * a| ≤ 1 / 2) : (1 / 2 : ℝ) ^ 2 ≤ (s * a + t) ^ 2 := by
  have h1 : 1 / 2 ≤ |s * a + t| := by
    have := abs_sub_abs_le_abs_sub t (-(s * a))
    rw [abs_neg, ht, sub_neg_eq_add, add_comm] at this
    linarith
  have := sq_le_sq' (by linarith [abs_nonneg (s * a + t)]) h1
  simpa [sq_abs] using this

end OscInt.StationaryPhase.LocalCritAux

namespace OscInt.StationaryPhase.LocalCritAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

/-- Enlarging the constant and lowering the frequency in a bound `C M / m'^N`. -/
theorem bound_mono {x C C' M m m' : ℝ} {N : ℕ} (hx : x ≤ C' * M / m' ^ N) (hC : max C' 0 ≤ C) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hmm : m ≤ m') : x ≤ C * M / m ^ N := by
  have hm0 : 0 < m ^ N := pow_pos (by linarith) N
  have hmm' : m ^ N ≤ m' ^ N := pow_le_pow_left₀ (by linarith) hmm N
  have h1 : C' * M ≤ C * M := mul_le_mul_of_nonneg_right ((le_max_left C' 0).trans hC) hM
  have h2 : 0 ≤ C * M := mul_nonneg ((le_max_right C' 0).trans hC) hM
  calc x ≤ C' * M / m' ^ N := hx
    _ ≤ C * M / m' ^ N := div_le_div_of_nonneg_right h1 (hm0.trans_le hmm').le
    _ ≤ C * M / m ^ N := div_le_div_of_nonneg_left h2 hm0 hmm'

/-- (N1), bounded linear terms: the parameter set `{(σ, p) : ‖p‖ ≤ R, |∇(Ψ_σ + p·)| ≥ c on K}` is compact. -/
theorem nonStat_small (hNS : NonStatCoreFacts) (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (N : ℕ)
    (Ψ : Λ → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (c R : ℝ) (hΨ : FamilyCk (N + 1) Ψ) (hK : IsCompact K)
    (hc : 0 < c) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound N K A M → ‖p‖ ≤ R → (∀ k ∈ K, GradLower (Ψ σ) p k c) → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m ^ N := by
  set S : Set (Λ × (ℝ × ℝ)) := {q | ‖q.2‖ ≤ R ∧ ∀ k ∈ K, GradLower (Ψ q.1) q.2 k c} with hS
  have hd := fun k v => (continuous_fderiv_apply hΨ (by omega) v).comp
    (continuous_fst.prodMk (continuous_const (y := k)) : Continuous fun q : Λ × (ℝ × ℝ) => (q.1, k))
  have hSeq : S = {q : Λ × (ℝ × ℝ) | ‖q.2‖ ≤ R} ∩ ⋂ k ∈ K, {q | GradLower (Ψ q.1) q.2 k c} := by
    ext q; simp [hS]
  have hScl : IsClosed S := by
    rw [hSeq]
    refine (isClosed_le (continuous_norm.comp continuous_snd) continuous_const).inter
      (isClosed_biInter fun k _ => isClosed_le continuous_const ?_)
    exact (((hd k (1, 0)).add continuous_snd.fst).pow 2).add (((hd k (0, 1)).add continuous_snd.snd).pow 2)
  have hScp : IsCompact S := (isCompact_univ.prod (isCompact_closedBall (0 : ℝ × ℝ) R)).of_isClosed_subset
    hScl fun q hq => ⟨mem_univ _, by simpa using hq.1⟩
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScp
  have hΦ : FamilyCk (N + 1) (fun q : S => fun k => Ψ q.1.1 k + lin q.1.2 k) :=
    familyCk_comp (familyAddLinear Λ (N + 1) Ψ univ hΨ)
      (f := fun q : S => (q.1.1, (⟨q.1.2, mem_univ _⟩ : (univ : Set (ℝ × ℝ)))))
      (continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _))
  obtain ⟨C, hC⟩ := hNS S N _ K c hΦ hK hc fun q k hk => by
    have := q.2.2 k hk
    simp only [GradLower] at this ⊢
    rw [fderiv_add_lin' ((hΨ.1 q.1.1).differentiable (by simp)),
      fderiv_add_lin' ((hΨ.1 q.1.1).differentiable (by simp))]
    simpa using this
  exact ⟨C, fun A M σ p m hA hp hg hm => hC A M ⟨(σ, p), hp, hg⟩ m hA hm⟩

end OscInt.StationaryPhase.LocalCritAux

namespace OscInt.StationaryPhase.LocalCritAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint

/-- The gradient lower bound `1/2` for `sΨ_σ + u·` when `‖u‖ = 1` (max norm) and `s |∂ᵢΨ_σ| ≤ 1/2`. -/
theorem gradLower_smul_add_lin {Ψ : ℝ × ℝ → ℝ} (hΨ : Differentiable ℝ Ψ) {s : ℝ} {u k : ℝ × ℝ}
    (hu : ‖u‖ = 1) (h1 : |s * fderiv ℝ Ψ k (1, 0)| ≤ 1 / 2) (h2 : |s * fderiv ℝ Ψ k (0, 1)| ≤ 1 / 2) :
    GradLower (fun k => s * Ψ k + lin u k) 0 k (1 / 2) := by
  simp only [GradLower, fderiv_smul_add_lin hΨ]
  simp only [mul_one, mul_zero, add_zero, zero_add, Prod.fst_zero, Prod.snd_zero]
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hu
  rcases max_choice |u.1| |u.2| with h | h <;> rw [h] at hu
  · nlinarith [sq_ge_quarter hu h1, sq_nonneg (s * fderiv ℝ Ψ k (0, 1) + u.2)]
  · nlinarith [sq_ge_quarter hu h2, sq_nonneg (s * fderiv ℝ Ψ k (1, 0) + u.1)]

/-- `m (Ψ + p·) = (m ‖p‖) (‖p‖⁻¹ Ψ + (‖p‖⁻¹ p)·)` for `p ≠ 0`. -/
theorem phase_rescale (Ψ : ℝ × ℝ → ℝ) (m : ℝ) {p : ℝ × ℝ} (hp : p ≠ 0) :
    (fun k => m * (Ψ k + lin p k)) =
      fun k => (m * ‖p‖) * (‖p‖⁻¹ * Ψ k + lin (‖p‖⁻¹ • p) k) := by
  have : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  funext k
  simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp

/-- (N1), large linear terms: the family `(σ, s, u) ↦ sΨ_σ + u·` over `Λ × [0, 1/R] × S¹`. -/
theorem nonStat_large (hNS : NonStatCoreFacts) (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (N : ℕ)
    (Ψ : Λ → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (G R : ℝ) (hΨ : FamilyCk (N + 1) Ψ) (hK : IsCompact K)
    (hR : 1 ≤ R) (hGR : 2 * G ≤ R)
    (hbd : ∀ σ, ∀ k ∈ K, |fderiv ℝ (Ψ σ) k (1, 0)| ≤ G ∧ |fderiv ℝ (Ψ σ) k (0, 1)| ≤ G) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound N K A M → R < ‖p‖ → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m ^ N := by
  have : CompactSpace (Metric.sphere (0 : ℝ × ℝ) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hΦ := familyAddLinear (Λ × Icc (0 : ℝ) (1 / R)) (N + 1) (fun q k => (q.2 : ℝ) * Ψ q.1 k)
    (Metric.sphere 0 1) (familyCk_smul hΨ _)
  have hsG : ∀ s ∈ Icc (0 : ℝ) (1 / R), ∀ t : ℝ, |t| ≤ G → |s * t| ≤ 1 / 2 := fun s hs t ht => by
    rw [abs_mul, abs_of_nonneg hs.1]
    have h1 : s * |t| ≤ (1 / R) * G := mul_le_mul hs.2 ht (abs_nonneg _) (by positivity)
    have h2 : (1 / R) * G ≤ 1 / 2 := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]; linarith
    linarith
  obtain ⟨C, hC⟩ := hNS _ N _ K (1 / 2) hΦ hK (by norm_num) fun q k hk =>
    gradLower_smul_add_lin ((hΨ.1 q.1.1).differentiable (by simp)) (by simp)
      (hsG _ q.1.2.2 _ (hbd _ k hk).1) (hsG _ q.1.2.2 _ (hbd _ k hk).2)
  refine ⟨max C 0, fun A M σ p m hA hp hm => ?_⟩
  have hp0 : 0 < ‖p‖ := by linarith
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  have hs : ‖p‖⁻¹ ∈ Icc (0 : ℝ) (1 / R) :=
    ⟨by positivity, by rw [one_div]; exact inv_anti₀ (by linarith) hp.le⟩
  have hu : ‖p‖⁻¹ • p ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp0.ne']
  have hm' : m ≤ m * ‖p‖ := le_mul_of_one_le_right (by linarith) (by linarith)
  have := hC A M ((σ, ⟨‖p‖⁻¹, hs⟩), ⟨‖p‖⁻¹ • p, hu⟩) (m * ‖p‖) hA (hm.trans hm')
  rw [phase_rescale (Ψ σ) m hpne]
  exact bound_mono this le_rfl (ampBound_nonneg' hA) hm hm'

end OscInt.StationaryPhase.LocalCritAux

namespace OscInt.StationaryPhase

open Set MeasureTheory OscInt.Statements OscInt.Blueprint LocalCritAux

/-- **S2.1** from the compact non-stationary core (N2), by the compactification (N1) of the linear term. -/
theorem nonStationary_of (hNS : NonStatCoreFacts) : NonStationaryStatement := by
  intro Λ _ _ N Ψ K c hΨ hK hc
  obtain ⟨G, hG, hbd⟩ := exists_bound_partials hΨ (by omega) hK
  obtain ⟨C₁, hC₁⟩ := nonStat_small hNS Λ N Ψ K c (2 * G + 1) hΨ hK hc
  obtain ⟨C₂, hC₂⟩ := nonStat_large hNS Λ N Ψ K G (2 * G + 1) hΨ hK (by linarith) (by linarith) hbd
  refine ⟨max C₁ 0 + max C₂ 0, fun A M σ p m hA hg hm => ?_⟩
  have hM := ampBound_nonneg' hA
  rcases le_or_gt ‖p‖ (2 * G + 1) with hp | hp
  · exact bound_mono (hC₁ A M σ p m hA hp hg hm)
      (le_add_of_le_of_nonneg le_rfl (le_max_right _ _)) hM hm le_rfl
  · exact bound_mono (hC₂ A M σ p m hA hp hm)
      (le_add_of_nonneg_left (le_max_right _ _)) hM hm le_rfl

end OscInt.StationaryPhase
