import Blueprint.StationaryPhase
import OscInt.StationaryPhase.Partition
import OscInt.StationaryPhase.Change

/-!
# R2: localisation of oscillatory integral bounds

We prove `OscInt.StationaryPhase.localization : OscInt.Blueprint.LocalizationFacts`: if every point
`(τ₀, k₀) ∈ T × K` (with `T` compact, `K ⊆ ℝ²` compact) has a local bound `|I(mQ_τ, A)| ≤ C M m^{-r}` for
`τ` near `τ₀` and amplitudes supported in a small closed ball around `k₀`, then the bound holds uniformly in
`τ ∈ T` for all amplitudes supported in `K`.

Route: `docs/proof-S2S3.md` (R2), organised as two successive compactness arguments, which avoids the
bookkeeping of subsets `S` of a cover of `T × K`:
1. (`LocalizeAux.uniform_near`) Fix `τ₀`. The balls `ball k δ_k` (data of `LocalBound Q τ₀ k r`, `k ∈ K`) cover
   `K`; take a finite subcover, a smooth partition of unity `χ_i` subordinate to it (`PartitionAux`, F2a) and the
   cut-off constants of `ampBoundMul` (F2b). On the finite intersection `U = ⋂ U_{k_i}` of the neighbourhoods,
   `A = ∑ χ_i A` gives the bound with constant `∑ |C_i| C_mul,i`.
2. (`localization`) Cover the compact space `T` by finitely many of these neighbourhoods and add the constants.
Linearity of the Bochner integral needs integrability of `e^{imQ_τ} A`; if it fails, the integral is `0` and the
bound is trivial (all constants are nonnegative). No regularity of `Q` is used.
-/

namespace OscInt.StationaryPhase

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint

namespace LocalizeAux

/-- The bound `M` in an amplitude bound is nonnegative. -/
theorem ampBound_nonneg {n : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M) :
    0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0 (Nat.zero_le _) 0)

/-- Amplitude bounds are monotone in the support set. -/
theorem ampBound_mono {n : ℕ} {K K' : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M)
    (hK : K ⊆ K') : AmpBound n K' A M :=
  ⟨h.1, h.2.1.trans hK, h.2.2⟩

/-- A partition of unity on `K` decomposes any `A` with `tsupport A ⊆ K`. -/
theorem eq_sum_mul_of_partition {ι : Type*} [Fintype ι] {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ}
    (χ : ι → ℝ × ℝ → ℝ) (hsum : ∀ k ∈ K, ∑ i, χ i k = 1) (hA : tsupport A ⊆ K) (k : ℝ × ℝ) :
    A k = ∑ i, (χ i k : ℂ) * A k := by
  by_cases hk : k ∈ K
  · rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum k hk, Complex.ofReal_one, one_mul]
  · have : A k = 0 := image_eq_zero_of_notMem_tsupport (fun h => hk (hA h))
    simp [this]

/-- Oscillatory integrals split along a partition of unity (integrable case). -/
theorem oscInt2_eq_sum_of_integrable {ι : Type*} [Fintype ι] {K : Set (ℝ × ℝ)} (Φ : ℝ × ℝ → ℝ)
    {A : ℝ × ℝ → ℂ} (χ : ι → ℝ × ℝ → ℝ) (hχc : ∀ i, Continuous (χ i))
    (hχ01 : ∀ i k, χ i k ∈ Icc (0 : ℝ) 1) (hsum : ∀ k ∈ K, ∑ i, χ i k = 1) (hA : tsupport A ⊆ K)
    (hint : Integrable (fun k => Complex.exp (↑(Φ k) * Complex.I) * A k)) :
    oscInt2 Φ A = ∑ i, oscInt2 Φ (fun k => (χ i k : ℂ) * A k) := by
  have hpiece : ∀ i, Integrable (fun k => Complex.exp (↑(Φ k) * Complex.I) * ((χ i k : ℂ) * A k)) := by
    intro i
    have h := hint.bdd_mul (c := 1) (f := fun k => (χ i k : ℂ))
      (Complex.continuous_ofReal.comp (hχc i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ01 i k).1]; exact (hχ01 i k).2)
    refine h.congr (Filter.Eventually.of_forall fun k => ?_)
    simp only; ring
  unfold oscInt2
  rw [← integral_finsetSum _ (fun i _ => hpiece i)]
  congr 1
  funext k
  conv_lhs => rw [eq_sum_mul_of_partition χ hsum hA k]
  rw [Finset.mul_sum]

/-- Bounds on the pieces of a partition of unity give a bound on the whole oscillatory integral. -/
theorem norm_oscInt2_le_sum {ι : Type*} [Fintype ι] {K : Set (ℝ × ℝ)} (Φ : ℝ × ℝ → ℝ)
    {A : ℝ × ℝ → ℂ} (χ : ι → ℝ × ℝ → ℝ) (hχc : ∀ i, Continuous (χ i))
    (hχ01 : ∀ i k, χ i k ∈ Icc (0 : ℝ) 1) (hsum : ∀ k ∈ K, ∑ i, χ i k = 1) (hA : tsupport A ⊆ K)
    (B : ι → ℝ) (hB0 : ∀ i, 0 ≤ B i) (hB : ∀ i, ‖oscInt2 Φ (fun k => (χ i k : ℂ) * A k)‖ ≤ B i) :
    ‖oscInt2 Φ A‖ ≤ ∑ i, B i := by
  by_cases hint : Integrable (fun k => Complex.exp (↑(Φ k) * Complex.I) * A k)
  · rw [oscInt2_eq_sum_of_integrable Φ χ hχc hχ01 hsum hA hint]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hB i)
  · have : oscInt2 Φ A = 0 := integral_undef hint
    rw [this, norm_zero]
    exact Finset.sum_nonneg fun i _ => hB0 i

/-- Uniformity over `K` near a fixed `τ₀`: the local bounds at the points `(τ₀, k)`, `k ∈ K`, give a bound with
one constant for all `τ` in a neighbourhood of `τ₀` and all amplitudes supported in `K`. -/
theorem uniform_near {T : Type} [TopologicalSpace T] (Q : T → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (r : ℝ)
    (hK : IsCompact K) (τ₀ : T) (h : ∀ k ∈ K, LocalBound Q τ₀ k r) :
    ∃ U ∈ nhds τ₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (τ : T) (m : ℝ),
      τ ∈ U → AmpBound 2 K A M → 1 ≤ m → ‖oscInt2 (fun k => m * Q τ k) A‖ ≤ C * M * m ^ (-r) := by
  choose U hU δ hδ C hC using fun k : K => h k.1 k.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => Metric.ball k.1 (δ k))
    (fun _ => Metric.isOpen_ball) (fun k hk => mem_iUnion.mpr ⟨⟨k, hk⟩, Metric.mem_ball_self (hδ _)⟩)
  have hcov : K ⊆ ⋃ i : t, Metric.ball i.1.1 (δ i.1) := by
    intro k hk
    obtain ⟨i, hi, hki⟩ := mem_iUnion₂.mp (ht hk)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hki⟩
  obtain ⟨χ, hχ, hcs, hsub, hχ01, hsum⟩ := PartitionAux.exists_smooth_partition_compact K
    (fun i : t => Metric.ball i.1.1 (δ i.1)) hK (fun _ => Metric.isOpen_ball) hcov
  choose Cm hCm0 hCm using fun i : t => ampBoundMul 2 (χ i) (hχ i) (hcs i)
  refine ⟨⋂ i : t, U i.1, (Filter.iInter_mem).mpr fun i => hU i.1,
    ∑ i : t, |C i.1| * Cm i, Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hCm0 i),
    fun A M τ m hτ hA hm => ?_⟩
  have hM := ampBound_nonneg hA
  have hmr : 0 ≤ m ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hm) _
  have hτi : ∀ i : t, τ ∈ U i.1 := fun i => mem_iInter.mp hτ i
  rw [Finset.sum_mul, Finset.sum_mul]
  refine norm_oscInt2_le_sum _ χ (fun i => (hχ i).continuous) hχ01 hsum hA.2.1 _
    (fun i => mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (hCm0 i)) hM) hmr) fun i => ?_
  have hAi : AmpBound 2 (Metric.closedBall i.1.1 (δ i.1)) (fun k => (χ i k : ℂ) * A k) (Cm i * M) :=
    ampBound_mono (hCm i K A M hA)
      (inter_subset_right.trans ((hsub i).trans Metric.ball_subset_closedBall))
  calc ‖oscInt2 (fun k => m * Q τ k) (fun k => (χ i k : ℂ) * A k)‖
      ≤ C i.1 * (Cm i * M) * m ^ (-r) := hC i.1 _ _ τ m (hτi i) hAi hm
    _ ≤ |C i.1| * (Cm i * M) * m ^ (-r) := by
        gcongr
        · exact mul_nonneg (hCm0 i) hM
        · exact le_abs_self _
    _ = |C i.1| * Cm i * M * m ^ (-r) := by ring

end LocalizeAux

/-- **R2** Localisation: local bounds at every point of `T × K` (`T` compact, `K` compact) give a global
bound, uniform in `τ ∈ T`. -/
theorem localization : OscInt.Blueprint.LocalizationFacts := by
  intro T _ _ Q K r hK h
  choose U hU C hC0 hC using fun τ₀ : T => LocalizeAux.uniform_near Q K r hK τ₀ (h τ₀)
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := T)).elim_nhds_subcover U (fun τ _ => hU τ)
  refine ⟨∑ σ ∈ t, C σ, fun A M τ m hA hm => ?_⟩
  obtain ⟨σ, hσ, hτ⟩ := mem_iUnion₂.mp (ht (mem_univ τ))
  have hM := LocalizeAux.ampBound_nonneg hA
  have hmr : 0 ≤ m ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hm) _
  calc ‖oscInt2 (fun k => m * Q τ k) A‖ ≤ C σ * M * m ^ (-r) := hC σ A M τ m hτ hA hm
    _ ≤ (∑ σ ∈ t, C σ) * M * m ^ (-r) := by
        gcongr
        exact Finset.single_le_sum (fun σ _ => hC0 σ) hσ

end OscInt.StationaryPhase
