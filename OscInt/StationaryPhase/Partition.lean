import Blueprint.StationaryPhase
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# F2a: smooth partitions of unity on `ℝ × ℝ`

We prove `OscInt.Blueprint.PartitionFacts`: a finite open cover `U` of a compact set `K ⊆ ℝ²` admits smooth
(`C^∞`) functions `χ i` with values in `[0, 1]`, compact support, `tsupport (χ i) ⊆ U i`, and `∑ χ i = 1` on `K`.

Route: first a general lemma for any finite-dimensional real normed space (`exists_smooth_partition_compact`):
shrink each `U i` to `U i ∩ ball 0 R` with `K ⊆ ball 0 R`, apply Mathlib's manifold partition of unity
`SmoothPartitionOfUnity.exists_isSubordinate` with the model `𝓘(ℝ, E)`, and convert with
`contMDiff_iff_contDiff`. Supports lie in `closedBall 0 R`, hence are compact.

The auxiliary lemma `PartitionAux.contDiff_omega_hasCompactSupport_eq_zero` records a trap: in this Mathlib
`ContDiff ℝ ⊤` means `ContDiff ℝ ω` (analytic), and a compactly supported analytic function on `ℝ × ℝ` is zero,
so the statement must use `ContDiff ℝ ∞`.
-/

namespace OscInt.StationaryPhase

open Set Filter Topology
open scoped ContDiff Manifold

namespace PartitionAux

/-- A compactly supported analytic function on `ℝ × ℝ` (`ContDiff ℝ ω`, which is what `ContDiff ℝ ⊤` means in
this Mathlib) vanishes identically, by the identity principle. -/
theorem contDiff_omega_hasCompactSupport_eq_zero (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ω f)
    (hc : HasCompactSupport f) : f = 0 := by
  have hne : (tsupport f)ᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact (inferInstance : NoncompactSpace (ℝ × ℝ)).noncompact_univ (h ▸ hc.isCompact)
  obtain ⟨z, hz⟩ := hne
  have hz' : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have := (hf.analyticOnNhd (s := univ)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) hz'
  funext x
  exact this (mem_univ x)

/-- Smooth partitions of unity subordinate to a finite open cover of a compact set in a finite-dimensional
real normed space, with compactly supported members. -/
theorem exists_smooth_partition_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (K : Set E) (U : ι → Set E)
    (hK : IsCompact K) (hU : ∀ i, IsOpen (U i)) (hKU : K ⊆ ⋃ i, U i) :
    ∃ χ : ι → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧ (∀ i, tsupport (χ i) ⊆ U i) ∧
        (∀ i x, χ i x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ K, ∑ i, χ i x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E)
  have hcov : K ⊆ ⋃ i, U i ∩ Metric.ball 0 R := by
    intro k hk
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hKU hk)
    exact mem_iUnion.mpr ⟨i, hi, hR hk⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
    (fun i => U i ∩ Metric.ball 0 R) (fun i => (hU i).inter Metric.isOpen_ball) hcov
  refine ⟨fun i => f i, fun i => contMDiff_iff_contDiff.mp (f i).contMDiff, fun i => ?_,
    fun i => (hf i).trans inter_subset_left, fun i k => ⟨f.nonneg i k, f.le_one i k⟩,
    fun k hk => ?_⟩
  · exact (isCompact_closedBall (0 : E) R).of_isClosed_subset
      (isClosed_tsupport _) ((hf i).trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  · have := f.sum_eq_one hk
    rwa [finsum_eq_sum_of_fintype] at this

end PartitionAux

/-- **F2a** Smooth partitions of unity on `ℝ × ℝ` subordinate to a finite open cover of a compact set. -/
theorem partition : OscInt.Blueprint.PartitionFacts :=
  fun _ K U hK hU hKU => PartitionAux.exists_smooth_partition_compact K U hK hU hKU


end OscInt.StationaryPhase
