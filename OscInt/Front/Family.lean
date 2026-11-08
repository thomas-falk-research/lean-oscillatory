import OscInt.StationaryPhase.Final
import OscInt.Statements.Family

/-!
# Front-end batch 3, R1: S2.2F and S3c by re-assembly of the proved parts of S2.2 and S3

Statements: `OscInt/Statements/Family.lean` (stamp `stamps/20261108T002603Z-9d03130c8f3a`, pre-proof FAITHFUL ×2,
reviews stamped `stamps/20261108T010546Z-7bb457958327`). Route: `docs/proof-API3.md`, R1. The proofs copy
`OscInt.StationaryPhase.stationaryPhase_of` and `fold_of` with the parameter space `Λ × K'` and use the hypothesis
only at critical points.
-/

namespace OscInt.API

open OscInt.Statements OscInt.StationaryPhase

/-- **S2.2F** Nondegenerate stationary phase, uniform over a compact family. -/
theorem stationaryPhaseFamily : StationaryPhaseFamilyStatement := by
  intro Λ _ _ Ψ K K' hΨ hK hK' hcrit
  have := compactSpace_prod_subtype Λ hK'
  let Q : Λ × K' → ℝ × ℝ → ℝ := fun q k => Ψ q.1 k + lin q.2.1 k
  have hQ : FamilyCk 4 Q := familyAddLinear Λ 4 Ψ K' hΨ
  have h2 : ∀ σ, ContDiff ℝ 2 (Ψ σ) := fun σ => (hΨ.1 σ).of_le (by norm_num)
  obtain ⟨C, hCb⟩ := localization (Λ × K') Q K 1 hK fun q k hk => by
    by_cases hcr : IsCritical (Q q) 0 k
    · refine (localCrit_of normalForm normalizedData coreEstimate _ Q q k hQ hcr).1 ?_
      have hc := (isCritical_add_lin ((h2 q.1).differentiable (by norm_num)) q.2.1 k).mp hcr
      simpa [Q, hessDet_add_lin (h2 q.1) q.2.1] using hcrit q.1 q.2.1 q.2.2 k hk hc
    · exact localNonCrit _ Q q k (familyCk_of_le (by norm_num) hQ) hcr
  refine ⟨C, fun A M σ p m hA hp hm => ?_⟩
  have := hCb A M (σ, ⟨p, hp⟩) m hA hm
  rw [Real.rpow_neg_one] at this
  simpa [Q, div_eq_mul_inv] using this

/-- **S3c** Uniform fold estimate with the fold condition only at critical points. -/
theorem foldCrit : FoldCritStatement := by
  intro Λ _ _ Ψ K K' hΨ hK hK' hfold
  have := compactSpace_prod_subtype Λ hK'
  let Q : Λ × K' → ℝ × ℝ → ℝ := fun q k => Ψ q.1 k + lin q.2.1 k
  have hQ : FamilyCk 4 Q := familyAddLinear Λ 4 Ψ K' hΨ
  have h2 : ∀ σ, ContDiff ℝ 2 (Ψ σ) := fun σ => (hΨ.1 σ).of_le (by norm_num)
  obtain ⟨C, hCb⟩ := localization (Λ × K') Q K (5 / 6) hK fun q k hk => by
    by_cases hcr : IsCritical (Q q) 0 k
    · have hc := (isCritical_add_lin ((h2 q.1).differentiable (by norm_num)) q.2.1 k).mp hcr
      exact (localCrit_of normalForm normalizedData coreEstimate _ Q q k hQ hcr).2
        ((foldOrNondeg_add_lin (h2 q.1) q.2.1 k).mpr (hfold q.1 q.2.1 q.2.2 k hk hc))
    · exact LocalBound.of_one (by norm_num) (localNonCrit _ Q q k (familyCk_of_le (by norm_num) hQ) hcr)
  refine ⟨C, fun A M σ p m hA hp hm => ?_⟩
  have := hCb A M (σ, ⟨p, hp⟩) m hA hm
  simpa [Q, show (-(5 : ℝ) / 6) = -(5 / 6) by ring] using this

end OscInt.API
