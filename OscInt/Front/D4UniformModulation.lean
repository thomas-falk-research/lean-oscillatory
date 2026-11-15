/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4Uniform
import OscInt.Front.Core

/-! # Batch D4U, part P-mod (route `docs/proof-D4U.md`) -/

namespace OscInt.D4UniformAux.ModAux

open Filter Topology OscInt.Statements OscInt.Blueprint.D4Uniform

/-- The slice identity of `OscInt.API.FamilyAux.iteratedFDeriv_slice`, for a general normed codomain. -/
theorem iteratedFDeriv_slice {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {f : E × (ℝ × ℝ) → G} (hf : ContDiff ℝ n f) (σ : E) (k : ℝ × ℝ) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun k' => f (σ, k')) k =
      (iteratedFDeriv ℝ j f (σ, k)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ E (ℝ × ℝ)) := by
  have hg : ContDiff ℝ n (fun z : E × (ℝ × ℝ) => f ((σ, 0) + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun k' : ℝ × ℝ => f (σ, k')) =
      (fun z : E × (ℝ × ℝ) => f ((σ, 0) + z)) ∘ ContinuousLinearMap.inr ℝ E (ℝ × ℝ) := by
    funext k'; simp
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast hj),
    iteratedFDeriv_comp_add_left]
  simp

/-- The joint modulated amplitude `F (y, κ) = e^{i lin y κ} A κ`. -/
noncomputable def modF (A : ℝ × ℝ → ℂ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Complex.exp (↑(lin q.1 q.2) * Complex.I) * A q.2

theorem contDiff_modF {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 2 A) : ContDiff ℝ 2 (modF A) := by
  have hlin : ContDiff ℝ 2 (fun q : (ℝ × ℝ) × (ℝ × ℝ) => lin q.1 q.2) := by
    unfold lin; fun_prop
  have hc : ContDiff ℝ 2 (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((lin q.1 q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hlin
  exact (Complex.contDiff_exp.comp (hc.mul contDiff_const)).mul (hA.comp contDiff_snd)

theorem contDiff_slice {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 2 A) (y : ℝ × ℝ) :
    ContDiff ℝ 2 (fun κ => modF A (y, κ)) :=
  (contDiff_modF hA).comp (contDiff_const.prodMk contDiff_id)

theorem tsupport_slice (A : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    tsupport (fun κ => modF A (y, κ)) ⊆ tsupport A :=
  tsupport_mul_subset_right

/-- The slice derivatives are jointly continuous. -/
theorem continuous_slice {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 2 A) {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => iteratedFDeriv ℝ j (fun κ => modF A (q.1, κ)) q.2) := by
  have hF := contDiff_modF hA
  have hc : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)) (iteratedFDeriv ℝ j (modF A) q) :=
    (ContinuousLinearMap.continuous _).comp (hF.continuous_iteratedFDeriv (by exact_mod_cast hj))
  refine hc.congr fun q => ?_
  rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply, ← iteratedFDeriv_slice hF q.1 q.2 hj]

/-- One order: a uniform modulus in `y` for the `j`-th slice derivative. -/
theorem exists_rho {δ R : ℝ} {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 2 A) (hsupp : tsupport A ⊆ Metric.closedBall 0 δ)
    {j : ℕ} (hj : j ≤ 2) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ y ∈ Metric.closedBall (0 : ℝ × ℝ) R, ∀ z ∈ Metric.closedBall (0 : ℝ × ℝ) R, dist y z < ρ →
      ∀ κ, ‖iteratedFDeriv ℝ j (fun κ => modF A (y, κ)) κ - iteratedFDeriv ℝ j (fun κ => modF A (z, κ)) κ‖ ≤ η := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) R ×ˢ Metric.closedBall (0 : ℝ × ℝ) δ) :=
    (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 δ)
  have hu := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (continuous_slice hA hj).continuousOn) η hη
  obtain ⟨ρ, hρ, hρu⟩ := hu
  refine ⟨ρ, hρ, fun y hy z hz hyz κ => ?_⟩
  by_cases hκ : κ ∈ Metric.closedBall (0 : ℝ × ℝ) δ
  · have := hρu (y, κ) ⟨hy, hκ⟩ (z, κ) ⟨hz, hκ⟩ (by simpa [Prod.dist_eq] using hyz)
    rw [← dist_eq_norm]; exact this.le
  · have h0 : ∀ w : ℝ × ℝ, iteratedFDeriv ℝ j (fun κ => modF A (w, κ)) κ = 0 := fun w =>
      image_eq_zero_of_notMem_tsupport fun h =>
        hκ (hsupp (tsupport_slice A w (tsupport_iteratedFDeriv_subset j h)))
    rw [h0 y, h0 z, sub_zero, norm_zero]; exact hη.le

end OscInt.D4UniformAux.ModAux

namespace OscInt.D4UniformAux

open Filter Topology OscInt.Statements OscInt.Blueprint.D4Uniform ModAux

/-- **P-mod** The modulation family is C²-totally bounded on `B̄(0, δ)`. -/
theorem modulation : ModulationFacts := by
  intro δ A M R hδ hA
  refine ⟨?_, fun η hη => ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact OscInt.API.ampBoundOfContDiff 2 _ _ (isCompact_closedBall 0 δ) (contDiff_slice hA.1 y)
      ((tsupport_slice A y).trans hA.2.1)
  obtain ⟨ρ₀, hρ₀, h₀⟩ := exists_rho (R := R) hA.1 hA.2.1 (j := 0) (by norm_num) hη
  obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_rho (R := R) hA.1 hA.2.1 (j := 1) (by norm_num) hη
  obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_rho (R := R) hA.1 hA.2.1 (j := 2) (by norm_num) hη
  set ρ := min ρ₀ (min ρ₁ ρ₂)
  have hρ : 0 < ρ := lt_min hρ₀ (lt_min hρ₁ hρ₂)
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : ℝ × ℝ) R) hρ
  refine ⟨(fun y => fun κ => modF A (y, κ)) '' t, htf.image _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, mem_closedBall_zero_iff.mp (hts hy), rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Metric.closedBall (0 : ℝ × ℝ) R := mem_closedBall_zero_iff.mpr hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcov hy')
  have hd : dist y z < ρ := Metric.mem_ball.mp hyz
  refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
  have hcy := contDiff_slice hA.1 y
  have hcz := contDiff_slice hA.1 z
  refine ⟨hcy.sub hcz, ?_, fun j hj κ => ?_⟩
  · refine (closure_mono (Function.support_sub _ _)).trans ?_
    rw [closure_union]
    exact Set.union_subset ((tsupport_slice A y).trans hA.2.1) ((tsupport_slice A z).trans hA.2.1)
  change ‖iteratedFDeriv ℝ j ((fun κ => modF A (y, κ)) - fun κ => modF A (z, κ)) κ‖ ≤ η
  rw [iteratedFDeriv_sub_apply (hcy.of_le (by exact_mod_cast hj)).contDiffAt
    (hcz.of_le (by exact_mod_cast hj)).contDiffAt]
  interval_cases j
  · exact h₀ y hy' z (hts hz) (hd.trans_le (min_le_left _ _)) κ
  · exact h₁ y hy' z (hts hz) (hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))) κ
  · exact h₂ y hy' z (hts hz) (hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))) κ

end OscInt.D4UniformAux
