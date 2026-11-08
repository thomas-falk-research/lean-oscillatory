import OscInt

/-! Non-vacuity and plant-falsity checks for the API3 sanity data, written by the blind post-proof referee post-A in its
scratch during its review of 11a9ecf (`review/2026-11-08-API3-post-proof-A.md`) and added here unchanged except for
this header and the removal of its `#print axioms` lines. It uses only proved theorems; it complements the conditional
sanity theorems of `OscInt/Front/FamilySanity.lean` by proving that the planted hypotheses are false on the data and
that critical points exist where the docstrings say so. -/

open OscInt.Statements OscInt.API OscInt.API.FamilySanity OscInt.API.ConvertAux

-- 0. The sanity theorems instantiated with the proved theorems (not only with the statements as hypotheses).
example := foldCrit_fold_bite foldCrit
example := stationaryPhaseFamily_sign_bite familyCk_of_uncurry stationaryPhaseFamily
example := foldCrit_sign_bite familyCk_of_uncurry foldCrit
example := stationaryPhaseOn_kink stationaryPhaseOn
example := foldOn_kink foldOn

-- 1. Bite 1 (x³ + y³, K = closedBall 0 2, K' = {(0, -3)}): a critical point exists in K, it is degenerate
--    (so S2.2/S2.2F do not apply), and 0 ∈ K is not fold-or-nondegenerate (stamped file; so S3 does not apply).
theorem cubes_crit_exists : IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (0, -3) (0, 1) ∧
    ((0 : ℝ), (1 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ) 2 ∧
    hessDet (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [IsCritical, sanity_fd_cubes]; norm_num
  · simp [Metric.mem_closedBall, Prod.norm_def]
  · simp [hessDet, sanity_dd_cubes]

-- S2.2-type hypothesis fails on bite 1 (so S2.2F does not give this bound):
theorem cubes_not_nondeg_at_crit : ¬ (∀ p ∈ ({((0 : ℝ), (-3 : ℝ))} : Set (ℝ × ℝ)),
    ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
      IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) p k → hessDet (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) k ≠ 0) :=
  fun h => h _ rfl _ cubes_crit_exists.2.1 cubes_crit_exists.1 cubes_crit_exists.2.2

-- S3-type hypothesis fails on bite 1:
theorem cubes_not_fold_everywhere : ¬ (∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
    FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) k) :=
  fun h => sanity_FoldCrit_bite.2.2.2.2 (h 0 (Metric.mem_closedBall_self (by norm_num)))

-- Plant p ↦ 0 is false on bite 1 (proved, not only "the proof script breaks"):
theorem cubes_zero_plant_false : ¬ (∀ p ∈ ({((0 : ℝ), (-3 : ℝ))} : Set (ℝ × ℝ)),
    ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
      IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 k → FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) k) :=
  fun h => sanity_FoldCrit_bite.2.2.2.2 (h _ rfl 0 (Metric.mem_closedBall_self (by norm_num))
    (by simp only [IsCritical, sanity_fd_cubes]; norm_num))

-- 2. Bite 2 (sign family, σ ∈ [1, 2], K' = {(4, 0)}): every member has a critical point in K (non-vacuous for the
--    infinite family), and the plant p ↦ -p is false (σ = 1, k = 0 critical with hessDet = 0).
theorem sign_crit_exists (σ : Set.Icc (1 : ℝ) 2) :
    ∃ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2, IsCritical (signFamily σ) (4, 0) k := by
  have hσ : (1 : ℝ) ≤ σ := σ.2.1
  have hσ0 : (0 : ℝ) < σ := by linarith
  set t : ℝ := -(1 + 1 / (σ : ℝ)) with ht
  have h1 : (σ : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hσ
  have h2 : 0 < (σ : ℝ)⁻¹ := by positivity
  have hmem : t ∈ Set.Icc ((-2 : ℝ) ^ 3) ((0 : ℝ) ^ 3) := by
    rw [ht]; constructor <;> norm_num <;> linarith
  obtain ⟨x, hx, hx3⟩ := intermediate_value_Icc (show (-2 : ℝ) ≤ 0 by norm_num)
    ((continuous_pow 3).continuousOn) hmem
  refine ⟨(x, 0), ?_, ?_, ?_⟩
  · simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, norm_zero]
    refine max_le ?_ (by norm_num)
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  · rw [signFamily_fd]; simp only at hx3 ⊢
    have : (σ : ℝ) * (4 * x ^ 3 + 4) = -4 := by
      rw [hx3, ht]; field_simp; ring
    linarith
  · rw [signFamily_fd]; simp

theorem sign_negp_plant_false : ¬ (∀ σ : Set.Icc (1 : ℝ) 2, ∀ p ∈ ({((4 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)),
    ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2, IsCritical (signFamily σ) (-p) k → hessDet (signFamily σ) k ≠ 0) := by
  intro h
  have := h ⟨1, by norm_num, by norm_num⟩ (4, 0) rfl 0 (Metric.mem_closedBall_self (by norm_num))
    (by simp only [IsCritical, signFamily_fd]; norm_num)
  simp [signFamily_hessDet] at this

-- 3. Bite 3 (kink phase, U = {k₁ > -3}, K = closedBall 0 2, K' = {L₀}): a critical point of Ψ + L₀ exists in K,
--    and the plant + L ↦ - L is false (k = 0 critical for Ψ - L₀ with det = 0).
theorem kink_crit_exists : ∃ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2, fderiv ℝ kinkPhase k + L₀ = 0 := by
  have hmem : (-2 : ℝ) ∈ Set.Icc ((-2 : ℝ) ^ 3) ((0 : ℝ) ^ 3) := by norm_num
  obtain ⟨x, hx, hx3⟩ := intermediate_value_Icc (show (-2 : ℝ) ≤ 0 by norm_num)
    ((continuous_pow 3).continuousOn) hmem
  have hk : ((x, (0 : ℝ)) : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 2 := by
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, norm_zero]
    refine max_le ?_ (by norm_num)
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  refine ⟨(x, 0), hk, ?_⟩
  rw [(kinkPhase_eventuallyEq _ (closedBall_subset_kinkU hk)).fderiv_eq, functional_eq_zero_iff]
  simp only at hx3
  simp only [add_apply, signFamily_fd, L₀, smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul]
  constructor <;> norm_num [hx3]

theorem kink_negL_plant_false : ¬ (∀ L ∈ ({L₀} : Set ((ℝ × ℝ) →L[ℝ] ℝ)), ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
    fderiv ℝ kinkPhase k - L = 0 → (hessianMatrix kinkPhase k).det ≠ 0) := by
  intro h
  have h0U : (0 : ℝ × ℝ) ∈ kinkU := closedBall_subset_kinkU (Metric.mem_closedBall_self (by norm_num))
  have hP : ContDiffAt ℝ 2 (signFamily 1) 0 := by rw [signFamily_eq]; fun_prop
  apply h L₀ rfl 0 (Metric.mem_closedBall_self (by norm_num))
  · rw [(kinkPhase_eventuallyEq _ h0U).fderiv_eq, functional_eq_zero_iff]
    simp only [sub_apply, signFamily_fd, L₀, smul_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    norm_num
  · rw [kink_hessianMatrix 0 h0U, ← hessDet_eq_det _ _ hP, signFamily_hessDet]; simp

-- 4. Family-local form FE-S2.2L / FE-S3L on a family singular outside U, with S = [1, 2] ⊊ V = (0, 3), E = ℝ.
noncomputable def kinkFam (σ : ℝ) (k : ℝ × ℝ) : ℝ := σ * (k.1 ^ 4 + 4 * |k.1 + 3| - 12) + k.2 ^ 2

theorem kinkFam_eq_on (σ : ℝ) (k : ℝ × ℝ) (hk : k ∈ kinkU) : kinkFam σ k = signFamily σ k := by
  have : 0 < k.1 + 3 := by have h3 : -3 < k.1 := hk; linarith
  simp only [kinkFam, signFamily, abs_of_pos this]; ring

theorem kinkFam_contDiffOn :
    ContDiffOn ℝ 4 (Function.uncurry kinkFam) (Set.Ioo (0 : ℝ) 3 ×ˢ kinkU) := by
  have : ContDiff ℝ 4 (Function.uncurry signFamily) := signFamily_uncurry_contDiff
  exact this.contDiffOn.congr fun q hq => kinkFam_eq_on q.1 q.2 hq.2

theorem kinkFam_not_C1 : ¬ ContDiff ℝ 1 (kinkFam 1) := by
  have : kinkFam 1 = kinkPhase := by funext k; simp only [kinkFam, kinkPhase]; ring
  rw [this]; exact kinkPhase_not_contDiff

theorem kinkFam_det_ne (σ : ℝ) (hσ : σ ∈ Set.Icc (1 : ℝ) 2) (k : ℝ × ℝ) (hk : k ∈ kinkU)
    (hc : fderiv ℝ (kinkFam σ) k + L₀ = 0) : (hessianMatrix (kinkFam σ) k).det ≠ 0 := by
  have hev : kinkFam σ =ᶠ[nhds k] signFamily σ :=
    Filter.eventually_of_mem (kinkU_isOpen.mem_nhds hk) (kinkFam_eq_on σ)
  rw [hev.fderiv_eq, functional_eq_zero_iff] at hc
  obtain ⟨h1, -⟩ := hc
  simp only [add_apply, signFamily_fd, L₀, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul] at h1
  have hσ0 : (0 : ℝ) < σ := by linarith [hσ.1]
  have hx : k.1 ≠ 0 := by intro h0; rw [h0] at h1; norm_num at h1; linarith
  have hP : ContDiffAt ℝ 2 (signFamily σ) k := by rw [signFamily_eq]; fun_prop
  have hH : hessianMatrix (kinkFam σ) k = hessianMatrix (signFamily σ) k := by
    simp only [hessianMatrix, (hev.iteratedFDeriv ℝ 2).eq_of_nhds]
  rw [hH, ← hessDet_eq_det _ _ hP, signFamily_hessDet]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hσ0.ne') (pow_ne_zero 2 hx)

theorem stationaryPhaseLocal_kinkFam : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M σ m : ℝ), σ ∈ Set.Icc (1 : ℝ) 2 →
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkFam σ k + L₀ k)) * Complex.I) * A k‖ ≤ C * M / m := by
  obtain ⟨C, hC⟩ := stationaryPhaseLocal ℝ kinkFam (Set.Icc 1 2) (Set.Ioo 0 3) (Metric.closedBall 0 2) kinkU {L₀}
    isCompact_Icc isOpen_Ioo (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) (isCompact_closedBall _ _)
    kinkU_isOpen closedBall_subset_kinkU isCompact_singleton kinkFam_contDiffOn
    (fun σ hσ L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      exact kinkFam_det_ne σ hσ k (closedBall_subset_kinkU hk) hc)
  exact ⟨C, fun A M σ m hσ hA hs hM hm => hC A M σ L₀ m hσ hA hs hM (Set.mem_singleton _) hm⟩


-- 5. FE-S3l in Mathlib idiom on the critical-points-only fold (x³ + y³, K = closedBall 0 2, K' = {-3 • snd}):
--    the hypothesis is discharged through the fold (rank-one) branch of FoldOrNondegMatrix via C7.
noncomputable def Lm3 : (ℝ × ℝ) →L[ℝ] ℝ := (-3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem foldOn_cubes : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * ((k.1 ^ 3 + k.2 ^ 3) + Lm3 k)) * Complex.I) * A k‖ ≤
      C * M * m ^ (-(5 : ℝ) / 6) := by
  have hv : vecOf Lm3 = (0, -3) := by simp [vecOf, Lm3]
  obtain ⟨C, hC⟩ := foldOn (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (Metric.closedBall 0 2) Set.univ {Lm3}
    (isCompact_closedBall _ _) isOpen_univ (Set.subset_univ _) isCompact_singleton
    (by fun_prop : ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3)).contDiffOn
    (fun L hL k hk hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL
      have hcr : IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (0, -3) k := by
        rw [← hv]; exact (isCritical_iff Lm3 k).2 hc
      have hf := cubes_fold_at_crit (0, -3) rfl k hk hcr
      exact ((foldOrNondeg_iff _ k (by fun_prop)).1).1 hf)
  exact ⟨C, fun A M m hA hs hM hm => hC A M Lm3 m hA hs hM (Set.mem_singleton _) hm⟩

