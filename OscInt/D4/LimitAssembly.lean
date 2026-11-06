import Blueprint.D4LimitS42
import OscInt.D4.Assembly

/-!
# S4.2 assembly against the blueprint interfaces

`D4LimitStatement` from the S4.1′ parts (D2–D7), S3 (`OscInt.fold`), S2.1 (`OscInt.nonStationary`), the S4.3
statement, and the new parts E1–E3 (`Blueprint/D4LimitS42.lean`). Route: `docs/proof-S42.md`.

* `evenCutoff`: a D7 cut-off made even, `(χ + χ(−·))/2`.
* `exists_piece_bound`: the dyadic piece bound of the S4.1′ assembly with linear term `0` (the same argument as in
  `d4BoundNe_of`, stated as a lemma; that proof is not refactored, to keep the reviewed file unchanged).
* `d4Limit_of`: Steps 1–5 of the route.
-/

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase
open scoped ContDiff

/-- An even cut-off with the D7 properties. -/
theorem exists_even_cutoff (hCut : CutoffFacts) :
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧ (∀ z, ‖z‖ ≤ 1 → χ z = 1) ∧
      tsupport χ ⊆ Metric.closedBall 0 2 ∧ (∀ z, χ ((2 : ℝ) • z) ≤ χ z) ∧ ∀ z, χ (-z) = χ z := by
  obtain ⟨χ, hχ, hχ01, hχ1, hχs, hχmono⟩ := hCut
  refine ⟨fun z => (χ z + χ (-z)) / 2, ?_, fun z => ?_, fun z hz => ?_, ?_, fun z => ?_, fun z => ?_⟩
  · exact (hχ.add (hχ.comp contDiff_neg)).div_const 2
  · exact ⟨by linarith [(hχ01 z).1, (hχ01 (-z)).1], by linarith [(hχ01 z).2, (hχ01 (-z)).2]⟩
  · simp only [hχ1 z hz, hχ1 (-z) (by rwa [norm_neg])]; norm_num
  · refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
    by_contra hout
    have h1 : χ z = 0 := image_eq_zero_of_notMem_tsupport fun hm => hout (hχs hm)
    have h2 : χ (-z) = 0 := image_eq_zero_of_notMem_tsupport fun hm => hout (by
      have := hχs hm; rwa [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff] at this)
    exact hz (by simp [h1, h2])
  · have := hχmono (-z); rw [smul_neg] at this; linarith [hχmono z]
  · simp only [neg_neg, add_comm]

/-- The dyadic piece bound (route Step 0), for a normalised phase with `disc ≠ 0` and a given D7 cut-off. -/
theorem exists_piece_bound (hR : RescaleFamilyFacts) (hCG : CubicGaugeFacts) (hGF : GaugeFoldFacts)
    (hGO : GaugeOpenFacts)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 4 φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    (hdd : ∀ v w, dd φ 0 v w = 0) (hdisc : disc (cubicCoeffs φ) ≠ 0)
    (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1)
    (hχs : tsupport χ ⊆ Metric.closedBall 0 2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ × ℝ → ℂ) (M : ℝ),
      AmpBound 2 (Metric.closedBall 0 ε₀) A M → ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 1 ≤ t * ε ^ 3 →
        ‖oscInt2 (fun κ => t * φ κ) (fun κ => ((χ (ε⁻¹ • κ) - χ ((2 : ℝ) • (ε⁻¹ • κ)) : ℝ) : ℂ) * A κ)‖ ≤
          ε ^ 2 * (K * M * (t * ε ^ 3) ^ (-(5 : ℝ) / 6)) := by
  have hfam : FamilyCk 4 (rescale φ) := hR φ hφ hφ0 hφ1 hdd
  have h0 : ∀ z ∈ annulus, 0 < foldGauge (rescale φ 0) z ∧ 0 < hessNorm (rescale φ 0) z := by
    intro z hz
    have : rescale φ 0 = cubicPoly (cubicCoeffs φ) := by funext z; simp [rescale]
    rw [this]
    exact hCG _ hdisc z (ne_zero_of_mem_annulus hz)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hGO ℝ (rescale φ) 0 annulus (familyCk_of_le (by norm_num) hfam) isCompact_annulus h0)
  set ε₀ : ℝ := min 1 (r / 2) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min one_pos (half_pos hr)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  let Ψ : Icc (0 : ℝ) ε₀ → ℝ × ℝ → ℝ := fun σ => rescale φ σ.1
  have hΨ : FamilyCk 4 Ψ := familyCk_comp Subtype.val continuous_subtype_val hfam
  have hfold : ∀ σ, ∀ z ∈ annulus, FoldOrNondeg (Ψ σ) z := by
    intro σ z hz
    have hσ : dist σ.1 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg σ.2.1]
      exact lt_of_le_of_lt (σ.2.2.trans (min_le_right _ _)) (half_lt_self hr)
    obtain ⟨h1, h2⟩ := hball hσ z hz
    exact hGF _ ((hfam.1 σ.1).of_le (by norm_num)) z h1 h2
  obtain ⟨C₃, hC₃⟩ := OscInt.fold _ Ψ annulus (Metric.closedBall 0 1) hΨ isCompact_annulus
    (isCompact_closedBall 0 1) hfold
  let β : ℝ × ℝ → ℝ := fun z => χ z - χ ((2 : ℝ) • z)
  have hβ : ContDiff ℝ ∞ β := hχ.sub (hχ.comp (contDiff_const_smul 2))
  have hβsupp : tsupport β ⊆ annulus := by
    refine closure_minimal (fun z hz => ?_) isClosed_annulus
    have h2z : ‖(2 : ℝ) • z‖ = 2 * ‖z‖ := by rw [norm_smul, Real.norm_two]
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hb : χ ((2 : ℝ) • z) = 1 := hχ1 _ (by rw [h2z]; linarith)
      have ha : χ z = 1 := hχ1 _ (by linarith)
      exact hz (by simp [β, ha, hb])
    · by_contra hlt
      push Not at hlt
      have hout : ∀ w : ℝ × ℝ, 2 < ‖w‖ → χ w = 0 := fun w hw =>
        image_eq_zero_of_notMem_tsupport fun hm => by
          have := hχs hm; rw [mem_closedBall_zero_iff] at this; linarith
      have ha : χ z = 0 := hout z hlt
      have hb : χ ((2 : ℝ) • z) = 0 := hout _ (by rw [h2z]; linarith)
      exact hz (by simp [β, ha, hb])
  have hβcs : HasCompactSupport β :=
    IsCompact.of_isClosed_subset isCompact_annulus (isClosed_tsupport β) hβsupp
  obtain ⟨Cβ, hCβ0, hCβ⟩ := ampBoundMul 2 β hβ hβcs
  refine ⟨ε₀, hε₀, hε₀1, max C₃ 0 * Cβ, mul_nonneg (le_max_right _ _) hCβ0,
    fun A M hA ε t hε hεε₀ hm => ?_⟩
  have hM : 0 ≤ M := LocalizeAux.ampBound_nonneg hA
  have hε0 : ε ≠ 0 := hε.ne'
  have ht0 : 0 < t := by
    by_contra h; push Not at h
    have : t * ε ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  let σ : Icc (0 : ℝ) ε₀ := ⟨ε, hε.le, hεε₀⟩
  have hphase : (fun κ => t * φ κ) = fun κ => t * φ κ + lin 0 κ := by funext κ; simp [lin]
  have hpe : (fun κ => ((χ (ε⁻¹ • κ) - χ ((2 : ℝ) • (ε⁻¹ • κ)) : ℝ) : ℂ) * A κ) =
      fun κ => (β (ε⁻¹ • κ) : ℂ) * A κ := rfl
  rw [hphase, hpe, piece_eq φ β A t ε 0 ht0.ne' hε]
  set L := smulEquiv ε hε0
  have hA' := ampBoundAffine 2 _ A M 0 L hA
  have hA'' := hCβ _ _ _ hA'
  simp only [zero_add, L, smulEquiv_apply] at hA''
  have hLn : max 1 ‖((smulEquiv ε hε0 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 = 1 := by
    have h1 := norm_smulEquiv_le ε hε0 (by rw [abs_of_pos hε]; exact hεε₀.trans hε₀1)
    rw [max_eq_left h1, one_pow]
  rw [hLn, one_mul] at hA''
  have hAj : AmpBound 2 annulus (fun z => (β z : ℂ) * A (ε • z)) (Cβ * M) :=
    LocalizeAux.ampBound_mono hA'' (inter_subset_right.trans hβsupp)
  have hp0 : ((t * ε ^ 2)⁻¹ • (0 : ℝ × ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by simp
  have h3 := hC₃ _ _ σ _ _ hAj hp0 hm
  refine mul_le_mul_of_nonneg_left (h3.trans ?_) (sq_nonneg ε)
  have hr0 : 0 ≤ (t * ε ^ 3) ^ (-(5 : ℝ) / 6) := Real.rpow_nonneg (by linarith) _
  calc C₃ * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) ≤ max C₃ 0 * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hCβ0 hM)) hr0
    _ = max C₃ 0 * Cβ * M * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) := by ring

/-- `s = t^{-1/3}` satisfies `t s³ = 1` and `t^{2/3} s² = 1`. -/
theorem rpow_third_identities (t : ℝ) (ht : 0 < t) :
    0 < t ^ (-(1 : ℝ) / 3) ∧ t * (t ^ (-(1 : ℝ) / 3)) ^ 3 = 1 ∧ t ^ ((2 : ℝ) / 3) * (t ^ (-(1 : ℝ) / 3)) ^ 2 = 1 := by
  have hs : 0 < t ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  refine ⟨hs, ?_, ?_⟩
  · have : (t ^ (-(1 : ℝ) / 3)) ^ 3 = t⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num [Real.rpow_neg_one]
    rw [this, mul_inv_cancel₀ ht.ne']
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    norm_num

/-- Route Step 3: the inner piece after the substitution `κ = t^{-1/3} w`. -/
theorem inner_eq (φ : ℝ × ℝ → ℝ) (χ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (t R : ℝ) (ht : 0 < t) :
    ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
        oscInt2 (fun κ => t * φ κ) (fun κ => ((χ ((R * t ^ (-(1 : ℝ) / 3))⁻¹ • κ) : ℝ) : ℂ) * A κ) =
      oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3)))
        (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ) * A (t ^ (-(1 : ℝ) / 3) • w)) := by
  obtain ⟨hs, h3, h2⟩ := rpow_third_identities t ht
  set s := t ^ (-(1 : ℝ) / 3) with hs_def
  have hs0 : s ≠ 0 := hs.ne'
  rw [affineChange _ _ 0 (smulEquiv s hs0), det_smulEquiv, ← mul_assoc]
  have hc : ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * ((|s ^ 2| : ℝ) : ℂ) = 1 := by
    rw [abs_of_nonneg (sq_nonneg s), ← Complex.ofReal_mul, h2, Complex.ofReal_one]
  rw [hc, one_mul]
  congr 1
  · funext w
    simp only [zero_add, smulEquiv_apply, rescale, if_neg hs0]
    have ht' : t = (s ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [ht']; field_simp
  · funext w
    simp only [zero_add, smulEquiv_apply, smul_smul]
    congr 3
    field_simp

/-- Route Step 1: the pieces at scale `ρ`; `none` is the inner disc, `some j` the annulus at `2^{j+1} ρ`. -/
noncomputable def piecesAt (χ : ℝ × ℝ → ℝ) (ρ : ℝ) (N : ℕ) (i : Option (Fin N)) (κ : ℝ × ℝ) : ℝ :=
  i.elim (χ (ρ⁻¹ • κ)) (fun j => χ ((2 ^ ((j : ℕ) + 1) * ρ)⁻¹ • κ) -
    χ ((2 : ℝ) • ((2 ^ ((j : ℕ) + 1) * ρ)⁻¹ • κ)))

theorem sum_piecesAt (χ : ℝ × ℝ → ℝ) (hχ1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1) (ρ δ : ℝ) (hρ : 0 < ρ) (N : ℕ)
    (hN : δ ≤ 2 ^ N * ρ) : ∀ κ ∈ Metric.closedBall (0 : ℝ × ℝ) δ, ∑ i, piecesAt χ ρ N i κ = 1 := by
  intro κ hκ
  have hstep : ∀ j : ℕ, (2 : ℝ) • ((2 ^ (j + 1) * ρ)⁻¹ • κ) = (2 ^ j * ρ)⁻¹ • κ := by
    intro j; rw [smul_smul]; congr 1; rw [pow_succ]; field_simp
  rw [Fintype.sum_option]
  simp only [piecesAt, Option.elim]
  rw [Fin.sum_univ_eq_sum_range (fun j => χ ((2 ^ (j + 1) * ρ)⁻¹ • κ) -
    χ ((2 : ℝ) • ((2 ^ (j + 1) * ρ)⁻¹ • κ))) N]
  simp only [hstep]
  rw [Finset.sum_range_sub (fun j => χ ((2 ^ j * ρ)⁻¹ • κ)) N]
  simp only [pow_zero, one_mul]
  rw [add_sub_cancel]
  apply hχ1
  have hpos : 0 < 2 ^ N * ρ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  rw [mem_closedBall_zero_iff] at hκ
  calc (2 ^ N * ρ)⁻¹ * ‖κ‖ ≤ (2 ^ N * ρ)⁻¹ * (2 ^ N * ρ) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **S4.2** from the interfaces (route `docs/proof-S42.md`, Steps 0–5). -/
theorem d4Limit_of (hR : RescaleFamilyFacts) (hCG : CubicGaugeFacts) (hGF : GaugeFoldFacts)
    (hGO : GaugeOpenFacts) (hCut : CutoffFacts)
    (hE1 : CubicCutoffLimitFacts) (hE2 : InnerLimitFacts) (hE3 : DyadicTailFacts)
    (hPos : D4ConstantPosStatement) : D4LimitStatement := by
  intro φ hφ hφ0 hφ1 hdd hdisc
  obtain ⟨χ, hχ, hχ01, hχ1, hχs, hχmono, hχeven⟩ := exists_even_cutoff hCut
  obtain ⟨ε₀, hε₀, hε₀1, K, hK0, hpiece⟩ :=
    exists_piece_bound hR hCG hGF hGO φ hφ hφ0 hφ1 hdd hdisc χ hχ hχ1 hχs
  refine ⟨ε₀ / 2, by positivity, fun A M hA => ?_⟩
  set q := cubicCoeffs φ with hq_def
  set c : ℂ := ((d4Constant q : ℝ) : ℂ) with hc_def
  have hM : 0 ≤ M := LocalizeAux.ampBound_nonneg hA
  have hA' : AmpBound 2 (Metric.closedBall 0 ε₀) A M :=
    LocalizeAux.ampBound_mono hA (Metric.closedBall_subset_closedBall (by linarith))
  have hAc : Continuous A := hA.1.continuous
  have hχc : Continuous χ := hχ.continuous
  have hχcs : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport χ) hχs
  have hL := hE1 q hdisc hPos.1 (hPos.2.2 q hdisc).1 χ hχ hχcs hχeven hχ1
  have hfam : FamilyCk 4 (rescale φ) := hR φ hφ hφ0 hφ1 hdd
  have hcont : Continuous (fun p : ℝ × (ℝ × ℝ) => rescale φ p.1 p.2) := by
    have h := (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) ℝ).continuous.comp (hfam.2 0 (by norm_num))
    refine h.congr fun p => ?_
    simp [iteratedFDeriv_zero_eq_comp]
  have hres0 : rescale φ 0 = cubicForm q := by funext w; simp [rescale, cubicPoly, cubicForm, q]
  rw [Metric.tendsto_atTop]
  intro η hη
  have hev1 : ∀ᶠ R : ℝ in atTop, 3 * (K * M) * R ^ (-(1 : ℝ) / 2) < η / 3 := by
    have h : Tendsto (fun R : ℝ => 3 * (K * M) * R ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2) (by norm_num)).const_mul (3 * (K * M))
      simpa [neg_div] using this
    exact h.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ R : ℝ in atTop,
      ‖oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ)) - c‖ * ‖A 0‖ < η / 3 := by
    have h : Tendsto (fun R : ℝ => ‖oscInt2 (cubicForm q) (fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ)) - c‖ * ‖A 0‖)
        atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hL).mul_const ‖A 0‖
    exact h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R, hR1, hRa, hRb⟩ := ((eventually_ge_atTop (1 : ℝ)).and (hev1.and hev2)).exists
  set B : ℝ × ℝ → ℂ := fun w => ((χ (R⁻¹ • w) : ℝ) : ℂ) with hB_def
  have hBc : Continuous B := by
    simp only [hB_def]; exact Complex.continuous_ofReal.comp (hχc.comp (continuous_const_smul _))
  have hBcs : HasCompactSupport B :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (R * 2)) (isClosed_tsupport _)
      (tsupport_rescale_subset χ 2 R (by linarith) hχs)
  have hin := hE2 (rescale φ) hcont B hBc hBcs A hAc
  rw [hres0] at hin
  have hs : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    simpa [neg_div] using tendsto_rpow_neg_atTop (y := (1 : ℝ) / 3) (by norm_num)
  have hev3 : ∀ᶠ t : ℝ in atTop, ‖oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3)))
      (fun w => B w * A (t ^ (-(1 : ℝ) / 3) • w)) - oscInt2 (cubicForm q) B * A 0‖ < η / 3 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp (hin.comp hs)).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := (hev3.and (eventually_gt_atTop 0)).exists_forall_of_atTop
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hinner, ht0⟩ := hT t ht
  obtain ⟨hs0, h3, h2⟩ := rpow_third_identities t ht0
  set ρ := R * t ^ (-(1 : ℝ) / 3) with hρ_def
  have hρ : 0 < ρ := mul_pos (by linarith) hs0
  obtain ⟨N, hN1, hN2, hN3⟩ := hE3 t R (ε₀ / 2) ht0 hR1 (by positivity)
  set Φ : ℝ × ℝ → ℝ := fun κ => t * φ κ with hΦ_def
  have hpc : ∀ i, Continuous (piecesAt χ ρ N i) := by
    intro i; cases i with
    | none => unfold piecesAt; simp only [Option.elim]; fun_prop
    | some j => unfold piecesAt; simp only [Option.elim]; fun_prop
  have hp01 : ∀ i κ, piecesAt χ ρ N i κ ∈ Icc (0 : ℝ) 1 := by
    intro i κ; cases i with
    | none => exact hχ01 _
    | some j =>
      simp only [piecesAt, Option.elim]
      exact ⟨sub_nonneg.mpr (hχmono _), by
        linarith [(hχ01 ((2 : ℝ) • ((2 ^ ((j : ℕ) + 1) * ρ)⁻¹ • κ))).1,
          (hχ01 ((2 ^ ((j : ℕ) + 1) * ρ)⁻¹ • κ)).2]⟩
  have hsum := sum_piecesAt χ hχ1 ρ (ε₀ / 2) hρ N hN1
  have hφc : Continuous φ := hφ.continuous
  have hAcs : HasCompactSupport A :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (ε₀ / 2)) (isClosed_tsupport A) hA.2.1
  have hint : Integrable (fun κ => Complex.exp (↑(Φ κ) * Complex.I) * A κ) := by
    refine Continuous.integrable_of_hasCompactSupport (by simp only [hΦ_def]; fun_prop) ?_
    exact hAcs.mul_left
  have hdec := LocalizeAux.oscInt2_eq_sum_of_integrable Φ (piecesAt χ ρ N) hpc hp01 hsum hA.2.1 hint
  -- the outer pieces
  have hout : ∀ j : Fin N, ‖oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ)‖ ≤
      (2 ^ ((j : ℕ) + 1) * ρ) ^ 2 * (K * M * (t * (2 ^ ((j : ℕ) + 1) * ρ) ^ 3) ^ (-(5 : ℝ) / 6)) := by
    intro j
    have hε : 0 < 2 ^ ((j : ℕ) + 1) * ρ := by positivity
    have hεε₀ : 2 ^ ((j : ℕ) + 1) * ρ ≤ ε₀ := by
      have := hN2 j j.2; simp only [← hρ_def] at this; linarith
    have hm : 1 ≤ t * (2 ^ ((j : ℕ) + 1) * ρ) ^ 3 := by
      have he : t * (2 ^ ((j : ℕ) + 1) * ρ) ^ 3 = (2 ^ ((j : ℕ) + 1) * R) ^ 3 * (t * (t ^ (-(1 : ℝ) / 3)) ^ 3) := by
        rw [hρ_def]; ring
      rw [he, h3, mul_one]
      exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hR1)
    exact hpiece A M hA' _ t hε hεε₀ hm
  have hinner_eq : ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
      oscInt2 Φ (fun κ => (piecesAt χ ρ N none κ : ℂ) * A κ) =
      oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3))) (fun w => B w * A (t ^ (-(1 : ℝ) / 3) • w)) :=
    inner_eq φ χ A t R ht0
  have htt : t ^ ((2 : ℝ) / 3) * t ^ (-(2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add ht0]; norm_num
  have hsumo : ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
      ∑ j : Fin N, oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ)‖ ≤
      3 * (K * M) * R ^ (-(1 : ℝ) / 2) := by
    have hpos23 : 0 ≤ t ^ ((2 : ℝ) / 3) := Real.rpow_nonneg ht0.le _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos23]
    calc t ^ ((2 : ℝ) / 3) * ‖∑ j : Fin N, oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ)‖
        ≤ t ^ ((2 : ℝ) / 3) * ∑ j : Fin N, (2 ^ ((j : ℕ) + 1) * ρ) ^ 2 *
            (K * M * (t * (2 ^ ((j : ℕ) + 1) * ρ) ^ 3) ^ (-(5 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hout j)) hpos23
      _ = t ^ ((2 : ℝ) / 3) * (K * M * ∑ j ∈ Finset.range N, (2 ^ (j + 1) * ρ) ^ 2 *
            (t * (2 ^ (j + 1) * ρ) ^ 3) ^ (-(5 : ℝ) / 6)) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => (2 ^ (j + 1) * ρ) ^ 2 *
            (K * M * (t * (2 ^ (j + 1) * ρ) ^ 3) ^ (-(5 : ℝ) / 6))) N, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ t ^ ((2 : ℝ) / 3) * (K * M * (3 * R ^ (-(1 : ℝ) / 2) * t ^ (-(2 : ℝ) / 3))) := by
          have h := hN3; simp only [← hρ_def] at h
          gcongr
      _ = 3 * (K * M) * R ^ (-(1 : ℝ) / 2) * (t ^ ((2 : ℝ) / 3) * t ^ (-(2 : ℝ) / 3)) := by ring
      _ = 3 * (K * M) * R ^ (-(1 : ℝ) / 2) := by rw [htt, mul_one]
  rw [dist_eq_norm, hdec, Fintype.sum_option, mul_add, hinner_eq]
  calc ‖oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3))) (fun w => B w * A (t ^ (-(1 : ℝ) / 3) • w)) +
        ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * ∑ j : Fin N, oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ) -
        c * A 0‖
      ≤ ‖oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3))) (fun w => B w * A (t ^ (-(1 : ℝ) / 3) • w)) -
          oscInt2 (cubicForm q) B * A 0‖ + ‖oscInt2 (cubicForm q) B - c‖ * ‖A 0‖ +
          ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
            ∑ j : Fin N, oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ)‖ := by
        rw [← norm_mul]
        set X := oscInt2 (rescale φ (t ^ (-(1 : ℝ) / 3))) (fun w => B w * A (t ^ (-(1 : ℝ) / 3) • w))
        set Y := ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
          ∑ j : Fin N, oscInt2 Φ (fun κ => (piecesAt χ ρ N (some j) κ : ℂ) * A κ)
        set L0 := oscInt2 (cubicForm q) B
        have he : X + Y - c * A 0 = (X - L0 * A 0) + (L0 - c) * A 0 + Y := by ring
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < η / 3 + η / 3 + η / 3 := by
        refine add_lt_add_of_lt_of_le (add_lt_add hinner hRb) (hsumo.trans hRa.le)
    _ = η := by ring

end OscInt.D4
