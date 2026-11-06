import Blueprint.D4
import OscInt.StationaryPhase.Final

/-!
# S4.1 assembly against the blueprint interfaces

`D4BoundStatement` from the parts D1–D9 of `Blueprint/D4.lean`, the infrastructure parts F1c, F1d, F2b (proved
in `OscInt/StationaryPhase/`), S3 (`OscInt.fold`) and S2.1 (`OscInt.nonStationary`). Route: `docs/proof-S4.md`.

1. Normalise (D1): `φ(0) = 0`, `∇φ(0) = 0`, the gradient moves into the linear term `y' = y + t ∇φ(0)`.
2. Rescaled family (D2) on `Λ = [0, ε₀]`; at `ε = 0` it is the cubic part, whose gauge is positive on the annulus
   (D3), hence for `ε ≤ ε₀` (D5), hence `FoldOrNondeg` (D4).
3. Dyadic partition `χ(·/ε_J) + ∑_{j<J} β(·/ε_j) = 1` on `B̄(0, ε₀)` with `β = χ − χ(2·)` (D7), `ε_j = ε₀/2ʲ`,
   `J` from D9. Piece `j`: rescale `κ = ε_j z` (F1c), phase `m (Ψ_ε + p·)` with `m = t ε³ ≥ 1`, `p = y'/(t ε²)`;
   S3 for `‖p‖ ≤ G`, S2.1 (`N = 1`) for `‖p‖ ≥ G` (D6). Inner piece: trivial bound (D8).
4. Sum (D9): `≤ (16 + 4 D C_β) M t^{-2/3}`.
-/

namespace OscInt.D4

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase
open scoped ContDiff

theorem familyCk_comp {Λ Λ' : Type} [TopologicalSpace Λ] [TopologicalSpace Λ'] {n : ℕ}
    {Ψ : Λ → ℝ × ℝ → ℝ} (f : Λ' → Λ) (hf : Continuous f) (h : FamilyCk n Ψ) :
    FamilyCk n (fun σ => Ψ (f σ)) :=
  ⟨fun σ => h.1 (f σ), fun j hj => (h.2 j hj).comp (hf.prodMap continuous_id)⟩

theorem ampBound_of_le {m n : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (hmn : m ≤ n)
    (h : AmpBound n K A M) : AmpBound m K A M :=
  ⟨h.1.of_le (by exact_mod_cast hmn), h.2.1, fun j hj => h.2.2 j (hj.trans hmn)⟩

theorem ampBound_mono_bound {n : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M M' : ℝ} (hM : M ≤ M')
    (h : AmpBound n K A M) : AmpBound n K A M' :=
  ⟨h.1, h.2.1, fun j hj k => (h.2.2 j hj k).trans hM⟩

theorem annulus_eq : annulus = Metric.closedBall 0 2 ∩ {z : ℝ × ℝ | 1 / 2 ≤ ‖z‖} := by
  ext z; simp [annulus, and_comm]

theorem isCompact_annulus : IsCompact annulus := by
  rw [annulus_eq]
  exact (isCompact_closedBall 0 2).inter_right (isClosed_le continuous_const continuous_norm)

theorem isClosed_annulus : IsClosed annulus := isCompact_annulus.isClosed

theorem ne_zero_of_mem_annulus {z : ℝ × ℝ} (hz : z ∈ annulus) : z ≠ 0 := by
  rintro rfl; have := hz.1; norm_num at this

theorem lin_smul_left (c : ℝ) (p k : ℝ × ℝ) : lin (c • p) k = c * lin p k := by
  simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem lin_smul_right (c : ℝ) (p k : ℝ × ℝ) : lin p (c • k) = c * lin p k := by
  simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Multiplication by a nonzero scalar as a continuous linear equivalence of `ℝ²`. -/
noncomputable def smulEquiv (ε : ℝ) (hε : ε ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε)

theorem smulEquiv_apply (ε : ℝ) (hε : ε ≠ 0) (z : ℝ × ℝ) : smulEquiv ε hε z = ε • z := by
  simp [smulEquiv, ContinuousLinearEquiv.smulLeft, Units.smul_def]

theorem det_smulEquiv (ε : ℝ) (hε : ε ≠ 0) :
    LinearMap.det ((smulEquiv ε hε : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = ε ^ 2 := by
  have h : ((smulEquiv ε hε : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = ε • LinearMap.id := by
    ext <;> simp [smulEquiv_apply]
  rw [h, LinearMap.det_smul, LinearMap.det_id, Module.finrank_prod, Module.finrank_self]
  ring

theorem norm_smulEquiv_le (ε : ℝ) (hε : ε ≠ 0) (hε1 : |ε| ≤ 1) :
    ‖((smulEquiv ε hε : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [ContinuousLinearEquiv.coe_coe, smulEquiv_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hε1 (norm_nonneg z)

/-- One dyadic piece after rescaling `κ = ε z`. -/
theorem piece_eq (ψ : ℝ × ℝ → ℝ) (β : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (t ε : ℝ) (y : ℝ × ℝ) (ht : t ≠ 0)
    (hε : 0 < ε) :
    ‖oscInt2 (fun κ => t * ψ κ + lin y κ) (fun κ => (β (ε⁻¹ • κ) : ℂ) * A κ)‖ =
      ε ^ 2 * ‖oscInt2 (fun z => (t * ε ^ 3) * (rescale ψ ε z + lin ((t * ε ^ 2)⁻¹ • y) z))
        (fun z => (β z : ℂ) * A (ε • z))‖ := by
  have hε0 : ε ≠ 0 := hε.ne'
  rw [affineChange _ _ 0 (smulEquiv ε hε0), det_smulEquiv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_abs, abs_of_nonneg (sq_nonneg ε)]
  congr 2
  congr 1
  · funext z
    simp only [zero_add, smulEquiv_apply, rescale, ite_eq_right hε0, lin_smul_left, lin_smul_right]
    field_simp
  · funext z
    simp only [zero_add, smulEquiv_apply, inv_smul_smul₀ hε0]

/-- Support of a rescaled cut-off. -/
theorem tsupport_rescale_subset (f : ℝ × ℝ → ℝ) (R e : ℝ) (he : 0 < e)
    (hf : tsupport f ⊆ Metric.closedBall 0 R) :
    tsupport (fun κ : ℝ × ℝ => (f (e⁻¹ • κ) : ℂ)) ⊆ Metric.closedBall 0 (e * R) := by
  refine closure_minimal (fun κ hκ => ?_) Metric.isClosed_closedBall
  have h1 : e⁻¹ • κ ∈ Function.support f := fun h0 => hκ (by simp [h0])
  have h2 := hf (subset_tsupport f h1)
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)] at h2
  rw [mem_closedBall_zero_iff]
  calc ‖κ‖ = e * (e⁻¹ * ‖κ‖) := by field_simp
    _ ≤ e * R := by gcongr

/-- The dyadic cut-off pieces: `none` is the inner piece `χ(·/ε_J)`, `some j` the annular piece `β(·/ε_j)`. -/
noncomputable def pieces (χ : ℝ × ℝ → ℝ) (δ : ℝ) (J : ℕ) (i : Option (Fin J)) (κ : ℝ × ℝ) : ℝ :=
  i.elim (χ ((δ / 2 ^ J)⁻¹ • κ)) (fun j => χ ((δ / 2 ^ (j : ℕ))⁻¹ • κ) - χ ((2 : ℝ) • ((δ / 2 ^ (j : ℕ))⁻¹ • κ)))

theorem sum_pieces (χ : ℝ × ℝ → ℝ) (hχ1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1) (δ : ℝ) (hδ : 0 < δ) (J : ℕ) :
    ∀ κ ∈ Metric.closedBall (0 : ℝ × ℝ) δ, ∑ i, pieces χ δ J i κ = 1 := by
  intro κ hκ
  have hstep : ∀ j : ℕ, (2 : ℝ) • ((δ / 2 ^ j)⁻¹ • κ) = (δ / 2 ^ (j + 1))⁻¹ • κ := by
    intro j; rw [smul_smul]; congr 1; rw [pow_succ]; field_simp
  rw [Fintype.sum_option]
  simp only [pieces, Option.elim]
  rw [Fin.sum_univ_eq_sum_range (fun j => χ ((δ / 2 ^ j)⁻¹ • κ) - χ ((2 : ℝ) • ((δ / 2 ^ j)⁻¹ • κ))) J]
  simp only [hstep]
  rw [Finset.sum_range_sub' (fun j => χ ((δ / 2 ^ j)⁻¹ • κ)) J]
  simp only [pow_zero, div_one]
  rw [add_sub_cancel]
  apply hχ1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  rw [mem_closedBall_zero_iff] at hκ
  calc δ⁻¹ * ‖κ‖ ≤ δ⁻¹ * δ := by gcongr
    _ = 1 := inv_mul_cancel₀ hδ.ne'

/-- **S4.1** from the interfaces. -/
theorem d4Bound_of (hN : NormalizeFacts) (hR : RescaleFamilyFacts) (hCG : CubicGaugeFacts)
    (hGF : GaugeFoldFacts) (hGO : GaugeOpenFacts) (hGB : GradBoundFacts) (hCut : CutoffFacts)
    (hTB : TrivialBoundFacts) (hDS : DyadicSumFacts) : D4BoundStatement := by
  intro φ hφ hdd hdisc
  obtain ⟨hψ4, hψ0, hψ1, hψdd, hψddd, hψI⟩ := hN φ hφ
  set ψ := normalize φ with hψ_def
  have hcc : cubicCoeffs ψ = cubicCoeffs φ := by simp only [cubicCoeffs, hψddd]
  have hdd0 : ∀ v w, dd ψ 0 v w = 0 := fun v w => by rw [hψdd]; exact hdd v w
  have hfam : FamilyCk 4 (rescale ψ) := hR ψ hψ4 hψ0 hψ1 hdd0
  -- the gauge at `ε = 0` and nearby
  have h0 : ∀ z ∈ annulus, 0 < foldGauge (rescale ψ 0) z ∧ 0 < hessNorm (rescale ψ 0) z := by
    intro z hz
    have : rescale ψ 0 = cubicPoly (cubicCoeffs ψ) := by funext z; simp [rescale]
    rw [this]
    exact hCG _ (by rw [hcc]; exact hdisc.ne) z (ne_zero_of_mem_annulus hz)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hGO ℝ (rescale ψ) 0 annulus (familyCk_of_le (by norm_num) hfam) isCompact_annulus h0)
  set ε₀ : ℝ := min 1 (r / 2) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min one_pos (half_pos hr)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  let Ψ : Icc (0 : ℝ) ε₀ → ℝ × ℝ → ℝ := fun σ => rescale ψ σ.1
  have hΨ : FamilyCk 4 Ψ := familyCk_comp Subtype.val continuous_subtype_val hfam
  have hfold : ∀ σ, ∀ z ∈ annulus, FoldOrNondeg (Ψ σ) z := by
    intro σ z hz
    have hσ : dist σ.1 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg σ.2.1]
      exact lt_of_le_of_lt (σ.2.2.trans (min_le_right _ _)) (half_lt_self hr)
    obtain ⟨h1, h2⟩ := hball hσ z hz
    exact hGF _ ((hfam.1 σ.1).of_le (by norm_num)) z h1 h2
  obtain ⟨G, hG⟩ := hGB _ Ψ annulus (familyCk_of_le (by norm_num) hΨ) isCompact_annulus
  obtain ⟨C₃, hC₃⟩ := OscInt.fold _ Ψ annulus (Metric.closedBall 0 G) hΨ isCompact_annulus
    (isCompact_closedBall 0 G) hfold
  obtain ⟨C₁, hC₁⟩ := OscInt.nonStationary _ 1 Ψ annulus 1 (familyCk_of_le (by norm_num) hΨ)
    isCompact_annulus one_pos
  -- the cut-offs
  obtain ⟨χ, hχ, hχ01, hχ1, hχs, hχmono⟩ := hCut
  let β : ℝ × ℝ → ℝ := fun z => χ z - χ ((2 : ℝ) • z)
  have hχc : Continuous χ := hχ.continuous
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
  set D : ℝ := max (max C₃ C₁) 0 with hD_def
  have hD0 : 0 ≤ D := le_max_right _ _
  refine ⟨ε₀, hε₀, 16 + 4 * D * Cβ, fun A M y t hA ht => ?_⟩
  have hM : 0 ≤ M := LocalizeAux.ampBound_nonneg hA
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  rw [hψI A t y]
  set y' := y + t • grad0 φ
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := hDS ε₀ t hε₀ hε₀1 ht
  set e : ℕ → ℝ := fun j => ε₀ / 2 ^ j with he_def
  have he : ∀ j, 0 < e j := fun j => div_pos hε₀ (pow_pos two_pos j)
  have heε : ∀ j, e j ≤ ε₀ := fun j => div_le_self hε₀.le (one_le_pow₀ one_le_two)
  set Φ : ℝ × ℝ → ℝ := fun κ => t * ψ κ + lin y' κ
  set B : Option (Fin J) → ℝ := fun i =>
    i.elim (4 * (e J * 2) ^ 2 * M) (fun j => e j ^ 2 * (D * (Cβ * M) * (t * e j ^ 3) ^ (-(5 : ℝ) / 6)))
  have hpc : ∀ i, Continuous (pieces χ ε₀ J i) := by
    intro i; cases i with
    | none => unfold pieces; simp only [Option.elim]; fun_prop
    | some j => unfold pieces; simp only [Option.elim]; fun_prop
  have hp01 : ∀ i κ, pieces χ ε₀ J i κ ∈ Icc (0 : ℝ) 1 := by
    intro i κ; cases i with
    | none => exact hχ01 _
    | some j =>
      simp only [pieces, Option.elim]
      exact ⟨sub_nonneg.mpr (hχmono _), by linarith [(hχ01 ((2 : ℝ) • ((ε₀ / 2 ^ (j : ℕ))⁻¹ • κ))).1,
        (hχ01 ((ε₀ / 2 ^ (j : ℕ))⁻¹ • κ)).2]⟩
  have hB0 : ∀ i, 0 ≤ B i := by
    intro i; cases i with
    | none => exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM
    | some j => exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hD0 (mul_nonneg hCβ0 hM))
        (Real.rpow_nonneg (mul_nonneg ht0.le (pow_nonneg (he j).le 3)) _))
  have hAc : Continuous A := hA.1.continuous
  have hA0 : ∀ κ, ‖A κ‖ ≤ M := fun κ => by
    simpa [norm_iteratedFDeriv_zero] using hA.2.2 0 (Nat.zero_le 2) κ
  have hpiece : ∀ i, ‖oscInt2 Φ (fun κ => (pieces χ ε₀ J i κ : ℂ) * A κ)‖ ≤ B i := by
    intro i; cases i with
    | none =>
      refine hTB Φ _ M (e J * 2) ((Complex.continuous_ofReal.comp (hpc none)).mul hAc) (fun κ => ?_) ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp01 none κ).1]
        calc pieces χ ε₀ J none κ * ‖A κ‖ ≤ 1 * M :=
              mul_le_mul (hp01 none κ).2 (hA0 κ) (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      · exact (tsupport_mul_subset_left (f := fun κ => (pieces χ ε₀ J none κ : ℂ)) (g := A)).trans
          (tsupport_rescale_subset χ 2 (e J) (he J) hχs)
    | some j =>
      set ε := e j
      have hε := he j
      have hε0 : ε ≠ 0 := hε.ne'
      have hm : 1 ≤ t * ε ^ 3 := hJ1 j j.2
      let σ : Icc (0 : ℝ) ε₀ := ⟨ε, hε.le, heε j⟩
      set p : ℝ × ℝ := (t * ε ^ 2)⁻¹ • y'
      have hpe : (fun κ => (pieces χ ε₀ J (some j) κ : ℂ) * A κ) =
          fun κ => (β (ε⁻¹ • κ) : ℂ) * A κ := rfl
      rw [hpe, piece_eq ψ β A t ε y' ht0.ne' hε]
      -- amplitude bound for the rescaled piece
      set L := smulEquiv ε hε0
      have hA' := ampBoundAffine 2 _ A M 0 L hA
      have hA'' := hCβ _ _ _ hA'
      simp only [zero_add, L, smulEquiv_apply] at hA''
      have hLn : max 1 ‖((smulEquiv ε hε0 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ^ 2 = 1 := by
        have h1 := norm_smulEquiv_le ε hε0 (by rw [abs_of_pos hε]; exact (heε j).trans hε₀1)
        rw [max_eq_left h1, one_pow]
      rw [hLn, one_mul] at hA''
      have hAj : AmpBound 2 annulus (fun z => (β z : ℂ) * A (ε • z)) (Cβ * M) :=
        LocalizeAux.ampBound_mono hA'' (inter_subset_right.trans hβsupp)
      have hfin : ‖oscInt2 (fun z => (t * ε ^ 3) * (Ψ σ z + lin p z)) (fun z => (β z : ℂ) * A (ε • z))‖ ≤
          D * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) := by
        have hCM : 0 ≤ Cβ * M * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) :=
          mul_nonneg (mul_nonneg hCβ0 hM) (Real.rpow_nonneg (by linarith) _)
        by_cases hp : ‖p‖ ≤ G
        · calc _ ≤ C₃ * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) :=
                hC₃ _ _ σ p _ hAj (mem_closedBall_zero_iff.mpr hp) hm
            _ ≤ D * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  ((le_max_left _ _).trans (le_max_left _ _)) (mul_nonneg hCβ0 hM))
                  (Real.rpow_nonneg (by linarith) _)
        · have h1 := hC₁ _ _ σ p _ (ampBound_of_le (by norm_num) hAj)
            (fun k hk => hG σ k hk p (le_of_lt (not_le.mp hp))) hm
          have hmr : (t * ε ^ 3) ^ (-(1 : ℝ)) ≤ (t * ε ^ 3) ^ (-(5 : ℝ) / 6) :=
            Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
          calc _ ≤ C₁ * (Cβ * M) / (t * ε ^ 3) ^ 1 := h1
            _ = C₁ * (Cβ * M) * (t * ε ^ 3) ^ (-(1 : ℝ)) := by
                rw [pow_one, Real.rpow_neg_one, div_eq_mul_inv]
            _ ≤ D * (Cβ * M) * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) := by
                apply mul_le_mul ?_ hmr (Real.rpow_nonneg (by linarith) _) (mul_nonneg hD0 (mul_nonneg hCβ0 hM))
                exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
                  (mul_nonneg hCβ0 hM)
      exact mul_le_mul_of_nonneg_left hfin (sq_nonneg ε)
  have hsum := sum_pieces χ hχ1 ε₀ hε₀ J
  calc ‖oscInt2 Φ A‖ ≤ ∑ i, B i :=
        LocalizeAux.norm_oscInt2_le_sum Φ (pieces χ ε₀ J) hpc hp01 hsum hA.2.1 B hB0 hpiece
    _ = 16 * (e J) ^ 2 * M + D * (Cβ * M) *
          ∑ j ∈ Finset.range J, e j ^ 2 * (t * e j ^ 3) ^ (-(5 : ℝ) / 6) := by
        rw [Fintype.sum_option]
        simp only [B, Option.elim]
        rw [Fin.sum_univ_eq_sum_range (fun j => e j ^ 2 * (D * (Cβ * M) * (t * e j ^ 3) ^ (-(5 : ℝ) / 6))) J,
          Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 16 * t ^ (-(2 : ℝ) / 3) * M + D * (Cβ * M) * (4 * t ^ (-(2 : ℝ) / 3)) := by
        gcongr
    _ = (16 + 4 * D * Cβ) * M * t ^ (-(2 : ℝ) / 3) := by ring

end OscInt.D4
