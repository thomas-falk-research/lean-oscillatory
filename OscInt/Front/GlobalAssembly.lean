import OscInt.Front.Local
import Blueprint.Global

/-!
# Batch GD: the lead's assemblies against the blueprint interfaces

Route `docs/proof-GD.md` R3, R4. GD-C by induction on the exceptional set: one D4 point is cut out by a bump (R1, R2),
the remainder lives on a smaller compact set. GD, GD-F, GD-N split the linear terms into a compact ball (GD-C,
FE-S3l, FE-S2.2l) and large ones (FE-S2.1l with `N = 1`).
-/

namespace OscInt.API.GlobalAux

open OscInt.Statements OscInt.Blueprint.GD Filter Topology MeasureTheory
open scoped ContDiff

/-- The integrand `e^{im(Ψ + L)} A` is continuous when `A` is continuous with `tsupport A ⊆ U`, `U` open, and `Ψ` is
continuous on `U` (the phase may be arbitrary outside `U`). -/
theorem continuous_integrand {Ψ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hΨ : ContinuousOn Ψ U)
    {A : ℝ × ℝ → ℂ} (hA : Continuous A) (hAU : tsupport A ⊆ U) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ) :
    Continuous fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k := by
  rw [continuous_iff_continuousAt]
  intro k
  by_cases hk : k ∈ U
  · have hc : ContinuousAt Ψ k := hΨ.continuousAt (hU.mem_nhds hk)
    have : ContinuousAt (fun k => (↑(m * (Ψ k + L k)) : ℂ)) k :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (hc.add L.continuous.continuousAt))
    exact ((Complex.continuous_exp.continuousAt.comp (this.mul continuousAt_const))).mul hA.continuousAt
  · have h0 : A =ᶠ[𝓝 k] 0 := by
      rw [← notMem_tsupport_iff_eventuallyEq]; exact fun h => hk (hAU h)
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [h0] with y hy
    simp [hy]

theorem integrable_integrand {Ψ : ℝ × ℝ → ℝ} {U K : Set (ℝ × ℝ)} (hU : IsOpen U) (hΨ : ContinuousOn Ψ U)
    (hK : IsCompact K) (hKU : K ⊆ U) {A : ℝ × ℝ → ℂ} (hA : Continuous A) (hAK : tsupport A ⊆ K)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ) :
    Integrable fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k :=
  (continuous_integrand hU hΨ hA (hAK.trans hKU) L m).integrable_of_hasCompactSupport
    ((HasCompactSupport.intro hK fun k hk => by
      exact image_eq_zero_of_notMem_tsupport (fun h => hk (hAK h))).mul_left)

/-- `M ≥ 0` from the bound of order `0`. -/
theorem M_nonneg {A : ℝ × ℝ → ℂ} {M : ℝ} (hM : ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) : 0 ≤ M :=
  (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)

/-- A bound with rate `5/6` (or `1`) is a bound with rate `2/3` for `m ≥ 1`, after replacing `C` by `max C 0`. -/
theorem rate_mono {x C M m r s : ℝ} (hM : 0 ≤ M) (hm : 1 ≤ m) (hrs : r ≤ s) (h : x ≤ C * M * m ^ r) :
    x ≤ max C 0 * M * m ^ s :=
  h.trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) (Real.rpow_le_rpow_of_exponent_le hm hrs)
    (by positivity) (mul_nonneg (le_max_right _ _) hM))

/-- The amplitude `χ A` for a real `χ`, and the remainder `A − χ A`. -/
theorem cut_split (χ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (E : ℝ × ℝ → ℂ) (k : ℝ × ℝ) :
    E k * A k = E k * ((χ k : ℂ) * A k) + E k * (A k - (χ k : ℂ) * A k) := by ring

/-- Derivative bounds of `A − χ A`. -/
theorem sub_bound {A B : ℝ × ℝ → ℂ} {M M' : ℝ} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B)
    (hMA : ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) (hMB : ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j B k‖ ≤ M') :
    ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j (fun k => A k - B k) k‖ ≤ M + M' := by
  intro j hj k
  have hj' : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj
  rw [show (fun k => A k - B k) = A - B from rfl,
    iteratedFDeriv_sub_apply (hA.contDiffAt.of_le hj') (hB.contDiffAt.of_le hj')]
  exact (norm_sub_le _ _).trans (add_le_add (hMA j hj k) (hMB j hj k))

/-- **The induction on `D`** (GD-C for every compact `K ⊆ U`, given the D4 pieces). -/
theorem crit_induction (hD4 : D4PieceFacts) (hB : BumpFacts) (hMul : MulBoundFacts)
    (Ψ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)) (hU : IsOpen U) (hK' : IsCompact K')
    (hΨ : ContDiffOn ℝ 4 Ψ U) (D : Finset (ℝ × ℝ)) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → (↑D : Set (ℝ × ℝ)) ⊆ U → ClassifiedCrit Ψ K K' D →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3) := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro K hK hKU _ hcl
    obtain ⟨C, hC⟩ := OscInt.API.foldOn Ψ K U K' hK hU hKU hK' hΨ
      (fun L hL k hk hc => hcl.1 L hL k hk (Finset.notMem_empty k) hc)
    exact ⟨max C 0, fun A M L m hA hs hM hL hm =>
      rate_mono (M_nonneg hM) hm (by norm_num) (hC A M L m hA hs hM hL hm)⟩
  | insert k₀ D hk₀ ih =>
    intro K hK hKU hDU hcl
    have hk₀U : k₀ ∈ U := hDU (Finset.mem_insert_self k₀ D)
    obtain ⟨δ, hδ, C₀, hC₀⟩ := hD4 Ψ U k₀ hU hk₀U hΨ (hcl.2 k₀ (Finset.mem_insert_self k₀ D))
    obtain ⟨χ, hχ, hχs, hχ1, -, Bχ, hBχ⟩ := hB k₀ δ hδ
    have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    obtain ⟨Cm, hCm⟩ := hMul χ Bχ hχ2 hBχ
    set K₁ := K ∩ (Metric.ball k₀ (δ / 2))ᶜ with hK₁
    have hK₁c : IsCompact K₁ := hK.inter_right Metric.isOpen_ball.isClosed_compl
    have hK₁U : K₁ ⊆ U := Set.inter_subset_left.trans hKU
    have hcl₁ : ClassifiedCrit Ψ K₁ K' D := by
      refine ⟨fun L hL k hk hkD hc => hcl.1 L hL k hk.1 ?_ hc, fun k hk => hcl.2 k (Finset.mem_insert_of_mem hk)⟩
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => hk.2 ?_, hkD⟩
      rw [h]; exact Metric.mem_ball_self (half_pos hδ)
    obtain ⟨C₁, hC₁⟩ := ih K₁ hK₁c hK₁U (fun x hx => hDU (Finset.mem_insert_of_mem hx)) hcl₁
    have hΨc : ContinuousOn Ψ U := hΨ.continuousOn
    refine ⟨C₀ * Cm + C₁ * (1 + Cm), fun A M L m hA hs hM hL hm => ?_⟩
    have hχA : ContDiff ℝ 2 fun k => (χ k : ℂ) * A k :=
      (Complex.ofRealCLM.contDiff.comp hχ2).mul hA
    have hMχ := hCm A M hA hM
    -- the piece at `k₀`
    have hs₀ : tsupport (fun k => (χ k : ℂ) * A k) ⊆ Metric.closedBall k₀ δ :=
      (tsupport_mul_subset_left.trans (by
        intro x hx; exact hχs (by simpa [tsupport, Function.support] using hx)))
    have h0 := hC₀ (fun k => (χ k : ℂ) * A k) (Cm * M) L m hχA hs₀ hMχ hm
    -- the remainder
    have hR : ContDiff ℝ 2 fun k => A k - (χ k : ℂ) * A k := hA.sub hχA
    have hsR : tsupport (fun k => A k - (χ k : ℂ) * A k) ⊆ K₁ := by
      apply closure_minimal _ (hK.isClosed.inter Metric.isOpen_ball.isClosed_compl)
      intro x hx
      refine ⟨hs (subset_tsupport _ fun h => hx (by simp [h])), fun hb => hx ?_⟩
      simp [hχ1 x (Metric.ball_subset_closedBall (Metric.mem_ball.mpr (Metric.mem_ball.mp hb)))]
    have h1 := hC₁ _ (M + Cm * M) L m hR hsR (sub_bound hA hχA hM hMχ) hL hm
    -- split the integral
    have hI0 := integrable_integrand hU hΨc hK hKU hχA.continuous (tsupport_mul_subset_right.trans hs) L m
    have hI1 := integrable_integrand hU hΨc hK₁c hK₁U hR.continuous hsR L m
    rw [show (fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k) =
        fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * ((χ k : ℂ) * A k) +
          Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * (A k - (χ k : ℂ) * A k) from
        funext fun k => cut_split χ A (fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I)) k,
        integral_add hI0 hI1]
    refine (norm_add_le _ _).trans ?_
    have hM0 := M_nonneg hM
    have e : (C₀ * Cm + C₁ * (1 + Cm)) * M * m ^ (-(2 : ℝ) / 3) =
        C₀ * (Cm * M) * m ^ (-(2 : ℝ) / 3) + C₁ * (M + Cm * M) * m ^ (-(2 : ℝ) / 3) := by ring
    rw [e]; exact add_le_add h0 h1

/-- GD-C from the parts. -/
theorem globalDecayCrit_of (hD4 : D4PieceFacts) (hB : BumpFacts) (hMul : MulBoundFacts) :
    GlobalDecayCritStatement :=
  fun Ψ K U K' D hK hU hKU hDU hK' hΨ hcl => crit_induction hD4 hB hMul Ψ U K' hU hK' hΨ D K hK hKU hDU hcl

/-- From bounds over every ball of linear terms to a bound over all linear terms (large `‖L‖` by FE-S2.1l, `N = 1`),
for a rate `m^{-r}` with `r ≤ 1`. -/
theorem allL_of (hLL : LargeLFacts) (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hΨ : ContDiffOn ℝ 4 Ψ U) (r : ℝ) (hr : r ≤ 1)
    (hsmall : ∀ R : ℝ, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ Metric.closedBall (0 : (ℝ × ℝ) →L[ℝ] ℝ) R → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-r)) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-r) := by
  obtain ⟨R, hR⟩ := hLL Ψ K U hK hU hKU (hΨ.of_le (by norm_num))
  obtain ⟨C₀, hC₀⟩ := hsmall R
  obtain ⟨C₁, hC₁⟩ := OscInt.API.nonStationaryOn 1 Ψ K U 1 hK hU hKU (hΨ.of_le (by norm_num)) one_pos
  refine ⟨max C₀ 0 + max C₁ 0, fun A M L m hA hs hM hm => ?_⟩
  have hM0 := M_nonneg hM
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hp : 0 ≤ m ^ (-r) := (Real.rpow_pos_of_pos hm0 _).le
  have hsum : max C₀ 0 * M * m ^ (-r) + max C₁ 0 * M * m ^ (-r) = (max C₀ 0 + max C₁ 0) * M * m ^ (-r) := by ring
  by_cases hL : ‖L‖ ≤ R
  · have h := rate_mono hM0 hm le_rfl
      (hC₀ A M L m hA hs hM (by rwa [Metric.mem_closedBall, dist_zero_right]) hm)
    rw [← hsum]
    exact h.trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (le_max_right _ _) hM0) hp))
  · have h1 := hC₁ A M L m (hA.of_le (by norm_num)) hs (fun j hj k => hM j (hj.trans (by norm_num)) k)
      (fun k hk => hR L (le_of_not_ge hL) k hk) hm
    have h2 : C₁ * M / m ^ 1 ≤ max C₁ 0 * M * m ^ (-r) := by
      rw [pow_one, div_eq_mul_inv, ← Real.rpow_neg_one]
      exact rate_mono hM0 hm (by linarith) le_rfl
    rw [← hsum]
    exact (h1.trans h2).trans (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (le_max_right _ _) hM0) hp))

/-- GD from GD-C and the large-`L` part. -/
theorem globalDecay_of (hD4 : D4PieceFacts) (hB : BumpFacts) (hMul : MulBoundFacts) (hLL : LargeLFacts) :
    GlobalDecayStatement := by
  intro Ψ K U D hK hU hKU hDU hΨ hcl
  have := allL_of hLL Ψ K U hK hU hKU hΨ (2 / 3) (by norm_num) fun R =>
    globalDecayCrit_of hD4 hB hMul Ψ K U (Metric.closedBall 0 R) D hK hU hKU hDU (isCompact_closedBall _ _) hΨ
      ⟨fun _ _ k hk hkD _ => hcl.1 k hk hkD, hcl.2⟩ |>.imp fun C hC A M L m hA hs hM hL hm => by
        simpa [neg_div] using hC A M L m hA hs hM hL hm
  simpa [neg_div] using this

/-- GD-F from FE-S3l and the large-`L` part. -/
theorem globalFold_of (hLL : LargeLFacts) : GlobalFoldStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  have := allL_of hLL Ψ K U hK hU hKU hΨ (5 / 6) (by norm_num) fun R =>
    OscInt.API.foldOn Ψ K U (Metric.closedBall 0 R) hK hU hKU (isCompact_closedBall _ _) hΨ
      (fun _ _ k hk _ => hcl k hk) |>.imp fun C hC A M L m hA hs hM hL hm => by
        simpa [neg_div] using hC A M L m hA hs hM hL hm
  simpa [neg_div] using this

/-- GD-N from FE-S2.2l and the large-`L` part. -/
theorem globalNondeg_of (hLL : LargeLFacts) : GlobalNondegStatement := by
  intro Ψ K U hK hU hKU hΨ hcl
  obtain ⟨C, hC⟩ := allL_of hLL Ψ K U hK hU hKU hΨ 1 le_rfl fun R =>
    OscInt.API.stationaryPhaseOn Ψ K U (Metric.closedBall 0 R) hK hU hKU (isCompact_closedBall _ _) hΨ
      (fun _ _ k hk _ => hcl k hk) |>.imp fun C hC A M L m hA hs hM hL hm => by
        rw [Real.rpow_neg_one, ← div_eq_mul_inv]; exact hC A M L m hA hs hM hL hm
  refine ⟨C, fun A M L m hA hs hM hm => ?_⟩
  have := hC A M L m hA hs hM hm
  rwa [Real.rpow_neg_one, ← div_eq_mul_inv] at this

end OscInt.API.GlobalAux
