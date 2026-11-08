/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeKernel
import OscInt.Front.Core

/-!
# T6L: the leading term of the lattice kernel on the diagonal (GD-P4)

Route `docs/proof-GD.md` R9. Unfold the torus integral, cut the weight with a bump at `k₀ = (π/2, π/2)`; the piece
at `k₀` is F2 for `φ(κ) = −sin κ₁ − sin κ₂ + κ₁ + κ₂` after translation, the remainder is non-stationary
(FE-S2.1l with `N = 1`).
-/

namespace OscInt.API.LatticeLimitAux

open OscInt.Statements OscInt.Blueprint.GD OscInt.API.Torus OscInt.API.LatticeKernelAux OscInt.API.GlobalAux
  Filter Topology MeasureTheory
open scoped ContDiff

/-- The lattice symbol. -/
noncomputable def sym (k : ℝ × ℝ) : ℝ := Real.cos k.1 + Real.cos k.2

/-- The diagonal linear term `k₁ + k₂`. -/
noncomputable def diagL : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The D4 point on the diagonal. -/
noncomputable def kpt : ℝ × ℝ := (Real.pi / 2, Real.pi / 2)

/-- The translated phase. -/
noncomputable def ph (κ : ℝ × ℝ) : ℝ := -Real.sin κ.1 - Real.sin κ.2 + κ.1 + κ.2

/-- The integrand `e^{i m (ω + k₁ + k₂)}`. -/
noncomputable def E (m : ℝ) (k : ℝ × ℝ) : ℂ := Complex.exp (↑(m * (sym k + diagL k)) * Complex.I)

theorem diagL_apply (k : ℝ × ℝ) : diagL k = k.1 + k.2 := by simp [diagL]

theorem integrand_eq (n : ℕ) (k : ℝ × ℝ) : latticeIntegrand n ((n : ℤ), (n : ℤ)) k = E n k := by
  unfold latticeIntegrand E
  rw [diagL_apply]
  congr 3
  simp only [sym, Int.cast_natCast]
  ring

theorem kernel_eq (n : ℕ) :
    latticeKernel n ((n : ℤ), (n : ℤ)) = ∫ k : ℝ × ℝ, E n k * (unfoldWeight k : ℂ) := by
  rw [latticeKernel_eq]
  congr 1; ext k
  rw [integrand_eq, mul_comm]

theorem phase_translate (κ : ℝ × ℝ) : sym (kpt + κ) + diagL (kpt + κ) = Real.pi + ph κ := by
  have h := OscInt.API.LatticeSymbol.diagPhaseFacts.2.2.2.2.2 κ
  simp only [sym, diagL_apply, kpt, Prod.fst_add, Prod.snd_add, ph]
  exact h

theorem neg_one_pow_mul_exp (n : ℕ) (x : ℝ) :
    (-1 : ℂ) ^ n * Complex.exp (↑((n : ℝ) * (Real.pi + x)) * Complex.I) =
      Complex.exp (↑((n : ℝ) * x) * Complex.I) := by
  have : (↑((n : ℝ) * (Real.pi + x)) * Complex.I : ℂ) =
      n * (Real.pi * Complex.I) + ↑((n : ℝ) * x) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, ← mul_assoc, ← mul_pow]
  norm_num

/-- The piece at `k₀` after translation. -/
theorem piece_eq (n : ℕ) (A : ℝ × ℝ → ℂ) :
    (-1 : ℂ) ^ n * ∫ k, E n k * A k =
      ∫ κ : ℝ × ℝ, Complex.exp (↑((n : ℝ) * ph κ) * Complex.I) * A (kpt + κ) := by
  rw [← integral_add_left_eq_self (μ := volume) (fun k => E n k * A k) kpt, ← integral_const_mul]
  congr 1; ext κ
  simp only [E, phase_translate]
  rw [← mul_assoc, neg_one_pow_mul_exp]

theorem fderiv_sym_add (k v : ℝ × ℝ) :
    (fderiv ℝ sym k + diagL) v = (1 - Real.sin k.1) * v.1 + (1 - Real.sin k.2) * v.2 := by
  rw [add_apply, show sym = fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2 from rfl,
    OscInt.API.LatticeSymbol.fderiv_latticeSymbol, diagL_apply]
  ring

theorem sin_eq_one_bounded {x : ℝ} (hx : |x| ≤ 4) (h : Real.sin x = 1) : x = Real.pi / 2 := by
  have h2 : Real.cos x ^ 2 = 0 := by
    have := Real.sin_sq_add_cos_sq x
    rw [h] at this; linarith
  rcases OscInt.API.LatticeSymbolAux.cos_eq_zero_bounded hx (pow_eq_zero_iff two_ne_zero |>.mp h2) with e | e
  · exact e
  · rw [e, Real.sin_neg, Real.sin_pi_div_two] at h; norm_num at h

theorem grad_ne_zero {k : ℝ × ℝ} (hk : k ∈ Metric.closedBall (0 : ℝ × ℝ) 4) (hne : k ≠ kpt) :
    fderiv ℝ sym k + diagL ≠ 0 := by
  intro h
  have h1 := fderiv_sym_add k (1, 0)
  have h2 := fderiv_sym_add k (0, 1)
  rw [h] at h1 h2
  simp only [zero_apply, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  rw [mem_closedBall_zero_iff] at hk
  have a1 : |k.1| ≤ 4 := (norm_fst_le k).trans hk
  have a2 : |k.2| ≤ 4 := (norm_snd_le k).trans hk
  exact hne (Prod.ext (sin_eq_one_bounded a1 (by linarith)) (sin_eq_one_bounded a2 (by linarith)))

/-- The compact set off the bump core. -/
theorem isCompact_K₁ (ρ : ℝ) : IsCompact (Metric.closedBall (0 : ℝ × ℝ) 4 ∩ (Metric.ball kpt ρ)ᶜ) :=
  (isCompact_closedBall _ _).inter_right Metric.isOpen_ball.isClosed_compl

theorem grad_lower (ρ : ℝ) (hρ : 0 < ρ) : ∃ c > 0, ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 4 ∩ (Metric.ball kpt ρ)ᶜ,
    c ≤ ‖fderiv ℝ sym k + diagL‖ := by
  rcases (Metric.closedBall (0 : ℝ × ℝ) 4 ∩ (Metric.ball kpt ρ)ᶜ).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  have hs : ContDiff ℝ 2 sym := by unfold sym; fun_prop
  have hcont : Continuous fun k => ‖fderiv ℝ sym k + diagL‖ :=
    ((hs.continuous_fderiv (by norm_num)).add continuous_const).norm
  obtain ⟨k₁, hk₁, hmin⟩ := (isCompact_K₁ ρ).exists_isMinOn hne hcont.continuousOn
  refine ⟨_, norm_pos_iff.mpr (grad_ne_zero hk₁.1 ?_), fun k hk => hmin hk⟩
  rintro rfl; exact hk₁.2 (Metric.mem_ball_self hρ)

/-- The remainder is `O(1/n)`. -/
theorem remainder_bound (ρ : ℝ) (hρ : 0 < ρ) (R : ℝ × ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (hs : tsupport R ⊆ Metric.closedBall 0 4 ∩ (Metric.ball kpt ρ)ᶜ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖∫ k, E n k * R k‖ ≤ C / n := by
  obtain ⟨c, hc, hcK⟩ := grad_lower ρ hρ
  have hR1 : ContDiff ℝ (1 : ℕ) R := hR.of_le (by norm_num)
  obtain ⟨M, -, -, hM⟩ := OscInt.API.ampBoundOfContDiff 1 _ R (isCompact_K₁ ρ) hR1 hs
  obtain ⟨C, hC⟩ := OscInt.API.nonStationaryOn 1 sym _ Set.univ c (isCompact_K₁ ρ) isOpen_univ
    (Set.subset_univ _) (by unfold sym; fun_prop) hc
  refine ⟨C * M, fun n hn => ?_⟩
  have := hC R M diagL n hR1 hs hM hcK (by exact_mod_cast hn)
  simpa [E, pow_one] using this

/-- `n^{2/3} (−1)ⁿ I n → 0` when `‖I n‖ ≤ C/n`. -/
theorem remainder_tendsto (C : ℝ) (I : ℕ → ℂ) (h : ∀ n : ℕ, 1 ≤ n → ‖I n‖ ≤ C / n) :
    Tendsto (fun n : ℕ => (((n : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * (-1 : ℂ) ^ n * I n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc _ ≤ (n : ℝ) ^ ((2 : ℝ) / 3) * (C / n) := mul_le_mul_of_nonneg_left (h n hn) (by positivity)
    _ = _ := by
      rw [show (-(1 / 3 : ℝ)) = 2 / 3 - 1 by norm_num, Real.rpow_sub hn0, Real.rpow_one]; ring

theorem integrable_E (n : ℕ) {A : ℝ × ℝ → ℂ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hA : Continuous A)
    (hs : tsupport A ⊆ K) : Integrable fun k => E n k * A k :=
  integrable_integrand isOpen_univ (by unfold sym; fun_prop : Continuous sym).continuousOn hK (Set.subset_univ _)
    hA hs diagL n

/-- The piece at `k₀`: F2 along the integers. -/
theorem piece_tendsto {δ : ℝ} (hlim : ∀ A : ℝ × ℝ → ℂ, ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ →
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
          ∫ k : ℝ × ℝ, Complex.exp (↑(t * ph k) * Complex.I) * A k) atTop
        (𝓝 ((d4ClosedConstant (-1 / 48) : ℂ) * A 0)))
    (P : ℝ × ℝ → ℂ) (hP : ContDiff ℝ 2 P) (hs : tsupport P ⊆ Metric.closedBall kpt δ) (h0 : P kpt = 1) :
    Tendsto (fun n : ℕ => (((n : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * ((-1 : ℂ) ^ n * ∫ k, E n k * P k)) atTop
      (𝓝 (d4ClosedConstant (-1 / 48) : ℂ)) := by
  have hB : ContDiff ℝ 2 (fun κ => P (kpt + κ)) := hP.comp (contDiff_const.add contDiff_id)
  have := (hlim _ hB (OscInt.API.GlobalLocalAux.tsupport_translate_subset hs)).comp tendsto_natCast_atTop_atTop
  rw [add_zero, h0, mul_one] at this
  refine this.congr fun n => ?_
  simp only [Function.comp, piece_eq]

/-- The bump piece and the remainder of the weight. -/
theorem cut_supports {δ : ℝ} {χ : ℝ × ℝ → ℝ} (hχs : tsupport χ ⊆ Metric.closedBall kpt δ)
    (hχ1 : ∀ k ∈ Metric.closedBall kpt (δ / 2), χ k = 1) {η : ℝ × ℝ → ℂ}
    (hηs : tsupport η ⊆ Metric.closedBall 0 4) :
    tsupport (fun k => (χ k : ℂ) * η k) ⊆ Metric.closedBall kpt δ ∧
      tsupport (fun k => η k - (χ k : ℂ) * η k) ⊆ Metric.closedBall 0 4 ∩ (Metric.ball kpt (δ / 2))ᶜ := by
  refine ⟨tsupport_mul_subset_left.trans (by
    intro x hx; exact hχs (by simpa [tsupport, Function.support] using hx)), ?_⟩
  apply closure_minimal _ (Metric.isClosed_closedBall.inter Metric.isOpen_ball.isClosed_compl)
  intro x hx
  refine ⟨hηs (subset_tsupport _ fun h => hx (by simp [h])), fun hb => hx ?_⟩
  simp [hχ1 x (Metric.ball_subset_closedBall (Metric.mem_ball.mpr (Metric.mem_ball.mp hb)))]

/-- **T6L** (`LatticeLaplacianLimitStatement`). -/
theorem latticeLaplacianLimit_proof : OscInt.Statements.LatticeLaplacianLimitStatement := by
  obtain ⟨hφ, h0, h1, h2, hdisc, -⟩ := OscInt.API.LatticeSymbol.diagPhaseFacts
  obtain ⟨δ, hδ, hlim⟩ := OscInt.API.d4LimitClosedForm _ hφ h0 h1 h2 (by rw [hdisc]; norm_num)
  rw [hdisc] at hlim
  obtain ⟨χ, hχ, hχs, hχ1, -, -, -⟩ := OscInt.API.GlobalLocal.bumpFacts kpt δ hδ
  obtain ⟨-, hη, hηs, -⟩ := weight_amp
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hP : ContDiff ℝ 2 fun k => (χ k : ℂ) * (unfoldWeight k : ℂ) :=
    (Complex.ofRealCLM.contDiff.comp hχ2).mul hη
  obtain ⟨hPs, hRs⟩ := cut_supports hχs hχ1 hηs
  have hP0 : (χ kpt : ℂ) * (unfoldWeight kpt : ℂ) = 1 := by
    rw [hχ1 kpt (Metric.mem_closedBall_self (half_pos hδ).le), kpt, unfoldWeight_pi_div_two]; simp
  obtain ⟨C, hC⟩ := remainder_bound (δ / 2) (half_pos hδ) _ (hη.sub hP) hRs
  have hT := (piece_tendsto hlim _ hP hPs hP0).add (remainder_tendsto C _ hC)
  rw [add_zero] at hT
  refine hT.congr fun n => ?_
  have hI0 := integrable_E n (isCompact_closedBall kpt δ) hP.continuous hPs
  have hI1 := integrable_E n (isCompact_K₁ (δ / 2)) (hη.sub hP).continuous hRs
  rw [kernel_eq, show (fun k => E n k * (unfoldWeight k : ℂ)) = fun k => E n k * ((χ k : ℂ) * (unfoldWeight k : ℂ))
      + E n k * ((unfoldWeight k : ℂ) - (χ k : ℂ) * (unfoldWeight k : ℂ)) from
    funext (cut_split χ (fun k => (unfoldWeight k : ℂ)) (E n)), integral_add hI0 hI1]
  ring

end OscInt.API.LatticeLimitAux
