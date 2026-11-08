import OscInt.Front.Local
import Blueprint.Global

/-!
# Batch GD, part GD-P1: local helpers for the global decay assemblies

Route: `docs/proof-GD.md`, R1 (local D4 pieces at a point `k₀`, by translation from FE-S4.1′L), R2 (bumps and the
Leibniz bound for multiplied amplitudes) and R4 (large linear terms are non-critical on a compact set).
-/

namespace OscInt.API.GlobalLocalAux

open OscInt.Statements MeasureTheory
open scoped ContDiff

/-- The translate of a function supported in `B̄(k₀, δ)` is supported in `B̄(0, δ)`. -/
theorem tsupport_translate_subset {A : ℝ × ℝ → ℂ} {k₀ : ℝ × ℝ} {δ : ℝ}
    (hsupp : tsupport A ⊆ Metric.closedBall k₀ δ) :
    tsupport (fun κ => A (k₀ + κ)) ⊆ Metric.closedBall 0 δ := by
  refine closure_minimal (fun κ hκ => ?_) Metric.isClosed_closedBall
  have h : k₀ + κ ∈ Metric.closedBall k₀ δ := hsupp (subset_tsupport _ hκ)
  simpa [Metric.mem_closedBall, dist_eq_norm] using h

/-- The integrand at `k₀ + κ` splits off the unimodular factor `e^{i m L(k₀)}`. -/
theorem integrand_translate (Ψ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ) (k₀ κ : ℝ × ℝ) :
    Complex.exp (↑(m * (Ψ (k₀ + κ) + L (k₀ + κ))) * Complex.I) * A (k₀ + κ) =
      Complex.exp (↑(m * L k₀) * Complex.I) *
        (Complex.exp (↑(m * Ψ (k₀ + κ) + (m • L) κ) * Complex.I) * A (k₀ + κ)) := by
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_add, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Derivative bound for the complexification of a real function. -/
theorem norm_iteratedFDeriv_ofReal_le {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {i : ℕ} (hi : i ≤ 2) (k : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun k => (χ k : ℂ)) k‖ ≤ ‖iteratedFDeriv ℝ i χ k‖ := by
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hχ.contDiffAt (x := k)) (i := i) (by exact_mod_cast hi)
  exact le_of_eq h

end OscInt.API.GlobalLocalAux

namespace OscInt.API.GlobalLocal

open OscInt.Statements OscInt.Blueprint.GD OscInt.API.GlobalLocalAux MeasureTheory
open scoped ContDiff

/-- **R1** Local D4 pieces at a point `k₀`. -/
theorem d4PieceFacts : OscInt.Blueprint.GD.D4PieceFacts := by
  intro Ψ U k₀ hU hk₀ hΨ hD4
  obtain ⟨h2, a, b, c, d, h3, hdisc⟩ := hD4
  have hU₀ : IsOpen ((fun κ => k₀ + κ) ⁻¹' U) := hU.preimage (continuous_const.add continuous_id)
  have h0 : (0 : ℝ × ℝ) ∈ (fun κ => k₀ + κ) ⁻¹' U := by simpa using hk₀
  have hφ : ContDiffOn ℝ 4 (fun κ => Ψ (k₀ + κ)) ((fun κ => k₀ + κ) ⁻¹' U) :=
    hΨ.comp (contDiffOn_const.add contDiffOn_id) (fun x hx => hx)
  have hD : ∀ n, iteratedFDeriv ℝ n (fun κ => Ψ (k₀ + κ)) 0 = iteratedFDeriv ℝ n Ψ k₀ := fun n => by
    rw [iteratedFDeriv_comp_add_left, add_zero]
  obtain ⟨δ, hδ, C, hC⟩ := OscInt.API.d4BoundLocal (fun κ => Ψ (k₀ + κ)) _ a b c d hU₀ h0 hφ
    (by rw [hD]; exact h2) (fun x y => by rw [hD]; exact h3 x y) hdisc
  refine ⟨δ, hδ, C, fun A M L m hA hsupp hM hm => ?_⟩
  have hB : ContDiff ℝ 2 (fun κ => A (k₀ + κ)) := hA.comp (contDiff_const.add contDiff_id)
  have hBM : ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j (fun κ => A (k₀ + κ)) k‖ ≤ M := fun j hj k => by
    rw [iteratedFDeriv_comp_add_left]; exact hM j hj _
  have key := hC (fun κ => A (k₀ + κ)) M (m • L) m hB (tsupport_translate_subset hsupp) hBM hm
  rw [← integral_add_left_eq_self (μ := volume)
    (fun k => Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k) k₀]
  simp only [integrand_translate Ψ A L m k₀]
  rw [integral_const_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact key

/-- **R2a** Smooth bumps. -/
theorem bumpFacts : OscInt.Blueprint.GD.BumpFacts := by
  intro k₀ ρ hρ
  let f : ContDiffBump k₀ := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  have hbd : ∀ j : ℕ, ∃ C : ℝ, ∀ k, ‖iteratedFDeriv ℝ j f k‖ ≤ C := fun j =>
    ((f.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (f.hasCompactSupport.iteratedFDeriv j)
  obtain ⟨C₀, h₀⟩ := hbd 0
  obtain ⟨C₁, h₁⟩ := hbd 1
  obtain ⟨C₂, h₂⟩ := hbd 2
  refine ⟨f, f.contDiff, by rw [f.tsupport_eq], fun k hk => f.one_of_mem_closedBall hk,
    fun k => ⟨f.nonneg, f.le_one⟩, max C₀ (max C₁ C₂), fun j hj k => ?_⟩
  interval_cases j
  · exact (h₀ k).trans (le_max_left _ _)
  · exact (h₁ k).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h₂ k).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **R2b** Leibniz bound for amplitudes multiplied by a bounded `C²` real function. -/
theorem mulBoundFacts : OscInt.Blueprint.GD.MulBoundFacts := by
  intro χ B hχ hB
  refine ⟨4 * max B 0, fun A M hA hM j hj k => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) k)
  have hχC : ContDiff ℝ 2 (fun k => (χ k : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  refine (norm_iteratedFDeriv_mul_le hχC hA k (by exact_mod_cast hj)).trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun k => (χ k : ℂ)) k‖ *
      ‖iteratedFDeriv ℝ (j - i) A k‖ ≤ (j.choose i : ℝ) * (max B 0 * M) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : ‖iteratedFDeriv ℝ i (fun k => (χ k : ℂ)) k‖ ≤ max B 0 :=
      (norm_iteratedFDeriv_ofReal_le hχ (hij.trans hj) k).trans ((hB i (hij.trans hj) k).trans (le_max_left _ _))
    have h2 : ‖iteratedFDeriv ℝ (j - i) A k‖ ≤ M := hM _ (by omega) k
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by exact_mod_cast Nat.sum_range_choose j
  have h4 : (2 : ℝ) ^ j ≤ 4 := by interval_cases j <;> norm_num
  rw [hsum, mul_assoc]
  exact mul_le_mul_of_nonneg_right h4 (mul_nonneg (le_max_right _ _) hM0)

/-- **R4** Large linear terms are non-critical on a compact set. -/
theorem largeLFacts : OscInt.Blueprint.GD.LargeLFacts := by
  intro Ψ K U hK hU hKU hΨ
  have hc : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
  refine ⟨B + 1, fun L hL k hk => ?_⟩
  have h1 := hB k hk
  have h2 := norm_sub_le (fderiv ℝ Ψ k + L) (fderiv ℝ Ψ k)
  rw [add_sub_cancel_left] at h2
  linarith

end OscInt.API.GlobalLocal
