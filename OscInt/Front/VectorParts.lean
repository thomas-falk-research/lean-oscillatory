/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Vector

/-!
# Batch VT: the part P-transfer (route `docs/proof-VT.md`)

A bound for every scalar amplitude against `e^{iθ}` holds for every amplitude with values in a complex Banach space `E`
(any universe), by Hahn–Banach and the commutation of a continuous linear functional with the Bochner integral.
-/

namespace OscInt.VectorAux

open OscInt.Statements OscInt.Blueprint MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integrand_continuous (K U : Set (ℝ × ℝ)) (θ : ℝ × ℝ → ℝ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hθ : ContinuousOn θ U) (A : ℝ × ℝ → E) (hA : Continuous A) (hs : tsupport A ⊆ K) :
    Continuous fun k => Complex.exp (↑(θ k) * Complex.I) • A k := by
  rw [continuous_iff_continuousAt]
  intro k
  by_cases hk : k ∈ tsupport A
  · have hc : ContinuousAt θ k := hθ.continuousAt (hU.mem_nhds (hKU (hs hk)))
    exact ((Complex.continuous_exp.continuousAt.comp
      ((Complex.continuous_ofReal.continuousAt.comp hc).mul continuousAt_const))).smul hA.continuousAt
  · have h0 : A =ᶠ[nhds k] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hk
    refine (continuousAt_const (y := (0 : E))).congr ?_
    filter_upwards [h0] with y hy
    simp [hy]

theorem transfer (K U : Set (ℝ × ℝ)) (θ : ℝ × ℝ → ℝ) (B : ℝ → ℝ) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hθ : ContinuousOn θ U)
    (hS : ∀ (A : ℝ × ℝ → ℂ) (M : ℝ), ContDiff ℝ 2 A → tsupport A ⊆ K →
      (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(θ k) * Complex.I) * A k‖ ≤ B M)
    (A : ℝ × ℝ → E) (M : ℝ) (hA : ContDiff ℝ 2 A) (hs : tsupport A ⊆ K)
    (hM : ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) :
    ‖∫ k : ℝ × ℝ, Complex.exp (↑(θ k) * Complex.I) • A k‖ ≤ B M := by
  set f : ℝ × ℝ → E := fun k => Complex.exp (↑(θ k) * Complex.I) • A k
  have hfc : Continuous f := integrand_continuous K U θ hU hKU hθ A hA.continuous hs
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro hK fun k hk => ?_
    have : A k = 0 := image_eq_zero_of_notMem_tsupport (fun h => hk (hs h))
    simp [f, this]
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  obtain ⟨g, hg1, hgv⟩ := exists_dual_vector'' ℂ (∫ k, f k)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)
  set gR : E →L[ℝ] ℂ := g.restrictScalars ℝ
  have hgR : ‖gR‖ ≤ 1 := by rw [ContinuousLinearMap.norm_restrictScalars]; exact hg1
  have hbound := hS (fun k => g (A k)) M (gR.contDiff.comp hA)
    ((tsupport_comp_subset (map_zero g) A).trans hs)
    (fun j hj k => by
      have h1 : iteratedFDeriv ℝ j (fun k => g (A k)) k = iteratedFDeriv ℝ j (gR ∘ A) k := rfl
      rw [h1]
      calc ‖iteratedFDeriv ℝ j (gR ∘ A) k‖ ≤ ‖gR‖ * ‖iteratedFDeriv ℝ j A k‖ :=
            gR.norm_iteratedFDeriv_comp_left hA.contDiffAt (by exact_mod_cast hj)
        _ ≤ 1 * M := mul_le_mul hgR (hM j hj k) (norm_nonneg _) zero_le_one
        _ = M := one_mul M)
  have hcomm : g (∫ k, f k) = ∫ k, Complex.exp (↑(θ k) * Complex.I) * g (A k) := by
    rw [← g.integral_comp_comm hfi]
    congr 1; funext k; simp [f, map_smul, smul_eq_mul]
  calc ‖∫ k, f k‖ = ‖g (∫ k, f k)‖ := by rw [hgv]; simp
    _ = ‖∫ k, Complex.exp (↑(θ k) * Complex.I) * g (A k)‖ := by rw [hcomm]
    _ ≤ B M := hbound

theorem vecTransfer : VecTransferFacts := fun K U θ B hK hU hKU hθ hS _ _ _ _ A M hA hs hM =>
  transfer K U θ B hK hU hKU hθ hS A M hA hs hM

end OscInt.VectorAux
