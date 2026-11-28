/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay

/-!
# Batch K2: the lead's assemblies against the blueprint interfaces

Route `docs/proof-K2.md` (sections 3, 4 and 8). Written after the answers to the blind pre-proof reviews were stamped
(`stamps/20261128T023440Z-e368c37563ab`) and the route referee was answered.

* `monomialAsymptotic_of`: K2-MA from P10a and P10b.
* `monomialLower_of`: K2-ML from K2-MA (the threshold is exactly `4/(m t r^{m−1}) ≤ t^{−1/m}/(24m)`).
* `torusLocalization_of`: K2-F from P13 and P14.
-/

namespace OscInt.K2.AssemblyAux

open OscInt.Statements OscInt.Blueprint.K2 Filter Topology MeasureTheory
open scoped ContDiff

/-- The threshold of K2-ML turns the remainder of K2-MA into half of the leading term's lower bound. -/
theorem remainder_le_of_threshold {m : ℕ} {r t : ℝ} (hm : 2 ≤ m) (hr : 0 < r) (ht : 0 < t)
    (hth : 96 * r ^ (1 - (m : ℝ)) ≤ t ^ (1 - 1 / (m : ℝ))) :
    4 / ((m : ℝ) * t * r ^ (m - 1)) ≤ t ^ (-(1 : ℝ) / (m : ℝ)) / (24 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrm : 0 < r ^ (m - 1) := pow_pos hr _
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
  have h1 : r ^ (1 - (m : ℝ)) = (r ^ (m - 1))⁻¹ := by
    rw [← Real.rpow_natCast, hcast, ← Real.rpow_neg hr.le]; ring_nf
  have h2 : t ^ (1 - 1 / (m : ℝ)) = t * t ^ (-(1 : ℝ) / (m : ℝ)) := by
    rw [show (1 - 1 / (m : ℝ)) = 1 + (-(1 : ℝ) / (m : ℝ)) by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h1, h2] at hth
  have htm : 0 < t ^ (-(1 : ℝ) / (m : ℝ)) := Real.rpow_pos_of_pos ht _
  -- `96 / r^(m-1) ≤ t · t^(-1/m)`
  have key : 96 ≤ t * t ^ (-(1 : ℝ) / (m : ℝ)) * r ^ (m - 1) := by
    have := mul_le_mul_of_nonneg_right hth hrm.le
    rwa [mul_assoc, inv_mul_cancel₀ hrm.ne', mul_one] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [key]

end OscInt.K2.AssemblyAux

namespace OscInt.K2

open OscInt.Statements OscInt.Blueprint.K2 Filter Topology MeasureTheory AssemblyAux
open scoped ContDiff

/-- **K2-MA** from the two halves P10a and P10b. -/
theorem monomialAsymptotic_of (hP : MonomialPositivityFacts) (hT : MonomialTailFacts) :
    MonomialAsymptoticStatement := by
  intro m σ hm hσ
  obtain ⟨C, hre, hlim⟩ := hP m σ hm hσ
  exact ⟨C, hre, hlim, fun b r t hb ht => hT m σ C b r t hm hσ hlim hb ht⟩

/-- **K2-ML** from K2-MA. -/
theorem monomialLower_of (h : MonomialAsymptoticStatement) : MonomialLowerStatement := by
  intro m σ b r t hm hσ hb ht hth
  obtain ⟨C, hre, -, hbound⟩ := h m σ hm hσ
  have hr : 0 < r := hb.2.2.1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrem := remainder_le_of_threshold hm hr ht hth
  have hb' := hbound b r t hb ht
  set I : ℂ := ∫ x : ℝ, (b x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)
  set s : ℝ := t ^ (-(1 : ℝ) / (m : ℝ))
  have hs : 0 < s := Real.rpow_pos_of_pos ht _
  -- `‖s C‖ ≥ s Re C ≥ s/(12m)`
  have hsC : s / (12 * (m : ℝ)) ≤ ‖((s : ℝ) : ℂ) * C‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hC : C.re ≤ ‖C‖ := Complex.re_le_norm C
    have : s / (12 * (m : ℝ)) = s * (1 / (12 * (m : ℝ))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (hre.trans hC) hs.le
  have htri : ‖((s : ℝ) : ℂ) * C‖ ≤ ‖I‖ + ‖I - ((s : ℝ) : ℂ) * C‖ := by
    have := norm_sub_le I (I - ((s : ℝ) : ℂ) * C)
    simpa using this
  have : s / (12 * (m : ℝ)) - s / (24 * (m : ℝ)) = s / (24 * (m : ℝ)) := by field_simp; ring
  linarith

/-- **K2-F** from P13 (summable coefficients, uniformly in the offset) and P14 (the torus expansion). With
`n = ⌊t p⌋` and `δ = t p − n ∈ [0, 1)²`, the localised integral is `Σ_j (4π²)⁻¹ c_j(δ) K(t, n + j)`. -/
theorem torusLocalization_of (h13 : FourierDecayFacts) (h14 : TorusExpansionFacts) :
    TorusLocalizationStatement := by
  intro χ hχ hsupp
  obtain ⟨S, hS⟩ := h13 χ hχ hsupp
  refine ⟨(4 * Real.pi ^ 2 : ℝ)⁻¹ * S, ?_⟩
  intro Ψ t p B hΨ hper1 hper2 hB
  set n : ℤ × ℤ := (⌊t * p.1⌋, ⌊t * p.2⌋) with hn
  set δ : ℝ × ℝ := (Int.fract (t * p.1), Int.fract (t * p.2)) with hδ
  have hδmem : δ ∈ Set.Icc (0 : ℝ × ℝ) 1 := by
    refine ⟨⟨Int.fract_nonneg _, Int.fract_nonneg _⟩, ⟨(Int.fract_lt_one _).le, (Int.fract_lt_one _).le⟩⟩
  obtain ⟨hsum, hle⟩ := hS δ hδmem
  set c : ℤ × ℤ → ℂ := fun j => ∫ k in torusBox, χ k *
    Complex.exp (↑((δ.1 - j.1) * k.1 + (δ.2 - j.2) * k.2) * Complex.I) with hc
  set g : ℝ × ℝ → ℂ := fun k =>
    Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  have hexp := h14 χ hχ hsupp δ hsum g hgc
  -- the localised integral is the expanded one
  have hloc : (∫ k in torusBox, χ k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)) =
      ∫ k in torusBox, χ k * Complex.exp (↑(δ.1 * k.1 + δ.2 * k.2) * Complex.I) * g k := by
    congr 1; funext k
    have hr : t * (Ψ k + lin p k) =
        (δ.1 * k.1 + δ.2 * k.2) + (t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) := by
      have h1 : t * p.1 = (⌊t * p.1⌋ : ℝ) + Int.fract (t * p.1) := (Int.floor_add_fract _).symm
      have h2 : t * p.2 = (⌊t * p.2⌋ : ℝ) + Int.fract (t * p.2) := (Int.floor_add_fract _).symm
      simp only [hδ, hn, lin]
      linear_combination k.1 * h1 + k.2 * h2
    simp only [hg]
    rw [hr, Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]
  -- each lattice integral is a coefficient of `e^{itΨ}` at `n + j`
  have hK : ∀ j : ℤ × ℤ, ‖∫ k in torusBox,
      Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k‖ ≤ B := by
    intro j
    have := hB (n.1 + j.1, n.2 + j.2)
    convert this using 3
    funext k
    simp only [hg]
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hK 0)
  set f : ℤ × ℤ → ℂ := fun j => ((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ) * c j *
    ∫ k in torusBox, Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k with hf
  have hfle : ∀ j, ‖f j‖ ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := by
    intro j
    simp only [hf, norm_mul]
    have h4 : ‖((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℂ)‖ = (4 * Real.pi ^ 2 : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h4]
    have := hK j
    have hc0 : 0 ≤ ‖c j‖ := norm_nonneg _
    have hpi : 0 ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ := by positivity
    calc (4 * Real.pi ^ 2 : ℝ)⁻¹ * ‖c j‖ * ‖∫ k in torusBox,
          Complex.exp (↑((j.1 : ℝ) * k.1 + (j.2 : ℝ) * k.2) * Complex.I) * g k‖
        ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * ‖c j‖ * B := by gcongr
      _ = (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := by ring
  have hsumf : Summable (fun j => ‖f j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hfle (hsum.mul_left _)
  rw [hloc, ← hexp.tsum_eq]
  calc ‖∑' j, f j‖ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hsumf
    _ ≤ ∑' j, (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ‖c j‖ := hsumf.tsum_le_tsum hfle (hsum.mul_left _)
    _ = (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * ∑' j, ‖c j‖ := tsum_mul_left
    _ ≤ (4 * Real.pi ^ 2 : ℝ)⁻¹ * B * S := by gcongr
    _ = (4 * Real.pi ^ 2 : ℝ)⁻¹ * S * B := by ring

end OscInt.K2
