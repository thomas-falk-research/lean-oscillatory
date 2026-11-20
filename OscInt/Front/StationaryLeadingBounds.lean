/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryLeading

/-! # Batch SPL, part assembly-bounds: SPL-S, SPL-K, SPL-A from SPL-I (route `docs/proof-SPL.md`, sections 4 to 6, 10)

By SPL-I, `|R(g, λ)| = λ^{−3/2} |∫ g‴(t) κ(√λ t) dt| ≤ λ^{−3/2} ∫ |g‴(t)| |κ(√λ t)| dt`. SPL-K bounds `|κ|` by `7/8`.
SPL-S is the first-moment argument: if `|κ(√λ t)| ‖g‴‖₁ < ∫ |g‴| |κ(√λ ·)|` for every `t`, integrating against `|g‴|`
forces `g‴ = 0` almost everywhere, a contradiction; `κ` is odd, so `τ = √λ |t₀| ≥ 0`. SPL-A is P-bump with `k = κ`
and SPL-I at `λ = 1`.
-/

namespace OscInt.StationaryLeadingAux

open MeasureTheory OscInt.Statements OscInt.Blueprint.StationaryLeading

/-- For a continuous kernel `k` bounded by `M` and an integrable `f`, `t ↦ f(t) k(r t)` is integrable. -/
theorem splB_integrable_mul_kernel {k f : ℝ → ℂ} {M : ℝ} (hk : Continuous k) (hM : ∀ t, ‖k t‖ ≤ M)
    (hf : Integrable f) (r : ℝ) : Integrable fun t => f t * k (r * t) :=
  hf.mul_bdd (hk.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => hM (r * t))

/-- For a continuous kernel `k` bounded by `M` and an integrable `f`, `t ↦ |f(t)| |k(r t)|` is integrable. -/
theorem splB_integrable_norm_mul_norm {k f : ℝ → ℂ} {M : ℝ} (hk : Continuous k) (hM : ∀ t, ‖k t‖ ≤ M)
    (hf : Integrable f) (r : ℝ) : Integrable fun t => ‖f t‖ * ‖k (r * t)‖ := by
  have h := (splB_integrable_mul_kernel hk hM hf r).norm
  simp only [norm_mul] at h
  exact h

/-- `|∫ f(t) k(r t) dt| ≤ ∫ |f(t)| |k(r t)| dt`. -/
theorem splB_norm_integral_le (k f : ℝ → ℂ) (r : ℝ) :
    ‖∫ t, f t * k (r * t)‖ ≤ ∫ t, ‖f t‖ * ‖k (r * t)‖ := by
  have h := norm_integral_le_integral_norm (μ := volume) fun t => f t * k (r * t)
  simp only [norm_mul] at h
  exact h

/-- From SPL-I: `|R(g, λ)| = λ^{−3/2} |∫ g‴(t) κ(√λ t) dt|`. -/
theorem splB_norm_remainder (hI : StationaryLeadingIdentityStatement) {g g₁ g₂ g₃ : ℝ → ℂ} {lam : ℝ}
    (hg : SplAmplitude g g₁ g₂ g₃) (hlam : 0 < lam) :
    ‖splRemainder g lam‖ = lam ^ (-(3 : ℝ) / 2) * ‖∫ t, g₃ t * splKernel (Real.sqrt lam * t)‖ := by
  rw [hI g g₁ g₂ g₃ lam hg hlam, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hlam.le _)]

/-- From SPL-I: `|R(g, λ)| ≤ λ^{−3/2} ∫ |g‴(t)| |κ(√λ t)| dt`. -/
theorem splB_norm_remainder_le (hI : StationaryLeadingIdentityStatement) {g g₁ g₂ g₃ : ℝ → ℂ} {lam : ℝ}
    (hg : SplAmplitude g g₁ g₂ g₃) (hlam : 0 < lam) :
    ‖splRemainder g lam‖ ≤ lam ^ (-(3 : ℝ) / 2) * ∫ t, ‖g₃ t‖ * ‖splKernel (Real.sqrt lam * t)‖ := by
  rw [splB_norm_remainder hI hg hlam]
  exact mul_le_mul_of_nonneg_left (splB_norm_integral_le splKernel g₃ _) (Real.rpow_nonneg hlam.le _)

/-- An odd kernel has `|k(r |t|)| = |k(r t)|`. -/
theorem splB_norm_kernel_mul_abs {k : ℝ → ℂ} (hodd : ∀ t, k (-t) = -k t) (r t : ℝ) :
    ‖k (r * |t|)‖ = ‖k (r * t)‖ := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h, mul_neg, hodd, norm_neg]

/-- If `f ≥ 0`, `∫ f = N`, `∫ f w = A` and `w(t) N < A` for every `t`, then `f = 0` almost everywhere. -/
theorem splB_ae_zero_of_forall_lt {f w : ℝ → ℝ} {A N : ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf : Integrable f)
    (hfw : Integrable fun t => f t * w t) (hN : ∫ t, f t = N) (hA : ∫ t, f t * w t = A)
    (hcon : ∀ t, w t * N < A) : f =ᵐ[volume] 0 := by
  have hint : Integrable fun t => A * f t - N * (f t * w t) := (hf.const_mul A).sub (hfw.const_mul N)
  have hnn : 0 ≤ fun t => A * f t - N * (f t * w t) := fun t => by
    have h : A * f t - N * (f t * w t) = f t * (A - w t * N) := by ring
    simp only [Pi.zero_apply]
    rw [h]
    exact mul_nonneg (hf0 t) (sub_nonneg.2 (hcon t).le)
  have hzero : ∫ t, (A * f t - N * (f t * w t)) = 0 := by
    rw [integral_sub (hf.const_mul A) (hfw.const_mul N), integral_const_mul, integral_const_mul, hN, hA]
    ring
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hint).1 hzero] with t ht
  have h : f t * (A - w t * N) = 0 := by
    simp only [Pi.zero_apply] at ht
    rw [← ht]
    ring
  rcases mul_eq_zero.1 h with h0 | h0
  · simpa using h0
  · exact absurd h0 (sub_pos.2 (hcon t)).ne'

/-- The first-moment argument: for `f ≥ 0` integrable with `f w` integrable, some `t₀` has `∫ f w ≤ w(t₀) ∫ f`. -/
theorem splB_exists_integral_mul_le {f w : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf : Integrable f)
    (hfw : Integrable fun t => f t * w t) : ∃ t₀, ∫ t, f t * w t ≤ w t₀ * ∫ t, f t := by
  by_contra hcon
  have hlt : ∀ t, w t * ∫ t, f t < ∫ t, f t * w t := fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩
  have hae := splB_ae_zero_of_forall_lt hf0 hf hfw rfl rfl hlt
  have hN : ∫ t, f t = 0 := by
    rw [integral_congr_ae hae]
    simp
  have hA : ∫ t, f t * w t = 0 := by
    have h : (fun t => f t * w t) =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hae] with t ht
      simp only [Pi.zero_apply] at ht
      rw [ht, zero_mul]
    rw [integral_congr_ae h]
    simp
  have h := hlt 0
  rw [hN, hA, mul_zero] at h
  exact lt_irrefl _ h

/-- **SPL-K** from SPL-I and P-kernel: `|R(g, λ)| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}`. -/
theorem stationaryLeadingSevenEighths_of (hI : StationaryLeadingIdentityStatement) (hK : SplKernelFacts) :
    StationaryLeadingSevenEighthsStatement := by
  intro g g₁ g₂ g₃ lam hg hlam
  obtain ⟨-, -, -, -, -, -, hcont, hb⟩ := hK
  have hg3 : Integrable g₃ := hg.2.2.2.2.2.2
  have h2 : ∫ t, ‖g₃ t‖ * ‖splKernel (Real.sqrt lam * t)‖ ≤ ∫ t, ‖g₃ t‖ * (7 / 8 : ℝ) :=
    integral_mono (splB_integrable_norm_mul_norm hcont hb hg3 _) (hg3.norm.mul_const _)
      fun t => mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  rw [integral_mul_const] at h2
  calc ‖splRemainder g lam‖
      ≤ lam ^ (-(3 : ℝ) / 2) * ∫ t, ‖g₃ t‖ * ‖splKernel (Real.sqrt lam * t)‖ := splB_norm_remainder_le hI hg hlam
    _ ≤ lam ^ (-(3 : ℝ) / 2) * ((∫ t, ‖g₃ t‖) * (7 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hlam.le _)
    _ = (7 / 8 : ℝ) * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := by ring

/-- **SPL-A** from SPL-I at `λ = 1`, P-kernel and P-bump with `k = κ`, `M = 7/8`. -/
theorem stationaryLeadingAttained_of (hI : StationaryLeadingIdentityStatement) (hK : SplKernelFacts)
    (hB : SplBumpFacts) : StationaryLeadingAttainedStatement := by
  intro τ ε hτ hε
  obtain ⟨-, -, -, -, -, hodd, hcont, hb⟩ := hK
  obtain ⟨g, g₁, g₂, g₃, hg, hsm, hcs, hne, hle⟩ := hB splKernel (7 / 8) τ ε hcont hodd hb hτ hε
  refine ⟨g, g₁, g₂, g₃, hg, hsm, hcs, hne, ?_⟩
  rw [splB_norm_remainder hI hg one_pos]
  simpa using hle

/-- **SPL-S** from SPL-I and P-kernel: `|R(g, λ)| ≤ |κ(τ)| ‖g‴‖₁ λ^{−3/2}` for some `τ ≥ 0`. -/
theorem stationaryLeading_of (hI : StationaryLeadingIdentityStatement) (hK : SplKernelFacts) :
    StationaryLeadingStatement := by
  intro g g₁ g₂ g₃ lam hg hlam
  obtain ⟨-, -, -, -, -, hodd, hcont, hb⟩ := hK
  have hg3 : Integrable g₃ := hg.2.2.2.2.2.2
  obtain ⟨t₀, ht₀⟩ := splB_exists_integral_mul_le (f := fun t => ‖g₃ t‖)
    (w := fun t => ‖splKernel (Real.sqrt lam * t)‖) (fun t => norm_nonneg _) hg3.norm
    (splB_integrable_norm_mul_norm hcont hb hg3 _)
  refine ⟨Real.sqrt lam * |t₀|, mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  rw [splB_norm_kernel_mul_abs hodd]
  calc ‖splRemainder g lam‖
      ≤ lam ^ (-(3 : ℝ) / 2) * ∫ t, ‖g₃ t‖ * ‖splKernel (Real.sqrt lam * t)‖ := splB_norm_remainder_le hI hg hlam
    _ ≤ lam ^ (-(3 : ℝ) / 2) * (‖splKernel (Real.sqrt lam * t₀)‖ * ∫ t, ‖g₃ t‖) :=
        mul_le_mul_of_nonneg_left ht₀ (Real.rpow_nonneg hlam.le _)
    _ = ‖splKernel (Real.sqrt lam * t₀)‖ * (∫ t, ‖g₃ t‖) * lam ^ (-(3 : ℝ) / 2) := by ring

end OscInt.StationaryLeadingAux
