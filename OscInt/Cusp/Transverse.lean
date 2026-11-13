/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Cusp
import OscInt.StationaryPhase.Local

/-!
# Transverse nonstationary estimate for the cusp assembly

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`.

The proof uses the existing global directional integration-by-parts identity.
The quotient amplitude is globally C¹ because it is locally zero away from its
support. Thus no derivative lower bound outside the support box is needed.
-/

namespace OscInt.Cusp.TransverseAux

open Set MeasureTheory Complex OscInt.Statements
open OscInt.StationaryPhase.LocalAux

/-- Product rule for `A/g`, the directional derivative bound for `A`, and
`inv_bound_arith` bound the new amplitude using only one derivative of `A`. -/
theorem norm_transverse_quotient {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ 1 A) {x : ℝ × ℝ} {phase c D M : ℝ}
    (hgx : g x ≠ 0) (hlow : c ≤ |g x|)
    (hup : |fderiv ℝ g x (0, 1)| ≤ D) (hc : 0 < c)
    (h0 : ‖iteratedFDeriv ℝ 0 A x‖ ≤ M) (h1 : ‖iteratedFDeriv ℝ 1 A x‖ ≤ M) :
    ‖cexp (↑phase * I) * fderiv ℝ (fun y => (g y)⁻¹ • A y) x (0, 1)‖ ≤
      (1 / c + D / c ^ 2) * M := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    fderiv_inv_smul_apply (hg.differentiable (by norm_num) x)
      (hA.differentiable (by norm_num) x) hgx]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_neg, abs_inv, abs_inv, abs_pow, mul_assoc]
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_one] at h1
  refine inv_bound_arith hc hlow (norm_nonneg _) ?_
    (norm_nonneg _) h0 (abs_nonneg _) hup
  have hv : ‖fderiv ℝ A x (0, 1)‖ ≤ ‖fderiv ℝ A x‖ := by
    simpa [Prod.norm_def] using (fderiv ℝ A x).le_opNorm (0, 1)
  exact hv.trans h1

/-- Integrating by parts once in the second coordinate replaces `A` by
`∂₂(A/∂₂Φ)`; compact support removes every boundary contribution. -/
theorem norm_oscInt2_transverse {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) {c D : ℝ} (hc : 0 < c)
    (hlow : ∀ k ∈ K, c ≤ |fderiv ℝ Φ k (0, 1)|)
    (hup : ∀ k ∈ K, |dd Φ k (0, 1) (0, 1)| ≤ D)
    {A : ℝ × ℝ → ℂ} {M m : ℝ} (hA : AmpBound 1 K A M) (hm : 1 ≤ m) :
    ‖oscInt2 (fun k => m * Φ k) A‖ ≤
      (1 / c + D / c ^ 2) * volume.real K * M / m := by
  obtain ⟨hAc, hAs, hAb⟩ := hA
  set g : ℝ × ℝ → ℝ := fun k => fderiv ℝ Φ k (0, 1)
  have hg : ContDiff ℝ 1 g := contDiff_fderiv_apply (n := 1) hΦ (0, 1)
  have hg0 : ∀ x ∈ K, g x ≠ 0 := fun x hx h =>
    (hc.trans_le (hlow x hx)).ne' (by simp [g] at h; simp [h])
  set B : ℝ × ℝ → ℂ := fun x => (g x)⁻¹ • A x
  have hB : ContDiff ℝ 1 B := contDiff_inv_smul hg hAc hg0 hAs
  have hBs : tsupport B ⊆ K := (tsupport_smul_subset_right _ _).trans hAs
  have hBc : HasCompactSupport B := hK.of_isClosed_subset (isClosed_tsupport _) hBs
  have hphase : ContDiff ℝ 1 (fun k => m * Φ k) :=
    contDiff_const.mul (hΦ.of_le (by norm_num))
  have ibp := integral_cexp_phase_mul_fderiv volume hphase hB hBc (0, 1)
  have hfd : ∀ x, fderiv ℝ (fun k => m * Φ k) x (0, 1) = m * g x := fun x => by
    rw [fderiv_const_mul (hΦ.differentiable (by norm_num) x)]; rfl
  have hpt : ∀ x, (cexp (↑(m * Φ x) * I) * (I * ↑(m * g x))) * B x =
      (↑m * I) * (cexp (↑(m * Φ x) * I) * A x) := fun x =>
    cexp_mul_inv_smul_eq m (Φ x) (g x) (A x) fun h0 => by
      by_contra hx
      exact hg0 x (hAs (subset_tsupport _ hx)) h0
  simp only [hfd, hpt, integral_const_mul] at ibp
  have hm0 : (0 : ℝ) < m := by linarith
  have hosc : ‖oscInt2 (fun k => m * Φ k) A‖ * m =
      ‖∫ x, cexp (↑(m * Φ x) * I) * fderiv ℝ B x (0, 1)‖ := by
    rw [ibp, norm_neg, norm_mul, oscInt2, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    ring
  have hbd : ‖∫ x, cexp (↑(m * Φ x) * I) * fderiv ℝ B x (0, 1)‖ ≤
      (1 / c + D / c ^ 2) * volume.real K * M := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ fun h => hx (hBs h)]; simp]
    refine (norm_setIntegral_le_of_norm_le_const (C := (1 / c + D / c ^ 2) * M)
      hK.measure_lt_top fun x hx => ?_).trans_eq (by ring)
    exact norm_transverse_quotient hg hAc (hg0 x hx) (hlow x hx)
      (hup x hx) hc (hAb 0 (by norm_num) x) (hAb 1 (by norm_num) x)
  rw [le_div_iff₀ hm0, hosc]
  exact hbd

end OscInt.Cusp.TransverseAux

namespace OscInt.Cusp

open Set MeasureTheory OscInt.Statements

/-- **A3-P4.** The constant is chosen from the box and the two transverse
derivative bounds before the phase, amplitude, amplitude bound, and frequency. -/
theorem transverseNonStat : OscInt.Blueprint.TransverseNonStatFacts := by
  intro a b c D _ha _hb hc
  refine ⟨(1 / c + D / c ^ 2) * volume.real (Icc (-a) a ×ˢ Icc (-b) b), ?_⟩
  intro Φ A M m hΦ hder hA hm
  exact TransverseAux.norm_oscInt2_transverse (isCompact_Icc.prod isCompact_Icc)
    hΦ hc (fun k hk => (hder k hk).1) (fun k hk => (hder k hk).2) hA hm

end OscInt.Cusp
