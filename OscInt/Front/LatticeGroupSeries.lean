/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeGroupFourierStencil
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Batch LS, part P-series: the kernel as a power series

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `KernelSeriesFacts` from `FourierStencilFacts`, with the complex exponential series.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeSeriesAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup OscInt.LatticeFourierAux MeasureTheory

noncomputable def seriesTerm (d : ℕ) (t : ℝ) (z : Fin d → ℤ) (n : ℕ) (k : Fin d → ℝ) : ℂ :=
  ((Complex.I * t) ^ n / n.factorial) * (symbol d k : ℂ) ^ n * character d z k

theorem symbol_abs_le (d : ℕ) (k : Fin d → ℝ) : |symbol d k| ≤ 4 * d := by
  have hsum : |∑ j, Real.cos (k j)| ≤ (d : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => Real.abs_cos_le_one (k j))
    simpa using h
  unfold symbol
  have h := abs_sub (2 * ∑ j, Real.cos (k j)) (2 * (d : ℝ))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (show 0 ≤ 2 * (d : ℝ) by positivity)] at h
  nlinarith

theorem seriesTerm_norm_le (d : ℕ) (t : ℝ) (z : Fin d → ℤ) (n : ℕ) (k : Fin d → ℝ) :
    ‖seriesTerm d t z n k‖ ≤ (4 * d * |t|) ^ n / n.factorial := by
  have hchar : ‖character d z k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he : ‖seriesTerm d t z n k‖ = (|t| * |symbol d k|) ^ n / n.factorial := by
    simp only [seriesTerm, norm_mul, norm_div, norm_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul, hchar, mul_one, Complex.norm_natCast]
    rw [mul_pow]
    ring
  rw [he]
  have hb : |t| * |symbol d k| ≤ 4 * d * |t| := by
    nlinarith [mul_le_mul_of_nonneg_left (symbol_abs_le d k) (abs_nonneg t)]
  gcongr

theorem seriesTerm_hasSum (d : ℕ) (t : ℝ) (z : Fin d → ℤ) (k : Fin d → ℝ) :
    HasSum (fun n => seriesTerm d t z n k)
      (Complex.exp ((Complex.I * t) * (symbol d k : ℂ)) * character d z k) := by
  -- NormedSpace.expSeries_div_hasSum_exp is over ℂ, then multiplied by the character.
  have h := (NormedSpace.expSeries_div_hasSum_exp ((Complex.I * t) * (symbol d k : ℂ))).mul_right
    (character d z k)
  rw [← Complex.exp_eq_exp_ℂ] at h
  convert h using 1
  funext n
  simp only [seriesTerm, mul_pow]
  ring

theorem seriesTerm_integrable (d : ℕ) (t : ℝ) (z : Fin d → ℤ) (n : ℕ) :
    IntegrableOn (seriesTerm d t z n) (hypercubeBox d) := by
  have h : IntegrableOn (fun k => ((Complex.I * t) ^ n / n.factorial) *
      ((symbol d k : ℂ) ^ n * character d z k)) (hypercubeBox d) :=
    (term_integrable d n z).const_mul _
  convert h using 1
  funext k
  simp only [seriesTerm, mul_assoc]

theorem integral_series_hasSum (d : ℕ) (t : ℝ) (z : Fin d → ℤ) :
    HasSum (fun n => ∫ k in hypercubeBox d, seriesTerm d t z n k)
      (∫ k in hypercubeBox d,
        Complex.exp ((Complex.I * t) * (symbol d k : ℂ)) * character d z k) := by
  let _ : IsFiniteMeasure (volume.restrict (hypercubeBox d)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (box_compact d).measure_lt_top⟩
  -- DCT for series: all hypotheses refer to the restricted box measure.
  refine hasSum_integral_of_dominated_convergence
    (fun n (_ : Fin d → ℝ) => (4 * d * |t|) ^ n / n.factorial)
    (fun n => (seriesTerm_integrable d t z n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (seriesTerm_norm_le d t z n))
    (Filter.Eventually.of_forall fun _ => Real.summable_pow_div_factorial (4 * d * |t|))
    (integrable_const _) (Filter.Eventually.of_forall (seriesTerm_hasSum d t z))

theorem gauge_integrand (d : ℕ) (t : ℝ) (z : Fin d → ℤ) (k : Fin d → ℝ) :
    Complex.exp (↑(-(2 * (d : ℝ) * t)) * Complex.I) *
      Complex.exp (↑(2 * t * ∑ j, Real.cos (k j) + ∑ j, (z j : ℝ) * k j) * Complex.I) =
    Complex.exp ((Complex.I * t) * (symbol d k : ℂ)) * character d z k := by
  -- The gauge -2idt and the argument 2t are both retained before expanding.
  unfold character symbol
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem kernel_integral (d : ℕ) (t : ℝ) (z : Fin d → ℤ) :
    schrodingerKernel d t z = (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
      ∫ k in hypercubeBox d,
        Complex.exp ((Complex.I * t) * (symbol d k : ℂ)) * character d z k := by
  rw [schrodingerKernel, hypercubicKernel, mul_assoc, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (gauge_integrand d t z)

theorem kernelSeries_of (hF : FourierStencilFacts) : KernelSeriesFacts := by
  intro d t z
  have h := (integral_series_hasSum d t z).mul_left (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ)
  rw [← kernel_integral] at h
  convert h using 1
  funext n
  rw [show stencil d n z = coefficient d n z from hF d n z, coefficient]
  change _ = _ * ∫ k in hypercubeBox d, seriesTerm d t z n k
  have hf : (fun k => seriesTerm d t z n k) = fun k =>
      ((Complex.I * t) ^ n / n.factorial) * ((symbol d k : ℂ) ^ n * character d z k) := by
    funext k
    simp only [seriesTerm, mul_assoc]
  rw [hf, integral_const_mul]
  ring

theorem kernelSeriesFacts : KernelSeriesFacts := kernelSeries_of fourierStencilFacts

end OscInt.LatticeSeriesAux
