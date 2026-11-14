/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import OscInt.Front.HypercubicFinal
import OscInt.Front.HypercubicSanity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Batch LS, part P-bound: the kernel bound from TdE′

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `KernelBoundFacts`, reusing `OscInt.API.hypercubicCubeRoot` (TdE′).

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeKernelBoundAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup MeasureTheory
open scoped ComplexConjugate

theorem box_measure_real (d : ℕ) : volume.real (hypercubeBox d) = (2 * Real.pi) ^ d := by
  -- The existing box-volume lemma fixes the normalization, including d=0.
  rw [measureReal_def, OscInt.API.HypercubicSanity.hypercubeBox_volume,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

theorem hypercubic_norm_trivial (d : ℕ) (s : ℝ) (z : Fin d → ℤ) :
    ‖hypercubicKernel d s z‖ ≤ (2 * Real.pi) ^ d := by
  have hv : volume (hypercubeBox d) < ⊤ := by
    rw [OscInt.API.HypercubicSanity.hypercubeBox_volume]
    finiteness
  -- norm_setIntegral_le_of_norm_le_const requires only finite box volume and |exp(i r)|=1.
  have h := norm_setIntegral_le_of_norm_le_const (f := fun k : Fin d → ℝ =>
    Complex.exp (↑(s * ∑ j, Real.cos (k j) + ∑ j, (z j : ℝ) * k j) * Complex.I))
    (C := 1) hv (fun k _ => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [hypercubicKernel, one_mul, box_measure_real] using h

theorem hypercubic_conjugate (d : ℕ) (s : ℝ) (z : Fin d → ℤ) :
    conj (hypercubicKernel d s z) = hypercubicKernel d (-s) (-z) := by
  -- integral_conj moves conjugation inside, requiring no change of variables.
  rw [hypercubicKernel, hypercubicKernel, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with k
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.neg_apply,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  push_cast
  ring

theorem hypercubic_norm_decay (d : ℕ) (s : ℝ) (z : Fin d → ℤ) (hs : s ≠ 0) :
    ‖hypercubicKernel d s z‖ ≤ (8 * (1 + Real.sqrt 7) / 3) ^ d * |s| ^ (-(d : ℝ) / 3) := by
  rcases lt_or_gt_of_ne hs with hn | hp
  · -- TdE′ is applied at positive time -s and site -z.
    have h := OscInt.API.hypercubicCubeRoot d (-s) (-z) (neg_pos.mpr hn)
    rw [← hypercubic_conjugate] at h
    simpa only [Complex.norm_conj, abs_of_neg hn] using h
  · simpa only [abs_of_pos hp] using OscInt.API.hypercubicCubeRoot d s z hp

theorem schrodinger_norm (d : ℕ) (t : ℝ) (z : Fin d → ℤ) :
    ‖schrodingerKernel d t z‖ = ((2 * Real.pi) ^ d)⁻¹ * ‖hypercubicKernel d (2 * t) z‖ := by
  -- The gauge has norm one; the remaining prefactor is positive and real.
  rw [schrodingerKernel, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem kernelBoundFacts : KernelBoundFacts := by
  intro d t z ht
  rw [schrodinger_norm]
  refine le_min ?_ ?_
  · -- Multiply the trivial kernel bound by the exact inverse volume.
    have h := mul_le_mul_of_nonneg_left (hypercubic_norm_trivial d (2 * t) z)
      (show 0 ≤ ((2 * Real.pi) ^ d)⁻¹ by positivity)
    simpa only [inv_mul_cancel₀ (show (2 * Real.pi) ^ d ≠ 0 by positivity)] using h
  · have h := mul_le_mul_of_nonneg_left
      (hypercubic_norm_decay d (2 * t) z (mul_ne_zero (by norm_num) ht))
      (show 0 ≤ ((2 * Real.pi) ^ d)⁻¹ by positivity)
    -- abs_mul, div_pow and ring normalize the coefficient to the Blueprint spelling.
    convert h using 1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow]
    ring

end OscInt.LatticeKernelBoundAux
