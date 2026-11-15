/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeGroupStencil
import OscInt.Front.LatticeGroupSeries
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Batch LS, part P-conv: the solution is the convolution with the kernel

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `KernelConvFacts` from `StencilFacts` and `KernelSeriesFacts`; the operator series is over ℂ, as the route revision requires.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeConvAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup OscInt.LatticeStencilAux OscInt.LatticeSeriesAux

noncomputable def seriesCoefficient (t : ℝ) (n : ℕ) : ℂ := (Complex.I * t) ^ n / n.factorial

noncomputable def doubleTerm (d : ℕ) (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ)
    (n : ℕ) (y : Fin d → ℤ) : ℂ := seriesCoefficient t n * (stencil d n (x - y) * f y)

theorem coefficient_norm (t : ℝ) (n : ℕ) :
    ‖seriesCoefficient t n‖ = |t| ^ n / n.factorial := by
  simp only [seriesCoefficient, norm_div, norm_pow, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul, Complex.norm_natCast]

theorem double_row_summable (d : ℕ) (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ) (n : ℕ) :
    Summable (fun y => ‖doubleTerm d f t x n y‖) := by
  simpa only [doubleTerm, norm_mul] using
    (convolution_norm_summable (stencil_l1 d n).1 f x).mul_left ‖seriesCoefficient t n‖

theorem double_row_bound (d : ℕ) (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ) (n : ℕ) :
    ∑' y, ‖doubleTerm d f t x n y‖ ≤ ((4 * d * |t|) ^ n / n.factorial) * ‖f‖ := by
  simp only [doubleTerm, norm_mul (seriesCoefficient t n), tsum_mul_left]
  have hrow := convolution_norm_bound (stencil_l1 d n).1 f x
  have hL := mul_le_mul_of_nonneg_right (stencil_l1 d n).2 (norm_nonneg f)
  have h := mul_le_mul_of_nonneg_left (hrow.trans hL) (norm_nonneg (seriesCoefficient t n))
  refine h.trans_eq ?_
  rw [coefficient_norm, mul_pow]
  ring

theorem double_norm_summable (d : ℕ) (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ) :
    Summable (fun p : ℕ × (Fin d → ℤ) => ‖doubleTerm d f t x p.1 p.2‖) := by
  -- summable_prod_of_nonneg is applied to the norms before exchanging any sums.
  refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨double_row_summable d f t x, ?_⟩
  exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => norm_nonneg _))
    (double_row_bound d f t x) ((Real.summable_pow_div_factorial (4 * d * |t|)).mul_right ‖f‖)

theorem complex_smul_pow (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d) (c : ℂ) (n : ℕ) :
    (c • A) ^ n = c ^ n • A ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- All actions in this induction are complex; no real-scalar tower is requested.
      ext f x
      simp only [pow_succ, ih, mul_apply_eq_comp, smul_apply]
      rw [map_smul]
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring

theorem time_generator (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d) (t : ℝ) :
    t • (Complex.I • A) = (Complex.I * t) • A := by
  -- This is the explicit scalar conversion prescribed by the route referee.
  ext f x
  simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

theorem exp_coordinate_series (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d)
    (f : LatticeL2 d) (t : ℝ) (x : Fin d → ℤ) :
    HasSum (fun n => seriesCoefficient t n * ((A ^ n) f x))
      (NormedSpace.exp (t • (Complex.I • A)) f x) := by
  let ev : (LatticeL2 d →L[ℂ] LatticeL2 d) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : Fin d → ℤ => ℂ) 2 x).comp (ContinuousLinearMap.apply ℂ _ f)
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((Complex.I * t) • A)).mapL ev
  rw [time_generator]
  -- mapL evaluates both the operator and the coordinate, preserving the HasSum limit.
  have hev : ∀ B, ev B = B f x := fun B => rfl
  simp only [hev] at h
  simp only [complex_smul_pow, smul_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at h
  convert h using 1
  funext n
  unfold seriesCoefficient
  ring

theorem kernel_column_hasSum (hK : KernelSeriesFacts) (d : ℕ) (f : LatticeL2 d)
    (t : ℝ) (x y : Fin d → ℤ) :
    HasSum (fun n => doubleTerm d f t x n y) (schrodingerKernel d t (x - y) * f y) := by
  -- P-series is used with its sign, gauge, and lattice subtraction intact.
  simpa only [doubleTerm, seriesCoefficient, mul_assoc] using (hK d t (x - y)).mul_right (f y)

theorem kernel_convolution_summable (hK : KernelSeriesFacts) (d : ℕ) (f : LatticeL2 d)
    (t : ℝ) (x : Fin d → ℤ) :
    Summable (fun y => ‖schrodingerKernel d t (x - y) * f y‖) := by
  have hnorm := double_norm_summable d f t x
  -- The transpose norm sum is summable; its inner norm sum dominates each kernel term.
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_) hnorm.prod_symm.prod
  rw [← (kernel_column_hasSum hK d f t x y).tsum_eq]
  exact norm_tsum_le_tsum_norm (hnorm.prod_symm.prod_factor y)

theorem kernelConv_of (hS : StencilFacts) (hK : KernelSeriesFacts) : KernelConvFacts := by
  intro d A hA f t x
  refine ⟨kernel_convolution_summable hK d f t x, ?_⟩
  have hnorm := double_norm_summable d f t x
  have hdouble : Summable (Function.uncurry (doubleTerm d f t x)) := hnorm.of_norm
  calc NormedSpace.exp (t • (Complex.I • A)) f x =
        ∑' n, seriesCoefficient t n * ((A ^ n) f x) := (exp_coordinate_series d A f t x).tsum_eq.symm
    _ = ∑' n, ∑' y, doubleTerm d f t x n y := by
      apply tsum_congr
      intro n
      rw [((hS d A hA n).2 f x).2, ← tsum_mul_left]
      rfl
    _ = ∑' y, ∑' n, doubleTerm d f t x n y := hdouble.tsum_comm.symm
    _ = ∑' y, schrodingerKernel d t (x - y) * f y :=
      tsum_congr fun y => (kernel_column_hasSum hK d f t x y).tsum_eq

theorem kernelConvFacts : KernelConvFacts := kernelConv_of stencilFacts kernelSeriesFacts

end OscInt.LatticeConvAux
