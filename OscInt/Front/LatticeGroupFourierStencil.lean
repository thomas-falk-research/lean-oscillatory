/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import OscInt.Front.HypercubicFinal
import OscInt.Front.HypercubicSanity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Batch LS, part P-fourier: the Fourier form of the stencils

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `FourierStencilFacts`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeFourierAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup MeasureTheory

noncomputable def symbol (d : ℕ) (k : Fin d → ℝ) : ℝ :=
  2 * ∑ j, Real.cos (k j) - 2 * d

noncomputable def character (d : ℕ) (z : Fin d → ℤ) (k : Fin d → ℝ) : ℂ :=
  Complex.exp (↑(∑ j, (z j : ℝ) * k j) * Complex.I)

noncomputable def coefficient (d n : ℕ) (z : Fin d → ℤ) : ℂ :=
  (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
    ∫ k in hypercubeBox d, (symbol d k : ℂ) ^ n * character d z k

theorem box_compact (d : ℕ) : IsCompact (hypercubeBox d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem term_integrable (d n : ℕ) (z : Fin d → ℤ) :
    IntegrableOn (fun k => (symbol d k : ℂ) ^ n * character d z k) (hypercubeBox d) := by
  -- ContinuousOn.integrableOn_compact, with the actual product box.
  apply ContinuousOn.integrableOn_compact (box_compact d)
  unfold symbol character
  fun_prop

theorem character_add (d : ℕ) (z w : Fin d → ℤ) (k : Fin d → ℝ) :
    character d (z + w) k = character d z k * character d w k := by
  -- Exp of a sum factors; casts and finite sums are linear.
  unfold character
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  push_cast
  ring

theorem character_unit (d : ℕ) (j : Fin d) (k : Fin d → ℝ) :
    character d (latticeUnit d j) k = Complex.exp ((k j : ℂ) * Complex.I) := by
  classical
  simp [character, latticeUnit, Pi.single_apply]

theorem character_neg_unit (d : ℕ) (j : Fin d) (k : Fin d → ℝ) :
    character d (-latticeUnit d j) k = Complex.exp ((-k j : ℂ) * Complex.I) := by
  classical
  simp [character, latticeUnit, Pi.single_apply]

theorem character_pair (r : ℝ) :
    Complex.exp ((r : ℂ) * Complex.I) + Complex.exp ((-r : ℂ) * Complex.I) =
      2 * (Real.cos r : ℂ) := by
  -- Euler's formula is used as an exact identity, not a numerical approximation.
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

theorem character_laplacian (d : ℕ) (z : Fin d → ℤ) (k : Fin d → ℝ) :
    latticeLaplacian d (fun w => character d w k) z =
      (symbol d k : ℂ) * character d z k := by
  unfold latticeLaplacian
  simp_rw [sub_eq_add_neg, character_add, character_unit, character_neg_unit]
  have heach : ∀ j : Fin d,
      character d z k * Complex.exp ((k j : ℂ) * Complex.I) +
      character d z k * Complex.exp ((-k j : ℂ) * Complex.I) + -(2 * character d z k) =
      (2 * (Real.cos (k j) : ℂ) - 2) * character d z k := by
    intro j
    rw [← mul_add, character_pair]
    ring
  simp_rw [heach]
  rw [← Finset.sum_mul]
  congr 1
  simp only [symbol, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring

theorem interval_character (q : ℤ) :
    (∫ x in (-Real.pi)..Real.pi, Complex.exp (↑((q : ℝ) * x) * Complex.I)) =
      if q = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [intervalIntegral.integral_const, two_mul]
  · have hc : (q : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hq) Complex.I_ne_zero
    have he : (fun x : ℝ => Complex.exp (↑((q : ℝ) * x) * Complex.I)) =
        fun x : ℝ => Complex.exp (((q : ℂ) * Complex.I) * x) := by
      funext x
      congr 1
      push_cast
      ring
    rw [he, integral_exp_mul_complex hc, ite_eq_right hq]
    have hp : ((q : ℂ) * Complex.I) * Real.pi = (q : ℂ) * (Real.pi * Complex.I) := by ring
    have hm : ((q : ℂ) * Complex.I) * ↑(-Real.pi) = (q : ℂ) * (-(Real.pi * Complex.I)) := by
      push_cast
      ring
    -- Integer periodicity makes the two endpoint values exactly equal.
    rw [hp, hm, Complex.exp_int_mul, Complex.exp_int_mul,
      Complex.exp_pi_mul_I, Complex.exp_neg_pi_mul_I, sub_self, zero_div]

theorem coefficient_zero (d : ℕ) (z : Fin d → ℤ) :
    coefficient d 0 z = if z = 0 then 1 else 0 := by
  classical
  have hi : (∫ k in hypercubeBox d, character d z k) =
      ∏ j, if z j = 0 then (2 * Real.pi : ℂ) else 0 := by
    have hK := OscInt.API.hypercubicKernelFactor d 0 z
    simpa only [hypercubicKernel, character, zero_mul, zero_add, latticeKernel1,
      interval_character] using hK
  unfold coefficient
  simp only [pow_zero, one_mul, hi]
  by_cases hz : z = 0
  · subst z
    simp only [Pi.zero_apply, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hp : ((2 * Real.pi) ^ d : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hp]
  · rw [ite_eq_right hz]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hprod : (∏ j, if z j = 0 then (2 * Real.pi : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [ite_eq_right hj]
    rw [hprod, mul_zero]

theorem integral_laplacian (d n : ℕ) (z : Fin d → ℤ) :
    (∫ k in hypercubeBox d, (symbol d k : ℂ) ^ n *
      latticeLaplacian d (fun w => character d w k) z) =
      latticeLaplacian d (fun w => ∫ k in hypercubeBox d,
        (symbol d k : ℂ) ^ n * character d w k) z := by
  -- Every finite sum/add/sub exchange is justified by term_integrable.
  unfold latticeLaplacian
  simp_rw [Finset.mul_sum, mul_sub, mul_add]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have hp := term_integrable d n (z + latticeUnit d j)
    have hm := term_integrable d n (z - latticeUnit d j)
    have hz := (term_integrable d n z).const_mul 2
    have hr : (fun k => (symbol d k : ℂ) ^ n * (2 * character d z k)) =
        fun k => 2 * ((symbol d k : ℂ) ^ n * character d z k) := by funext k; ring
    have hz' : IntegrableOn (fun k => (symbol d k : ℂ) ^ n * (2 * character d z k))
        (hypercubeBox d) := by rw [hr]; exact hz
    rw [integral_sub ?_ hz', integral_add hp hm, hr, integral_const_mul]
    exact hp.add hm
  · intro j _
    have hp := term_integrable d n (z + latticeUnit d j)
    have hm := term_integrable d n (z - latticeUnit d j)
    convert ((hp.add hm).sub ((term_integrable d n z).const_mul 2)).integrable using 1
    funext k
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

theorem coefficient_succ (d n : ℕ) (z : Fin d → ℤ) :
    coefficient d (n + 1) z = latticeLaplacian d (coefficient d n) z := by
  have hfun : (fun k => (symbol d k : ℂ) ^ (n + 1) * character d z k) =
      fun k => (symbol d k : ℂ) ^ n * latticeLaplacian d (fun w => character d w k) z := by
    funext k
    rw [character_laplacian, pow_succ]
    ring
  -- Finite linearity commutes the normalization with the lattice Laplacian.
  unfold coefficient
  rw [hfun, integral_laplacian]
  simp only [latticeLaplacian, Finset.mul_sum, mul_add, mul_sub]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourierStencilFacts : FourierStencilFacts := by
  intro d n z
  change stencil d n z = coefficient d n z
  induction n generalizing z with
  | zero => exact (coefficient_zero d z).symm
  | succ n ih =>
      rw [stencil, coefficient_succ]
      unfold latticeLaplacian
      simp_rw [ih]

end OscInt.LatticeFourierAux
