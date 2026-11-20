/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.PeriodicAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Batch PA, part P-shift: the contour shift (route `docs/proof-PA.md`)

Cauchy's theorem on the rectangle with corners `0` and `2π + ib`, `|b| < a`, for `g z = v z * exp (-(k z) i)`; the two
vertical sides cancel because `g` is `2π`-periodic on the strip.
-/

namespace OscInt.PeriodicAnalyticAux

open OscInt.Statements OscInt.Blueprint.PeriodicAnalytic

/-- A point whose imaginary part lies between `0` and `b`, with `|b| < a`, is in the open strip of half-width `a`. -/
theorem contourShift_mem_openStrip {a b : ℝ} (hb : |b| < a) {z : ℂ} (hz : z.im ∈ Set.uIcc (0 : ℝ) b) :
    z ∈ openStrip a := by
  have h : |z.im - 0| ≤ |b - 0| := Set.abs_sub_left_of_mem_uIcc hz
  rw [sub_zero, sub_zero] at h
  exact lt_of_le_of_lt h hb

/-- The closed rectangle with corners `0` and `2π + ib` lies in the open strip when `|b| < a`. -/
theorem contourShift_rect_subset {a b : ℝ} (hb : |b| < a) :
    (Set.uIcc (0 : ℝ) (2 * Real.pi) ×ℂ Set.uIcc (0 : ℝ) b) ⊆ openStrip a :=
  fun _ hz => contourShift_mem_openStrip hb hz.2

/-- Cauchy on the rectangle for a function holomorphic and `2π`-periodic on the strip: the integral over `[0, 2π]`
is the same at height `0` and at height `b`. -/
theorem contourShift_of_periodic (g : ℂ → ℂ) {a b : ℝ} (hb : |b| < a)
    (hg : DifferentiableOn ℂ g (openStrip a))
    (hper : ∀ z ∈ openStrip a, g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), g (θ : ℂ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g ((θ : ℂ) + (b : ℂ) * Complex.I) := by
  have hre : (((2 * Real.pi : ℝ) : ℂ) + (b : ℂ) * Complex.I).re = 2 * Real.pi := by simp
  have him : (((2 * Real.pi : ℝ) : ℂ) + (b : ℂ) * Complex.I).im = b := by simp
  have hD : DifferentiableOn ℂ g
      (Set.uIcc (0 : ℂ).re (((2 * Real.pi : ℝ) : ℂ) + (b : ℂ) * Complex.I).re ×ℂ
        Set.uIcc (0 : ℂ).im (((2 * Real.pi : ℝ) : ℂ) + (b : ℂ) * Complex.I).im) := by
    rw [hre, him, Complex.zero_re, Complex.zero_im]
    exact hg.mono (contourShift_rect_subset hb)
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0
    (((2 * Real.pi : ℝ) : ℂ) + (b : ℂ) * Complex.I) hD
  rw [hre, him, Complex.zero_re, Complex.zero_im] at H
  have hside : ∫ y in (0 : ℝ)..b, g (((2 * Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y in (0 : ℝ)..b, g (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hmem : (y : ℂ) * Complex.I ∈ openStrip a :=
      contourShift_mem_openStrip hb (by simpa using hy)
    show g (((2 * Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I) = g (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
    rw [Complex.ofReal_zero, zero_add, add_comm]
    exact hper _ hmem
  rw [hside, add_sub_cancel_right, sub_eq_zero] at H
  simpa using H

/-- The integrand `v z * exp (-(k z) i)` is holomorphic on the strip. -/
theorem contourShift_differentiableOn {v : ℂ → ℂ} {a : ℝ} (k : ℤ)
    (hv : DifferentiableOn ℂ v (openStrip a)) :
    DifferentiableOn ℂ (fun z : ℂ => v z * Complex.exp (-((k : ℂ) * z) * Complex.I)) (openStrip a) :=
  hv.mul (by fun_prop)

/-- The exponential factor `exp (-(k z) i)` has period `2π` for an integer `k`. -/
theorem contourShift_exp_periodic (k : ℤ) (z : ℂ) :
    Complex.exp (-((k : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ))) * Complex.I) =
      Complex.exp (-((k : ℂ) * z) * Complex.I) := by
  have h : -((k : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ))) * Complex.I =
      -((k : ℂ) * z) * Complex.I - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- **P-shift** The Fourier integral of a periodic-analytic function is unchanged when the contour moves to height
`b`, `|b| < a`. -/
theorem contourShiftFacts : ContourShiftFacts := by
  intro v a M b k hv hb
  have key := contourShift_of_periodic (fun z : ℂ => v z * Complex.exp (-((k : ℂ) * z) * Complex.I)) hb
    (contourShift_differentiableOn k hv.1)
    (fun z hz => by
      show v (z + ((2 * Real.pi : ℝ) : ℂ)) *
          Complex.exp (-((k : ℂ) * (z + ((2 * Real.pi : ℝ) : ℂ))) * Complex.I) =
        v z * Complex.exp (-((k : ℂ) * z) * Complex.I)
      rw [hv.2.1 z hz, contourShift_exp_periodic])
  have hleft : ∀ θ : ℝ, v (θ : ℂ) * Complex.exp (↑(-((k : ℝ) * θ)) * Complex.I) =
      v (θ : ℂ) * Complex.exp (-((k : ℂ) * (θ : ℂ)) * Complex.I) := by
    intro θ
    rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_intCast]
  simp_rw [hleft]
  exact key

end OscInt.PeriodicAnalyticAux
