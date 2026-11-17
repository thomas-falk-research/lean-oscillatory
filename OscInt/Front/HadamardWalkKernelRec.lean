/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.HadamardWalk
import OscInt.Front.HadamardWalkSanity

/-!
# Batch HW, part H-rec: the kernel at the times `0`, `1` and its recursion in time

Route `docs/proof-HW.md`, H1 and H2. With `u = e^{−iω(k)}`, `v = e^{iω(k)}` (`u v = 1`) the numerator of the kernel's
amplitude at time `t` is `N_t = u^t − (−1)^t v^t`, and `N_{t+2} = (u − v) N_{t+1} + N_t`. Since
`u − v = −i√2 sin k`, `(u − v) e^{−ixk} = (e^{−i(x+1)k} − e^{−i(x−1)k}) / √2`: the integrand of `K(t + 2, x)` is, at
every `k`, the combination of the integrands of `K(t + 1, x ± 1)` and `K(t, x)`; the recursion follows by linearity
of the interval integral (the integrands are continuous). The times `0` and `1` are the first sanity layer's
`hadamardKernel_zero`, `hadamardKernel_one`.
-/

namespace OscInt.HadamardWalkAux

open OscInt.Statements OscInt.Blueprint.HadamardWalk OscInt.API.HadamardWalkSanity

/-- The integrand of `hadamardKernel t x`, copied from the definition of the kernel. -/
noncomputable def hwRec_integrand (t : ℕ) (x : ℤ) (k : ℝ) : ℂ :=
  (Complex.exp (↑(-((t : ℝ) * hadamardDispersion k)) * Complex.I) -
        (-1 : ℂ) ^ t * Complex.exp (↑((t : ℝ) * hadamardDispersion k) * Complex.I)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ) *
    Complex.exp (↑(-((x : ℝ) * k)) * Complex.I)

/-- The kernel is `(2π)⁻¹` times the integral of `hwRec_integrand` (by definition). -/
theorem hwRec_kernel_eq (t : ℕ) (x : ℤ) :
    hadamardKernel t x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ k in (-Real.pi)..Real.pi, hwRec_integrand t x k := rfl

/-- `e^{−inθ} = (e^{−iθ})^n` for a natural number `n`. -/
theorem hwRec_exp_neg_nat (n : ℕ) (θ : ℝ) :
    Complex.exp (↑(-((n : ℝ) * θ)) * Complex.I) = Complex.exp (↑(-θ) * Complex.I) ^ n := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `e^{inθ} = (e^{iθ})^n` for a natural number `n`. -/
theorem hwRec_exp_nat (n : ℕ) (θ : ℝ) :
    Complex.exp (↑((n : ℝ) * θ) * Complex.I) = Complex.exp (↑θ * Complex.I) ^ n := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `e^{−iθ} e^{iθ} = 1`. -/
theorem hwRec_exp_neg_mul_exp (θ : ℝ) :
    Complex.exp (↑(-θ) * Complex.I) * Complex.exp (↑θ * Complex.I) = 1 := by
  rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul, neg_add_cancel, Complex.exp_zero]

/-- The recursion of the numerators `N_t = u^t − (−1)^t v^t` when `u v = 1`: `N_{t+2} = (u − v) N_{t+1} + N_t`. -/
theorem hwRec_numerator (u v : ℂ) (h : u * v = 1) (t : ℕ) :
    u ^ (t + 2) - (-1 : ℂ) ^ (t + 2) * v ^ (t + 2) =
      (u - v) * (u ^ (t + 1) - (-1 : ℂ) ^ (t + 1) * v ^ (t + 1)) + (u ^ t - (-1 : ℂ) ^ t * v ^ t) := by
  linear_combination (u ^ t - (-1 : ℂ) ^ t * v ^ t) * h

/-- `e^{−i(x+1)k} = e^{−ixk} e^{−ik}` for an integer `x`. -/
theorem hwRec_site_succ (x : ℤ) (k : ℝ) :
    Complex.exp (↑(-(((x + 1 : ℤ) : ℝ) * k)) * Complex.I) =
      Complex.exp (↑(-((x : ℝ) * k)) * Complex.I) * Complex.exp (↑(-k) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e^{−i(x−1)k} = e^{−ixk} e^{ik}` for an integer `x`. -/
theorem hwRec_site_pred (x : ℤ) (k : ℝ) :
    Complex.exp (↑(-(((x - 1 : ℤ) : ℝ) * k)) * Complex.I) =
      Complex.exp (↑(-((x : ℝ) * k)) * Complex.I) * Complex.exp (↑k * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- The shift: `(e^{−iω(k)} − e^{iω(k)}) e^{−ixk} = (e^{−i(x+1)k} − e^{−i(x−1)k}) / √2`. -/
theorem hwRec_shift (x : ℤ) (k : ℝ) :
    (Complex.exp (↑(-hadamardDispersion k) * Complex.I) - Complex.exp (↑(hadamardDispersion k) * Complex.I)) *
        Complex.exp (↑(-((x : ℝ) * k)) * Complex.I) =
      (Complex.exp (↑(-(((x + 1 : ℤ) : ℝ) * k)) * Complex.I) -
        Complex.exp (↑(-(((x - 1 : ℤ) : ℝ) * k)) * Complex.I)) / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt_two_ne_zero
  rw [hwRec_site_succ, hwRec_site_pred, ← mul_sub, exp_neg_sub_exp, exp_neg_sub_exp, sin_hadamardDispersion,
    eq_div_iff h2]
  push_cast
  field_simp

/-- The recursion of the integrands at every `k`. -/
theorem hwRec_integrand_rec (t : ℕ) (x : ℤ) (k : ℝ) :
    hwRec_integrand (t + 2) x k =
      (hwRec_integrand (t + 1) (x + 1) k - hwRec_integrand (t + 1) (x - 1) k) / ((Real.sqrt 2 : ℝ) : ℂ) +
        hwRec_integrand t x k := by
  have hN := hwRec_numerator _ _ (hwRec_exp_neg_mul_exp (hadamardDispersion k)) t
  have hS := hwRec_shift x k
  simp only [hwRec_integrand, hwRec_exp_neg_nat, hwRec_exp_nat]
  rw [hN]
  linear_combination
    ((Complex.exp (↑(-hadamardDispersion k) * Complex.I) ^ (t + 1) -
        (-1 : ℂ) ^ (t + 1) * Complex.exp (↑(hadamardDispersion k) * Complex.I) ^ (t + 1)) /
      ((Real.sqrt (2 * (1 + Real.cos k ^ 2)) : ℝ) : ℂ)) * hS

/-- The dispersion relation is continuous. -/
theorem hwRec_continuous_dispersion : Continuous hadamardDispersion :=
  Real.continuous_arcsin.comp (Real.continuous_sin.div_const _)

/-- The integrand of the kernel is continuous in `k`. -/
theorem hwRec_continuous_integrand (t : ℕ) (x : ℤ) : Continuous (hwRec_integrand t x) := by
  have hω : Continuous hadamardDispersion := hwRec_continuous_dispersion
  unfold hwRec_integrand
  refine Continuous.mul (Continuous.div ?_ ?_ fun k => kernel_denominator_ne_zero k) ?_ <;> fun_prop

/-- The recursion of the kernel in time. -/
theorem hwRec_kernel_rec (t : ℕ) (x : ℤ) :
    hadamardKernel (t + 2) x =
      (hadamardKernel (t + 1) (x + 1) - hadamardKernel (t + 1) (x - 1)) / ((Real.sqrt 2 : ℝ) : ℂ) +
        hadamardKernel t x := by
  have i1 : IntervalIntegrable (hwRec_integrand (t + 1) (x + 1)) MeasureTheory.volume (-Real.pi) Real.pi :=
    (hwRec_continuous_integrand _ _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (hwRec_integrand (t + 1) (x - 1)) MeasureTheory.volume (-Real.pi) Real.pi :=
    (hwRec_continuous_integrand _ _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (hwRec_integrand t x) MeasureTheory.volume (-Real.pi) Real.pi :=
    (hwRec_continuous_integrand _ _).intervalIntegrable _ _
  have e : ∫ k in (-Real.pi)..Real.pi, hwRec_integrand (t + 2) x k =
      ∫ k in (-Real.pi)..Real.pi,
        ((hwRec_integrand (t + 1) (x + 1) k - hwRec_integrand (t + 1) (x - 1) k) / ((Real.sqrt 2 : ℝ) : ℂ) +
          hwRec_integrand t x k) :=
    intervalIntegral.integral_congr fun k _ => hwRec_integrand_rec t x k
  rw [hwRec_kernel_eq, hwRec_kernel_eq, hwRec_kernel_eq, hwRec_kernel_eq, e,
    intervalIntegral.integral_add ((i1.sub i2).div_const _) i3, intervalIntegral.integral_div,
    intervalIntegral.integral_sub i1 i2]
  ring

/-- **H-rec**: the kernel at the times `0` and `1` and its recursion in time. -/
theorem hadamardKernelRecFacts : HadamardKernelRecFacts :=
  ⟨hadamardKernel_zero, hadamardKernel_one, hwRec_kernel_rec⟩

end OscInt.HadamardWalkAux
