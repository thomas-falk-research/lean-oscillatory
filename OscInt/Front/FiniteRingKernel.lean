/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing
import OscInt.Front.PeriodicAnalyticAlias

/-!
# Batch FR, part FR1: the ring kernel (FR-K) and its evenness in the site variable (F-even)

Route `docs/proof-FR.md`, parts F-kernel and F-even, with the note of the route referee (`N = 0` in F-even).

* `ringKernelStatement_part`: each mode `s ↦ e^{i(2s(cos θ_j − 1) + rθ_j)}` has derivative `i · 2(cos θ_j − 1)` times
  itself, and its second difference in `r` is `2(cos θ_j − 1)` times itself (`e^{iθ} + e^{−iθ} = 2 cos θ`); the datum
  at `t = 0` is the sum of the node phases (`alias_exp_mul_eq_one`, `alias_sum_exp_eq_zero`); the period `N` is
  `e^{2πij} = 1`.
* `ringEvenFacts`: the mode `N − j` at `r` is the mode `j` at `−r` for `j ≤ N`; the sum is re-indexed by
  `Finset.sum_range_reflect` after a shift of the index by one, and the mode `N` is the mode `0`.
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

/-- Adding an integer multiple of `2πi` to the exponent does not change the exponential. -/
theorem ringK_exp_add_int (z : ℂ) (n : ℤ) :
    Complex.exp (z + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = Complex.exp z := by
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The time derivative of one mode `s ↦ e^{i(2sc + d)}` is `i · 2c` times the mode. -/
theorem ringK_mode_hasDerivAt (c d t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((2 * s * c + d : ℝ) : ℂ) * Complex.I))
      (Complex.I * (((2 * c : ℝ) : ℂ) * Complex.exp (((2 * t * c + d : ℝ) : ℂ) * Complex.I))) t := by
  have h0 : HasDerivAt (fun s : ℝ => 2 * s * c + d) (2 * c) t := by
    have h := (((hasDerivAt_id t).const_mul 2).mul_const c).add_const d
    simpa using h
  have h1 : HasDerivAt (fun s : ℝ => ((2 * s * c + d : ℝ) : ℂ) * Complex.I) (((2 * c : ℝ) : ℂ) * Complex.I) t :=
    h0.ofReal_comp.mul_const Complex.I
  have h2 := h1.cexp
  convert h2 using 1
  ring

/-- The second difference in the site variable of one mode: `m(r + 1) + m(r − 1) − 2m(r) = 2(cos θ − 1) m(r)`. -/
theorem ringK_mode_shift (a θ : ℝ) (r : ℤ) :
    Complex.exp (((a + ((r + 1 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) +
        Complex.exp (((a + ((r - 1 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) -
        2 * Complex.exp (((a + (r : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      ((2 * (Real.cos θ - 1) : ℝ) : ℂ) * Complex.exp (((a + (r : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  have e1 : Complex.exp (((a + ((r + 1 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((a + (r : ℝ) * θ : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Complex.exp (((a + ((r - 1 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((a + (r : ℝ) * θ : ℝ) : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc : (2 : ℂ) * Complex.cos (θ : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I) :=
    Complex.two_cos (θ : ℂ)
  have hcast : ((2 * (Real.cos θ - 1) : ℝ) : ℂ) = 2 * Complex.cos (θ : ℂ) - 2 := by
    push_cast
    ring
  rw [e1, e2, hcast, hc]
  ring

/-- FR-K (a): the ring kernel solves the equation in the site variable (for every `N`). -/
theorem ringK_hasDerivAt (N : ℕ) (t : ℝ) (r : ℤ) :
    HasDerivAt (fun s : ℝ => ringKernel N s r)
      (Complex.I * (ringKernel N t (r + 1) + ringKernel N t (r - 1) - 2 * ringKernel N t r)) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.range N) (fun j _ =>
    ringK_mode_hasDerivAt (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1)
      ((r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) t)).const_mul (((N : ℝ) : ℂ)⁻¹)
  simp only [ringKernel]
  convert h using 1
  rw [← mul_add, mul_left_comm 2, ← mul_sub, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
    mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ringK_mode_shift]

/-- FR-K (b): at time `0` the ring kernel is the unit datum of the ring. -/
theorem ringK_zero {N : ℕ} (hN : 0 < N) (r : ℤ) :
    ringKernel N 0 r = (if (N : ℤ) ∣ r then 1 else 0) := by
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr hN.ne')
  have hterm : ∀ j : ℕ,
      Complex.exp (((2 * 0 * (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1) +
        (r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    intro j
    rw [mul_zero, zero_mul, zero_add]
  simp only [ringKernel]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  by_cases hdvd : (N : ℤ) ∣ r
  · rw [ite_eq_left hdvd]
    obtain ⟨m, rfl⟩ := hdvd
    rw [mul_comm (N : ℤ) m, Finset.sum_congr rfl fun j _ => OscInt.PeriodicAnalyticAux.alias_exp_mul_eq_one hN m j,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (by rwa [Complex.ofReal_natCast] at hN')
  · rw [ite_eq_right hdvd, OscInt.PeriodicAnalyticAux.alias_sum_exp_eq_zero hN r hdvd, mul_zero]

/-- FR-K (c): the ring kernel has period `N` in the site variable. -/
theorem ringK_period {N : ℕ} (hN : 0 < N) (t : ℝ) (r : ℤ) :
    ringKernel N t (r + (N : ℤ)) = ringKernel N t r := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [ringKernel]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (congrArg Complex.exp ?_).trans (ringK_exp_add_int _ (j : ℤ))
  push_cast
  field_simp
  ring

/-- The mode `N − j` at the site `r` is the mode `j` at the site `−r`, for `j ≤ N`. -/
theorem ringK_reflect_mode {N : ℕ} (hN : 0 < N) (t : ℝ) (r : ℤ) (j : ℕ) (hj : j ≤ N) :
    Complex.exp (((2 * t * (Real.cos (2 * Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ)) - 1) +
        (r : ℝ) * (2 * Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * t * (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1) +
        ((-r : ℤ) : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hθ : 2 * Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ) = 2 * Real.pi - 2 * Real.pi * (j : ℝ) / (N : ℝ) := by
    rw [Nat.cast_sub hj]
    field_simp
  rw [hθ, Real.cos_two_pi_sub]
  refine (congrArg Complex.exp ?_).trans (ringK_exp_add_int _ r)
  push_cast
  ring

/-- F-even for `0 < N`: the ring kernel is even in the site variable. -/
theorem ringK_even_pos {N : ℕ} (hN : 0 < N) (t : ℝ) (r : ℤ) : ringKernel N t (-r) = ringKernel N t r := by
  have hsum : ∀ F : ℕ → ℂ, F N = F 0 →
      ∑ j ∈ Finset.range N, F (N - j) = ∑ j ∈ Finset.range N, F j := by
    intro F hF
    have h1 : ∑ j ∈ Finset.range N, F (N - j) = ∑ j ∈ Finset.range N, F (N - 1 - j + 1) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < N := Finset.mem_range.mp hj
      congr 1
      omega
    have h2 : ∑ j ∈ Finset.range N, F (N - 1 - j + 1) = ∑ j ∈ Finset.range N, F (j + 1) :=
      Finset.sum_range_reflect (fun i => F (i + 1)) N
    have h3 : ∑ j ∈ Finset.range N, F (j + 1) + F 0 = ∑ j ∈ Finset.range N, F j + F N := by
      rw [← Finset.sum_range_succ' F N, Finset.sum_range_succ F N]
    rw [h1, h2]
    rw [hF] at h3
    exact add_right_cancel h3
  simp only [ringKernel]
  congr 1
  rw [← hsum (fun j : ℕ => Complex.exp (((2 * t * (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1) +
    (r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    exact (ringK_reflect_mode hN t r j (Finset.mem_range.mp hj).le).symm
  · have h := ringK_reflect_mode hN t r 0 (Nat.zero_le N)
    rw [Nat.sub_zero] at h
    rw [h]
    simp

/-- **FR-K** The ring kernel solves the equation, is the unit datum at time `0` and has period `N`. -/
theorem ringKernelStatement_part : RingKernelStatement := by
  intro N t r hN
  exact ⟨ringK_hasDerivAt N t r, ringK_zero hN r, ringK_period hN t r⟩

/-- **F-even** The ring kernel is even in the site variable, for every `N` (both sides are `0` when `N = 0`). -/
theorem ringEvenFacts : RingEvenFacts := by
  intro N t r
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [ringKernel]
  · exact ringK_even_pos hN t r

end OscInt.FiniteRingAux
