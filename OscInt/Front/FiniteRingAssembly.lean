/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing

/-!
# Batch FR: the lead's assembly against the blueprint (route `docs/proof-FR.md`)

FR-P from the method of images (FR-S), the light cone (LC-1 at time `2t`) and the bound for a sum over images;
FR-U from FR-K, the datum identity and the energy argument; FC-K from FR-K and evenness; FC-U from FC-K and the
energy argument on the chain; FC-P from FR-P at `x − y` and `x + y` and the light cone at `x + y`. Written after the
stamp of the review answers (`stamps/20261116T225756Z-5792039264f0`) and compiled before any part was proved.
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

/-- **F-line** The line kernel outside the light cone, from LC-1 at time `2t`. -/
theorem lineKernel_norm_le (hLC : LatticeKernel1LightConeStatement) (t η : ℝ) (n : ℤ) (hη : 0 ≤ η) :
    ‖lineKernel t n‖ ≤ Real.exp (2 * |t| * Real.sinh η) * Real.exp (-(|(n : ℝ)| * η)) := by
  have h := hLC (2 * t) η n hη
  have h2 : |2 * t| = 2 * |t| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h2] at h
  have hpi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  unfold lineKernel
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpi]
  calc (2 * Real.pi)⁻¹ * ‖latticeKernel1 (2 * t) (n : ℝ)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * Real.exp (2 * |t| * Real.sinh η - |(n : ℝ)| * η)) := by gcongr
    _ = Real.exp (2 * |t| * Real.sinh η) * Real.exp (-(|(n : ℝ)| * η)) := by
        rw [← Real.exp_add, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul, sub_eq_add_neg]

/-- **FR-P** from the method of images, the light cone and the bound for a sum over images. -/
theorem ringFiniteSize_of (hS : RingCosetSumStatement) (hLC : LatticeKernel1LightConeStatement)
    (hI : ImageSumFacts) : RingFiniteSizeStatement := by
  intro N t η r hN hη
  exact hI (lineKernel t) (Real.exp (2 * |t| * Real.sinh η)) η N r (ringKernel N t r) (Real.exp_pos _).le hη hN
    (fun n => lineKernel_norm_le hLC t η n hη.le) (hS N t r hN)

/-- **FR-U** from FR-K, the datum identity and the energy argument, applied to the difference. -/
theorem ringUnique_of (hK : RingKernelStatement) (hD : RingDatumFacts) (hE : RingEnergyFacts) :
    RingUniqueStatement := by
  intro N u hN hper hder t x
  have key := hE N (fun s z => u s z - ∑ y ∈ Finset.range N, ringKernel N s (z - (y : ℤ)) * u 0 (y : ℤ)) hN ?_ ?_ ?_ t x
  · exact sub_eq_zero.mp key
  · intro s z
    rw [hper s z]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show z + (N : ℤ) - (y : ℤ) = z - (y : ℤ) + (N : ℤ) by ring, (hK N s (z - (y : ℤ)) hN).2.2]
  · intro s z
    have h1 := hder s z
    have h2 : HasDerivAt (fun τ : ℝ => ∑ y ∈ Finset.range N, ringKernel N τ (z - (y : ℤ)) * u 0 (y : ℤ))
        (∑ y ∈ Finset.range N, Complex.I * (ringKernel N s (z - (y : ℤ) + 1) + ringKernel N s (z - (y : ℤ) - 1) -
          2 * ringKernel N s (z - (y : ℤ))) * u 0 (y : ℤ)) s :=
      HasDerivAt.fun_sum fun y _ => ((hK N s (z - (y : ℤ)) hN).1).mul_const (u 0 (y : ℤ))
    convert h1.sub h2 using 1
    simp only [show ∀ y : ℕ, z + 1 - (y : ℤ) = z - (y : ℤ) + 1 from fun y => by ring,
      show ∀ y : ℕ, z - 1 - (y : ℤ) = z - (y : ℤ) - 1 from fun y => by ring]
    simp only [mul_sub, mul_add, Finset.mul_sum, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [mul_assoc]
    ring
  · intro z
    have h0 : ∀ y : ℕ, ringKernel N 0 (z - (y : ℤ)) = if (N : ℤ) ∣ z - (y : ℤ) then 1 else 0 :=
      fun y => (hK N 0 (z - (y : ℤ)) hN).2.1
    simp only [h0]
    rw [hD N (u 0) z hN (hper 0), sub_self]

/-- **FC-K** from FR-K and evenness of the ring kernel. -/
theorem chainKernel_of (hK : RingKernelStatement) (hEv : RingEvenFacts) : ChainKernelStatement := by
  intro M t x y hy1 hyM
  have hN : 0 < 2 * (M + 1) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := (hK (2 * (M + 1)) t (x - y) hN).1
    have h2 := (hK (2 * (M + 1)) t (x + y) hN).1
    simp only [chainKernel]
    rw [show x + 1 - y = x - y + 1 by ring, show x - 1 - y = x - y - 1 by ring,
      show x + 1 + y = x + y + 1 by ring, show x - 1 + y = x + y - 1 by ring]
    convert h1.sub h2 using 1
    ring
  · simp only [chainKernel, zero_sub, zero_add]
    rw [hEv, sub_self]
  · simp only [chainKernel]
    have e : (M : ℤ) + 1 + y = -((M : ℤ) + 1 - y) + ((2 * (M + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e, (hK (2 * (M + 1)) t (-((M : ℤ) + 1 - y)) hN).2.2, hEv, sub_self]
  · intro hx1 hxM
    simp only [chainKernel]
    rw [(hK (2 * (M + 1)) 0 (x - y) hN).2.1, (hK (2 * (M + 1)) 0 (x + y) hN).2.1]
    have hNc : ((2 * (M + 1) : ℕ) : ℤ) = 2 * ((M : ℤ) + 1) := by push_cast; ring
    have hsum : ¬ ((2 * (M + 1) : ℕ) : ℤ) ∣ x + y := by
      intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [hNc, abs_of_pos (by omega)]; omega)
      omega
    simp only [hsum, ite_false, sub_zero]
    by_cases hxy : x = y
    · subst hxy; simp
    · have hdiff : ¬ ((2 * (M + 1) : ℕ) : ℤ) ∣ x - y := by
        intro hd
        have := Int.eq_zero_of_abs_lt_dvd hd (by rw [hNc, abs_lt]; constructor <;> omega)
        omega
      simp only [hdiff, hxy, ite_false]

/-- **FC-U** from FC-K and the energy argument on the chain, applied to the difference. -/
theorem chainUnique_of (hCK : ChainKernelStatement) (hE : ChainEnergyFacts) : ChainUniqueStatement := by
  intro M u hwall hder t x hx1 hxM
  have key := hE M (fun s z => u s z - ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), chainKernel M s z y * u 0 y) ?_ ?_ ?_ t x
    hx1 hxM
  · exact sub_eq_zero.mp key
  · intro s
    constructor
    · rw [(hwall s).1, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun y hy => by
        rw [(hCK M s 0 y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2).2.1, zero_mul]
    · rw [(hwall s).2, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun y hy => by
        rw [(hCK M s 0 y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2).2.2.1, zero_mul]
  · intro s z hz1 hzM
    have h1 := hder s z hz1 hzM
    have h2 : HasDerivAt (fun τ : ℝ => ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), chainKernel M τ z y * u 0 y)
        (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), Complex.I * (chainKernel M s (z + 1) y + chainKernel M s (z - 1) y -
          2 * chainKernel M s z y) * u 0 y) s :=
      HasDerivAt.fun_sum fun y hy =>
        ((hCK M s z y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2).1).mul_const (u 0 y)
    convert h1.sub h2 using 1
    simp only [mul_sub, mul_add, Finset.mul_sum, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [mul_assoc]
    ring
  · intro z hz1 hzM
    have h0 : ∀ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), chainKernel M 0 z y * u 0 y = if z = y then u 0 y else 0 := by
      intro y hy
      rw [(hCK M 0 z y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2).2.2.2 hz1 hzM]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h0, Finset.sum_ite_eq]
    simp only [Finset.mem_Icc, hz1, hzM, and_self, ite_true, sub_self]

/-- **FC-P** from FR-P at `x − y` and `x + y` on the ring of `2(M + 1)` sites and the light cone at `x + y`. -/
theorem chainFiniteSize_of (hP : RingFiniteSizeStatement) (hLC : LatticeKernel1LightConeStatement) :
    ChainFiniteSizeStatement := by
  intro M t η x y hη hx1 hxM hy1 hyM
  have hN : 0 < 2 * (M + 1) := by omega
  have h1 := hP (2 * (M + 1)) t η (x - y) hN hη
  have h2 := hP (2 * (M + 1)) t η (x + y) hN hη
  have h3 := lineKernel_norm_le hLC t η (x + y) hη.le
  have hNc : η * ((2 * (M + 1) : ℕ) : ℝ) = 2 * ((M : ℝ) + 1) * η := by push_cast; ring
  rw [hNc] at h1 h2
  have hpos : |((x + y : ℤ) : ℝ)| = ((x + y : ℤ) : ℝ) := abs_of_pos (by exact_mod_cast (by omega : 0 < x + y))
  rw [hpos] at h3
  have hsplit : chainKernel M t x y - lineKernel t (x - y) =
      (ringKernel (2 * (M + 1)) t (x - y) - lineKernel t (x - y)) -
        (ringKernel (2 * (M + 1)) t (x + y) - lineKernel t (x + y)) - lineKernel t (x + y) := by
    simp only [chainKernel]; ring
  rw [hsplit]
  calc ‖(ringKernel (2 * (M + 1)) t (x - y) - lineKernel t (x - y)) -
        (ringKernel (2 * (M + 1)) t (x + y) - lineKernel t (x + y)) - lineKernel t (x + y)‖
      ≤ ‖ringKernel (2 * (M + 1)) t (x - y) - lineKernel t (x - y)‖ +
          ‖ringKernel (2 * (M + 1)) t (x + y) - lineKernel t (x + y)‖ + ‖lineKernel t (x + y)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 2 * Real.exp (2 * |t| * Real.sinh η) * Real.cosh (((x - y : ℤ) : ℝ) * η) /
            (Real.exp (2 * ((M : ℝ) + 1) * η) - 1) +
          2 * Real.exp (2 * |t| * Real.sinh η) * Real.cosh (((x + y : ℤ) : ℝ) * η) /
            (Real.exp (2 * ((M : ℝ) + 1) * η) - 1) +
          Real.exp (2 * |t| * Real.sinh η) * Real.exp (-(((x + y : ℤ) : ℝ) * η)) := by gcongr
    _ = _ := by ring

end OscInt.FiniteRingAux
