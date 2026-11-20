/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Batch FR, part FR4: the datum identity and the energy argument on the ring (route `docs/proof-FR.md`, F-unique)

`ringDatumFacts`: over one period `y < N` exactly one `y` has `N ∣ x − y`, the residue of `x`, and a function of
period `N` takes the same value at `x` and at its residue.
`ringEnergyFacts`: the energy `Σ_{x<N} conj(w_x) w_x` of a solution of period `N` has derivative `0` (the sum over a
period of `F(x) − F(x + 1)` with `F(z) = conj(w_z) w_{z−1} − w_z conj(w_{z−1})`), so it is constant, hence `0`
for a solution whose datum at `t = 0` is `0` (the premise of the proposition).
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

/-- A function of period `N` is unchanged by adding any integer multiple of `N`. -/
theorem ringE_add_mul (N : ℕ) (f : ℤ → ℂ) (hf : ∀ z : ℤ, f (z + (N : ℤ)) = f z) (z k : ℤ) :
    f (z + k * (N : ℤ)) = f z := by
  induction k using Int.induction_on with
  | zero => rw [zero_mul, add_zero]
  | succ k ih => rw [show z + ((k : ℤ) + 1) * (N : ℤ) = z + (k : ℤ) * (N : ℤ) + (N : ℤ) by ring, hf, ih]
  | pred k ih =>
    have h := hf (z + (-(k : ℤ) - 1) * (N : ℤ))
    rw [show z + (-(k : ℤ) - 1) * (N : ℤ) + (N : ℤ) = z + -(k : ℤ) * (N : ℤ) by ring, ih] at h
    exact h.symm

/-- A function of period `N` takes the same value at `x` and at the residue `x % N`. -/
theorem ringE_emod (N : ℕ) (f : ℤ → ℂ) (hf : ∀ z : ℤ, f (z + (N : ℤ)) = f z) (x : ℤ) :
    f (x % (N : ℤ)) = f x := by
  have h := ringE_add_mul N f hf (x % (N : ℤ)) (x / (N : ℤ))
  rw [mul_comm, Int.emod_add_mul_ediv x (N : ℤ)] at h
  exact h.symm

/-- For `0 < N` the residue `x % N` is the cast of a natural number below `N`. -/
theorem ringE_residue (N : ℕ) (hN : 0 < N) (x : ℤ) : ∃ y ∈ Finset.range N, (y : ℤ) = x % (N : ℤ) := by
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have h0 : 0 ≤ x % (N : ℤ) := Int.emod_nonneg x hNz.ne'
  have h1 : x % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos x hNz
  refine ⟨(x % (N : ℤ)).toNat, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg h0⟩
  have h2 : ((x % (N : ℤ)).toNat : ℤ) < (N : ℤ) := by rw [Int.toNat_of_nonneg h0]; exact h1
  exact_mod_cast h2

/-- **F-datum** The indicator of `N ∣ x − y` summed against a function of period `N` over one period. -/
theorem ringDatumFacts : RingDatumFacts := by
  intro N f x hN hf
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  obtain ⟨y₀, hy₀, hyx⟩ := ringE_residue N hN x
  rw [Finset.sum_eq_single y₀]
  · have hd : (N : ℤ) ∣ x - (y₀ : ℤ) := by
      rw [hyx]
      exact Int.dvd_self_sub_of_emod_eq rfl
    rw [ite_eq_left hd, one_mul, hyx]
    exact ringE_emod N f hf x
  · intro y hy hne
    have hnd : ¬ (N : ℤ) ∣ x - (y : ℤ) := by
      rintro ⟨c, hc⟩
      apply hne
      have hx : x = (y : ℤ) + (N : ℤ) * c := by rw [← hc]; ring
      have hylt : (y : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.mp hy
      have hy0 : (0 : ℤ) ≤ (y : ℤ) := Int.natCast_nonneg y
      have h3 : x % (N : ℤ) = (y : ℤ) := by
        rw [hx, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hy0 hylt]
      have h4 : (y : ℤ) = (y₀ : ℤ) := by rw [hyx, h3]
      exact_mod_cast h4
    rw [ite_eq_right hnd, zero_mul]
  · intro h
    exact absurd hy₀ h

/-- Shift of the summation index by one over a full period. -/
theorem ringE_shift (N : ℕ) (F : ℤ → ℂ) (hF : ∀ z : ℤ, F (z + (N : ℤ)) = F z) :
    ∑ x ∈ Finset.range N, F ((x : ℤ) + 1) = ∑ x ∈ Finset.range N, F (x : ℤ) := by
  have h1 := Finset.sum_range_succ (fun k : ℕ => F (k : ℤ)) N
  have h2 := Finset.sum_range_succ' (fun k : ℕ => F (k : ℤ)) N
  have h3 : F (N : ℤ) = F ((0 : ℕ) : ℤ) := by
    have h := hF 0
    rw [zero_add] at h
    rw [h, Nat.cast_zero]
  simp only [Nat.cast_add, Nat.cast_one] at h2
  rw [h1, h3] at h2
  exact (add_right_cancel h2).symm

/-- The energy `Σ_{x<N} conj(w_x) w_x` of a solution of period `N` has derivative `0` at every time. -/
theorem ringE_hasDerivAt (N : ℕ) (w : ℝ → ℤ → ℂ)
    (hper : ∀ (t : ℝ) (x : ℤ), w t (x + (N : ℤ)) = w t x)
    (hder : ∀ (t : ℝ) (x : ℤ),
      HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ x ∈ Finset.range N, star (w s (x : ℤ)) * w s (x : ℤ)) 0 t := by
  have h : ∀ x ∈ Finset.range N, HasDerivAt (fun s : ℝ => star (w s (x : ℤ)) * w s (x : ℤ))
      (star (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ))) * w t (x : ℤ) +
        star (w t (x : ℤ)) * (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ)))) t :=
    fun x _ => (hder t (x : ℤ)).star.mul (hder t (x : ℤ))
  have hsum := HasDerivAt.fun_sum h
  have hF : ∀ z : ℤ, star (w t (z + (N : ℤ))) * w t (z + (N : ℤ) - 1) -
      w t (z + (N : ℤ)) * star (w t (z + (N : ℤ) - 1))
      = star (w t z) * w t (z - 1) - w t z * star (w t (z - 1)) := by
    intro z
    rw [show z + (N : ℤ) - 1 = z - 1 + (N : ℤ) by ring, hper, hper]
  have hshift := ringE_shift N (fun z : ℤ => star (w t z) * w t (z - 1) - w t z * star (w t (z - 1))) hF
  have hterm : ∀ x ∈ Finset.range N,
      star (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ))) * w t (x : ℤ) +
        star (w t (x : ℤ)) * (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ))) =
      Complex.I * ((star (w t (x : ℤ)) * w t ((x : ℤ) - 1) - w t (x : ℤ) * star (w t ((x : ℤ) - 1))) -
        (star (w t ((x : ℤ) + 1)) * w t ((x : ℤ) + 1 - 1) -
          w t ((x : ℤ) + 1) * star (w t ((x : ℤ) + 1 - 1)))) := by
    intro x _
    rw [add_sub_cancel_right]
    simp only [Complex.star_def, map_mul, map_sub, map_add, Complex.conj_I, map_ofNat]
    ring
  have hzero : ∑ x ∈ Finset.range N,
      (star (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ))) * w t (x : ℤ) +
        star (w t (x : ℤ)) * (Complex.I * (w t ((x : ℤ) + 1) + w t ((x : ℤ) - 1) - 2 * w t (x : ℤ)))) = 0 := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, hshift, sub_self, mul_zero]
  rw [hzero] at hsum
  exact hsum

/-- **F-energy** A solution of period `N` of the equation with zero datum is zero. -/
theorem ringEnergyFacts : RingEnergyFacts := by
  intro N w hN hper hder h0 t x
  have hd : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => ∑ y ∈ Finset.range N, star (w s (y : ℤ)) * w s (y : ℤ)) 0 s :=
    fun s => ringE_hasDerivAt N w hper hder s
  have hconst : ∑ y ∈ Finset.range N, star (w t (y : ℤ)) * w t (y : ℤ) =
      ∑ y ∈ Finset.range N, star (w 0 (y : ℤ)) * w 0 (y : ℤ) :=
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hE0 : ∑ y ∈ Finset.range N, star (w 0 (y : ℤ)) * w 0 (y : ℤ) = 0 :=
    Finset.sum_eq_zero fun y _ => by rw [h0, mul_zero]
  have hreal : ∑ y ∈ Finset.range N, star (w t (y : ℤ)) * w t (y : ℤ) =
      ((∑ y ∈ Finset.range N, Complex.normSq (w t (y : ℤ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  have hsum : ∑ y ∈ Finset.range N, Complex.normSq (w t (y : ℤ)) = 0 := by
    rw [hconst, hE0] at hreal
    exact_mod_cast hreal.symm
  have hall : ∀ y ∈ Finset.range N, w t (y : ℤ) = 0 := by
    intro y hy
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp hsum y hy
    exact Complex.normSq_eq_zero.mp h
  obtain ⟨y, hy, hyx⟩ := ringE_residue N hN x
  rw [← ringE_emod N (w t) (hper t) x, ← hyx]
  exact hall y hy

end OscInt.FiniteRingAux
