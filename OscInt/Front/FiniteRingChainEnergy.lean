/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.FiniteRing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Batch FR, part FR5: the energy argument on the open chain (`ChainEnergyFacts`)

Route `docs/proof-FR.md`, "Part C-unique". The energy is written in complex form,
`E(t) = Σ_{k<M} conj(w(t, k + 1)) w(t, k + 1)`. The derivative of the term at the site `x` is
`i (J(x) − J(x − 1))` with the current `J(x) = conj(w_x) w_{x+1} − conj(w_{x+1}) w_x`; the sum over the sites
telescopes to `i (J(M) − J(0))`, and both currents vanish by the wall conditions. So `E` is constant,
`E(0) = 0`, and `E(t)` is a sum of squared moduli.
-/

namespace OscInt.FiniteRingAux

open OscInt.Statements OscInt.Blueprint.FiniteRing

open scoped ComplexConjugate

/-- One site: `conj(d) a + conj(a) d` for `d = i (b + c − 2a)` is `i` times a difference of currents. -/
theorem chainE_site_algebra (a b c : ℂ) :
    conj (Complex.I * (b + c - 2 * a)) * a + conj a * (Complex.I * (b + c - 2 * a)) =
      Complex.I * ((conj a * b - conj b * a) - (conj c * a - conj a * c)) := by
  have h2 : conj (2 : ℂ) = 2 := Complex.conj_ofNat 2
  simp only [map_mul, map_add, map_sub, Complex.conj_I, h2]
  ring

/-- The derivative of `conj(w_x) w_x` at a site where the equation holds, as `i` times a difference of currents. -/
theorem chainE_site_hasDerivAt (w : ℝ → ℤ → ℂ) (t : ℝ) (x : ℤ)
    (h : HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t) :
    HasDerivAt (fun s : ℝ => conj (w s x) * w s x)
      (Complex.I * ((conj (w t x) * w t (x + 1) - conj (w t (x + 1)) * w t x) -
        (conj (w t (x - 1)) * w t x - conj (w t x) * w t (x - 1)))) t := by
  have hs : HasDerivAt (fun s : ℝ => conj (w s x))
      (conj (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x))) t := h.star
  have hm := hs.mul h
  rw [chainE_site_algebra] at hm
  exact hm

/-- A sum of `i (J(k + 1) − J(k))` over `k < M` telescopes to `i (J(M) − J(0))`. -/
theorem chainE_sum_telescope (J : ℕ → ℂ) (M : ℕ) :
    ∑ k ∈ Finset.range M, Complex.I * (J (k + 1) - J k) = Complex.I * (J M - J 0) := by
  rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- The complex energy of the chain has derivative zero at every time. -/
theorem chainE_energy_hasDerivAt (M : ℕ) (w : ℝ → ℤ → ℂ)
    (hwall : ∀ t : ℝ, w t 0 = 0 ∧ w t ((M : ℤ) + 1) = 0)
    (hder : ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range M, conj (w s ((k : ℤ) + 1)) * w s ((k : ℤ) + 1)) 0 t := by
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ → ℂ, ∀ j : ℕ,
      J j = conj (w t (j : ℤ)) * w t ((j : ℤ) + 1) - conj (w t ((j : ℤ) + 1)) * w t (j : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have hJ : ∀ k ∈ Finset.range M,
      HasDerivAt (fun s : ℝ => conj (w s ((k : ℤ) + 1)) * w s ((k : ℤ) + 1))
        (Complex.I * (J (k + 1) - J k)) t := by
    intro k hk
    have hkM : k < M := Finset.mem_range.mp hk
    have h1 : (1 : ℤ) ≤ (k : ℤ) + 1 := by omega
    have h2 : (k : ℤ) + 1 ≤ (M : ℤ) := by omega
    have h := chainE_site_hasDerivAt w t ((k : ℤ) + 1) (hder t ((k : ℤ) + 1) h1 h2)
    have e1 : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
    rw [e1] at h
    have e2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [hJdef (k + 1), hJdef k, e2]
    exact h
  have hsum := HasDerivAt.fun_sum hJ
  have hz : ∑ k ∈ Finset.range M, Complex.I * (J (k + 1) - J k) = 0 := by
    rw [chainE_sum_telescope J M, hJdef M, hJdef 0, Nat.cast_zero, (hwall t).2, (hwall t).1]
    simp only [map_zero, mul_zero, zero_mul, sub_zero]
  rw [hz] at hsum
  exact hsum

/-- The complex energy of the chain is zero at every time when the datum is zero. -/
theorem chainE_energy_eq_zero (M : ℕ) (w : ℝ → ℤ → ℂ)
    (hwall : ∀ t : ℝ, w t 0 = 0 ∧ w t ((M : ℤ) + 1) = 0)
    (hder : ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t)
    (h0 : ∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) → w 0 x = 0) (t : ℝ) :
    ∑ k ∈ Finset.range M, conj (w t ((k : ℤ) + 1)) * w t ((k : ℤ) + 1) = 0 := by
  have hd := chainE_energy_hasDerivAt M w hwall hder
  have hc := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (f := fun s : ℝ => ∑ k ∈ Finset.range M, conj (w s ((k : ℤ) + 1)) * w s ((k : ℤ) + 1))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hc' : ∑ k ∈ Finset.range M, conj (w t ((k : ℤ) + 1)) * w t ((k : ℤ) + 1) =
      ∑ k ∈ Finset.range M, conj (w 0 ((k : ℤ) + 1)) * w 0 ((k : ℤ) + 1) := hc
  rw [hc']
  apply Finset.sum_eq_zero
  intro k hk
  have hkM : k < M := Finset.mem_range.mp hk
  rw [h0 ((k : ℤ) + 1) (by omega) (by omega), mul_zero]

/-- A finite sum of `conj(z_k) z_k` that vanishes has every `z_k` equal to zero. -/
theorem chainE_term_eq_zero (M : ℕ) (z : ℕ → ℂ) (h : ∑ k ∈ Finset.range M, conj (z k) * z k = 0)
    (k : ℕ) (hk : k < M) : z k = 0 := by
  have hr : ((∑ j ∈ Finset.range M, Complex.normSq (z j) : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum, ← h]
    exact Finset.sum_congr rfl (fun j _ => Complex.normSq_eq_conj_mul_self)
  have hr' : ∑ j ∈ Finset.range M, Complex.normSq (z j) = 0 := Complex.ofReal_eq_zero.mp hr
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (z j))).mp hr'
  exact Complex.normSq_eq_zero.mp (hall k (Finset.mem_range.mpr hk))

/-- **C-energy** A solution on the sites `1, …, M` that vanishes at the two walls and has zero datum is zero. -/
theorem chainEnergyFacts : ChainEnergyFacts := by
  intro M w hwall hder h0 t x hx1 hxM
  have hE := chainE_energy_eq_zero M w hwall hder h0 t
  have hk : (x - 1).toNat < M := by omega
  have hz := chainE_term_eq_zero M (fun k : ℕ => w t ((k : ℤ) + 1)) hE (x - 1).toNat hk
  have hx : (((x - 1).toNat : ℕ) : ℤ) + 1 = x := by omega
  simp only [hx] at hz
  exact hz

end OscInt.FiniteRingAux
