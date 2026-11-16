/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.FiniteRing

/-! # Blueprint for batch FR (FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P): intermediate propositions, definitions only

Route: `docs/proof-FR.md`. Five propositions; FR-K and FR-S are proved directly as parts; the assembly
`OscInt/Front/FiniteRingAssembly.lean` proves the other five statements from these, from FR-K, FR-S and from LC-1. -/

namespace OscInt.Blueprint.FiniteRing

open OscInt.Statements

/-- **F-even** The ring kernel is even in the site variable. -/
def RingEvenFacts : Prop :=
  ∀ (N : ℕ) (t : ℝ) (r : ℤ), ringKernel N t (-r) = ringKernel N t r

/-- **F-images** A statement about series, with no kernel in it: if `|g(n)| ≤ A e^{−|n|η}` and the series of `g` over
the coset `r + Nℤ` has sum `S`, then `|S − g(r)| ≤ 2A cosh(rη) / (e^{ηN} − 1)`. -/
def ImageSumFacts : Prop :=
  ∀ (g : ℤ → ℂ) (A η : ℝ) (N : ℕ) (r : ℤ) (S : ℂ), 0 ≤ A → 0 < η → 0 < N →
    (∀ n : ℤ, ‖g n‖ ≤ A * Real.exp (-(|(n : ℝ)| * η))) →
    HasSum (fun m : ℤ => g (r + m * (N : ℤ))) S →
    ‖S - g r‖ ≤ 2 * A * Real.cosh ((r : ℝ) * η) / (Real.exp (η * (N : ℝ)) - 1)

/-- **F-datum** Summing a function of period `N` against the indicator of `N ∣ x − y` over one period `y < N`
returns its value at `x`. -/
def RingDatumFacts : Prop :=
  ∀ (N : ℕ) (f : ℤ → ℂ) (x : ℤ), 0 < N → (∀ z : ℤ, f (z + (N : ℤ)) = f z) →
    ∑ y ∈ Finset.range N, (if (N : ℤ) ∣ x - (y : ℤ) then (1 : ℂ) else 0) * f (y : ℤ) = f x

/-- **F-energy** A solution of period `N` of the equation with zero datum is zero. -/
def RingEnergyFacts : Prop :=
  ∀ (N : ℕ) (w : ℝ → ℤ → ℂ), 0 < N → (∀ (t : ℝ) (x : ℤ), w t (x + (N : ℤ)) = w t x) →
    (∀ (t : ℝ) (x : ℤ),
      HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t) →
    (∀ x : ℤ, w 0 x = 0) → ∀ (t : ℝ) (x : ℤ), w t x = 0

/-- **C-energy** A solution of the equation on the sites `1, …, M` that vanishes at the two walls and has zero datum
is zero. -/
def ChainEnergyFacts : Prop :=
  ∀ (M : ℕ) (w : ℝ → ℤ → ℂ), (∀ t : ℝ, w t 0 = 0 ∧ w t ((M : ℤ) + 1) = 0) →
    (∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      HasDerivAt (fun s : ℝ => w s x) (Complex.I * (w t (x + 1) + w t (x - 1) - 2 * w t x)) t) →
    (∀ x : ℤ, 1 ≤ x → x ≤ (M : ℤ) → w 0 x = 0) →
    ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) → w t x = 0

end OscInt.Blueprint.FiniteRing
