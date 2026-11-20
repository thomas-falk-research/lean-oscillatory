/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: batch FR (ring of `N` sites, open chain of `M` sites)

Only `import OscInt.API` and Mathlib. Unconditional uses of the theorems of batch FR:
* `ring_close_to_line`: FR-P at `η = 1`, a bound with no free parameter;
* `chain_close_to_line`: FC-P at `η = 1`;
* `chain_two_sites`: on the chain of 2 sites every solution is given by the closed-form kernel
  (`C₂(t; 1, 1) = e^{−2it} cos t`, `C₂(t; 1, 2) = i e^{−2it} sin t`), from FC-U and the sanity data;
* the sanity data, now without hypotheses.
-/

open OscInt.Statements OscInt.API

/-- FR-P at `η = 1`: the ring of `N` sites against the line. -/
theorem ring_close_to_line (N : ℕ) (t : ℝ) (r : ℤ) (hN : 0 < N) :
    ‖ringKernel N t r - lineKernel t r‖ ≤
      2 * Real.exp (2 * |t| * Real.sinh 1) * Real.cosh ((r : ℝ) * 1) / (Real.exp (1 * (N : ℝ)) - 1) :=
  ringFiniteSize N t 1 r hN one_pos

/-- FC-P at `η = 1`: the open chain of `M` sites against the line. -/
theorem chain_close_to_line (M : ℕ) (t : ℝ) (x y : ℤ) (hx1 : 1 ≤ x) (hxM : x ≤ (M : ℤ)) (hy1 : 1 ≤ y)
    (hyM : y ≤ (M : ℤ)) :
    ‖chainKernel M t x y - lineKernel t (x - y)‖ ≤
      Real.exp (2 * |t| * Real.sinh 1) *
        (Real.exp (-(((x + y : ℤ) : ℝ) * 1)) +
          2 * (Real.cosh (((x - y : ℤ) : ℝ) * 1) + Real.cosh (((x + y : ℤ) : ℝ) * 1)) /
            (Real.exp (2 * ((M : ℝ) + 1) * 1) - 1)) :=
  chainFiniteSize M t 1 x y one_pos hx1 hxM hy1 hyM

/-- FC-U on the chain of two sites, at the first site: a solution is its datum transported by the closed-form
kernel. -/
theorem chain_two_sites (u : ℝ → ℤ → ℂ) (hwall : ∀ t : ℝ, u t 0 = 0 ∧ u t (((2 : ℕ) : ℤ) + 1) = 0)
    (hder : ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ ((2 : ℕ) : ℤ) →
      HasDerivAt (fun s : ℝ => u s x) (Complex.I * (u t (x + 1) + u t (x - 1) - 2 * u t x)) t) (t : ℝ) :
    u t 1 = Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.cos t : ℝ) : ℂ) * u 0 1 +
      Complex.I * Complex.exp (↑(-(2 * t)) * Complex.I) * ((Real.sin t : ℝ) : ℂ) * u 0 2 := by
  have h := chainUnique 2 u hwall hder t 1 le_rfl (by norm_num)
  rw [h, show Finset.Icc (1 : ℤ) ((2 : ℕ) : ℤ) = {1, 2} from by decide, Finset.sum_pair (by norm_num),
    FiniteRingSanity2.chainKernel_two_diag, FiniteRingSanity2.chainKernel_two_off_transpose]

/-- The sanity datum of FC-P with a nonzero left side, now unconditional. -/
example (η : ℝ) (hη : 0 < η) := FiniteRingSanity2.chainP_two_one_one chainFiniteSize η hη

/-- The mode `iˣ e^{−2is}` on the ring of 4 sites, now unconditional. -/
example (t : ℝ) (x : ℤ) := FiniteRingSanity2.ringU_iMode ringUnique t x
