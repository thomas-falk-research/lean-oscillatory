/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Cusp
import OscInt.VanDerCorput.Final

/-!
# All derivative orders in van der Corput's estimate

The coefficient and induction are classical and occur in the work of J. Roos and M. Praveen.
This proof uses OscInt's explicit derivative chains and its existing split and amplitude lemmas.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`.
-/

namespace OscInt.Cusp.VdCkAux

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint
open OscInt.VanDerCorput.HigherAux

/-- The coefficient in the frozen statement; natural subtraction is intentional. -/
noncomputable def coefficient (k : ℕ) : ℝ := (5 : ℝ) * 2 ^ (k - 1) - 2

/-- The coefficient obeys the recursion contributed by two far intervals and one middle interval. -/
lemma coefficient_succ (k : ℕ) (hk : 1 ≤ k) :
    coefficient (k + 1) = 2 * coefficient k + 2 := by
  have hindex : k = (k - 1) + 1 := by omega
  have hpower : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
    calc
      (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℝ) ^ n) hindex
      _ = (2 : ℝ) ^ (k - 1) * 2 := pow_succ (2 : ℝ) (k - 1)
  simp only [coefficient, Nat.add_sub_cancel]
  rw [hpower]
  ring

/-- All coefficients, including unused indices zero and one, are positive. -/
lemma coefficient_pos (k : ℕ) : 0 < coefficient k := by
  induction k with
  | zero => norm_num [coefficient]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      norm_num [coefficient]
    · rw [coefficient_succ k (by omega)]
      linarith

/-- The order-two coefficient agrees with the existing square-root formulation. -/
lemma base_two {μ : ℝ} (hμ : 0 < μ) :
    8 / √μ = coefficient 2 * μ ^ (-(1 : ℝ) / 2) := by
  have hc : coefficient 2 = 8 := by norm_num [coefficient]
  have hexponent : -(1 : ℝ) / 2 = -((1 : ℝ) / 2) := by ring
  rw [hc, Real.sqrt_eq_rpow, div_eq_mul_inv, hexponent, Real.rpow_neg (le_of_lt hμ)]

/-- The threshold is `μ` times the radius, not the radius itself. -/
lemma radius_power (k : ℕ) (hk : 1 ≤ k) {μ : ℝ} (hμ : 0 < μ) :
    (μ * μ ^ (-(1 : ℝ) / ((k : ℝ) + 1))) ^ (-(1 : ℝ) / (k : ℝ)) =
      μ ^ (-(1 : ℝ) / ((k : ℝ) + 1)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkne : (k : ℝ) ≠ 0 := Ne.symm (ne_of_lt hkpos)
  have hksne : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [Real.mul_rpow (le_of_lt hμ) (Real.rpow_nonneg (le_of_lt hμ) _),
    ← Real.rpow_mul (le_of_lt hμ), ← Real.rpow_add hμ]
  congr 1
  field_simp [hkne, hksne]
  ring

/-- Exact arithmetic for the induction step. -/
lemma next_bound (k : ℕ) (hk : 1 ≤ k) {μ : ℝ} (hμ : 0 < μ) :
    2 * μ ^ (-(1 : ℝ) / ((k : ℝ) + 1)) +
      2 * (coefficient k *
        (μ * μ ^ (-(1 : ℝ) / ((k : ℝ) + 1))) ^ (-(1 : ℝ) / (k : ℝ))) =
      coefficient (k + 1) * μ ^ (-(1 : ℝ) / ((k : ℝ) + 1)) := by
  rw [radius_power k hk hμ, coefficient_succ k hk]
  ring

/-- Restrict the derivative chain to each far interval and apply induction. -/
lemma plain_all (hS : SplitFacts) (h2 : VdC2PlainFacts) (h3 : VdC3PlainFacts) :
    ∀ k : ℕ, 2 ≤ k → ∀ (D : ℕ → ℝ → ℝ) (a b μ : ℝ), a ≤ b → 0 < μ →
      DerivChain D k a b → (∀ x ∈ Ioo a b, μ ≤ |D k x|) →
      ‖∫ x in a..b, Complex.exp (↑(D 0 x) * Complex.I)‖ ≤
        coefficient k * μ ^ (-(1 : ℝ) / (k : ℝ)) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk D a b μ hab hμ hD hlow
    by_cases hbase : k = 1
    · subst k
      rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num]
      rw [← base_two hμ]
      exact h2 (D 0) (D 1) (D 2) a b μ hab hμ
        (hD 0 (by norm_num)) (hD 1 (by norm_num)) hlow
    by_cases hbase3 : k = 2
    · subst k
      have hc : coefficient 3 = 18 := by norm_num [coefficient]
      rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num]
      simpa only [hc, Nat.cast_ofNat] using
        (h3 (D 0) (D 1) (D 2) (D 3) a b μ hab hμ
          (hD 0 (by norm_num)) (hD 1 (by norm_num)) (hD 2 (by norm_num)) hlow)
    have hk2 : 2 ≤ k := by omega
    obtain ⟨-, d, hd, hdist⟩ := hS (D k) (D (k + 1)) a b μ hab hμ
      (hD k (by omega)) hlow
    have hr : 0 < μ ^ (-(1 : ℝ) / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hμ _
    simp only [Nat.cast_succ]
    rw [← next_bound k (by omega) hμ]
    refine split_bound (D 0) a b d _ _ hab hd (le_of_lt hr) (hD 0 (by omega)).1 ?_
    intro s t has hst htb hfar
    refine ih hk2 D s t _ hst (mul_pos hμ hr) ?_ ?_
    · intro j hj
      exact hasDerivOn_mono (hD j (by omega)) has htb
    · intro x hx
      have hxI : x ∈ Icc a b := ⟨le_trans has (le_of_lt hx.1), le_trans (le_of_lt hx.2) htb⟩
      exact le_trans (mul_le_mul_of_nonneg_left (hfar x hx) (le_of_lt hμ)) (hdist x hxI)

/-- Adding a linear phase changes exactly entries zero and one of the derivative chain. -/
noncomputable def shiftedChain (D : ℕ → ℝ → ℝ) (p : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => D 0 x + p * x
  | 1 => fun x => D 1 x + p
  | n + 2 => D (n + 2)

/-- Higher derivatives are unchanged by the linear term. -/
lemma shifted_high {k : ℕ} (hk : 2 ≤ k) (D : ℕ → ℝ → ℝ) (p : ℝ) :
    shiftedChain D p k = D k := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k => rfl

/-- Each link in the shifted chain follows from a link of the original chain. -/
lemma shifted_chain {D : ℕ → ℝ → ℝ} {k : ℕ} {a b : ℝ}
    (hD : DerivChain D k a b) (p : ℝ) : DerivChain (shiftedChain D p) k a b := by
  intro j hj
  cases j with
  | zero =>
    simpa [shiftedChain] using OscInt.VanDerCorput.HasDerivOn.add_linear (hD 0 hj) p
  | succ j =>
    cases j with
    | zero =>
      simpa [shiftedChain] using OscInt.VanDerCorput.HasDerivOn.add_const (hD 1 hj) p
    | succ j =>
      simpa [shiftedChain] using hD (j + 2) (by omega)

/-- The uniform primitive estimate gives the frozen amplitude norm without an extra factor. -/
lemma with_amplitude (hS : SplitFacts) (h2 : VdC2PlainFacts) (h3 : VdC3PlainFacts)
    (hA : AmplitudeTransferFacts) : VdCkStatement := by
  intro k D ψ ψ' a b μ p hk hab hμ hD hlow hψ
  let E := shiftedChain D p
  have hE : DerivChain E k a b := shifted_chain hD p
  change ‖oscInt (E 0) ψ a b‖ ≤
    coefficient k * μ ^ (-(1 : ℝ) / (k : ℝ)) * ampNorm ψ ψ' a b
  refine hA (E 0) ψ ψ' a b (coefficient k * μ ^ (-(1 : ℝ) / (k : ℝ))) hab
    (le_of_lt (mul_pos (coefficient_pos k) (Real.rpow_pos_of_pos hμ _)))
    (hE 0 (by omega)).1 hψ fun y hy => ?_
  refine plain_all hS h2 h3 k hk E a y μ hy.1 hμ ?_ ?_
  · intro j hj
    exact hasDerivOn_mono (hE j hj) le_rfl hy.2
  · intro x hx
    change μ ≤ |shiftedChain D p k x|
    rw [shifted_high hk D p]
    exact hlow x (Ioo_subset_Ioo le_rfl hy.2 hx)

end OscInt.Cusp.VdCkAux

namespace OscInt.Cusp

open OscInt.Statements OscInt.VanDerCorput

/-- **S1.k** The frozen derivative-chain estimate for every order at least two. -/
theorem vdcK : VdCkStatement :=
  VdCkAux.with_amplitude splitFacts (vdc2Plain splitFacts vdc1Plain)
    (vdc3Plain splitFacts (vdc2Plain splitFacts vdc1Plain)) amplitudeTransfer

end OscInt.Cusp
