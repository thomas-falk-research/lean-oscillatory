import OscInt.Statements.VanDerCorput

/-!
# Batch KL: the Kusmin–Landau inequality for exponential sums (statements only)

Mathematics: `docs/statements.md`, "Batch KL". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

With `e(x) = e^{2πix}`:
* KL-D `KusminLandauStatement` (Landau's form, on differences): if the differences `c_{n+1} − c_n`, `n < N`, are
  monotone and lie in `[k + λ, k + 1 − λ]` for an integer `k` and `0 < λ ≤ 1/2`, then
  `|Σ_{n=0}^{N} e(c_n)| ≤ cot(πλ/2)`.
* KL-C `KusminLandauTwoOverPiStatement`: under the same hypotheses, `|Σ_{n=0}^{N} e(c_n)| ≤ 2/(πλ)`.
* KL-F `KusminLandauDerivStatement` (the textbook form): if `f′` is monotone on `(a, b)` with
  `k + λ ≤ f′ ≤ k + 1 − λ` there, then `|Σ_{a ≤ n ≤ b} e(f(n))| ≤ cot(πλ/2)`.

Modelling choices: sequences are `ℕ → ℝ` and only `c 0, …, c N` matter; "monotone" is "nondecreasing or
nonincreasing"; `cot x` is written `Real.cos x / Real.sin x`; the sum of KL-F runs over the integers `n` with
`⌈a⌉ ≤ n ≤ ⌊b⌋` (`Finset.Icc`); derivatives are given as in S1 (`HasDerivOn`: `f` continuous on `[a, b]` with
derivative `f′` on `(a, b)`).
-/

namespace OscInt.Statements

open Set

/-- The exponential sum `Σ_{n=0}^{N} e^{2πi c_n}` (`N + 1` terms). -/
noncomputable def expSum (c : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), Complex.exp (↑(2 * Real.pi * c n) * Complex.I)

/-- The `N` differences `c (n + 1) − c n`, `n < N`, are monotone (nondecreasing, or nonincreasing) and lie in
`[k + lam, k + 1 − lam]`. -/
def DiffsMonotoneIn (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (lam : ℝ) : Prop :=
  ((∀ n, n + 1 < N → c (n + 1) - c n ≤ c (n + 2) - c (n + 1)) ∨
      (∀ n, n + 1 < N → c (n + 2) - c (n + 1) ≤ c (n + 1) - c n)) ∧
    ∀ n < N, (k : ℝ) + lam ≤ c (n + 1) - c n ∧ c (n + 1) - c n ≤ (k : ℝ) + 1 - lam

/-- **KL-D** The Kusmin–Landau inequality in Landau's sharp form, on differences:
`|Σ_{n=0}^{N} e(c_n)| ≤ cot(πλ/2)`. -/
def KusminLandauStatement : Prop :=
  ∀ (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 → DiffsMonotoneIn c N k lam →
    ‖expSum c N‖ ≤ Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2)

theorem statement_pin_KusminLandau : KusminLandauStatement = KusminLandauStatement := rfl

/-- **KL-C** The Kusmin–Landau inequality with the constant `2/π`: `|Σ_{n=0}^{N} e(c_n)| ≤ 2/(πλ)`. -/
def KusminLandauTwoOverPiStatement : Prop :=
  ∀ (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 → DiffsMonotoneIn c N k lam →
    ‖expSum c N‖ ≤ 2 / (Real.pi * lam)

theorem statement_pin_KusminLandauTwoOverPi :
    KusminLandauTwoOverPiStatement = KusminLandauTwoOverPiStatement := rfl

/-- **KL-F** The Kusmin–Landau inequality in its textbook form: `f′` monotone on `(a, b)` with values in
`[k + λ, k + 1 − λ]` gives `|Σ_{a ≤ n ≤ b} e(f(n))| ≤ cot(πλ/2)`. -/
def KusminLandauDerivStatement : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b : ℝ) (k : ℤ) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 → HasDerivOn f f' a b →
    (MonotoneOn f' (Ioo a b) ∨ AntitoneOn f' (Ioo a b)) →
    (∀ x ∈ Ioo a b, (k : ℝ) + lam ≤ f' x ∧ f' x ≤ (k : ℝ) + 1 - lam) →
    ‖∑ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋, Complex.exp (↑(2 * Real.pi * f (n : ℝ)) * Complex.I)‖ ≤
      Real.cos (Real.pi * lam / 2) / Real.sin (Real.pi * lam / 2)

theorem statement_pin_KusminLandauDeriv : KusminLandauDerivStatement = KusminLandauDerivStatement := rfl

end OscInt.Statements

/- Attribution, appended after the freeze; not part of the frozen text (stamps/pins.txt).
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: Apache-2.0 -/
