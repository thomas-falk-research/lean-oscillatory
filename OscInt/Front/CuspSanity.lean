/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Cusp
import OscInt.Front.Poly

/-! # Sanity theorems for batch A3 (S1.k, S5.1, S5.1′)

Written before the statements are stamped; no proof of a batch-A3 statement exists. Hypotheses are the named
definitions of `OscInt/Statements/Cusp.lean` (`DerivChain`, `IsA3Point`, `IsStableA3Point`), shared with the statements;
each gets satisfying generic data and bite data on which it must fail (lessons 11, 17, 38). Expected values were
computed exactly before this file was written (`numerics/a3/statement_checks.py`, checks E3).

* S1.k specialises to the reviewed S1.2 and S1.3 (`vdCk_to_vdC2`, `vdCk_to_vdC3`): the constants `5·2^{k−1} − 2` at
  `k = 2, 3` and the power `μ^{−1/k}` are pinned against the stamped statements.
* `DerivChain`: satisfied by a quartic with distinct coefficients (`k = 4`, `|D₄| = 1`); fails for a wrong derivative.
* `IsStableA3Point`, `IsA3Point`: satisfied at `0` by `x²y + 2y² + 3x⁴ + 5xy²` (`v = e₁`, `w = e₂`: `D²[w, w] = 4`,
  `D³[v, v, w] = 2`, `D⁴[v⁴] = 72`, reduced quartic `276`). Bites, each failing the condition it targets:
  `(y + x²/2)²` (the straight-line quartic `D⁴[v⁴] = 6` is nonzero but the reduced quartic is `0` for every kernel
  vector), `x³ + y²` (fold: `D³[v³] ≠ 0`), `x³ + y³` (Hessian zero), `x² + y²` (Hessian of rank two). `x⁴ + y²` is an A3
  point but not a stable one (`D³ = 0`).
* Non-vacuity through the statement constants: S5.1 applied to the generic datum, S5.1′ to `x⁴ + y²`.

Generic helper (proved here, reusable): `third_polar`, `D³f[v, v, w]` from three diagonal values (symmetry of the third
derivative, `OscInt.API.DerivAux.symm3`).
-/

namespace OscInt.API.CuspSanity

open OscInt.Statements OscInt.API.Poly OscInt.API.DerivAux Set
open scoped ContDiff

/-! ## Polarisation of the third derivative -/

theorem third_polar {f : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f k) (v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 f k ![v, v, w] =
      (iteratedFDeriv ℝ 3 f k ![v + w, v + w, v + w] - iteratedFDeriv ℝ 3 f k ![v - w, v - w, v - w] -
        2 * iteratedFDeriv ℝ 3 f k ![w, w, w]) / 6 := by
  simp only [iter3_eq, map_add, map_sub, add_apply, sub_apply]
  set F := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) k
  have s12 := fun a b c => (symm3 hf a b c).1
  have s23 := fun a b c => (symm3 hf a b c).2
  have e1 : F v w v = F v v w := (s23 v v w).symm
  have e2 : F w v v = F v v w := by rw [s12 w v v, e1]
  have e3 : F w w v = F v w w := by rw [s23 w w v, s12 w v w]
  have e4 : F w v w = F v w w := s12 w v w
  linarith [e1, e2, e3, e4]

/-- `![a, a]`, `![a, a, a]`, `![a, a, a, a]` are constant families. -/
theorem vec2_const (a : ℝ × ℝ) : (![a, a] : Fin 2 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

theorem vec3_const (a : ℝ × ℝ) : (![a, a, a] : Fin 3 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

theorem vec4_const (a : ℝ × ℝ) : (![a, a, a, a] : Fin 4 → ℝ × ℝ) = fun _ => a := by
  funext i; fin_cases i <;> rfl

/-! ## Quartic phases with a known expansion along lines through `0`

For `f(x, y) = c₂(x, y) + c₃(x, y) + c₄(x, y)` with homogeneous parts `c_j`, `f(t a) = c₂(a) t² + c₃(a) t³ + c₄(a) t⁴`, so
`Dʲf(0)[aʲ] = j! c_j(a)`. -/

/-- A quartic polynomial phase with given homogeneous parts of degree 2, 3, 4, written through its coefficients. -/
noncomputable def quartic (q : Fin 12 → ℝ) : ℝ × ℝ → ℝ := fun k =>
  q 0 * k.1 ^ 2 + q 1 * k.1 * k.2 + q 2 * k.2 ^ 2 +
    q 3 * k.1 ^ 3 + q 4 * k.1 ^ 2 * k.2 + q 5 * k.1 * k.2 ^ 2 + q 6 * k.2 ^ 3 +
    q 7 * k.1 ^ 4 + q 8 * k.1 ^ 3 * k.2 + q 9 * k.1 ^ 2 * k.2 ^ 2 + q 10 * k.1 * k.2 ^ 3 + q 11 * k.2 ^ 4

/-- The homogeneous parts of `quartic q` evaluated at `a`. -/
def part2 (q : Fin 12 → ℝ) (a : ℝ × ℝ) : ℝ := q 0 * a.1 ^ 2 + q 1 * a.1 * a.2 + q 2 * a.2 ^ 2

def part3 (q : Fin 12 → ℝ) (a : ℝ × ℝ) : ℝ :=
  q 3 * a.1 ^ 3 + q 4 * a.1 ^ 2 * a.2 + q 5 * a.1 * a.2 ^ 2 + q 6 * a.2 ^ 3

def part4 (q : Fin 12 → ℝ) (a : ℝ × ℝ) : ℝ :=
  q 7 * a.1 ^ 4 + q 8 * a.1 ^ 3 * a.2 + q 9 * a.1 ^ 2 * a.2 ^ 2 + q 10 * a.1 * a.2 ^ 3 + q 11 * a.2 ^ 4

theorem quartic_contDiff (q : Fin 12 → ℝ) : ContDiff ℝ ω (quartic q) := by
  unfold quartic
  fun_prop

theorem quartic_line (q : Fin 12 → ℝ) (a : ℝ × ℝ) (t : ℝ) :
    quartic q (0 + t • a) = ∑ i : Fin 5, ![0, 0, part2 q a, part3 q a, part4 q a] i * t ^ (i : ℕ) := by
  simp only [quartic, part2, part3, part4, zero_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Fin.sum_univ_five]
  simp
  ring

theorem quartic_d2 (q : Fin 12 → ℝ) (a : ℝ × ℝ) : iteratedFDeriv ℝ 2 (quartic q) 0 ![a, a] = 2 * part2 q a := by
  rw [vec2_const, iteratedFDeriv_diag_of_poly ((quartic_contDiff q).of_le le_top) 0 a _ (quartic_line q a) 2
    (by norm_num)]
  simp

theorem quartic_d3 (q : Fin 12 → ℝ) (a : ℝ × ℝ) : iteratedFDeriv ℝ 3 (quartic q) 0 ![a, a, a] = 6 * part3 q a := by
  rw [vec3_const, iteratedFDeriv_diag_of_poly ((quartic_contDiff q).of_le le_top) 0 a _ (quartic_line q a) 3
    (by norm_num)]
  simp [Nat.factorial]

theorem quartic_d4 (q : Fin 12 → ℝ) (a : ℝ × ℝ) :
    iteratedFDeriv ℝ 4 (quartic q) 0 ![a, a, a, a] = 24 * part4 q a := by
  rw [vec4_const, iteratedFDeriv_diag_of_poly ((quartic_contDiff q).of_le le_top) 0 a _ (quartic_line q a) 4
    (by norm_num)]
  simp [Nat.factorial]

/-- Mixed second derivative by polarisation: `D²f(0)[v, z] = part2(v + z) − part2(v) − part2(z)`. -/
theorem quartic_d2_mixed (q : Fin 12 → ℝ) (v z : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (quartic q) 0 ![v, z] = part2 q (v + z) - part2 q v - part2 q z := by
  rw [iteratedFDeriv_two_polar ((quartic_contDiff q).contDiffAt.of_le le_top), quartic_d2, quartic_d2, quartic_d2]
  ring

/-- Mixed third derivative by polarisation. -/
theorem quartic_d3_mixed (q : Fin 12 → ℝ) (v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (quartic q) 0 ![v, v, w] = part3 q (v + w) - part3 q (v - w) - 2 * part3 q w := by
  rw [third_polar ((quartic_contDiff q).contDiffAt.of_le le_top), quartic_d3, quartic_d3, quartic_d3]
  ring

/-! ## The data -/

/-- `x²y + 2y² + 3x⁴ + 5xy²` (generic stable A3 point at `0`). -/
def qGen : Fin 12 → ℝ := ![0, 0, 2, 0, 1, 5, 0, 3, 0, 0, 0, 0]
/-- `(y + x²/2)² = y² + x²y + x⁴/4` (reduced quartic zero: not A3). -/
noncomputable def qTrap : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 0, 1 / 4, 0, 0, 0, 0]
/-- `x³ + y²` (fold). -/
def qFold : Fin 12 → ℝ := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
/-- `x⁴ + y²` (A3, not stable). -/
def qNonv : Fin 12 → ℝ := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
/-- `x³ + y³` (Hessian zero). -/
def qRank0 : Fin 12 → ℝ := ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]
/-- `x² + y²` (Hessian of rank two). -/
def qNondeg : Fin 12 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Satisfiability -/

theorem gen_isStableA3 : IsStableA3Point (quartic qGen) 0 := by
  refine ⟨(1, 0), (0, 1), fun z => ?_, ?_, ?_, ?_, ?_⟩
  · rw [quartic_d2_mixed]; simp [part2, qGen]
  · rw [quartic_d2]; norm_num [part2, qGen]
  · rw [quartic_d3]; norm_num [part3, qGen]
  · rw [quartic_d2, quartic_d4, quartic_d3_mixed]; norm_num [part2, part3, part4, qGen]
  · rw [quartic_d3_mixed]; norm_num [part3, qGen]

theorem stable_isA3 {Ψ : ℝ × ℝ → ℝ} {k₀ : ℝ × ℝ} (h : IsStableA3Point Ψ k₀) : IsA3Point Ψ k₀ := by
  obtain ⟨v, w, h1, h2, h3, h4, -⟩ := h
  exact ⟨v, w, h1, h2, h3, h4⟩

theorem gen_isA3 : IsA3Point (quartic qGen) 0 := stable_isA3 gen_isStableA3

/-- The values claimed in the header for the generic datum. -/
theorem gen_values :
    iteratedFDeriv ℝ 2 (quartic qGen) 0 ![(0, 1), (0, 1)] = 4 ∧
      iteratedFDeriv ℝ 3 (quartic qGen) 0 ![(1, 0), (1, 0), (0, 1)] = 2 ∧
      iteratedFDeriv ℝ 4 (quartic qGen) 0 ![(1, 0), (1, 0), (1, 0), (1, 0)] = 72 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [quartic_d2]; norm_num [part2, qGen]
  · rw [quartic_d3_mixed]; norm_num [part3, qGen]
  · rw [quartic_d4]; norm_num [part4, qGen]

theorem nonv_isA3 : IsA3Point (quartic qNonv) 0 := by
  refine ⟨(1, 0), (0, 1), fun z => ?_, ?_, ?_, ?_⟩
  · rw [quartic_d2_mixed]; simp [part2, qNonv]
  · rw [quartic_d2]; norm_num [part2, qNonv]
  · rw [quartic_d3]; norm_num [part3, qNonv]
  · rw [quartic_d2, quartic_d4, quartic_d3_mixed]; norm_num [part2, part3, part4, qNonv]

/-! ## Bites -/

/-- A kernel vector of `D²f(0)` for a quartic whose quadratic part is `q₂ y²` (`q₂ ≠ 0`) lies on the `x`-axis. -/
theorem kernel_on_axis {q : Fin 12 → ℝ} (h0 : q 0 = 0) (h1 : q 1 = 0) (h2 : q 2 ≠ 0) {v : ℝ × ℝ}
    (hv : ∀ z, iteratedFDeriv ℝ 2 (quartic q) 0 ![v, z] = 0) : v.2 = 0 := by
  have := hv (0, 1)
  rw [quartic_d2_mixed] at this
  simp only [part2, h0, h1, Prod.fst_add, Prod.snd_add] at this
  have : 2 * q 2 * v.2 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linarith : q 2 = 0) h2
  · exact h

/-- **Bite (reduced quartic).** `(y + x²/2)²` has a rank-one Hessian, `D³[v³] = 0` and `D⁴[e₁⁴] = 6 ≠ 0`, but the
reduced quartic vanishes for every kernel vector `v` and every `w`: it is not an A3 point. -/
theorem trap_not_isA3 : ¬ IsA3Point (quartic qTrap) 0 := by
  rintro ⟨v, w, hv, -, -, h4⟩
  have hv2 : v.2 = 0 := kernel_on_axis (by simp [qTrap]) (by simp [qTrap]) (by norm_num [qTrap]) hv
  apply h4
  rw [quartic_d2, quartic_d4, quartic_d3_mixed]
  simp only [part2, part3, part4, qTrap, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hv2]
  norm_num
  ring

theorem trap_straight_quartic : iteratedFDeriv ℝ 4 (quartic qTrap) 0 ![(1, 0), (1, 0), (1, 0), (1, 0)] = 6 := by
  rw [quartic_d4]; norm_num [part4, qTrap]

/-- **Bite (fold).** `x³ + y²` is not an A3 point: on its kernel `D³[v³] = 6 v₁³ ≠ 0` unless `v = 0`, and `v = 0`
makes the reduced quartic `0`. -/
theorem fold_not_isA3 : ¬ IsA3Point (quartic qFold) 0 := by
  rintro ⟨v, w, hv, -, h3, h4⟩
  have hv2 : v.2 = 0 := kernel_on_axis (by simp [qFold]) (by simp [qFold]) (by norm_num [qFold]) hv
  rw [quartic_d3] at h3
  simp [part3, qFold, hv2] at h3
  have hv1 : v.1 = 0 := h3
  apply h4
  rw [quartic_d2, quartic_d4, quartic_d3_mixed]
  simp only [part2, part3, part4, qFold, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hv1, hv2]
  ring

/-- **Bite (Hessian zero).** `x³ + y³` has `D²f(0) = 0`, so no `w` has `D²[w, w] ≠ 0`. -/
theorem rank0_not_isA3 : ¬ IsA3Point (quartic qRank0) 0 := by
  rintro ⟨v, w, -, h2, -, -⟩
  apply h2
  rw [quartic_d2]; simp [part2, qRank0]

/-- **Bite (rank two).** `x² + y²`: the only kernel vector is `0`, and then the reduced quartic is `0`. -/
theorem nondeg_not_isA3 : ¬ IsA3Point (quartic qNondeg) 0 := by
  rintro ⟨v, w, hv, -, -, h4⟩
  have a := hv (1, 0)
  have b := hv (0, 1)
  rw [quartic_d2_mixed] at a b
  simp only [part2, qNondeg, Prod.fst_add, Prod.snd_add] at a b
  norm_num at a b
  have hv1 : v.1 = 0 := by nlinarith
  have hv2 : v.2 = 0 := by nlinarith
  apply h4
  rw [quartic_d2, quartic_d4, quartic_d3_mixed]
  simp only [part2, part3, part4, qNondeg, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hv1, hv2]
  norm_num

/-- **Bite (not stable).** `x⁴ + y²` is an A3 point (`nonv_isA3`) but not a stable one: its third derivative at `0`
vanishes, so `D³[v, v, w] = 0` for all `v w`. -/
theorem nonv_not_isStableA3 : ¬ IsStableA3Point (quartic qNonv) 0 := by
  rintro ⟨v, w, -, -, -, -, h5⟩
  apply h5
  rw [quartic_d3_mixed]
  simp [part3, qNonv]

/-! ## `DerivChain` -/

/-- `D₀ = x⁴/24 + 2x³/6 + 3x²/2 + 5x`, `D₁ = x³/6 + x² + 3x + 5`, `D₂ = x²/2 + 2x + 3`, `D₃ = x + 2`, `D₄ = 1`. -/
noncomputable def chain4 : ℕ → ℝ → ℝ
  | 0 => fun x => x ^ 4 / 24 + 2 * x ^ 3 / 6 + 3 * x ^ 2 / 2 + 5 * x
  | 1 => fun x => x ^ 3 / 6 + x ^ 2 + 3 * x + 5
  | 2 => fun x => x ^ 2 / 2 + 2 * x + 3
  | 3 => fun x => x + 2
  | _ => fun _ => 1

theorem chain4_hasDerivAt : ∀ j < 4, ∀ x : ℝ, HasDerivAt (chain4 j) (chain4 (j + 1) x) x := by
  intro j hj x
  interval_cases j
  · show HasDerivAt (fun x : ℝ => x ^ 4 / 24 + 2 * x ^ 3 / 6 + 3 * x ^ 2 / 2 + 5 * x) _ x
    exact HasDerivAt.congr_deriv (((((hasDerivAt_pow 4 x).div_const 24).fun_add
      (((hasDerivAt_pow 3 x).const_mul 2).div_const 6)).fun_add (((hasDerivAt_pow 2 x).const_mul 3).div_const 2)).fun_add
      ((hasDerivAt_id' x).const_mul 5)) (by simp [chain4]; ring)
  · show HasDerivAt (fun x : ℝ => x ^ 3 / 6 + x ^ 2 + 3 * x + 5) _ x
    exact HasDerivAt.congr_deriv (((((hasDerivAt_pow 3 x).div_const 6).fun_add (hasDerivAt_pow 2 x)).fun_add
      ((hasDerivAt_id' x).const_mul 3)).add_const 5) (by simp [chain4]; ring)
  · show HasDerivAt (fun x : ℝ => x ^ 2 / 2 + 2 * x + 3) _ x
    exact HasDerivAt.congr_deriv ((((hasDerivAt_pow 2 x).div_const 2).fun_add ((hasDerivAt_id' x).const_mul 2)).add_const 3)
      (by simp [chain4])
  · show HasDerivAt (fun x : ℝ => x + 2) _ x
    exact HasDerivAt.congr_deriv ((hasDerivAt_id' x).add_const 2) (by simp [chain4])

theorem chain4_satisfies : DerivChain chain4 4 0 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 1 ≤ |chain4 4 x| := by
  refine ⟨fun j hj => ⟨fun x _ => (chain4_hasDerivAt j hj x).continuousAt.continuousWithinAt,
    fun x _ => chain4_hasDerivAt j hj x⟩, fun x _ => by simp [chain4]⟩

/-- **Bite.** `D₀ = x²` with `D₁ = x` (the derivative is `2x`) is not a chain of length 1 on `[0, 1]`. -/
theorem wrong_chain : ¬ DerivChain (fun j => if j = 0 then fun x : ℝ => x ^ 2 else fun x => x) 1 0 1 := by
  intro h
  have h1 := (h 0 (by norm_num)).2 (1 / 2) ⟨by norm_num, by norm_num⟩
  simp only [zero_add, one_ne_zero, ↓reduceIte] at h1
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * (1 / 2 : ℝ)) (1 / 2) := by
    simpa using hasDerivAt_pow 2 (1 / 2 : ℝ)
  have := h1.unique h2
  norm_num at this

/-! ## S1.k specialises to S1.2 and S1.3 -/

theorem rpow_neg_half {μ : ℝ} (hμ : 0 < μ) : μ ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 / √μ := by
  rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / ((2 : ℕ) : ℝ)) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hμ.le]
  simp [one_div]

theorem vdCk_to_vdC2 (h : VdCkStatement) : VdC2Statement := by
  intro φ φ' φ'' ψ ψ' a b μ p hab hμ h1 h2 hlow hψ
  let D : ℕ → ℝ → ℝ := fun j => if j = 0 then φ else if j = 1 then φ' else φ''
  have hc : DerivChain D 2 a b := by
    intro j hj
    interval_cases j
    · simpa [D] using h1
    · simpa [D] using h2
  have := h 2 D ψ ψ' a b μ p le_rfl hab hμ hc (by simpa [D] using hlow) hψ
  rw [show ((5 : ℝ) * 2 ^ (2 - 1) - 2) = 8 by norm_num, rpow_neg_half hμ] at this
  calc ‖oscInt (fun x => φ x + p * x) ψ a b‖ = ‖oscInt (fun x => D 0 x + p * x) ψ a b‖ := rfl
    _ ≤ 8 * (1 / √μ) * ampNorm ψ ψ' a b := this
    _ = 8 / √μ * ampNorm ψ ψ' a b := by ring

theorem vdCk_to_vdC3 (h : VdCkStatement) : VdC3Statement := by
  intro φ φ' φ'' φ''' ψ ψ' a b μ p hab hμ h1 h2 h3 hlow hψ
  let D : ℕ → ℝ → ℝ := fun j => if j = 0 then φ else if j = 1 then φ' else if j = 2 then φ'' else φ'''
  have hc : DerivChain D 3 a b := by
    intro j hj
    interval_cases j
    · simpa [D] using h1
    · simpa [D] using h2
    · simpa [D] using h3
  have := h 3 D ψ ψ' a b μ p (by norm_num) hab hμ hc (by simpa [D] using hlow) hψ
  norm_num [D] at this ⊢
  exact this

/-! ## Non-vacuity through the statement constants -/

theorem cuspBound_gen (h : CuspBoundStatement) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * quartic qGen κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4) :=
  h _ ((quartic_contDiff qGen).of_le le_top) gen_isStableA3

theorem cuspBoundGen_nonv (h : CuspBoundGenStatement) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * quartic qNonv κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 : ℝ) / 4) :=
  h _ ((quartic_contDiff qNonv).of_le le_top) nonv_isA3

end OscInt.API.CuspSanity
