/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriBlueprint
import OscInt.Front.ConvertDeriv
import Mathlib

/-! # Batch TRI, part P-bridge: the reduced function's third and fourth derivatives

`docs/proof-TRI.md`, section 4, as revised by section 9 (items 1 and 2). For any `C^∞` phase `Ψ`, a kernel vector `v`
of the Hessian at `k₀`, a transverse vector `w` with `D²Ψ(k₀)[w, w] ≠ 0` and a reduced curve `h` on `|u| < ε`, the
reduced function `g = reducedFn Ψ k₀ v w h` satisfies

* `g‴(0) = D³Ψ(k₀)[v, v, v]`;
* `g⁗(0) = (D²Ψ(k₀)[w, w] D⁴Ψ(k₀)[v⁴] − 3 D³Ψ(k₀)[v, v, w]²) / D²Ψ(k₀)[w, w]`.

Route. Write `γ(u) = k₀ + u v + h(u) w`, so `γ′ = v + h′ w`.
1. `g′(u) = DΨ(γ u)[v] − DΨ(k₀)[v]` on `|u| < ε` (the `h′` terms cancel by the reduced-curve equation), so
   `g^{(j+1)}(0) = A^{(j)}(0)` with `A u = DΨ(γ u)[v]`.
2. Along `γ`, `u ↦ DⁿΨ(γ u)[m]` has derivative `Dⁿ⁺¹Ψ(γ u)[v, m] + h′(u) Dⁿ⁺¹Ψ(γ u)[w, m]` (chain rule in the
   first slot, expanded multilinearly). Every derivative below is a sum of fixed-slot evaluations along `γ` times
   scalar functions of `u`.
3. `B u = DΨ(γ u)[w]` is constant on `|u| < ε`; its first two derivatives at `0` give `h′(0) = 0` and
   `D³[v, v, w] + h″(0) D²[w, w] = 0`.
4. `A′(0) = D²[v, v] = 0`, `A″(0) = D³[v, v, v]`, `A‴(0) = D⁴[v⁴] + 3 h″(0) D³[v, v, w]`, using only the symmetry of
   the second and third derivatives (`OscInt.API.DerivAux.symm2`, `symm3`).
-/

namespace OscInt.API.ReducedBridge

open OscInt.Statements OscInt.API.TriBlueprint
open Filter Topology
open scoped ContDiff

/-! ## Fixed-slot evaluations along a curve -/

section Slots

variable {Ψ : ℝ × ℝ → ℝ}

/-- Chain rule for `t ↦ DⁿΨ(γ t)[m]` with fixed slots `m`: the new direction enters in the first slot. -/
theorem hasDerivAt_iteratedFDeriv_comp (hΨ : ContDiff ℝ ∞ Ψ) {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ} {u : ℝ}
    (hγ : HasDerivAt γ γ' u) {n : ℕ} (m : Fin n → ℝ × ℝ) :
    HasDerivAt (fun t => iteratedFDeriv ℝ n Ψ (γ t) m)
      (iteratedFDeriv ℝ (n + 1) Ψ (γ u) (Matrix.vecCons γ' m)) u := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n Ψ) (γ u) :=
    hΨ.contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have h1 := (hd.hasFDerivAt.continuousMultilinear_apply_const m).comp_hasDerivAt u hγ
  rw [iteratedFDeriv_succ_apply_left]
  convert h1 using 1
  · rfl
  · simp [Matrix.vecCons, Fin.tail_cons]

/-- Linearity in the first slot: `Dⁿ⁺¹Ψ(k)[a + c b, m] = Dⁿ⁺¹Ψ(k)[a, m] + c Dⁿ⁺¹Ψ(k)[b, m]`. -/
theorem iteratedFDeriv_cons_add_smul (k a b : ℝ × ℝ) (c : ℝ) {n : ℕ} (m : Fin n → ℝ × ℝ) :
    iteratedFDeriv ℝ (n + 1) Ψ k (Matrix.vecCons (a + c • b) m) =
      iteratedFDeriv ℝ (n + 1) Ψ k (Matrix.vecCons a m) +
        c * iteratedFDeriv ℝ (n + 1) Ψ k (Matrix.vecCons b m) := by
  simp only [Matrix.vecCons]
  rw [ContinuousMultilinearMap.cons_add, ContinuousMultilinearMap.cons_smul, smul_eq_mul]

/-- Symmetry of the second derivative of a `C^∞` function. -/
theorem iteratedFDeriv_two_swap (hΨ : ContDiff ℝ ∞ Ψ) (k a b : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 Ψ k ![a, b] = iteratedFDeriv ℝ 2 Ψ k ![b, a] := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simpa using DerivAux.symm2 (hΨ.contDiffAt.of_le (by simp)) a b

/-- Symmetry of the third derivative of a `C^∞` function: swap of the first two slots. -/
theorem iteratedFDeriv_three_swap₁₂ (hΨ : ContDiff ℝ ∞ Ψ) (k a b c : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 Ψ k ![a, b, c] = iteratedFDeriv ℝ 3 Ψ k ![b, a, c] := by
  rw [DerivAux.iter3_eq, DerivAux.iter3_eq]
  exact (DerivAux.symm3 (hΨ.contDiffAt.of_le (by simp)) a b c).1

/-- Symmetry of the third derivative of a `C^∞` function: swap of the last two slots. -/
theorem iteratedFDeriv_three_swap₂₃ (hΨ : ContDiff ℝ ∞ Ψ) (k a b c : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 Ψ k ![a, b, c] = iteratedFDeriv ℝ 3 Ψ k ![a, c, b] := by
  rw [DerivAux.iter3_eq, DerivAux.iter3_eq]
  exact (DerivAux.symm3 (hΨ.contDiffAt.of_le (by simp)) a b c).2

end Slots

/-! ## Evaluations along the curve `γ(u) = k₀ + u v + h(u) w` -/

section Curve

variable {Ψ : ℝ × ℝ → ℝ} {k₀ v w : ℝ × ℝ} {h : ℝ → ℝ}

/-- The curve `u ↦ k₀ + u v + h(u) w` along which `reducedFn` evaluates the phase. -/
def curve (k₀ v w : ℝ × ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ × ℝ :=
  k₀ + u • v + h u • w

/-- The fixed-slot evaluation `u ↦ DⁿΨ(γ u)[m]` along the curve. -/
noncomputable def jet (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (h : ℝ → ℝ) (n : ℕ) (m : Fin n → ℝ × ℝ) (u : ℝ) : ℝ :=
  iteratedFDeriv ℝ n Ψ (curve k₀ v w h u) m

theorem hasDerivAt_curve {u : ℝ} (hh : DifferentiableAt ℝ h u) :
    HasDerivAt (curve k₀ v w h) (v + deriv h u • w) u := by
  have := (((hasDerivAt_id u).smul_const v).const_add k₀).add (hh.hasDerivAt.smul_const w)
  convert this using 1
  · rfl
  · simp

/-- The chain rule along the curve, with the tangent `γ′ = v + h′ w` expanded in the first slot. -/
theorem hasDerivAt_jet (hΨ : ContDiff ℝ ∞ Ψ) (hh : Differentiable ℝ h) (n : ℕ) (m : Fin n → ℝ × ℝ) (u : ℝ) :
    HasDerivAt (jet Ψ k₀ v w h n m)
      (jet Ψ k₀ v w h (n + 1) (Matrix.vecCons v m) u +
        deriv h u * jet Ψ k₀ v w h (n + 1) (Matrix.vecCons w m) u) u := by
  have := hasDerivAt_iteratedFDeriv_comp hΨ (hasDerivAt_curve (k₀ := k₀) (v := v) (w := w) (hh u)) m
  rw [iteratedFDeriv_cons_add_smul] at this
  exact this

theorem jet_zero (h0 : h 0 = 0) (n : ℕ) (m : Fin n → ℝ × ℝ) :
    jet Ψ k₀ v w h n m 0 = iteratedFDeriv ℝ n Ψ k₀ m := by
  simp [jet, curve, h0]

/-- First derivative of `u ↦ DΨ(γ u)[z]`. -/
noncomputable def slot₁ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (h : ℝ → ℝ) (z : ℝ × ℝ) (u : ℝ) : ℝ :=
  jet Ψ k₀ v w h 2 ![v, z] u + deriv h u * jet Ψ k₀ v w h 2 ![w, z] u

/-- Second derivative of `u ↦ DΨ(γ u)[z]`. -/
noncomputable def slot₂ (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (h : ℝ → ℝ) (z : ℝ × ℝ) (u : ℝ) : ℝ :=
  (jet Ψ k₀ v w h 3 ![v, v, z] u + deriv h u * jet Ψ k₀ v w h 3 ![w, v, z] u) +
    (deriv (deriv h) u * jet Ψ k₀ v w h 2 ![w, z] u +
      deriv h u * (jet Ψ k₀ v w h 3 ![v, w, z] u + deriv h u * jet Ψ k₀ v w h 3 ![w, w, z] u))

theorem differentiable_deriv_h (hh : ContDiff ℝ ∞ h) : Differentiable ℝ h ∧ Differentiable ℝ (deriv h) ∧
    Differentiable ℝ (deriv (deriv h)) := by
  refine ⟨hh.differentiable (by simp), ?_, ?_⟩
  · simpa using (hh.iterate_deriv 1).differentiable (by simp)
  · simpa using (hh.iterate_deriv 2).differentiable (by simp)

variable (hΨ : ContDiff ℝ ∞ Ψ) (hh : ContDiff ℝ ∞ h)
include hΨ hh

theorem deriv_jet_one (z : ℝ × ℝ) : deriv (jet Ψ k₀ v w h 1 ![z]) = slot₁ Ψ k₀ v w h z := by
  funext u
  exact (hasDerivAt_jet hΨ (differentiable_deriv_h hh).1 1 ![z] u).deriv

theorem deriv_slot₁ (z : ℝ × ℝ) : deriv (slot₁ Ψ k₀ v w h z) = slot₂ Ψ k₀ v w h z := by
  obtain ⟨hd0, hd1, -⟩ := differentiable_deriv_h hh
  funext u
  have e := (hasDerivAt_jet (k₀ := k₀) (v := v) (w := w) hΨ hd0 2 ![v, z] u).add
    ((hd1 u).hasDerivAt.mul (hasDerivAt_jet (k₀ := k₀) (v := v) (w := w) hΨ hd0 2 ![w, z] u))
  rw [(show HasDerivAt (slot₁ Ψ k₀ v w h z) _ u from e).deriv, slot₂]

/-- Third derivative of `u ↦ DΨ(γ u)[z]` at `0`, where `h′(0) = 0`. -/
theorem deriv_slot₂_zero (h0 : h 0 = 0) (h1 : deriv h 0 = 0) (z : ℝ × ℝ) :
    deriv (slot₂ Ψ k₀ v w h z) 0 =
      iteratedFDeriv ℝ 4 Ψ k₀ ![v, v, v, z] +
        deriv (deriv h) 0 * (iteratedFDeriv ℝ 3 Ψ k₀ ![w, v, z] + 2 * iteratedFDeriv ℝ 3 Ψ k₀ ![v, w, z]) +
          deriv (deriv (deriv h)) 0 * iteratedFDeriv ℝ 2 Ψ k₀ ![w, z] := by
  obtain ⟨hd0, hd1, hd2⟩ := differentiable_deriv_h hh
  have J := fun (n : ℕ) (m : Fin n → ℝ × ℝ) => hasDerivAt_jet (k₀ := k₀) (v := v) (w := w) hΨ hd0 n m 0
  have e1 := (J 3 ![v, v, z]).add ((hd1 0).hasDerivAt.mul (J 3 ![w, v, z]))
  have e2 := ((hd2 0).hasDerivAt.mul (J 2 ![w, z])).add
    ((hd1 0).hasDerivAt.mul ((J 3 ![v, w, z]).add ((hd1 0).hasDerivAt.mul (J 3 ![w, w, z]))))
  rw [(show HasDerivAt (slot₂ Ψ k₀ v w h z) _ 0 from e1.add e2).deriv]
  simp only [Pi.add_apply, Pi.mul_apply, h1, jet_zero h0]
  ring

/-- Step 1: on `|u| < ε` the derivative of the reduced function is `DΨ(γ u)[v] − DΨ(k₀)[v]`. -/
theorem hasDerivAt_reducedFn {ε : ℝ} (hred : ReducedCurve Ψ k₀ v w ε h) {u : ℝ} (hu : |u| < ε) :
    HasDerivAt (reducedFn Ψ k₀ v w h) (jet Ψ k₀ v w h 1 ![v] u - fderiv ℝ Ψ k₀ v) u := by
  have hd0 := (differentiable_deriv_h hh).1
  have hγ := hasDerivAt_curve (k₀ := k₀) (v := v) (w := w) (hd0 u)
  have e1 := ((hΨ.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt u hγ
  have e2 : HasDerivAt (fun t => t • v + h t • w) (v + deriv h u • w) u := by
    have := ((hasDerivAt_id u).smul_const v).add ((hd0 u).hasDerivAt.smul_const w)
    convert this using 1
    · rfl
    · simp
  have e3 := (fderiv ℝ Ψ k₀).hasFDerivAt.comp_hasDerivAt u e2
  convert e1.sub e3 using 1
  · rfl
  · have hc : fderiv ℝ Ψ (curve k₀ v w h u) w = fderiv ℝ Ψ k₀ w := hred.2.2 u hu
    simp only [map_add, map_smul, hc, jet, iteratedFDeriv_one_apply, smul_eq_mul, Matrix.cons_val_zero]
    ring

end Curve

/-! ## The bridge -/

/-- **P-bridge** (`docs/proof-TRI.md`, section 4): along any reduced curve, the third and fourth derivatives of the
reduced function at `0` are `D³Ψ(k₀)[v³]` and the quartic invariant divided by `D²Ψ(k₀)[w, w]`. -/
theorem bridge : OscInt.API.TriBlueprint.Bridge := by
  intro Ψ k₀ v w ε h hΨ hker hw hε hred
  have hh := hred.1
  have h0 := hred.2.1
  set g := reducedFn Ψ k₀ v w h
  set c := fderiv ℝ Ψ k₀ v
  set A := jet Ψ k₀ v w h 1 ![v]
  set B := jet Ψ k₀ v w h 1 ![w]
  have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  -- Step 1: `g′ = A − c` near `0`, so `g^{(j+1)}(0) = A^{(j)}(0)` for `j ≥ 1`.
  have hg : deriv g =ᶠ[𝓝 0] fun u => A u - c := by
    filter_upwards [hball] with u hu
    exact (hasDerivAt_reducedFn hΨ hh hred (by simpa [Real.dist_eq] using hu)).deriv
  have hA : deriv (fun u => A u - c) = slot₁ Ψ k₀ v w h v := by
    funext u
    rw [deriv_sub_const, deriv_jet_one hΨ hh]
  have g3 : iteratedDeriv 3 g 0 = slot₂ Ψ k₀ v w h v 0 := by
    rw [iteratedDeriv_succ', hg.iteratedDeriv_eq, iteratedDeriv_succ', hA, iteratedDeriv_one,
      deriv_slot₁ hΨ hh]
  have g4 : iteratedDeriv 4 g 0 = deriv (slot₂ Ψ k₀ v w h v) 0 := by
    rw [iteratedDeriv_succ', hg.iteratedDeriv_eq, iteratedDeriv_succ', hA, iteratedDeriv_succ',
      deriv_slot₁ hΨ hh, iteratedDeriv_one]
  -- Step 3: `B` is constant near `0`, which gives `h′(0) = 0` and `D³[v, v, w] + h″(0) D²[w, w] = 0`.
  have hB : B =ᶠ[𝓝 0] fun _ => fderiv ℝ Ψ k₀ w := by
    filter_upwards [hball] with u hu
    have := hred.2.2 u (by simpa [Real.dist_eq] using hu)
    simpa [B, jet, iteratedFDeriv_one_apply, curve] using this
  have hB1 : slot₁ Ψ k₀ v w h w 0 = 0 := by
    have := hB.iteratedDeriv_eq 1
    rwa [iteratedDeriv_one, iteratedDeriv_one, deriv_jet_one hΨ hh, deriv_const] at this
  have hB2 : slot₂ Ψ k₀ v w h w 0 = 0 := by
    have := hB.iteratedDeriv_eq 2
    simp only [iteratedDeriv_succ', iteratedDeriv_zero, deriv_const'] at this
    rwa [deriv_jet_one hΨ hh, deriv_slot₁ hΨ hh] at this
  have hvw : iteratedFDeriv ℝ 2 Ψ k₀ ![v, w] = 0 := hker w
  have hwv : iteratedFDeriv ℝ 2 Ψ k₀ ![w, v] = 0 := by rw [iteratedFDeriv_two_swap hΨ, hker]
  have h1 : deriv h 0 = 0 := by
    simp only [slot₁, jet_zero h0, hvw, zero_add] at hB1
    exact (mul_eq_zero.1 hB1).resolve_right hw
  have h2 : iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] + deriv (deriv h) 0 * iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] = 0 := by
    simpa [slot₂, jet_zero h0, h1] using hB2
  -- Step 4: the third and fourth derivatives.
  refine ⟨?_, ?_⟩
  · rw [g3]
    simp [slot₂, jet_zero h0, h1, hwv]
  · rw [g4, deriv_slot₂_zero hΨ hh h0 h1, hwv, qinv, eq_div_iff hw,
      iteratedFDeriv_three_swap₁₂ hΨ k₀ w v v, iteratedFDeriv_three_swap₂₃ hΨ k₀ v w v]
    linear_combination 3 * iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] * h2

end OscInt.API.ReducedBridge
