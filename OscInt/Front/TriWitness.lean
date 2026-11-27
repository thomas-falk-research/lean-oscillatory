/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriBlueprint
import OscInt.Front.TriDeriv

/-! # Batch TRI, part P-wit: the A5 witness and the sextic

`docs/proof-TRI.md`, section 5, with the device of section 9, item 4. The computation is done once, at any point
`(x₀, y₀)` with `x₀ + y₀ ∈ 2πℤ` and `cos x₀ = −2α`, with `v = (1, 1)`, `w = (1, −1)`, in the variables
`c₀ = cos x₀`, `s₀ = sin x₀` (`c₀² = s₀² = 1/2`); the sign of `s₀` plays no role, so the same `w` serves every locus
point and no invariance lemma is needed.
* Steps 1 and 2: `reducedFn_eq`, `reducedCurve_iff` (via `triD1`, `triD2_mixed`).
* Steps 3 to 6: `gW_hasDerivAt`, `delta_identity`, `δW_derivs`, `gW_derivs` (Leibniz, `iteratedDeriv_fun_mul`, on a
  local identity, `EventuallyEq.iteratedDeriv_eq`).
* Step 7: `exists_cutoff`, `exists_curve` (`ContDiffBump`, `arcsin`), `point_A5`.
* `witSextic`, `witA5`: the blueprint propositions `WitSextic`, `WitA5`.
-/

namespace OscInt.API.TriWitness

open OscInt.Statements OscInt.API.TriDeriv OscInt.API.TriBlueprint
open Filter Topology
open scoped ContDiff

/-! ## The fourth power of the sine at `0` -/

/-- `−(1/2) sin⁴` and its derivatives, as a family. -/
noncomputable def sinQ (n : ℕ) (u : ℝ) : ℝ :=
  (if n = 0 then -(3 / 16) else 0) + cosT 2 0 n u / 4 - cosT 4 0 n u / 16

theorem sinQ_zero : sinQ 0 = fun u => -(1 / 2) * Real.sin u ^ 4 := by
  funext u
  simp only [sinQ, cosT, ite_true, pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero, zero_add]
  have h4 : Real.cos (u * 4) = 2 * Real.cos (u * 2) ^ 2 - 1 := by
    rw [show u * 4 = 2 * (u * 2) by ring, Real.cos_two_mul]
  rw [h4, show u * 2 = 2 * u by ring, Real.cos_two_mul]
  have hs : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by linarith [Real.sin_sq_add_cos_sq u]
  rw [show Real.sin u ^ 4 = (Real.sin u ^ 2) ^ 2 by ring, hs]
  ring

theorem sinQ_deriv (n : ℕ) : deriv (sinQ n) = sinQ (n + 1) := by
  funext u
  have := ((hasDerivAt_const u (if n = 0 then -(3 / 16) else (0 : ℝ))).add
    ((cosT_hasDerivAt 2 0 n u).div_const 4)).sub ((cosT_hasDerivAt 4 0 n u).div_const 16)
  have h2 : HasDerivAt (sinQ n) (0 + cosT 2 0 (n + 1) u / 4 - cosT 4 0 (n + 1) u / 16) u := this
  rw [h2.deriv]
  simp [sinQ]

theorem iteratedDeriv_sinQ (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => -(1 / 2) * Real.sin u ^ 4) = sinQ n := by
  induction n with
  | zero => rw [iteratedDeriv_zero, sinQ_zero]
  | succ n ih => rw [iteratedDeriv_succ, ih, sinQ_deriv]

theorem sinQ_vals : sinQ 0 0 = 0 ∧ sinQ 1 0 = 0 ∧ sinQ 2 0 = 0 ∧ sinQ 3 0 = 0 ∧ sinQ 4 0 = -12 := by
  have c3 : Real.cos (3 * (Real.pi / 2)) = 0 := by
    rw [show 3 * (Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp
  have c2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
  have c4 : Real.cos (4 * (Real.pi / 2)) = 1 := by
    rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring, Real.cos_two_pi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [sinQ, cosT, c2, c3, c4] <;> norm_num


/-! ## The core computation (section 5, steps 3 to 6), in the variables `c₀ = cos x₀`, `s₀ = sin x₀` -/

/-- The δ-identity of step 4, as a polynomial identity. -/
theorem delta_identity (c₀ s₀ a b c s : ℝ) (hc2 : c₀ ^ 2 = 1 / 2) (hs2 : s₀ ^ 2 = 1 / 2)
    (hab : b ^ 2 + a ^ 2 = 1) (hcs : s ^ 2 + c ^ 2 = 1) (hcurve : c * (s₀ * a + c₀ * b) = s₀) :
    (c₀ * a - s₀ * b - c₀ * c) * (2 * c₀ * c ^ 3 + (c₀ * a - s₀ * b - c₀ * c) * c ^ 2) =
      -(1 / 2) * s ^ 4 := by
  linear_combination (c ^ 2 * (a ^ 2 + b ^ 2)) * (hc2) + (c ^ 2 * (a ^ 2 + b ^ 2)) * hs2
    + c ^ 2 * hab - (c * (s₀ * a + c₀ * b) + s₀) * hcurve - hs2 - c ^ 4 * hc2
    + (1 / 2) * (s ^ 2 + 1 - c ^ 2) * hcs

/-- The reduced function in explicit form (step 1). -/
noncomputable def gW (α c₀ s₀ : ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  2 * Real.cos u * (c₀ * Real.cos (h u) - s₀ * Real.sin (h u)) + α * Real.cos (2 * u) + 2 * s₀ * h u

/-- `δ(u) = cos(θ + h u) − cos θ cos u` (step 3). -/
noncomputable def δW (c₀ s₀ : ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  c₀ * Real.cos (h u) - s₀ * Real.sin (h u) - c₀ * Real.cos u

theorem cdAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) : ContDiffAt ℝ n f x :=
  hf.contDiffAt.of_le (by exact_mod_cast le_top)

section Core

variable {α c₀ s₀ ε : ℝ} {h : ℝ → ℝ}

theorem δW_contDiff (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (δW c₀ s₀ h) := by
  unfold δW; fun_prop

/-- Steps 4 and 5: the derivatives of δ at `0`. -/
theorem δW_derivs (hε : 0 < ε) (hc2 : c₀ ^ 2 = 1 / 2) (hs2 : s₀ ^ 2 = 1 / 2)
    (hh : ContDiff ℝ ∞ h) (h0 : h 0 = 0)
    (hcurve : ∀ u, |u| < ε → Real.cos u * (s₀ * Real.cos (h u) + c₀ * Real.sin (h u)) = s₀) :
    iteratedDeriv 0 (δW c₀ s₀ h) 0 = 0 ∧ iteratedDeriv 1 (δW c₀ s₀ h) 0 = 0 ∧
      iteratedDeriv 2 (δW c₀ s₀ h) 0 = 0 ∧ iteratedDeriv 3 (δW c₀ s₀ h) 0 = 0 ∧
      iteratedDeriv 4 (δW c₀ s₀ h) 0 = -6 / c₀ := by
  set δ := δW c₀ s₀ h with hδdef
  set E : ℝ → ℝ := fun u => 2 * c₀ * Real.cos u ^ 3 + δ u * Real.cos u ^ 2 with hEdef
  have hδ : ContDiff ℝ ∞ δ := δW_contDiff hh
  have hE : ContDiff ℝ ∞ E := by rw [hEdef]; fun_prop
  have hloc : (fun u => δ u * E u) =ᶠ[𝓝 0] fun u => -(1 / 2) * Real.sin u ^ 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with u hu
    have hu' : |u| < ε := by simpa [Real.dist_eq] using hu
    exact delta_identity c₀ s₀ _ _ _ _ hc2 hs2 (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _)
      (hcurve u hu')
  have hL : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * iteratedDeriv i δ 0 * iteratedDeriv (n - i) E 0 = sinQ n 0 := by
    intro n
    rw [← iteratedDeriv_fun_mul (cdAt hδ n 0) (cdAt hE n 0), hloc.iteratedDeriv_eq, iteratedDeriv_sinQ]
  have hd0 : δ 0 = 0 := by simp [hδdef, δW, h0]
  have hE0 : E 0 = 2 * c₀ := by simp [hEdef, hd0]
  have hc0 : c₀ ≠ 0 := by rintro rfl; norm_num at hc2
  obtain ⟨q0, q1, q2, q3, q4⟩ := sinQ_vals
  have e1 := hL 1
  have e2 := hL 2
  have e3 := hL 3
  have e4 := hL 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero] at e1 e2 e3 e4
  norm_num [hd0, hE0] at e1 e2 e3 e4
  have h2c : 2 * c₀ ≠ 0 := mul_ne_zero two_ne_zero hc0
  have d1 : deriv δ 0 = 0 := (mul_eq_zero.1 (e1.trans q1)).resolve_right h2c
  have d2 : iteratedDeriv 2 δ 0 = 0 := by
    have : iteratedDeriv 2 δ 0 * (2 * c₀) = 0 := by rw [q2, d1] at e2; linarith
    exact (mul_eq_zero.1 this).resolve_right h2c
  have d3 : iteratedDeriv 3 δ 0 = 0 := by
    have : iteratedDeriv 3 δ 0 * (2 * c₀) = 0 := by rw [q3, d1, d2] at e3; linarith
    exact (mul_eq_zero.1 this).resolve_right h2c
  have d4 : iteratedDeriv 4 δ 0 * (2 * c₀) = -12 := by rw [q4, d1, d2, d3] at e4; linarith
  refine ⟨by rw [iteratedDeriv_zero]; exact hd0, by rw [iteratedDeriv_one]; exact d1, d2, d3, ?_⟩
  field_simp
  linarith

/-- Step 3: `g′ = −2 sin · δ` where the curve equation holds. -/
theorem gW_hasDerivAt (hc : c₀ = -2 * α) (hh : ContDiff ℝ ∞ h) (u : ℝ)
    (hcu : Real.cos u * (s₀ * Real.cos (h u) + c₀ * Real.sin (h u)) = s₀) :
    HasDerivAt (gW α c₀ s₀ h) (-2 * Real.sin u * δW c₀ s₀ h u) u := by
  have hd : HasDerivAt h (deriv h u) u := ((hh.differentiable (by simp)) u).hasDerivAt
  have H := ((((Real.hasDerivAt_cos u).const_mul 2).mul ((hd.cos.const_mul c₀).sub (hd.sin.const_mul s₀))).add
    ((((hasDerivAt_id' u).const_mul 2).cos).const_mul α)).add (hd.const_mul (2 * s₀))
  have key : 2 * -Real.sin u * (c₀ * Real.cos (h u) - s₀ * Real.sin (h u)) +
      2 * Real.cos u * (c₀ * (-Real.sin (h u) * deriv h u) - s₀ * (Real.cos (h u) * deriv h u)) +
      α * (-Real.sin (2 * u) * (2 * 1)) + 2 * s₀ * deriv h u = -2 * Real.sin u * δW c₀ s₀ h u := by
    rw [δW, Real.sin_two_mul]
    linear_combination (-2 * deriv h u) * hcu - 2 * Real.sin u * Real.cos u * hc
  convert H using 1
  · rfl
  · exact key.symm

/-- Step 6: the derivatives of the reduced function at `0`. -/
theorem gW_derivs (hε : 0 < ε) (hc : c₀ = -2 * α) (hc2 : c₀ ^ 2 = 1 / 2) (hs2 : s₀ ^ 2 = 1 / 2)
    (hh : ContDiff ℝ ∞ h) (h0 : h 0 = 0)
    (hcurve : ∀ u, |u| < ε → Real.cos u * (s₀ * Real.cos (h u) + c₀ * Real.sin (h u)) = s₀) :
    (∀ j ∈ Finset.Icc 1 5, iteratedDeriv j (gW α c₀ s₀ h) 0 = 0) ∧
      iteratedDeriv 6 (gW α c₀ s₀ h) 0 = -30 / α := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := δW_derivs hε hc2 hs2 hh h0 hcurve
  rw [iteratedDeriv_zero] at d0
  rw [iteratedDeriv_one] at d1
  set δ := δW c₀ s₀ h with hδdef
  have hδ : ContDiff ℝ ∞ δ := δW_contDiff hh
  have hS : ContDiff ℝ ∞ (fun u : ℝ => -2 * Real.sin u) := by fun_prop
  have hev : deriv (gW α c₀ s₀ h) =ᶠ[𝓝 0] fun u => -2 * Real.sin u * δ u := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with u hu
    exact (gW_hasDerivAt hc hh u (hcurve u (by simpa [Real.dist_eq] using hu))).deriv
  have hG : ∀ n : ℕ, iteratedDeriv (n + 1) (gW α c₀ s₀ h) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * iteratedDeriv i (fun u : ℝ => -2 * Real.sin u) 0 * iteratedDeriv (n - i) δ 0 := by
    intro n
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_fun_mul (cdAt hS n 0) (cdAt hδ n 0)]
  have hc0 : c₀ ≠ 0 := by rintro rfl; norm_num at hc2
  have hα : α ≠ 0 := by rintro rfl; apply hc0; rw [hc]; ring
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [Finset.mem_Icc] at hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have hn : n ≤ 4 := by omega
    rw [hG]
    interval_cases n <;> simp [Finset.sum_range_succ, d0, d1, d2, d3]
  · rw [hG]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [d0, d1, d2, d3, d4]
    rw [hc]
    field_simp
    ring

end Core

/-! ## Explicit forms at a point with `x₀ + y₀ ∈ 2πℤ` (section 5, steps 1 and 2) -/

section Point

variable {α x₀ y₀ : ℝ}

theorem curve_point (u t : ℝ) :
    ((x₀, y₀) + u • ((1 : ℝ), (1 : ℝ)) + t • ((1 : ℝ), (-1 : ℝ)) : ℝ × ℝ) = (x₀ + (u + t), y₀ + (u - t)) := by
  ext <;> simp <;> ring

theorem cos_y₀ (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) : Real.cos y₀ = Real.cos x₀ := by
  rw [show y₀ = (x₀ + y₀) - x₀ by ring, Real.cos_sub, hp, hps]; ring

theorem sin_y₀ (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) : Real.sin y₀ = -Real.sin x₀ := by
  rw [show y₀ = (x₀ + y₀) - x₀ by ring, Real.sin_sub, hp, hps]; ring

theorem phase_curve (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) (u t : ℝ) :
    triPhase α ((x₀, y₀) + u • ((1 : ℝ), (1 : ℝ)) + t • ((1 : ℝ), (-1 : ℝ))) =
      2 * Real.cos u * (Real.cos x₀ * Real.cos t - Real.sin x₀ * Real.sin t) + α * Real.cos (2 * u) := by
  rw [curve_point]
  simp only [triPhase]
  rw [show x₀ + (u + t) + (y₀ + (u - t)) = (x₀ + y₀) + 2 * u by ring, Real.cos_add (x₀ + y₀), hp, hps,
    Real.cos_add x₀, Real.cos_add y₀, cos_y₀ hp hps, sin_y₀ hp hps, Real.cos_add u t, Real.sin_add u t,
    Real.cos_sub u t, Real.sin_sub u t]
  ring

theorem fderiv_curve (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) (u t : ℝ) :
    fderiv ℝ (triPhase α) ((x₀, y₀) + u • ((1 : ℝ), (1 : ℝ)) + t • ((1 : ℝ), (-1 : ℝ))) ((1 : ℝ), (-1 : ℝ)) =
      -2 * Real.cos u * (Real.sin x₀ * Real.cos t + Real.cos x₀ * Real.sin t) := by
  rw [curve_point, triD1]
  simp only
  rw [Real.sin_add x₀, Real.sin_add y₀, cos_y₀ hp hps, sin_y₀ hp hps, Real.cos_add u t, Real.sin_add u t,
    Real.cos_sub u t, Real.sin_sub u t]
  ring

theorem fderiv_base_w (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) :
    fderiv ℝ (triPhase α) (x₀, y₀) ((1 : ℝ), (-1 : ℝ)) = -2 * Real.sin x₀ := by
  rw [triD1]
  simp only
  rw [sin_y₀ hp hps]
  ring

theorem fderiv_base (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) (u t : ℝ) :
    fderiv ℝ (triPhase α) (x₀, y₀) (u • ((1 : ℝ), (1 : ℝ)) + t • ((1 : ℝ), (-1 : ℝ))) = -2 * Real.sin x₀ * t := by
  rw [triD1]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [sin_y₀ hp hps, hps]
  ring

theorem reducedFn_eq (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) (h : ℝ → ℝ) :
    reducedFn (triPhase α) (x₀, y₀) ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (-1 : ℝ)) h =
      gW α (Real.cos x₀) (Real.sin x₀) h := by
  funext u
  rw [reducedFn, phase_curve hp hps, fderiv_base hp hps, gW]
  ring

theorem reducedCurve_iff (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) (ε : ℝ) (h : ℝ → ℝ) :
    ReducedCurve (triPhase α) (x₀, y₀) ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (-1 : ℝ)) ε h ↔
      ContDiff ℝ ∞ h ∧ h 0 = 0 ∧ ∀ u, |u| < ε →
        Real.cos u * (Real.sin x₀ * Real.cos (h u) + Real.cos x₀ * Real.sin (h u)) = Real.sin x₀ := by
  unfold ReducedCurve
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun u => imp_congr_right fun _ => ?_))
  rw [fderiv_curve hp hps, fderiv_base_w hp hps]
  constructor <;> intro H <;> linarith

theorem hess_kernel (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0)
    (hcx : Real.cos x₀ = -2 * α) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (triPhase α) (x₀, y₀) ![((1 : ℝ), (1 : ℝ)), z] = 0 := by
  rw [triD2_mixed]
  simp only
  rw [cos_y₀ hp hps, hp, hcx]
  ring

theorem hess_w (hp : Real.cos (x₀ + y₀) = 1) (hps : Real.sin (x₀ + y₀) = 0) :
    iteratedFDeriv ℝ 2 (triPhase α) (x₀, y₀) ![((1 : ℝ), (-1 : ℝ)), ((1 : ℝ), (-1 : ℝ))] =
      -2 * Real.cos x₀ := by
  rw [triD2_mixed]
  simp only
  rw [cos_y₀ hp hps]
  ring

end Point

/-! ## Existence of a reduced curve (section 5, step 7) -/

/-- A smooth `ψ` with `ψ = id` on `|u| < 1/8` and `|ψ| ≤ 1/4` (a `ContDiffBump` times the identity). -/
theorem exists_cutoff : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ u, |u| < 1 / 8 → ψ u = u) ∧ ∀ u, |ψ u| ≤ 1 / 4 := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨fun u => u * φ u, contDiff_id.mul φ.contDiff, fun u hu => ?_, fun u => ?_⟩
  · show u * φ u = u
    rw [φ.one_of_mem_closedBall (by simp [φ]; linarith), mul_one]
  · show |u * φ u| ≤ 1 / 4
    by_cases hu : |u| < 1 / 4
    · rw [abs_mul, abs_of_nonneg φ.nonneg]
      calc |u| * φ u ≤ |u| * 1 := by gcongr; exact φ.le_one
        _ ≤ 1 / 4 := by linarith
    · rw [φ.zero_of_le_dist (by simp [φ]; linarith)]; simp

/-- Step 7: a reduced curve on `|u| < 1/8`, through `arcsin`. -/
theorem exists_curve {c₀ s₀ : ℝ} (hc2 : c₀ ^ 2 = 1 / 2) (hs2 : s₀ ^ 2 = 1 / 2) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      ∀ u, |u| < 1 / 8 → Real.cos u * (s₀ * Real.cos (h u) + c₀ * Real.sin (h u)) = s₀ := by
  obtain ⟨ψ, hψ, hψid, hψb⟩ := exists_cutoff
  have hcosψ : ∀ u, 31 / 32 ≤ Real.cos (ψ u) := by
    intro u
    have h1 := Real.one_sub_sq_div_two_le_cos (x := ψ u)
    have h2 := abs_le.1 (hψb u)
    nlinarith
  set z : ℝ → ℝ := fun u => s₀ / Real.cos (ψ u) with hzdef
  have hz : ContDiff ℝ ∞ z :=
    contDiff_const.div (Real.contDiff_cos.comp hψ) fun u => by have := hcosψ u; positivity
  have hzlt : ∀ u, -1 < z u ∧ z u < 1 := by
    intro u
    have hc := hcosψ u
    have hcpos : 0 < Real.cos (ψ u) := by linarith
    have h1 : s₀ < Real.cos (ψ u) := by nlinarith
    have h2 : -Real.cos (ψ u) < s₀ := by nlinarith
    exact ⟨by rw [hzdef, lt_div_iff₀ hcpos]; linarith, by rw [hzdef, div_lt_one hcpos]; exact h1⟩
  have hzs : ContDiff ℝ ∞ fun u => Real.arcsin (z u) :=
    contDiff_iff_contDiffAt.2 fun u =>
      (Real.contDiffAt_arcsin (hzlt u).1.ne' (hzlt u).2.ne).comp u hz.contDiffAt
  have hsinb : ∀ u, Real.sin (Real.arcsin (z u)) = z u := fun u =>
    Real.sin_arcsin (hzlt u).1.le (hzlt u).2.le
  have hz0 : z 0 = s₀ := by
    have : ψ 0 = 0 := hψid 0 (by norm_num)
    simp [hzdef, this]
  have hs1 : -1 ≤ s₀ ∧ s₀ ≤ 1 := by constructor <;> nlinarith
  set a := Real.arcsin s₀ with hadef
  have hsa : Real.sin a = s₀ := Real.sin_arcsin hs1.1 hs1.2
  have hca : Real.cos a = |c₀| := by
    rw [hadef, Real.cos_arcsin, ← Real.sqrt_sq_eq_abs, hc2, hs2]; norm_num
  have hpa := Real.sin_sq_add_cos_sq a
  suffices H : ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧
      ∀ u, s₀ * Real.cos (h u) + c₀ * Real.sin (h u) = z u by
    obtain ⟨h, hh, h0, hS⟩ := H
    refine ⟨h, hh, h0, fun u hu => ?_⟩
    have hψu := hψid u hu
    have hcu : Real.cos u ≠ 0 := by have := hcosψ u; rw [hψu] at this; positivity
    rw [hS u, hzdef]
    simp only [hψu]
    field_simp
  rcases le_or_gt 0 c₀ with hc0 | hc0
  · rw [abs_of_nonneg hc0] at hca
    refine ⟨fun u => Real.arcsin (z u) - a, hzs.sub contDiff_const, by simp [hz0, hadef], fun u => ?_⟩
    simp only
    rw [Real.cos_sub, Real.sin_sub, hsinb, ← hsa, ← hca]
    linear_combination z u * hpa
  · rw [abs_of_neg hc0] at hca
    refine ⟨fun u => a - Real.arcsin (z u), contDiff_const.sub hzs, by simp [hz0, hadef], fun u => ?_⟩
    simp only
    rw [Real.cos_sub, Real.sin_sub, hsinb, ← hsa, show c₀ = -Real.cos a by rw [hca]; ring]
    linear_combination z u * hpa

/-! ## The exceptional coupling and the final theorems -/

section Final

variable {α : ℝ}

theorem alpha_sq (hα : |α| = triExceptional) : α ^ 2 = 1 / 8 := by
  rw [← sq_abs, hα, triExceptional_sq]

theorem cos_arccos_alpha (hα : |α| = triExceptional) : Real.cos (Real.arccos (-2 * α)) = -2 * α := by
  have h := abs_lt.1 (hα ▸ triExceptional_lt_half)
  exact Real.cos_arccos (by linarith) (by linarith)

/-- `−30/α = −60√2 · sign α` when `|α| = 1/(2√2)`. -/
theorem sextic_value (hα : |α| = triExceptional) : -30 / α = -60 * Real.sqrt 2 * SignType.sign α := by
  rw [triExceptional] at hα
  have hs : 0 < Real.sqrt 2 := by positivity
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rcases lt_trichotomy α 0 with h | h | h
  · rw [sign_neg h, abs_of_neg h] at *
    have : α = -(1 / (2 * Real.sqrt 2)) := by linarith
    subst this; simp only [SignType.coe_neg, SignType.coe_one]; field_simp; nlinarith
  · subst h; simp at hα
  · rw [sign_pos h, abs_of_pos h] at *
    subst hα; simp only [SignType.coe_one]; field_simp; nlinarith

/-- Every point with `x₀ + y₀ ∈ 2πℤ` and `cos x₀ = −2α`, `|α| = a*`, is an A5 point, with `v = (1, 1)`,
`w = (1, −1)` (section 5, step 7, and section 9, item 4). -/
theorem point_A5 (hα : |α| = triExceptional) {x₀ y₀ : ℝ} (hp : Real.cos (x₀ + y₀) = 1)
    (hps : Real.sin (x₀ + y₀) = 0) (hcx : Real.cos x₀ = -2 * α) : IsA5Point (triPhase α) (x₀, y₀) := by
  have hα2 := alpha_sq hα
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα2
  have hc2 : Real.cos x₀ ^ 2 = 1 / 2 := by rw [hcx]; nlinarith
  have hs2 : Real.sin x₀ ^ 2 = 1 / 2 := by nlinarith [Real.sin_sq_add_cos_sq x₀]
  obtain ⟨h, hh, h0, hcu⟩ := exists_curve hc2 hs2
  obtain ⟨H1, H6⟩ := gW_derivs (by norm_num : (0 : ℝ) < 1 / 8) hcx hc2 hs2 hh h0 hcu
  refine ⟨((1 : ℝ), (1 : ℝ)), ((1 : ℝ), (-1 : ℝ)), by simp, hess_kernel hp hps hcx, ?_, 1 / 8, by norm_num, h,
    (reducedCurve_iff hp hps _ h).2 ⟨hh, h0, hcu⟩, ?_, ?_⟩
  · rw [hess_w hp hps, hcx]
    intro H; apply hα0; linarith
  · rw [reducedFn_eq hp hps]; exact H1
  · rw [reducedFn_eq hp hps, H6]
    exact div_ne_zero (by norm_num) hα0

/-- **P-wit, the sextic** (section 5, steps 1 to 6). -/
theorem witSextic : OscInt.API.TriBlueprint.WitSextic := by
  intro α hα ε h hε hrc
  set θ := Real.arccos (-2 * α)
  have hp : Real.cos (θ + -θ) = 1 := by simp
  have hps : Real.sin (θ + -θ) = 0 := by simp
  have hcx := cos_arccos_alpha hα
  have hα2 := alpha_sq hα
  have hc2 : Real.cos θ ^ 2 = 1 / 2 := by rw [hcx]; nlinarith
  have hs2 : Real.sin θ ^ 2 = 1 / 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  obtain ⟨hh, h0, hcu⟩ := (reducedCurve_iff hp hps ε h).1 hrc
  rw [reducedFn_eq hp hps, (gW_derivs hε hcx hc2 hs2 hh h0 hcu).2, sextic_value hα]

/-- **P-wit, existence** (section 5, step 7, with the device of section 9, item 4). -/
theorem witA5 : OscInt.API.TriBlueprint.WitA5 := by
  intro α hα k ⟨j₁, j₂, hk⟩
  have hcx := cos_arccos_alpha hα
  set θ := Real.arccos (-2 * α)
  have hsum : ∀ a b : ℝ, a + b = 0 → Real.cos (a + 2 * Real.pi * j₁ + (b + 2 * Real.pi * j₂)) = 1 ∧
      Real.sin (a + 2 * Real.pi * j₁ + (b + 2 * Real.pi * j₂)) = 0 := by
    intro a b hab
    constructor
    · rw [show a + 2 * Real.pi * j₁ + (b + 2 * Real.pi * j₂) = ((j₁ + j₂ : ℤ) : ℝ) * (2 * Real.pi) by
        push_cast; linear_combination hab, Real.cos_int_mul_two_pi]
    · rw [show a + 2 * Real.pi * j₁ + (b + 2 * Real.pi * j₂) = ((2 * (j₁ + j₂) : ℤ) : ℝ) * Real.pi by
        push_cast; linear_combination hab, Real.sin_int_mul_pi]
  rcases hk with rfl | rfl
  · obtain ⟨hp, hps⟩ := hsum θ (-θ) (by ring)
    refine point_A5 hα hp hps ?_
    rw [show θ + 2 * Real.pi * j₁ = θ + (j₁ : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi, hcx]
  · obtain ⟨hp, hps⟩ := hsum (-θ) θ (by ring)
    refine point_A5 hα hp hps ?_
    rw [show -θ + 2 * Real.pi * j₁ = -θ + (j₁ : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi,
      Real.cos_neg, hcx]

end Final

end OscInt.API.TriWitness
