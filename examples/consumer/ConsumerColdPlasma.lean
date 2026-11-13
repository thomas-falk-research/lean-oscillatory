/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: transverse waves in a cold plasma (GD-N)

Only `import OscInt.API` and Mathlib. Answers the external application study of 2026-11-10
(`review/2026-11-10-external-followup-answers.md`, "The plasma application study").

Model (paper, not formalised here): a linear, homogeneous, cold, collisionless electron plasma with fixed ions, no
background magnetic field and the electric field along `z` obeys `∂_t² E_z − c² ΔE_z + ω_p² E_z = 0`, with dispersion
relation `ω = (ω_p² + c²|k|²)^{1/2}`. In the dimensionless variables `τ = ω_p t`, `X = ω_p x / c`, `κ = c k / ω_p`, a
transverse wave packet is `u(τ, X) = (2π)^{−2} ∫ e^{i(κ·X − τ (1 + |κ|²)^{1/2})} A(κ) dκ`. With
`Ψ(κ) = −(1 + κ₁² + κ₂²)^{1/2}`, `m = τ` and the linear term `L κ = (κ₁ X₁ + κ₂ X₂)/τ`, the integral is the one of GD-N.

This file proves that `Ψ` is smooth (analytic) on ℝ² (`plasmaPhase_contDiff`), that its Hessian determinant is
`(1 + κ₁² + κ₂²)^{−2} ≠ 0` everywhere (`plasmaPhase_hessian_det`), and applies the proved GD-N
(`OscInt.API.globalNondeg`, with `U = ℝ²`) to get `‖∫‖ ≤ C M / τ` (`coldPlasma_decay`).

The max-norm hazard: Lean's `‖κ‖` on `ℝ × ℝ` is the max norm, so the phase is written coordinatewise; written with
`‖κ‖ ^ 2` it would be a different (and non-smooth) function (`maxNorm_bite`).
-/

open OscInt.Statements

namespace ConsumerColdPlasma

/-- The dimensionless cold-plasma phase `Ψ(κ) = −(1 + κ₁² + κ₂²)^{1/2}` (coordinatewise, not with the max norm). -/
noncomputable def plasmaPhase (κ : ℝ × ℝ) : ℝ := -Real.sqrt (1 + κ.1 ^ 2 + κ.2 ^ 2)

theorem quad_pos (κ : ℝ × ℝ) : 0 < 1 + κ.1 ^ 2 + κ.2 ^ 2 := by positivity

/-- `Ψ` is analytic on ℝ² (`ContDiff ℝ ⊤`, i.e. `C^ω`, in this Mathlib). -/
theorem plasmaPhase_contDiff : ContDiff ℝ ⊤ plasmaPhase := by
  have h : ContDiff ℝ ⊤ (fun κ : ℝ × ℝ => 1 + κ.1 ^ 2 + κ.2 ^ 2) := by fun_prop
  exact (h.sqrt fun κ => (quad_pos κ).ne').neg

/-- The derivative in direction `v`, read off a derivative along the line `y + t v`. -/
theorem fderiv_apply_of_line {f : ℝ × ℝ → ℝ} {y v : ℝ × ℝ} {d : ℝ} (hf : DifferentiableAt ℝ f y)
    (h : HasDerivAt (fun t : ℝ => f (y + t • v)) d 0) : fderiv ℝ f y v = d := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact HasLineDerivAt.lineDeriv h

theorem hasDerivAt_quad_line (y v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => 1 + (y + t • v).1 ^ 2 + (y + t • v).2 ^ 2) (2 * (y.1 * v.1 + y.2 * v.2)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => y.1 + t * v.1) v.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add y.1
  have h2 : HasDerivAt (fun t : ℝ => y.2 + t * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add y.2
  have h := ((h1.pow 2).add (h2.pow 2)).const_add 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  convert h using 1
  · ext t; simp only [Pi.add_apply, Pi.pow_apply]; ring
  · simp; ring

/-- The first derivative: `DΨ(y) v = −(y · v) / (1 + |y|²)^{1/2}`. -/
theorem fderiv_plasmaPhase (y v : ℝ × ℝ) :
    fderiv ℝ plasmaPhase y v = -(y.1 * v.1 + y.2 * v.2) / Real.sqrt (1 + y.1 ^ 2 + y.2 ^ 2) := by
  have hq := quad_pos y
  have hs : 0 < Real.sqrt (1 + y.1 ^ 2 + y.2 ^ 2) := Real.sqrt_pos.2 hq
  refine fderiv_apply_of_line (plasmaPhase_contDiff.differentiable (by simp) y) ?_
  have h := ((hasDerivAt_quad_line y v).sqrt (by simpa using hq.ne')).neg
  simp only [zero_smul, add_zero] at h
  convert h using 1
  · rfl
  · field_simp

/-- The first derivative in direction `v` as a function of the point. -/
noncomputable def grad (v : ℝ × ℝ) (y : ℝ × ℝ) : ℝ :=
  -(y.1 * v.1 + y.2 * v.2) / Real.sqrt (1 + y.1 ^ 2 + y.2 ^ 2)

theorem grad_differentiable (v : ℝ × ℝ) : Differentiable ℝ (grad v) := by
  intro y
  have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => 1 + y.1 ^ 2 + y.2 ^ 2) y := by fun_prop
  have hN : DifferentiableAt ℝ (fun y : ℝ × ℝ => -(y.1 * v.1 + y.2 * v.2)) y := by fun_prop
  have hS : DifferentiableAt ℝ (fun y : ℝ × ℝ => Real.sqrt (1 + y.1 ^ 2 + y.2 ^ 2)) y :=
    hd.sqrt (quad_pos y).ne'
  have e : grad v = fun y : ℝ × ℝ => -(y.1 * v.1 + y.2 * v.2) * (Real.sqrt (1 + y.1 ^ 2 + y.2 ^ 2))⁻¹ := by
    funext y; simp only [grad, div_eq_mul_inv]
  rw [e]
  exact hN.mul (hS.inv (Real.sqrt_pos.2 (quad_pos y)).ne')

/-- The second derivative: `D²Ψ(k)[v, w] = ((k · v)(k · w) − (v · w)(1 + |k|²)) / (1 + |k|²)^{3/2}`. -/
theorem dd_plasmaPhase (k v w : ℝ × ℝ) :
    dd plasmaPhase k v w = ((k.1 * v.1 + k.2 * v.2) * (k.1 * w.1 + k.2 * w.2) -
      (v.1 * w.1 + v.2 * w.2) * (1 + k.1 ^ 2 + k.2 ^ 2)) / Real.sqrt (1 + k.1 ^ 2 + k.2 ^ 2) ^ 3 := by
  have hfun : (fun y => fderiv ℝ plasmaPhase y v) = grad v := funext fun y => fderiv_plasmaPhase y v
  rw [dd, hfun]
  have hq := quad_pos k
  have hs : 0 < Real.sqrt (1 + k.1 ^ 2 + k.2 ^ 2) := Real.sqrt_pos.2 hq
  have hss : Real.sqrt (1 + k.1 ^ 2 + k.2 ^ 2) ^ 2 = 1 + k.1 ^ 2 + k.2 ^ 2 := Real.sq_sqrt hq.le
  refine fderiv_apply_of_line (grad_differentiable v k) ?_
  have hS := (hasDerivAt_quad_line k w).sqrt (by simpa using hq.ne')
  have hN : HasDerivAt (fun t : ℝ => -((k + t • w).1 * v.1 + (k + t • w).2 * v.2))
      (-(w.1 * v.1 + w.2 * v.2)) 0 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h1 : HasDerivAt (fun t : ℝ => (k.1 + t * w.1) * v.1) (w.1 * v.1) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const w.1).const_add k.1).mul_const v.1
    have h2 : HasDerivAt (fun t : ℝ => (k.2 + t * w.2) * v.2) (w.2 * v.2) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const w.2).const_add k.2).mul_const v.2
    exact (h1.add h2).neg
  have h := hN.div hS (by simpa using hs.ne')
  simp only [zero_smul, add_zero] at h
  convert h using 1
  · rfl
  · field_simp
    rw [hss]
    ring

/-- **The Hessian determinant** of the cold-plasma phase is `(1 + κ₁² + κ₂²)^{−2}`. -/
theorem plasmaPhase_hessian_det (κ : ℝ × ℝ) :
    (hessianMatrix plasmaPhase κ).det = 1 / (1 + κ.1 ^ 2 + κ.2 ^ 2) ^ 2 := by
  rw [← OscInt.API.hessDet_eq_det plasmaPhase κ (plasmaPhase_contDiff.contDiffAt.of_le (by simp)), hessDet,
    dd_plasmaPhase, dd_plasmaPhase, dd_plasmaPhase]
  have hq := quad_pos κ
  have hs : 0 < Real.sqrt (1 + κ.1 ^ 2 + κ.2 ^ 2) := Real.sqrt_pos.2 hq
  have hss : Real.sqrt (1 + κ.1 ^ 2 + κ.2 ^ 2) ^ 2 = 1 + κ.1 ^ 2 + κ.2 ^ 2 := Real.sq_sqrt hq.le
  set s := Real.sqrt (1 + κ.1 ^ 2 + κ.2 ^ 2)
  rw [← hss]
  field_simp
  rw [hss]
  ring

theorem plasmaPhase_hessian_det_ne (κ : ℝ × ℝ) : (hessianMatrix plasmaPhase κ).det ≠ 0 := by
  rw [plasmaPhase_hessian_det]
  have := quad_pos κ
  positivity

/-- **Dispersive decay of cold-plasma transverse waves** (GD-N with `U = ℝ²`).

For every compact `K` there is `C` such that for every `C²` amplitude `A` supported in `K` with derivatives of order
`≤ 2` bounded by `M` (Mathlib's operator norms over `ℝ × ℝ` with the max norm), every linear term `L` and every
`τ ≥ 1`, `‖∫ e^{iτ(Ψ(κ) + L κ)} A(κ) dκ‖ ≤ C M / τ`. The constant is chosen before `L`, so with
`L κ = (κ₁ X₁ + κ₂ X₂)/τ` the bound `‖u(τ, X)‖ ≤ (2π)^{−2} C M / τ` is uniform in the observation point `X`.

Paper step, not formalised: the derivation of the wave equation `∂_t² E_z − c² ΔE_z + ω_p² E_z = 0` for a linear cold
collisionless electron plasma with fixed ions, `B₀ = 0` and `E` along `z`, its dispersion relation
`ω = (ω_p² + c²|k|²)^{1/2}`, the rescaling to dimensionless variables and the Fourier representation of `u`.
What it does not give: no damping (Landau or collisional), no nonlinear or kinetic effects, nothing about control or
simulation, and no explicit value of `C`. -/
theorem coldPlasma_decay (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (τ : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ τ →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(τ * (plasmaPhase k + L k)) * Complex.I) * A k‖ ≤ C * M / τ :=
  OscInt.API.globalNondeg plasmaPhase K Set.univ hK isOpen_univ (Set.subset_univ K)
    (plasmaPhase_contDiff.of_le (by simp)).contDiffOn fun κ _ => plasmaPhase_hessian_det_ne κ

/-- The max-norm hazard (bite datum): `‖(1, 1)‖² = 1` in Lean, not `1² + 1² = 2`, so `‖κ‖ ^ 2` is not `|κ|²`. -/
theorem maxNorm_bite : ‖((1 : ℝ), (1 : ℝ))‖ ^ 2 ≠ (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 := by
  simp [Prod.norm_def]

end ConsumerColdPlasma
