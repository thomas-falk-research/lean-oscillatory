/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase

/-!
# S2/S3 local analysis: normal form at a critical point (L2) and non-critical points (L1)

This file proves the blueprint propositions
* `OscInt.Blueprint.NormalFormFacts` (`normalForm`): at a critical point `k₀` of a `C⁴` phase `Ψ` with nonzero
  Hessian, a linear change of coordinates `k ↦ k₀ + L k` brings `Ψ` into the normal form `NormalPoint 2`
  (nondegenerate Hessian) or `NormalPoint 3` (fold: rank-one Hessian, nonzero cubic term along the kernel);
* `OscInt.Blueprint.LocalNonCritFacts` (`localNonCrit`): near a non-critical point of a `C²` family, the
  oscillatory integral decays like `m⁻¹`, uniformly on a neighbourhood of the parameter.

Route (`docs/proof-S2S3.md`, (L1), (L2) and revision items 1, 2).
(L2) By the chain rule `dd (Ψ ∘ (k₀ + L·)) 0 v w = dd Ψ k₀ (L v) (L w)` and likewise for `ddd`
(`dd_comp_affine`, `ddd_comp_affine`). By symmetry of second derivatives (`ContDiffAt.isSymmSndFDerivAt`) the
form `dd Ψ k₀` is given by three numbers `h₁₁, h₁₂, h₂₂` (`dd_eq_coord`). A direction `w` with
`H(w, w) ≠ 0` and an `H`-orthogonal `v` independent of `w` are written down explicitly (`exists_orth_pair`),
and `L` is the matrix with columns `v, w` (`exists_equiv_cols`). In the nondegenerate case `H(v, v) ≠ 0`
(`orth_self_ne_zero`); in the degenerate case `v` spans the kernel (`orth_mem_ker`, the rank-one identity
`H(v, z) H(w, w) = H(v, w) H(w, z)` when `det H = 0`).
(L1) Choose a coordinate direction `e` with `∂_e Q_{τ₀}(k₀) ≠ 0`. Joint continuity at `(τ₀, k₀)` gives a
product neighbourhood `U × ball k₀ ε` on which `|∂_e Q_τ| ≥ c > 0` and `‖D²Q_τ‖ ≤ D` (no compactness is
needed). For `A` supported in `closedBall k₀ (ε/2)` write `A = ∂_e Q · B` with `B = A / ∂_e Q` (`C¹`, compactly
supported) and integrate by parts once in direction `e`
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`): `i m I(mQ, A) = -∫ e^{imQ} ∂_e B`, and
`|∂_e B| ≤ (1/c + D/c²) M` (`norm_oscInt2_le_of_lower_fderiv`).
-/

namespace OscInt.StationaryPhase.LocalAux

open Set MeasureTheory Complex OscInt.Statements

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Directional derivative of `f` composed with an affine map `y ↦ a + L y`. -/
theorem fderiv_comp_affine_apply {f : E → F} (a : E) (L : G →L[ℝ] E) (x v : G)
    (hf : DifferentiableAt ℝ f (a + L x)) :
    fderiv ℝ (fun y => f (a + L y)) x v = fderiv ℝ f (a + L x) (L v) := by
  have hL : HasFDerivAt (fun y => a + L y) L x := L.hasFDerivAt.const_add a
  rw [show (fun y => f (a + L y)) = f ∘ fun y => a + L y from rfl, (hf.hasFDerivAt.comp x hL).fderiv]
  rfl

/-- For `f ∈ Cⁿ⁺¹`, the directional derivative `y ↦ Df(y) v` is `Cⁿ`. -/
theorem contDiff_fderiv_apply {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) (v : E) :
    ContDiff ℝ n (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

/-- `dd` of a `C²` function composed with an affine map. -/
theorem dd_comp_affine {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (y v w : ℝ × ℝ) : dd (fun k => Ψ (k₀ + L k)) y v w = dd Ψ (k₀ + L y) (L v) (L w) := by
  have h1 : (fun y => fderiv ℝ (fun k => Ψ (k₀ + L k)) y v) =
      fun y => (fun z => fderiv ℝ Ψ z (L v)) (k₀ + L y) :=
    funext fun y => fderiv_comp_affine_apply k₀ L y v (hΨ.differentiable (by norm_num) _)
  unfold dd
  rw [h1, fderiv_comp_affine_apply k₀ L y w
    ((contDiff_fderiv_apply (n := 1) hΨ (L v)).differentiable (by norm_num) _)]

/-- `ddd` of a `C³` function composed with an affine map. -/
theorem ddd_comp_affine {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (k₀ : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (y u v w : ℝ × ℝ) :
    ddd (fun k => Ψ (k₀ + L k)) y u v w = ddd Ψ (k₀ + L y) (L u) (L v) (L w) := by
  have h1 : (fun y => dd (fun k => Ψ (k₀ + L k)) y u v) =
      fun y => (fun z => dd Ψ z (L u) (L v)) (k₀ + L y) :=
    funext fun y => dd_comp_affine (hΨ.of_le (by norm_num)) k₀ L y u v
  have h2 : ContDiff ℝ 1 (fun z => dd Ψ z (L u) (L v)) :=
    contDiff_fderiv_apply (n := 1) (contDiff_fderiv_apply (n := 2) hΨ (L u)) (L v)
  unfold ddd
  rw [h1, fderiv_comp_affine_apply k₀ L y w (h2.differentiable (by norm_num) _)]

/-- `dd Ψ k v w` is the second derivative `D²Ψ(k) w v`. -/
theorem dd_eq_fderiv_fderiv {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (h : DifferentiableAt ℝ (fderiv ℝ Ψ) k)
    (v w : ℝ × ℝ) : dd Ψ k v w = fderiv ℝ (fderiv ℝ Ψ) k w v := by
  unfold dd
  rw [fderiv_clm_apply h (differentiableAt_const v)]
  simp

/-- Coordinate formula for the symmetric bilinear form `dd Ψ k` of a `C²` function. -/
theorem dd_eq_coord {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (k a b : ℝ × ℝ) :
    dd Ψ k a b = a.1 * b.1 * dd Ψ k (1, 0) (1, 0) + (a.1 * b.2 + a.2 * b.1) * dd Ψ k (1, 0) (0, 1) +
      a.2 * b.2 * dd Ψ k (0, 1) (0, 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) k :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _
  have hs := (hΨ.contDiffAt (x := k)).isSymmSndFDerivAt (by simp)
  simp only [dd_eq_fderiv_fderiv hd]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have ha : ((a1, a2) : ℝ × ℝ) = a1 • ((1 : ℝ), (0 : ℝ)) + a2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  have hb : ((b1, b2) : ℝ × ℝ) = b1 • ((1 : ℝ), (0 : ℝ)) + b2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [ha, hb]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hs (1, 0) (0, 1)]
  ring

/-- A linear automorphism of `ℝ²` with prescribed columns `v`, `w` (nonzero determinant). -/
theorem exists_equiv_cols (v w : ℝ × ℝ) (h : v.1 * w.2 - v.2 * w.1 ≠ 0) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), L (1, 0) = v ∧ L (0, 1) = w := by
  let f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w
  obtain ⟨d, hd⟩ : ∃ d, d = v.1 * w.2 - v.2 * w.1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd ▸ h
  let g : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((w.2 / d) • ContinuousLinearMap.fst ℝ ℝ ℝ - (w.1 / d) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((v.1 / d) • ContinuousLinearMap.snd ℝ ℝ ℝ - (v.2 / d) • ContinuousLinearMap.fst ℝ ℝ ℝ)
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g (fun x => ?_) (fun x => ?_), ?_, ?_⟩
  · ext <;> simp [f, g] <;> field_simp <;> rw [hd] <;> ring
  · ext <;> simp [f, g] <;> field_simp <;> rw [hd] <;> ring
  · ext <;> simp [f]
  · ext <;> simp [f]

/-- For a nonzero symmetric form `H = [[h₁₁, h₁₂], [h₁₂, h₂₂]]` on `ℝ²` there are `w` with `H(w, w) ≠ 0` and
`v` with `H(v, w) = 0` such that `(v, w)` is a basis. -/
theorem exists_orth_pair (h11 h12 h22 : ℝ) (h : ¬ (h11 = 0 ∧ h12 = 0 ∧ h22 = 0)) :
    ∃ v w : ℝ × ℝ, w.1 * w.1 * h11 + (w.1 * w.2 + w.2 * w.1) * h12 + w.2 * w.2 * h22 ≠ 0 ∧
      v.1 * w.1 * h11 + (v.1 * w.2 + v.2 * w.1) * h12 + v.2 * w.2 * h22 = 0 ∧
      v.1 * w.2 - v.2 * w.1 ≠ 0 := by
  by_cases h22' : h22 = 0
  · by_cases h11' : h11 = 0
    · have h12' : h12 ≠ 0 := fun h12' => h ⟨h11', h12', h22'⟩
      refine ⟨(1, -1), (1, 1), ?_, ?_, ?_⟩ <;> simp [h11', h22', h12']
    · exact ⟨(-h12, h11), (1, 0), by simp [h11'], by simp; ring, by simp [h11']⟩
  · exact ⟨(h22, -h12), (0, 1), by simp [h22'], by simp; ring, by simp [h22']⟩

/-- Nondegenerate case: if `H(v, w) = 0`, `(v, w)` is a basis and `det H ≠ 0`, then `H(v, v) ≠ 0`. -/
theorem orth_self_ne_zero (h11 h12 h22 : ℝ) (v w : ℝ × ℝ)
    (hvw : v.1 * w.1 * h11 + (v.1 * w.2 + v.2 * w.1) * h12 + v.2 * w.2 * h22 = 0)
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (hH : h11 * h22 - h12 ^ 2 ≠ 0) :
    v.1 * v.1 * h11 + (v.1 * v.2 + v.2 * v.1) * h12 + v.2 * v.2 * h22 ≠ 0 := by
  intro hvv
  have hp : (v.1 * w.2 - v.2 * w.1) * (v.1 * h11 + v.2 * h12) = 0 := by
    linear_combination w.2 * hvv - v.2 * hvw
  have hq : (v.1 * w.2 - v.2 * w.1) * (v.1 * h12 + v.2 * h22) = 0 := by
    linear_combination v.1 * hvw - w.1 * hvv
  have hp' := (mul_eq_zero.mp hp).resolve_left hdet
  have hq' := (mul_eq_zero.mp hq).resolve_left hdet
  have h1 : v.1 * (h11 * h22 - h12 ^ 2) = 0 := by linear_combination h22 * hp' - h12 * hq'
  have h2 : v.2 * (h11 * h22 - h12 ^ 2) = 0 := by linear_combination h11 * hq' - h12 * hp'
  have e1 := (mul_eq_zero.mp h1).resolve_right hH
  have e2 := (mul_eq_zero.mp h2).resolve_right hH
  exact hdet (by rw [e1, e2]; ring)

/-- Degenerate case: if `det H = 0`, `H(w, w) ≠ 0` and `H(v, w) = 0`, then `v` lies in the kernel of `H`. -/
theorem orth_mem_ker (h11 h12 h22 : ℝ) (v w z : ℝ × ℝ) (hH : h11 * h22 - h12 ^ 2 = 0)
    (hww : w.1 * w.1 * h11 + (w.1 * w.2 + w.2 * w.1) * h12 + w.2 * w.2 * h22 ≠ 0)
    (hvw : v.1 * w.1 * h11 + (v.1 * w.2 + v.2 * w.1) * h12 + v.2 * w.2 * h22 = 0) :
    v.1 * z.1 * h11 + (v.1 * z.2 + v.2 * z.1) * h12 + v.2 * z.2 * h22 = 0 := by
  have : (v.1 * z.1 * h11 + (v.1 * z.2 + v.2 * z.1) * h12 + v.2 * z.2 * h22) *
      (w.1 * w.1 * h11 + (w.1 * w.2 + w.2 * w.1) * h12 + w.2 * w.2 * h22) = 0 := by
    linear_combination (w.1 * z.1 * h11 + (w.1 * z.2 + w.2 * z.1) * h12 + w.2 * z.2 * h22) * hvw +
      (v.1 * w.2 - v.2 * w.1) * (z.1 * w.2 - z.2 * w.1) * hH
  exact (mul_eq_zero.mp this).resolve_right hww

/-- Sufficient conditions for `NormalPoint j` of `Ψ (k₀ + L ·)` at a critical point `k₀`, in terms of the
second and third derivatives of `Ψ` at `k₀` along the columns `L e₁`, `L e₂`. -/
theorem normalPoint_comp {Ψ : ℝ × ℝ → ℝ} {k₀ : ℝ × ℝ} (hΨ : ContDiff ℝ 4 Ψ) (hcrit : IsCritical Ψ 0 k₀)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (j : ℕ) (hww : dd Ψ k₀ (L (0, 1)) (L (0, 1)) ≠ 0)
    (hwv : dd Ψ k₀ (L (0, 1)) (L (1, 0)) = 0)
    (h2 : j = 2 → dd Ψ k₀ (L (1, 0)) (L (1, 0)) ≠ 0)
    (h3 : j = 3 → dd Ψ k₀ (L (1, 0)) (L (1, 0)) = 0 ∧ ddd Ψ k₀ (L (1, 0)) (L (1, 0)) (L (1, 0)) ≠ 0) :
    OscInt.Blueprint.NormalPoint j (fun k => Ψ (k₀ + L k)) := by
  have hc2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
  have hc3 : ContDiff ℝ 3 Ψ := hΨ.of_le (by norm_num)
  have hfd : ∀ a : ℝ × ℝ, fderiv ℝ Ψ k₀ a = 0 := by
    intro a
    obtain ⟨h1, h2⟩ := hcrit
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h1 h2
    have ha : a = a.1 • ((1 : ℝ), (0 : ℝ)) + a.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [ha, map_add, map_smul, map_smul, h1, h2]
    simp
  have hf : ∀ a, fderiv ℝ (fun k => Ψ (k₀ + L k)) 0 a = 0 := fun a => by
    have := fderiv_comp_affine_apply (f := Ψ) k₀ (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 0 a
      (hΨ.differentiable (by norm_num) _)
    simp only [ContinuousLinearEquiv.coe_coe, map_zero, add_zero] at this
    rw [this, hfd]
  have hd : ∀ a b, dd (fun k => Ψ (k₀ + L k)) 0 a b = dd Ψ k₀ (L a) (L b) := fun a b => by
    have := dd_comp_affine hc2 k₀ (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 0 a b
    simpa using this
  have hdd : ∀ a b c, ddd (fun k => Ψ (k₀ + L k)) 0 a b c = ddd Ψ k₀ (L a) (L b) (L c) :=
    fun a b c => by
      have := ddd_comp_affine hc3 k₀ (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 0 a b c
      simpa using this
  refine ⟨hf _, hf _, ?_, ?_, ?_, ?_⟩
  · rw [hd]; exact hww
  · rw [hd]; exact hwv
  · intro hj; rw [hd]; exact h2 hj
  · intro hj; rw [hd, hdd]; exact h3 hj

/-- Derivative of the oscillatory factor `e^{iφ}`. -/
theorem hasFDerivAt_cexp_phase {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {x : E} (hφ : HasFDerivAt φ φ' x) :
    HasFDerivAt (fun k => cexp (↑(φ k) * I))
      (cexp (↑(φ x) * I) • (I • (ofRealCLM.comp φ'))) x := by
  have h1 : HasFDerivAt (fun k => (φ k : ℂ)) (ofRealCLM.comp φ') x := ofRealCLM.hasFDerivAt.comp x hφ
  exact (h1.mul_const I).cexp

/-- Directional derivative of `e^{iφ}`. -/
theorem fderiv_cexp_phase_apply {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x) (v : E) :
    fderiv ℝ (fun k => cexp (↑(φ k) * I)) x v = cexp (↑(φ x) * I) * (I * ↑(fderiv ℝ φ x v)) := by
  rw [(hasFDerivAt_cexp_phase hφ.hasFDerivAt).fderiv]
  simp

/-- Integration by parts against `e^{iφ}` in the direction `v`, for a compactly supported `C¹` function `B`
on a finite-dimensional space with an additive Haar measure. -/
theorem integral_cexp_phase_mul_fderiv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) {B : E → ℂ}
    (hB : ContDiff ℝ 1 B) (hBc : HasCompactSupport B) (v : E) :
    ∫ x, cexp (↑(φ x) * I) * fderiv ℝ B x v ∂μ =
      -∫ x, (cexp (↑(φ x) * I) * (I * ↑(fderiv ℝ φ x v))) * B x ∂μ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hf : ContDiff ℝ 1 (fun k => cexp (↑(φ k) * I)) :=
    Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp hφ).mul contDiff_const)
  have hfc : Continuous fun x => fderiv ℝ (fun k => cexp (↑(φ k) * I)) x v :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hBd : Continuous fun x => fderiv ℝ B x v := (hB.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun x => fderiv ℝ (fun k => cexp (↑(φ k) * I)) x v * B x) μ :=
    (hfc.mul hB.continuous).integrable_of_hasCompactSupport hBc.mul_left
  have i2 : Integrable (fun x => cexp (↑(φ x) * I) * fderiv ℝ B x v) μ :=
    (hf.continuous.mul hBd).integrable_of_hasCompactSupport (hBc.fderiv_apply (𝕜 := ℝ) v).mul_left
  have i3 : Integrable (fun x => cexp (↑(φ x) * I) * B x) μ :=
    (hf.continuous.mul hB.continuous).integrable_of_hasCompactSupport hBc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hB.differentiable one_ne_zero) x)
  rw [key]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fderiv_cexp_phase_apply (hφd x)]

/-- `x ↦ g(x)⁻¹ • A(x)` is `C¹` when `g, A` are `C¹` and `g ≠ 0` on a set containing `tsupport A`. -/
theorem contDiff_inv_smul {g : E → ℝ} {A : E → ℂ} {U : Set E} (hg : ContDiff ℝ 1 g) (hA : ContDiff ℝ 1 A)
    (hg0 : ∀ x ∈ U, g x ≠ 0) (hsupp : tsupport A ⊆ U) :
    ContDiff ℝ 1 (fun x => (g x)⁻¹ • A x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (hg.contDiffAt.inv (hg0 x hx)).smul hA.contDiffAt
  · have h0 : A =ᶠ[nhds x] 0 := (notMem_tsupport_iff_eventuallyEq).1 fun h => hx (hsupp h)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

/-- Directional derivative of `g⁻¹ • A` where `g ≠ 0`. -/
theorem fderiv_inv_smul_apply {g : E → ℝ} {A : E → ℂ} {x : E} (hg : DifferentiableAt ℝ g x)
    (hA : DifferentiableAt ℝ A x) (hx : g x ≠ 0) (v : E) :
    fderiv ℝ (fun x => (g x)⁻¹ • A x) x v =
      (g x)⁻¹ • fderiv ℝ A x v + (-(g x ^ 2)⁻¹ * fderiv ℝ g x v) • A x := by
  have hinv : HasFDerivAt (fun y => (g y)⁻¹) ((-(g x ^ 2)⁻¹) • fderiv ℝ g x) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x hg.hasFDerivAt
  show fderiv ℝ ((fun y => (g y)⁻¹) • A) x v = _
  rw [(hinv.smul hA.hasFDerivAt).fderiv]
  simp

/-- `|∂_v ∂_v q(x)| ≤ ‖D²q(x)‖` for `‖v‖ ≤ 1`. -/
theorem abs_fderiv_fderiv_apply_le {q : E → ℝ} (hq : ContDiff ℝ 2 q) (x v : E) (hv : ‖v‖ ≤ 1) :
    |fderiv ℝ (fun y => fderiv ℝ q y v) x v| ≤ ‖iteratedFDeriv ℝ 2 q x‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp
  have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) q x ![v, v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← h2, ← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 q x).le_opNorm _).trans ?_
  have hp : ∏ i : Fin 2, ‖(![v, v] : Fin 2 → E) i‖ ≤ 1 := by
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [norm_nonneg v]
  nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 q x), Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) =>
    norm_nonneg ((![v, v] : Fin 2 → E) i)]

/-- Arithmetic for the pointwise bound on `∂_v(A/g)`. -/
theorem inv_bound_arith {c G a b d M D : ℝ} (hc : 0 < c) (hG : c ≤ G) (ha : 0 ≤ a) (ha' : a ≤ M)
    (hb : 0 ≤ b) (hb' : b ≤ M) (hd : 0 ≤ d) (hd' : d ≤ D) :
    G⁻¹ * a + (G ^ 2)⁻¹ * (d * b) ≤ (1 / c + D / c ^ 2) * M := by
  have hG0 : 0 < G := hc.trans_le hG
  have h1 : G⁻¹ * a ≤ M / c := by
    rw [inv_mul_eq_div]; exact div_le_div₀ (ha.trans ha') ha' hc hG
  have h2 : (G ^ 2)⁻¹ * (d * b) ≤ D * M / c ^ 2 := by
    rw [inv_mul_eq_div]
    exact div_le_div₀ (by nlinarith) (mul_le_mul hd' hb' hb (hd.trans hd')) (by positivity)
      (pow_le_pow_left₀ hc.le hG 2)
  calc G⁻¹ * a + (G ^ 2)⁻¹ * (d * b) ≤ M / c + D * M / c ^ 2 := add_le_add h1 h2
    _ = (1 / c + D / c ^ 2) * M := by ring

/-- Pointwise form of `∂_v(e^{imq}) · A/∂_vq = im e^{imq} A` (both sides vanish where `A = 0`). -/
theorem cexp_mul_inv_smul_eq (m φ g : ℝ) (a : ℂ) (h : g = 0 → a = 0) :
    (cexp (↑(m * φ) * I) * (I * ↑(m * g))) * (g⁻¹ • a) = (↑m * I) * (cexp (↑(m * φ) * I) * a) := by
  by_cases hg : g = 0
  · simp [h hg]
  · have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg
    rw [Complex.real_smul]
    push_cast
    field_simp

/-- Pointwise bound on `e^{iφ} ∂_e(A/∂_e q)`. -/
theorem norm_cexp_mul_fderiv_le {q : E → ℝ} (hq : ContDiff ℝ 2 q) {e : E} (he : ‖e‖ ≤ 1)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) {A : E → ℂ} (hA : ContDiff ℝ 1 A) {x : E} {φ c D M : ℝ}
    (hgx : g x ≠ 0) (hge : g = fun k => fderiv ℝ q k e) (hlow : c ≤ |fderiv ℝ q x e|)
    (hup : ‖iteratedFDeriv ℝ 2 q x‖ ≤ D) (hc : 0 < c)
    (h0 : ‖iteratedFDeriv ℝ 0 A x‖ ≤ M) (h1 : ‖iteratedFDeriv ℝ 1 A x‖ ≤ M) :
    ‖cexp (↑φ * I) * fderiv ℝ (fun x => (g x)⁻¹ • A x) x e‖ ≤ (1 / c + D / c ^ 2) * M := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    fderiv_inv_smul_apply (hg.differentiable one_ne_zero x) (hA.differentiable one_ne_zero x) hgx]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_inv,
    abs_pow, mul_assoc]
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_one] at h1
  have hd := abs_fderiv_fderiv_apply_le hq x e he
  rw [← hge] at hd
  have hlow' : c ≤ |g x| := by simpa [hge] using hlow
  refine inv_bound_arith hc hlow' (norm_nonneg _) ?_ (norm_nonneg _) h0 (abs_nonneg _) (hd.trans hup)
  exact ((fderiv ℝ A x).le_opNorm e).trans (by nlinarith [norm_nonneg (fderiv ℝ A x), norm_nonneg e])

/-- **Core of L1.** If `|∂_e q| ≥ c > 0` and `‖D²q‖ ≤ D` on `ball k₀ ε` (`‖e‖ ≤ 1`), then
`|I(mq, A)| ≤ (1/c + D/c²) |B̄(k₀, ε/2)| M / m` for every amplitude with bound `(2, B̄(k₀, ε/2), M)`.
Proof: one integration by parts in the direction `e`, with `A = ∂_e q · (A/∂_e q)`. -/
theorem norm_oscInt2_le_of_lower_fderiv {q : ℝ × ℝ → ℝ} (hq : ContDiff ℝ 2 q) {e : ℝ × ℝ} (he : ‖e‖ ≤ 1)
    {k₀ : ℝ × ℝ} {ε c D : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hlow : ∀ k ∈ Metric.ball k₀ ε, c ≤ |fderiv ℝ q k e|)
    (hup : ∀ k ∈ Metric.ball k₀ ε, ‖iteratedFDeriv ℝ 2 q k‖ ≤ D) {A : ℝ × ℝ → ℂ} {M m : ℝ}
    (hA : AmpBound 2 (Metric.closedBall k₀ (ε / 2)) A M) (hm : 1 ≤ m) :
    ‖oscInt2 (fun k => m * q k) A‖ ≤
      (1 / c + D / c ^ 2) * volume.real (Metric.closedBall k₀ (ε / 2)) * M * m ^ (-(1 : ℝ)) := by
  obtain ⟨hAc, hAs, hAb⟩ := hA
  set K := Metric.closedBall k₀ (ε / 2)
  have hK : K ⊆ Metric.ball k₀ ε := Metric.closedBall_subset_ball (half_lt_self hε)
  set g : ℝ × ℝ → ℝ := fun k => fderiv ℝ q k e
  have hg : ContDiff ℝ 1 g := contDiff_fderiv_apply (n := 1) hq e
  have hg0 : ∀ x ∈ Metric.ball k₀ ε, g x ≠ 0 := fun x hx h =>
    (hc.trans_le (hlow x hx)).ne' (by simp [g] at h; simp [h])
  have hA1 : ContDiff ℝ 1 A := hAc.of_le (by norm_num)
  set B : ℝ × ℝ → ℂ := fun x => (g x)⁻¹ • A x
  have hB : ContDiff ℝ 1 B := contDiff_inv_smul hg hA1 hg0 (hAs.trans hK)
  have hBs : tsupport B ⊆ K := (tsupport_smul_subset_right _ _).trans hAs
  have hBc : HasCompactSupport B := (isCompact_closedBall k₀ _).of_isClosed_subset (isClosed_tsupport _) hBs
  have hφ : ContDiff ℝ 1 (fun k => m * q k) := contDiff_const.mul (hq.of_le (by norm_num))
  have ibp := integral_cexp_phase_mul_fderiv volume hφ hB hBc e
  have hfd : ∀ x, fderiv ℝ (fun k => m * q k) x e = m * g x := fun x => by
    rw [fderiv_const_mul (hq.differentiable (by norm_num) x)]; rfl
  have hpt : ∀ x, (cexp (↑(m * q x) * I) * (I * ↑(m * g x))) * B x =
      (↑m * I) * (cexp (↑(m * q x) * I) * A x) := fun x =>
    cexp_mul_inv_smul_eq m (q x) (g x) (A x) fun h0 => by
      by_contra hx
      exact hg0 x (hK (hAs (subset_tsupport _ hx))) h0
  simp only [hfd, hpt, integral_const_mul] at ibp
  have hosc : ‖oscInt2 (fun k => m * q k) A‖ * m =
      ‖∫ x, cexp (↑(m * q x) * I) * fderiv ℝ B x e‖ := by
    rw [ibp, norm_neg, norm_mul, oscInt2, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < m)]
    ring
  have hbd : ‖∫ x, cexp (↑(m * q x) * I) * fderiv ℝ B x e‖ ≤
      (1 / c + D / c ^ 2) * volume.real K * M := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ fun h => hx (hBs h)]; simp]
    refine (norm_setIntegral_le_of_norm_le_const (C := (1 / c + D / c ^ 2) * M) measure_closedBall_lt_top
      fun x hx => ?_).trans_eq
      (by ring)
    exact norm_cexp_mul_fderiv_le hq he hg hA1 (hg0 x (hK hx)) rfl (hlow x (hK hx)) (hup x (hK hx)) hc
      (hAb 0 (by norm_num) x) (hAb 1 (by norm_num) x)
  have hm0 : (0 : ℝ) < m := by linarith
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hm0, hosc]
  exact hbd.trans_eq (by ring)

end OscInt.StationaryPhase.LocalAux

namespace OscInt.StationaryPhase

open Set MeasureTheory OscInt.Statements LocalAux

/-- **L2** Normal form at a critical point by a linear change of coordinates: the new second axis is a direction
`w` with `D²Ψ(k₀)[w, w] ≠ 0`, the new first axis a `D²Ψ(k₀)`-orthogonal direction `v`. -/
theorem normalForm : OscInt.Blueprint.NormalFormFacts := by
  intro Ψ k₀ hΨ hcrit
  have hc2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
  have hco := dd_eq_coord hc2 k₀
  set h11 := dd Ψ k₀ (1, 0) (1, 0)
  set h12 := dd Ψ k₀ (1, 0) (0, 1)
  set h22 := dd Ψ k₀ (0, 1) (0, 1)
  have hhess : hessDet Ψ k₀ = h11 * h22 - h12 ^ 2 := rfl
  -- a basis `(v, w)` adapted to the Hessian, whenever the Hessian is nonzero
  have hbasis : ¬ (h11 = 0 ∧ h12 = 0 ∧ h22 = 0) → ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      dd Ψ k₀ (L (0, 1)) (L (0, 1)) ≠ 0 ∧ dd Ψ k₀ (L (1, 0)) (L (0, 1)) = 0 ∧
      dd Ψ k₀ (L (0, 1)) (L (1, 0)) = 0 ∧ (L (1, 0)).1 * (L (0, 1)).2 - (L (1, 0)).2 * (L (0, 1)).1 ≠ 0 := by
    intro hne
    obtain ⟨v, w, hww, hvw, hdet⟩ := exists_orth_pair h11 h12 h22 hne
    obtain ⟨L, hL1, hL2⟩ := exists_equiv_cols v w hdet
    refine ⟨L, ?_, ?_, ?_, ?_⟩ <;> simp only [hL1, hL2] <;> try rw [hco]
    · exact hww
    · exact hvw
    · linear_combination hvw
    · exact hdet
  constructor
  · intro hH
    have hne : ¬ (h11 = 0 ∧ h12 = 0 ∧ h22 = 0) := fun ⟨a, b, c⟩ => hH (by rw [hhess, a, b, c]; ring)
    obtain ⟨L, hww, hvw, hwv, hdet⟩ := hbasis hne
    refine ⟨L, normalPoint_comp hΨ hcrit L 2 hww hwv (fun _ => ?_) (fun h => absurd h (by norm_num))⟩
    rw [hco] at hvw ⊢
    exact orth_self_ne_zero h11 h12 h22 _ _ hvw hdet (hhess ▸ hH)
  · intro hH hfold
    rcases hfold with h | ⟨⟨a, b, hab⟩, hker⟩
    · exact absurd hH h
    have hne : ¬ (h11 = 0 ∧ h12 = 0 ∧ h22 = 0) := fun ⟨e1, e2, e3⟩ => hab (by rw [hco, e1, e2, e3]; ring)
    obtain ⟨L, hww, hvw, hwv, hdet⟩ := hbasis hne
    have hk : ∀ z, dd Ψ k₀ (L (1, 0)) z = 0 := fun z => by
      rw [hco] at hww hvw ⊢
      exact orth_mem_ker h11 h12 h22 _ _ z (hhess ▸ hH) hww hvw
    have hv0 : L (1, 0) ≠ 0 := fun h0 => hdet (by rw [h0]; simp)
    exact ⟨L, normalPoint_comp hΨ hcrit L 3 hww hwv (fun h => absurd h (by norm_num))
      (fun _ => ⟨hk _, hker _ hv0 hk⟩)⟩

/-- **L1** Local bound with rate 1 at a non-critical point. -/
theorem localNonCrit : OscInt.Blueprint.LocalNonCritFacts := by
  intro T _ Q τ₀ k₀ hQ hnc
  obtain ⟨e, he, hne⟩ : ∃ e : ℝ × ℝ, ‖e‖ ≤ 1 ∧ fderiv ℝ (Q τ₀) k₀ e ≠ 0 := by
    by_contra! h
    exact hnc ⟨by simpa using h (1, 0) (by simp), by simpa using h (0, 1) (by simp)⟩
  have hc1 : Continuous fun p : T × (ℝ × ℝ) => fderiv ℝ (Q p.1) p.2 e := by
    simpa using (hQ.2 1 (by norm_num)).eval_const (fun _ : Fin 1 => e)
  have hc2 : Continuous fun p : T × (ℝ × ℝ) => ‖iteratedFDeriv ℝ 2 (Q p.1) p.2‖ := (hQ.2 2 le_rfl).norm
  set c := |fderiv ℝ (Q τ₀) k₀ e| / 2 with hc_def
  set D := ‖iteratedFDeriv ℝ 2 (Q τ₀) k₀‖ + 1 with hD_def
  have hc : 0 < c := half_pos (abs_pos.2 hne)
  have hS : {p : T × (ℝ × ℝ) | c < |fderiv ℝ (Q p.1) p.2 e| ∧
      ‖iteratedFDeriv ℝ 2 (Q p.1) p.2‖ < D} ∈ nhds (τ₀, k₀) :=
    ((isOpen_lt continuous_const hc1.abs).inter (isOpen_lt hc2 continuous_const)).mem_nhds
      ⟨half_lt_self (abs_pos.2 hne), show _ < D from lt_add_one _⟩
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hS
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨U, hU, ε / 2, half_pos hε, (1 / c + D / c ^ 2) * volume.real (Metric.closedBall k₀ (ε / 2)),
    fun A M τ m hτ hA hm => ?_⟩
  have hq : ContDiff ℝ 2 (Q τ) := hQ.1 τ
  have hmem : ∀ k ∈ Metric.ball k₀ ε, c < |fderiv ℝ (Q τ) k e| ∧ ‖iteratedFDeriv ℝ 2 (Q τ) k‖ < D :=
    fun k hk => hUV (mk_mem_prod hτ (hεV hk))
  have hlow : ∀ k ∈ Metric.ball k₀ ε, c ≤ |fderiv ℝ (Q τ) k e| := fun k hk => (hmem k hk).1.le
  have hup : ∀ k ∈ Metric.ball k₀ ε, ‖iteratedFDeriv ℝ 2 (Q τ) k‖ ≤ D := fun k hk => (hmem k hk).2.le
  have key := norm_oscInt2_le_of_lower_fderiv hq he hε hc hlow hup hA hm
  exact key

end OscInt.StationaryPhase
