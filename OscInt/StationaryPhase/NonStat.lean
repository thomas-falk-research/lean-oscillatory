/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase
import OscInt.StationaryPhase.Partition

/-!
# S2/S3: parametric calculus (F3) and non-stationary phase for a compact family (N2)

This file proves
* `OscInt.Blueprint.FamilyCalculusFacts` (`familyCalculus`): products and reciprocals of non-vanishing
  families of class `Cⁿ` over a topological parameter space are of class `Cⁿ`;
* `OscInt.Blueprint.NonStatCoreFacts` (`nonStatCore`): `|I(mΦ_τ, A)| ≤ C M m^{-N}` for a compact family
  `Φ` of class `Cᴺ⁺¹` with `|∇Φ_τ| ≥ c` on the compact set `K ⊇ tsupport A`.

Route: `docs/proof-S2S3.md`, (N2) with revision items 6 and 7.
* F3. A family of class `Cⁿ⁺¹` is a jointly continuous family whose family of derivatives is of class `Cⁿ`
  (`famC_succ_iff`, from `iteratedFDeriv_succ_eq_comp_right`). Then induction on `n`: for a bilinear `B`,
  `D(B(f, g)) = B(f, Dg) + B(Df, g)` (`ContinuousLinearMap.fderiv_of_bilinear`), which are again bilinear
  expressions (`FamC.bilinear`); and `D(1/f) = -(1/f)² Df` (`FamC.inv`).
* N2. With `G = (∂₁Φ)² + (∂₂Φ)² ≥ c²` on `T × K`, the tube lemma gives an open `V ⊇ K` with `G > c²/4` on
  `T × V`; a smooth cutoff `χ` (`partition`, one set) with `χ = 1` on `K`, `tsupport χ ⊆ V` makes
  `G̃ = G + (1 - χ) c²/4` positive everywhere, and `w = ∇Φ / G̃` is a family of class `Cᴺ` (F3) with
  `∇Φ · w = 1` on `K` (`exists_weights`). Integrating by parts in each coordinate direction
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) gives `I(mΦ, A) = (i/m) I(mΦ, div(w A))`
  (`oscInt2_eq_divAmp`); `div(w A)` has an amplitude bound of order one less with constant `2·2ⁿ⁺¹ W M`, `W` a
  bound for the derivatives of `w` on the compact `T × K` (Leibniz, `ampBound_divAmp`). Induction on the order
  (`nonStat_of_weights`), base case `|I| ≤ |K| M`.
-/

namespace OscInt.StationaryPhase.NonStatAux

open Set OscInt.Statements
open scoped ContDiff

universe u

variable {T : Type*} [TopologicalSpace T]
  {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A family `f τ : E → F` over a topological space `T` is of class `Cⁿ` if each member is `Cⁿ` and the
derivatives of order `≤ n` are jointly continuous in `(τ, k)`. -/
def FamC (n : ℕ) (f : T → E → F) : Prop :=
  (∀ τ, ContDiff ℝ n (f τ)) ∧ ∀ j ≤ n, Continuous (fun q : T × E => iteratedFDeriv ℝ j (f q.1) q.2)

/-- Class `Cⁿ` implies class `Cᵐ` for `m ≤ n`. -/
theorem FamC.of_le {m n : ℕ} {f : T → E → F} (h : FamC n f) (hmn : m ≤ n) : FamC m f :=
  ⟨fun τ => (h.1 τ).of_le (by exact_mod_cast hmn), fun j hj => h.2 j (hj.trans hmn)⟩

/-- A family of class `Cⁿ` is jointly continuous. -/
theorem FamC.continuous {n : ℕ} {f : T → E → F} (h : FamC n f) :
    Continuous (fun q : T × E => f q.1 q.2) := by
  have := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp (h.2 0 (Nat.zero_le _))
  exact this

/-- Class `C⁰`: continuous members and joint continuity. -/
theorem famC_zero_iff {f : T → E → F} :
    FamC 0 f ↔ (∀ τ, ContDiff ℝ 0 (f τ)) ∧ Continuous (fun q : T × E => f q.1 q.2) := by
  refine ⟨fun h => ⟨h.1, h.continuous⟩, fun h => ⟨h.1, fun j hj => ?_⟩⟩
  obtain rfl : j = 0 := Nat.le_zero.mp hj
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp h.2

/-- A family is of class `Cⁿ⁺¹` iff its members are `Cⁿ⁺¹`, it is jointly continuous, and the family of
derivatives is of class `Cⁿ`. -/
theorem famC_succ_iff {n : ℕ} {f : T → E → F} :
    FamC (n + 1) f ↔ (∀ τ, ContDiff ℝ (n + 1) (f τ)) ∧ Continuous (fun q : T × E => f q.1 q.2) ∧
      FamC n (fun τ => fderiv ℝ (f τ)) := by
  have hD : ∀ (j : ℕ) (q : T × E), iteratedFDeriv ℝ (j + 1) (f q.1) q.2 =
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm
        (iteratedFDeriv ℝ j (fderiv ℝ (f q.1)) q.2) := fun j q => iteratedFDeriv_succ_eq_comp_right
  constructor
  · intro h
    refine ⟨fun τ => by exact_mod_cast h.1 τ, h.continuous, fun τ => (h.1 τ).fderiv_right (by
      push_cast; exact le_rfl), fun j hj => ?_⟩
    have := (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp (h.2 (j + 1) (by omega))
    refine this.congr fun q => ?_
    simp only [Function.comp_apply, hD, LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun τ => by exact_mod_cast h1 τ, fun j hj => ?_⟩
    rcases j with _ | j
    · exact (famC_zero_iff.mpr ⟨fun τ => (h1 τ).of_le (by simp), h2⟩).2 0 le_rfl
    · simp_rw [hD]
      exact (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.continuous.comp (h3.2 j (by omega))


/-- Sums of families of class `Cⁿ`. -/
theorem FamC.add {n : ℕ} {f g : T → E → F} (hf : FamC n f) (hg : FamC n g) :
    FamC n (fun τ k => f τ k + g τ k) := by
  refine ⟨fun τ => (hf.1 τ).add (hg.1 τ), fun j hj => ?_⟩
  have h : ∀ q : T × E, iteratedFDeriv ℝ j (fun y => f q.1 y + g q.1 y) q.2 =
      iteratedFDeriv ℝ j (f q.1) q.2 + iteratedFDeriv ℝ j (g q.1) q.2 := fun q =>
    iteratedFDeriv_add_apply (f := f q.1) (g := g q.1) ((hf.1 _).of_le (by exact_mod_cast hj)).contDiffAt
      ((hg.1 _).of_le (by exact_mod_cast hj)).contDiffAt
  simp_rw [h]
  exact (hf.2 j hj).add (hg.2 j hj)

/-- A constant family of a `Cⁿ` function is of class `Cⁿ`. -/
theorem famC_const {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) : FamC n (fun _ : T => f) :=
  ⟨fun _ => hf, fun j hj => (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd⟩

/-- Composition with a fixed continuous linear map on the left. -/
theorem FamC.clm_comp {n : ℕ} {f : T → E → F} (hf : FamC n f) (L : F →L[ℝ] G) :
    FamC n (fun τ k => L (f τ k)) := by
  refine ⟨fun τ => L.contDiff.comp (hf.1 τ), fun j hj => ?_⟩
  have h : ∀ q : T × E, iteratedFDeriv ℝ j (fun y => L (f q.1 y)) q.2 =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (f q.1) q.2) := fun q =>
    L.iteratedFDeriv_comp_left (hf.1 q.1).contDiffAt (by exact_mod_cast hj)
  simp_rw [h]
  exact (L.compContinuousMultilinearMapL ℝ (fun _ : Fin j => E) F G).continuous.comp (hf.2 j hj)

/-- Products in the sense of a fixed continuous bilinear map: if `f` and `g` are families of class `Cⁿ`, so
is `B (f τ k) (g τ k)`. -/
theorem FamC.bilinear {n : ℕ} : ∀ {F G H : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : T → E → F} {g : T → E → G}, FamC n f → FamC n g →
    FamC n (fun τ k => B (f τ k) (g τ k)) := by
  induction n with
  | zero =>
    intro F G H _ _ _ _ _ _ B f g hf hg
    refine famC_zero_iff.mpr ⟨fun τ => ?_, ?_⟩
    · exact B.isBoundedBilinearMap.contDiff.comp ((hf.1 τ).prodMk (hg.1 τ))
    · exact B.isBoundedBilinearMap.continuous.comp (hf.continuous.prodMk hg.continuous)
  | succ n ih =>
    intro F G H _ _ _ _ _ _ B f g hf hg
    obtain ⟨hf1, hf2, hf3⟩ := famC_succ_iff.mp hf
    obtain ⟨hg1, hg2, hg3⟩ := famC_succ_iff.mp hg
    refine famC_succ_iff.mpr ⟨fun τ => B.isBoundedBilinearMap.contDiff.comp ((hf1 τ).prodMk (hg1 τ)),
      B.isBoundedBilinearMap.continuous.comp (hf2.prodMk hg2), ?_⟩
    have hd : (fun τ => fderiv ℝ (fun k => B (f τ k) (g τ k))) = fun τ k =>
        B.precompR E (f τ k) (fderiv ℝ (g τ) k) + B.precompL E (fderiv ℝ (f τ) k) (g τ k) := by
      funext τ k
      exact B.fderiv_of_bilinear ((hf1 τ).differentiable (by simp) k)
        ((hg1 τ).differentiable (by simp) k)
    rw [hd]
    exact (ih (B.precompR E) (hf.of_le (by omega)) hg3).add (ih (B.precompL E) hf3 (hg.of_le (by omega)))

/-- Pointwise products of real-valued families of class `Cⁿ`. -/
theorem FamC.mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {f g : T → E → ℝ}
    (hf : FamC n f) (hg : FamC n g) : FamC n (fun τ k => f τ k * g τ k) :=
  FamC.bilinear (ContinuousLinearMap.mul ℝ ℝ) hf hg

/-- Derivative of the reciprocal: `D(1/f) = -(f²)⁻¹ Df`. -/
theorem fderiv_inv_fun {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {k : E}
    (hf : DifferentiableAt ℝ f k) (hk : f k ≠ 0) :
    fderiv ℝ (fun y => (f y)⁻¹) k = (-((f k)⁻¹ * (f k)⁻¹)) • fderiv ℝ f k := by
  have h := ((hasFDerivAt_inv (𝕜 := ℝ) hk).comp k hf.hasFDerivAt).fderiv
  rw [show (fun y => (f y)⁻¹) = (fun x : ℝ => x⁻¹) ∘ f from rfl, h]
  ext v
  simp [pow_two, mul_comm]

/-- Reciprocals of non-vanishing real-valued families of class `Cⁿ`. -/
theorem FamC.inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} :
    ∀ {f : T → E → ℝ}, FamC n f → (∀ τ k, f τ k ≠ 0) → FamC n (fun τ k => (f τ k)⁻¹) := by
  induction n with
  | zero =>
    intro f hf h0
    refine famC_zero_iff.mpr ⟨fun τ => (hf.1 τ).inv (h0 τ), ?_⟩
    exact hf.continuous.inv₀ fun q => h0 q.1 q.2
  | succ n ih =>
    intro f hf h0
    obtain ⟨hf1, hf2, hf3⟩ := famC_succ_iff.mp hf
    refine famC_succ_iff.mpr ⟨fun τ => (hf1 τ).inv (h0 τ), hf2.inv₀ fun q => h0 q.1 q.2, ?_⟩
    have hd : (fun τ => fderiv ℝ (fun k => (f τ k)⁻¹)) = fun τ k =>
        (-ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
          ((f τ k)⁻¹ * (f τ k)⁻¹) (fderiv ℝ (f τ) k) := by
      funext τ k
      rw [fderiv_inv_fun ((hf1 τ).differentiable (by simp) k) (h0 τ k)]
      simp
    rw [hd]
    have hi := ih (hf.of_le (by omega)) h0
    exact FamC.bilinear _ (hi.mul hi) hf3

section Analytic
open MeasureTheory Complex

/-- Derivative of the phase factor `e^{i m Φ}`. -/
theorem fderiv_exp_phase {Φ₀ : ℝ × ℝ → ℝ} (m : ℝ) {k : ℝ × ℝ} (h : DifferentiableAt ℝ Φ₀ k)
    (v : ℝ × ℝ) :
    fderiv ℝ (fun y => exp (↑(m * Φ₀ y) * I)) k v =
      exp (↑(m * Φ₀ k) * I) * (↑(m * fderiv ℝ Φ₀ k v) * I) := by
  have hF : HasDerivAt (fun t : ℝ => exp (↑(m * t) * I))
      (exp (↑(m * Φ₀ k) * I) * ((m : ℂ) * I)) (Φ₀ k) := by
    have h1 : HasDerivAt (fun t : ℝ => ((m * t : ℝ) : ℂ)) (m : ℂ) (Φ₀ k) := by
      simpa using ((hasDerivAt_id (Φ₀ k)).const_mul m).ofReal_comp
    exact (h1.mul_const I).cexp
  have h2 := (hF.hasFDerivAt.comp k h.hasFDerivAt).fderiv
  rw [show (fun y => exp (↑(m * Φ₀ y) * I)) = (fun t : ℝ => exp (↑(m * t) * I)) ∘ Φ₀ from rfl, h2]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ofReal_mul]
  rw [Complex.real_smul]; ring

/-- A continuous compactly supported function times a continuous function is integrable. -/
theorem integrable_mul_of_hasCompactSupport {f g : ℝ × ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hgs : HasCompactSupport g) : Integrable (fun k => f k * g k) :=
  (hf.mul hg).integrable_of_hasCompactSupport (hgs.mul_left)

/-- One integration by parts against the phase factor in direction `v`. -/
theorem integral_exp_phase_mul_fderiv {Φ₀ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ₀) (m : ℝ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g) (v : ℝ × ℝ) :
    ∫ k, exp (↑(m * Φ₀ k) * I) * fderiv ℝ g k v =
      - ∫ k, exp (↑(m * Φ₀ k) * I) * (↑(m * fderiv ℝ Φ₀ k v) * I) * g k := by
  have hd : Differentiable ℝ Φ₀ := hΦ.differentiable one_ne_zero
  have he : Continuous fun k => exp (↑(m * Φ₀ k) * I) := by fun_prop
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfΦ : Continuous fun k => fderiv ℝ Φ₀ k v :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun k => exp (↑(m * Φ₀ k) * I)) (g := g) (v := v) ?_ ?_ ?_
    (fun k _ => by fun_prop) (fun k _ => hgd k)
  · rw [h]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [fderiv_exp_phase m (hd k)]
  · simp_rw [fderiv_exp_phase m (hd _)]
    refine integrable_mul_of_hasCompactSupport ?_ hg.continuous hgs
    exact he.mul ((continuous_ofReal.comp (continuous_const.mul hfΦ)).mul continuous_const)
  · exact integrable_mul_of_hasCompactSupport he
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hgs.fderiv_apply (𝕜 := ℝ) v)
  · exact integrable_mul_of_hasCompactSupport he hg.continuous hgs

/-- The divergence amplitude `div(w A) = ∂₁(w₁ A) + ∂₂(w₂ A)`. -/
noncomputable def divAmp (w₁ w₂ : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  fderiv ℝ (fun y => w₁ y • A y) k (1, 0) + fderiv ℝ (fun y => w₂ y • A y) k (0, 1)

/-- Pointwise: `e^{imΦ} A = (1/(im)) Σᵢ ∂ᵢ(e^{imΦ}) wᵢ A` where `∂Φ·w = 1` on the support of `A`. -/
theorem exp_phase_mul_eq {Φ₀ : ℝ × ℝ → ℝ} {m : ℝ} (hm : m ≠ 0) {w₁ w₂ : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ}
    (hw : ∀ k ∈ tsupport A, fderiv ℝ Φ₀ k (1, 0) * w₁ k + fderiv ℝ Φ₀ k (0, 1) * w₂ k = 1) (k : ℝ × ℝ) :
    exp (↑(m * Φ₀ k) * I) * A k = 1 / (I * m) *
      (exp (↑(m * Φ₀ k) * I) * (↑(m * fderiv ℝ Φ₀ k (1, 0)) * I) * (w₁ k • A k) +
        exp (↑(m * Φ₀ k) * I) * (↑(m * fderiv ℝ Φ₀ k (0, 1)) * I) * (w₂ k • A k)) := by
  by_cases hk : k ∈ tsupport A
  · have h := hw k hk
    have h' : ((fderiv ℝ Φ₀ k (1, 0) : ℂ) * w₁ k + (fderiv ℝ Φ₀ k (0, 1) : ℂ) * w₂ k) = 1 := by
      exact_mod_cast h
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hI : I * (m : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hm'
    calc exp (↑(m * Φ₀ k) * I) * A k = 1 / (I * m) * (I * m) * (exp (↑(m * Φ₀ k) * I) * A k *
          ((fderiv ℝ Φ₀ k (1, 0) : ℂ) * w₁ k + (fderiv ℝ Φ₀ k (0, 1) : ℂ) * w₂ k)) := by
          rw [h', one_div, inv_mul_cancel₀ hI]; ring
      _ = _ := by simp only [Complex.real_smul, ofReal_mul]; ring
  · rw [image_eq_zero_of_notMem_tsupport hk]; simp

/-- Integration by parts in both directions: `I(mΦ, A) = (i/m) I(mΦ, div(w A))`. -/
theorem oscInt2_eq_divAmp {Φ₀ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ₀) {m : ℝ} (hm : m ≠ 0)
    {w₁ w₂ : ℝ × ℝ → ℝ} (hw₁ : ContDiff ℝ 1 w₁) (hw₂ : ContDiff ℝ 1 w₂) {A : ℝ × ℝ → ℂ}
    (hA : ContDiff ℝ 1 A) (hAs : HasCompactSupport A)
    (hw : ∀ k ∈ tsupport A, fderiv ℝ Φ₀ k (1, 0) * w₁ k + fderiv ℝ Φ₀ k (0, 1) * w₂ k = 1) :
    oscInt2 (fun k => m * Φ₀ k) A = I / m * oscInt2 (fun k => m * Φ₀ k) (divAmp w₁ w₂ A) := by
  have hg₁ : ContDiff ℝ 1 (fun y => w₁ y • A y) := hw₁.smul hA
  have hg₂ : ContDiff ℝ 1 (fun y => w₂ y • A y) := hw₂.smul hA
  have hs₁ : HasCompactSupport (fun y => w₁ y • A y) := by
    have h := hAs.smul_left (f := w₁) (R := ℝ); exact h
  have hs₂ : HasCompactSupport (fun y => w₂ y • A y) := by
    have h := hAs.smul_left (f := w₂) (R := ℝ); exact h
  have he : Continuous fun k => exp (↑(m * Φ₀ k) * I) := by
    have := hΦ.continuous; fun_prop
  have hfΦ : ∀ v : ℝ × ℝ, Continuous fun k => fderiv ℝ Φ₀ k v := fun v =>
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ (v : ℝ × ℝ) (g : ℝ × ℝ → ℂ), Continuous g → HasCompactSupport g →
      Integrable (fun k => exp (↑(m * Φ₀ k) * I) * (↑(m * fderiv ℝ Φ₀ k v) * I) * g k) :=
    fun v g hg hgs => integrable_mul_of_hasCompactSupport
      (he.mul ((continuous_ofReal.comp (continuous_const.mul (hfΦ v))).mul continuous_const)) hg hgs
  have hintd : ∀ (v : ℝ × ℝ) (g : ℝ × ℝ → ℂ), ContDiff ℝ 1 g → HasCompactSupport g →
      Integrable (fun k => exp (↑(m * Φ₀ k) * I) * fderiv ℝ g k v) :=
    fun v g hg hgs => integrable_mul_of_hasCompactSupport he
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hgs.fderiv_apply (𝕜 := ℝ) v)
  unfold oscInt2
  simp_rw [exp_phase_mul_eq hm hw]
  rw [integral_const_mul, integral_add (hint _ _ hg₁.continuous hs₁) (hint _ _ hg₂.continuous hs₂)]
  unfold divAmp
  simp_rw [mul_add]
  rw [integral_add (hintd _ _ hg₁ hs₁) (hintd _ _ hg₂ hs₂), integral_exp_phase_mul_fderiv hΦ m hg₁ hs₁,
    integral_exp_phase_mul_fderiv hΦ m hg₂ hs₂]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hc : 1 / (I * m) = -(I / m) := by
    field_simp
    rw [I_sq]; ring
  rw [hc]; ring

/-- `Σᵢ C(n, i) aᵢ ≤ 2ⁿ B` when every `aᵢ ≤ B`, `i ≤ n`. -/
theorem sum_choose_mul_le {n : ℕ} {a : ℕ → ℝ} {B : ℝ} (h : ∀ i ≤ n, a i ≤ B) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i ≤ 2 ^ n * B := by
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left (h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _)
    _ = 2 ^ n * B := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

/-- Derivatives of a directional derivative: `‖Dʲ(∂ᵥg)(x)‖ ≤ ‖v‖ ‖Dʲ⁺¹g(x)‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → F} {j : ℕ}
    (hg : ContDiff ℝ (j + 1) g) (v x : E) :
    ‖iteratedFDeriv ℝ j (fun k => fderiv ℝ g k v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) g x‖ := by
  have hL : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L => by
      simpa [mul_comm] using L.le_opNorm v
  have h := (ContinuousLinearMap.apply ℝ F v).norm_iteratedFDeriv_comp_left (f := fderiv ℝ g) (x := x)
    (N := j) ((hg.fderiv_right le_rfl).contDiffAt) le_rfl
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Pointwise Leibniz bound for `w • A` when the derivatives of `w` are bounded by `W` on `K ⊇ tsupport A`
and those of `A` by `M`. -/
theorem norm_iteratedFDeriv_smul_le_of_bound {n : ℕ} {K : Set (ℝ × ℝ)} {w : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ}
    {W M : ℝ} (hw : ContDiff ℝ n w) (hWp : 0 ≤ W) (hW : ∀ l ≤ n, ∀ k ∈ K, ‖iteratedFDeriv ℝ l w k‖ ≤ W)
    (hA : AmpBound n K A M) (k : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => w y • A y) k‖ ≤ 2 ^ n * (W * M) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (Nat.zero_le _) k)
  refine (norm_iteratedFDeriv_smul_le hw hA.1 k le_rfl).trans ?_
  simp_rw [mul_assoc]
  refine sum_choose_mul_le (a := fun i => ‖iteratedFDeriv ℝ i w k‖ * ‖iteratedFDeriv ℝ (n - i) A k‖)
    fun i hi => ?_
  by_cases hk : k ∈ K
  · exact mul_le_mul (hW i hi k hk) (hA.2.2 _ (Nat.sub_le n i) k) (norm_nonneg _) hWp
  · have h0 : iteratedFDeriv ℝ (n - i) A k = 0 :=
      Function.notMem_support.mp fun h => hk (hA.2.1 (support_iteratedFDeriv_subset _ h))
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hWp hM

/-- `AmpBound` is monotone in the order. -/
theorem ampBound_of_le {n n' : ℕ} {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound n K A M)
    (hn : n' ≤ n) : AmpBound n' K A M :=
  ⟨h.1.of_le (by exact_mod_cast hn), h.2.1, fun j hj => h.2.2 j (hj.trans hn)⟩

/-- Directional derivatives lower the order by one. -/
theorem contDiff_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × ℝ → F} {n : ℕ}
    (hg : ContDiff ℝ (n + 1) g) (v : ℝ × ℝ) : ContDiff ℝ n (fun k => fderiv ℝ g k v) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

/-- Amplitude bound for `div(w A)`: order drops by one, constant `2 · 2ⁿ⁺¹ W M`. -/
theorem ampBound_divAmp {n : ℕ} {K : Set (ℝ × ℝ)} {w₁ w₂ : ℝ × ℝ → ℝ} {A : ℝ × ℝ → ℂ} {W M : ℝ}
    (hw₁ : ContDiff ℝ (n + 1) w₁) (hw₂ : ContDiff ℝ (n + 1) w₂) (hWp : 0 ≤ W)
    (hW₁ : ∀ l ≤ n + 1, ∀ k ∈ K, ‖iteratedFDeriv ℝ l w₁ k‖ ≤ W)
    (hW₂ : ∀ l ≤ n + 1, ∀ k ∈ K, ‖iteratedFDeriv ℝ l w₂ k‖ ≤ W) (hA : AmpBound (n + 1) K A M) :
    AmpBound n K (divAmp w₁ w₂ A) (2 * 2 ^ (n + 1) * (W * M)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (Nat.zero_le _) 0)
  have hg₁ : ContDiff ℝ (n + 1) (fun y => w₁ y • A y) := hw₁.smul hA.1
  have hg₂ : ContDiff ℝ (n + 1) (fun y => w₂ y • A y) := hw₂.smul hA.1
  have hd₁ := contDiff_fderiv_apply hg₁ (1, 0)
  have hd₂ := contDiff_fderiv_apply hg₂ (0, 1)
  refine ⟨hd₁.add hd₂, ?_, fun j hj k => ?_⟩
  · refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_fderiv_apply_subset ℝ _).trans ((tsupport_smul_subset_right _ _).trans hA.2.1)
    · exact (tsupport_fderiv_apply_subset ℝ _).trans ((tsupport_smul_subset_right _ _).trans hA.2.1)
  have hj' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have hb : ∀ (w : ℝ × ℝ → ℝ) (v : ℝ × ℝ), ‖v‖ = 1 → ContDiff ℝ (n + 1) w →
      (∀ l ≤ n + 1, ∀ k ∈ K, ‖iteratedFDeriv ℝ l w k‖ ≤ W) →
      ‖iteratedFDeriv ℝ j (fun k => fderiv ℝ (fun y => w y • A y) k v) k‖ ≤ 2 ^ (n + 1) * (W * M) := by
    intro w v hv hw hW
    have hj1 : j + 1 ≤ n + 1 := by omega
    refine (norm_iteratedFDeriv_fderiv_apply_le ((hw.smul hA.1).of_le (by exact_mod_cast hj1)) v k).trans ?_
    rw [hv, one_mul]
    refine (norm_iteratedFDeriv_smul_le_of_bound (hw.of_le (by exact_mod_cast hj1)) hWp
      (fun l hl => hW l (hl.trans hj1)) (ampBound_of_le hA hj1) k).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj1) (mul_nonneg hWp hM)
  have hsum : iteratedFDeriv ℝ j (divAmp w₁ w₂ A) k =
      iteratedFDeriv ℝ j (fun k => fderiv ℝ (fun y => w₁ y • A y) k (1, 0)) k +
        iteratedFDeriv ℝ j (fun k => fderiv ℝ (fun y => w₂ y • A y) k (0, 1)) k :=
    iteratedFDeriv_add_apply ((hd₁.of_le hj').contDiffAt) ((hd₂.of_le hj').contDiffAt)
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have h1 := hb w₁ (1, 0) (by simp) hw₁ hW₁
  have h2 := hb w₂ (0, 1) (by simp) hw₂ hW₂
  linarith

/-- Trivial bound: `|I(Q, A)| ≤ |K| M` for `A` supported in a compact `K` with `|A| ≤ M`. -/
theorem norm_oscInt2_le_volume {K : Set (ℝ × ℝ)} (hK : IsCompact K) (Q : ℝ × ℝ → ℝ) {A : ℝ × ℝ → ℂ}
    {M : ℝ} (hAK : tsupport A ⊆ K) (hM : ∀ k, ‖A k‖ ≤ M) :
    ‖oscInt2 Q A‖ ≤ (volume K).toReal * M := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hle : ∀ k, ‖exp (↑(Q k) * I) * A k‖ ≤ K.indicator (fun _ => M) k := by
    intro k
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
    by_cases hk : k ∈ K
    · rw [indicator_of_mem hk]; exact hM k
    · rw [indicator_of_notMem hk, image_eq_zero_of_notMem_tsupport (fun h => hk (hAK h)), norm_zero]
  have hint : Integrable (K.indicator fun _ : ℝ × ℝ => M) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hK.measure_lt_top.ne)
  calc ‖oscInt2 Q A‖ ≤ ∫ k, K.indicator (fun _ => M) k :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hle)
    _ = (volume K).toReal * M := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, measureReal_def]

/-- `‖(i/m) z‖ = ‖z‖ / m` for `m > 0`. -/
theorem norm_I_div_mul {m : ℝ} (hm : 0 < m) (z : ℂ) : ‖I / m * z‖ = ‖z‖ / m := by
  rw [norm_mul, norm_div, norm_I, Complex.norm_real, Real.norm_of_nonneg hm.le]; ring

/-- (N2) given the weights: if `w = (w₁, w₂)` satisfies `∇Φ_τ · w_τ = 1` on `K` and the derivatives of `w`
of order `≤ N` are bounded by `W` on `K`, then `|I(mΦ_τ, A)| ≤ C M m^{-n}` for `n ≤ N`, by induction on `n`
with `A ↦ div(w A)`. -/
theorem nonStat_of_weights {T : Type*} {N : ℕ} {Φ : T → ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hΦ : ∀ τ, ContDiff ℝ 1 (Φ τ)) {w₁ w₂ : T → ℝ × ℝ → ℝ} (hw₁ : ∀ τ, ContDiff ℝ N (w₁ τ))
    (hw₂ : ∀ τ, ContDiff ℝ N (w₂ τ)) {W : ℝ} (hWp : 0 ≤ W)
    (hW₁ : ∀ l ≤ N, ∀ τ, ∀ k ∈ K, ‖iteratedFDeriv ℝ l (w₁ τ) k‖ ≤ W)
    (hW₂ : ∀ l ≤ N, ∀ τ, ∀ k ∈ K, ‖iteratedFDeriv ℝ l (w₂ τ) k‖ ≤ W)
    (hid : ∀ τ, ∀ k ∈ K, fderiv ℝ (Φ τ) k (1, 0) * w₁ τ k + fderiv ℝ (Φ τ) k (0, 1) * w₂ τ k = 1) :
    ∀ n ≤ N, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (τ : T) (m : ℝ), AmpBound n K A M → 1 ≤ m →
      ‖oscInt2 (fun k => m * Φ τ k) A‖ ≤ C * M / m ^ n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨(volume K).toReal, fun A M τ m hA _ => ?_⟩
    rw [pow_zero, div_one]
    exact norm_oscInt2_le_volume hK _ hA.2.1 fun k => by simpa using hA.2.2 0 le_rfl k
  | succ n ih =>
    intro hn
    obtain ⟨C, hC⟩ := ih (by omega)
    refine ⟨C * (2 * 2 ^ (n + 1) * W), fun A M τ m hA hm => ?_⟩
    have hm0 : 0 < m := by linarith
    have hN1 : (1 : WithTop ℕ∞) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hnN : (↑(n + 1) : WithTop ℕ∞) ≤ N := by exact_mod_cast hn
    have hAs : HasCompactSupport A := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hA.2.1
    rw [oscInt2_eq_divAmp (hΦ τ) hm0.ne' ((hw₁ τ).of_le hN1) ((hw₂ τ).of_le hN1)
      (hA.1.of_le (by exact_mod_cast (show 1 ≤ n + 1 by omega))) hAs
      (fun k hk => hid τ k (hA.2.1 hk)), norm_I_div_mul hm0]
    have hB := ampBound_divAmp ((hw₁ τ).of_le hnN) ((hw₂ τ).of_le hnN) hWp
      (fun l hl k hk => hW₁ l (hl.trans hn) τ k hk) (fun l hl k hk => hW₂ l (hl.trans hn) τ k hk) hA
    rw [← mul_assoc] at hB
    have h := hC _ _ τ m hB hm
    calc ‖oscInt2 (fun k => m * Φ τ k) (divAmp (w₁ τ) (w₂ τ) A)‖ / m
        ≤ C * (2 * 2 ^ (n + 1) * W * M) / m ^ n / m := div_le_div_of_nonneg_right h hm0.le
      _ = C * (2 * 2 ^ (n + 1) * W) * M / m ^ (n + 1) := by field_simp; ring

end Analytic

/-- Uniform bounds for the derivatives of a family of class `Cᴺ` over a compact parameter space on a compact
set. -/
theorem FamC.exists_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] {N : ℕ}
    {w : T → ℝ × ℝ → ℝ} (hw : FamC N w) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ W, 0 ≤ W ∧ ∀ l ≤ N, ∀ τ, ∀ k ∈ K, ‖iteratedFDeriv ℝ l (w τ) k‖ ≤ W := by
  have h : ∀ l : Fin (N + 1), ∃ b, ∀ q ∈ (univ : Set T) ×ˢ K,
      ‖iteratedFDeriv ℝ l (w q.1) q.2‖ ≤ b := fun l =>
    (isCompact_univ.prod hK).exists_bound_of_continuousOn
      (hw.2 l (Nat.lt_succ_iff.mp l.2)).continuousOn
  choose b hb using h
  refine ⟨∑ l, max (b l) 0, Finset.sum_nonneg fun l _ => le_max_right _ _, fun l hl τ k hk => ?_⟩
  calc ‖iteratedFDeriv ℝ l (w τ) k‖ ≤ max (b ⟨l, Nat.lt_succ_of_le hl⟩) 0 :=
        (hb ⟨l, Nat.lt_succ_of_le hl⟩ (τ, k) ⟨mem_univ _, hk⟩).trans (le_max_left _ _)
    _ ≤ ∑ l, max (b l) 0 :=
        Finset.single_le_sum (f := fun l => max (b l) 0) (fun l _ => le_max_right _ _) (Finset.mem_univ _)

/-- The weights `w = ∇Φ / G̃` of (N2), `G̃ = |∇Φ|² + (1 - χ) c²/4` with the Euclidean square, `χ` a smooth
cutoff equal to `1` on `K` and supported where `|∇Φ|² > c²/4` for all `τ`: a family of class `Cᴺ` with
`∇Φ_τ · w_τ = 1` on `K`. -/
theorem exists_weights {T : Type} [TopologicalSpace T] [CompactSpace T] {N : ℕ} {Φ : T → ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} {c : ℝ} (hΦ : FamC (N + 1) Φ) (hK : IsCompact K) (hc : 0 < c)
    (hgrad : ∀ τ, ∀ k ∈ K, c ^ 2 ≤ fderiv ℝ (Φ τ) k (1, 0) ^ 2 + fderiv ℝ (Φ τ) k (0, 1) ^ 2) :
    ∃ w₁ w₂ : T → ℝ × ℝ → ℝ, FamC N w₁ ∧ FamC N w₂ ∧
      ∀ τ, ∀ k ∈ K, fderiv ℝ (Φ τ) k (1, 0) * w₁ τ k + fderiv ℝ (Φ τ) k (0, 1) * w₂ τ k = 1 := by
  have hD : FamC N (fun τ => fderiv ℝ (Φ τ)) := (famC_succ_iff.mp hΦ).2.2
  have hφ : ∀ v : ℝ × ℝ, FamC N (fun τ k => fderiv ℝ (Φ τ) k v) := fun v =>
    hD.clm_comp (ContinuousLinearMap.apply ℝ ℝ v)
  set G : T → ℝ × ℝ → ℝ := fun τ k => fderiv ℝ (Φ τ) k (1, 0) * fderiv ℝ (Φ τ) k (1, 0) +
    fderiv ℝ (Φ τ) k (0, 1) * fderiv ℝ (Φ τ) k (0, 1) with hGdef
  have hG : FamC N G := ((hφ _).mul (hφ _)).add ((hφ _).mul (hφ _))
  have hGK : ∀ τ, ∀ k ∈ K, c ^ 2 ≤ G τ k := fun τ k hk => by
    have := hgrad τ k hk; simp only [hGdef]; nlinarith
  have hG0 : ∀ τ k, 0 ≤ G τ k := fun τ k => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hO : IsOpen {q : T × (ℝ × ℝ) | c ^ 2 / 4 < G q.1 q.2} := isOpen_lt continuous_const hG.continuous
  have hsub : (univ : Set T) ×ˢ K ⊆ {q : T × (ℝ × ℝ) | c ^ 2 / 4 < G q.1 q.2} := by
    rintro ⟨τ, k⟩ ⟨-, hk⟩
    have := hGK τ k hk
    show c ^ 2 / 4 < G τ k
    nlinarith
  obtain ⟨u, V, -, hV, hu, hKV, huV⟩ := generalized_tube_lemma isCompact_univ hK hO hsub
  obtain ⟨χ, hχs, -, hχt, hχI, hχ1⟩ :=
    OscInt.StationaryPhase.partition 1 K (fun _ => V) hK (fun _ => hV) fun k hk => mem_iUnion.mpr ⟨0, hKV hk⟩
  have hGV : ∀ τ, ∀ k ∈ V, c ^ 2 / 4 < G τ k := fun τ k hk => by
    have := huV (show (τ, k) ∈ u ×ˢ V from ⟨hu (mem_univ τ), hk⟩); exact this
  set Gt : T → ℝ × ℝ → ℝ := fun τ k => G τ k + (1 - χ 0 k) * (c ^ 2 / 4) with hGtdef
  have hχN : ContDiff ℝ N (χ 0) := (hχs 0).of_le (by exact_mod_cast le_top)
  have hGt : FamC N Gt :=
    hG.add (famC_const ((contDiff_const.sub hχN).mul contDiff_const))
  have hpos : ∀ τ k, 0 < Gt τ k := by
    intro τ k
    have h1 := (hχI 0 k).2
    have hc4 : 0 < c ^ 2 / 4 := by positivity
    by_cases hk : k ∈ V
    · have := hGV τ k hk
      have : 0 ≤ (1 - χ 0 k) * (c ^ 2 / 4) := mul_nonneg (by linarith) hc4.le
      simp only [hGtdef]; linarith
    · have h0 : χ 0 k = 0 := image_eq_zero_of_notMem_tsupport fun h => hk (hχt 0 h)
      simp only [hGtdef, h0]; linarith [hG0 τ k]
  have hinv := hGt.inv fun τ k => (hpos τ k).ne'
  refine ⟨fun τ k => fderiv ℝ (Φ τ) k (1, 0) * (Gt τ k)⁻¹,
    fun τ k => fderiv ℝ (Φ τ) k (0, 1) * (Gt τ k)⁻¹, (hφ _).mul hinv, (hφ _).mul hinv,
    fun τ k hk => ?_⟩
  have h1 : χ 0 k = 1 := by simpa using hχ1 k hk
  have hGk : 0 < G τ k := lt_of_lt_of_le (by positivity) (hGK τ k hk)
  have hGt' : Gt τ k = G τ k := by simp only [hGtdef, h1]; ring
  show _ * (_ * (Gt τ k)⁻¹) + _ * (_ * (Gt τ k)⁻¹) = 1
  rw [hGt']
  have hGk' := hGk.ne'
  simp only [hGdef] at hGk' ⊢
  rw [← mul_assoc, ← mul_assoc, ← add_mul]
  exact mul_inv_cancel₀ hGk'

end OscInt.StationaryPhase.NonStatAux

namespace OscInt.StationaryPhase

open OscInt.StationaryPhase.NonStatAux OscInt.Statements

/-- **F3** Products and reciprocals of families of class `Cⁿ` are of class `Cⁿ`. -/
theorem familyCalculus : OscInt.Blueprint.FamilyCalculusFacts := by
  intro T _ n f g hf hg
  exact ⟨FamC.mul (E := ℝ × ℝ) hf hg, fun h0 => FamC.inv (E := ℝ × ℝ) hf h0⟩

/-- **N2** Non-stationary phase of order `N` for a compact family with `|∇Φ_τ| ≥ c` on `K`. -/
theorem nonStatCore : OscInt.Blueprint.NonStatCoreFacts := by
  intro T _ _ N Φ K c hΦ hK hc hgrad
  have hΦ' : FamC (N + 1) Φ := hΦ
  obtain ⟨w₁, w₂, hw₁, hw₂, hid⟩ := exists_weights hΦ' hK hc fun τ k hk => by
    simpa [GradLower] using hgrad τ k hk
  obtain ⟨W₁, hW₁p, hW₁⟩ := hw₁.exists_bound hK
  obtain ⟨W₂, -, hW₂⟩ := hw₂.exists_bound hK
  obtain ⟨C, hC⟩ := nonStat_of_weights hK (fun τ => (hΦ'.1 τ).of_le (by exact_mod_cast
      (show 1 ≤ N + 1 by omega))) hw₁.1 hw₂.1 (W := max W₁ W₂) (hW₁p.trans (le_max_left _ _))
    (fun l hl τ k hk => (hW₁ l hl τ k hk).trans (le_max_left _ _))
    (fun l hl τ k hk => (hW₂ l hl τ k hk).trans (le_max_right _ _)) hid N le_rfl
  exact ⟨C, hC⟩

end OscInt.StationaryPhase
