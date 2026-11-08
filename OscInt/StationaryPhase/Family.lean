/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase

/-!
# S2/S3 infrastructure: algebra of phase families (F1a, F1b, F1d)

This file proves the blueprint propositions
* `OscInt.Blueprint.FamilyAddLinearFacts` (`familyAddLinear`): adding the linear term `p·(·)`, `p ∈ P`, to a
  family of class `Cⁿ` gives a family of class `Cⁿ` over `Λ × P`;
* `OscInt.Blueprint.FamilyAffineFacts` (`familyAffine`): precomposing every member with a fixed affine map
  `k ↦ k₀ + L k` keeps class `Cⁿ`;
* `OscInt.Blueprint.AmpBoundAffineFacts` (`ampBoundAffine`): amplitude bounds under an affine change of
  variables, derivatives of order `j` picking up `‖L‖ʲ`.

Route. The iterated derivative is additive (`iteratedFDeriv_add_apply`) and commutes with scalars; `p·k` is
`p₁ • k₁ + p₂ • k₂`, so `Dʲ(p·)(k)` is linear in `p` with coefficients continuous in `k`.
For the affine map,
`Dʲ(f ∘ (a + L·))(x) = Dʲf(a + L x) ∘ (L, …, L)` (`ContinuousLinearMap.iteratedFDeriv_comp_right` and
`iteratedFDeriv_comp_add_left`), which is continuous in the data by continuity of precomposition
(`ContinuousMultilinearMap.continuous_precomp`) and has norm `≤ ‖Dʲf(a + L x)‖ ‖L‖ʲ`
(`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`).
-/

namespace OscInt.StationaryPhase.FamilyAux

open Set OscInt.Statements

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Iterated derivative of `f` composed with an affine map `y ↦ a + L y`. -/
theorem iteratedFDeriv_comp_affine {n : WithTop ℕ∞} {f : E → F} (hf : ContDiff 𝕜 n f) (a : E)
    (L : G →L[𝕜] E) (x : G) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun y => f (a + L y)) x =
      (iteratedFDeriv 𝕜 i f (a + L x)).compContinuousLinearMap fun _ => L := by
  have h : (fun y => f (a + L y)) = (fun z => f (a + z)) ∘ L := rfl
  have hg : ContDiff 𝕜 n (fun z => f (a + z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [h, L.iteratedFDeriv_comp_right hg x hi, iteratedFDeriv_comp_add_left]

/-- Norm bound for the iterated derivative of `f` composed with an affine map `y ↦ a + L y`. -/
theorem norm_iteratedFDeriv_comp_affine_le {n : WithTop ℕ∞} {f : E → F} (hf : ContDiff 𝕜 n f) (a : E)
    (L : G →L[𝕜] E) (x : G) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (fun y => f (a + L y)) x‖ ≤ ‖iteratedFDeriv 𝕜 i f (a + L x)‖ * ‖L‖ ^ i := by
  rw [iteratedFDeriv_comp_affine hf a L x hi]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv 𝕜 i f (a + L x)) fun _ : Fin i => L

/-- Joint continuity of iterated derivatives is preserved by composing with a fixed affine map. -/
theorem continuous_iteratedFDeriv_comp_affine {X : Type*} [TopologicalSpace X] {n : WithTop ℕ∞}
    {f : X → E → F} (hf : ∀ x, ContDiff 𝕜 n (f x)) (a : E) (L : G →L[𝕜] E) {i : ℕ} (hi : i ≤ n)
    (hc : Continuous fun q : X × E => iteratedFDeriv 𝕜 i (f q.1) q.2) :
    Continuous fun q : X × G => iteratedFDeriv 𝕜 i (fun y => f q.1 (a + L y)) q.2 := by
  simp_rw [iteratedFDeriv_comp_affine (hf _) a L _ hi]
  exact (ContinuousMultilinearMap.continuous_precomp _).comp
    (hc.comp (continuous_fst.prodMk (continuous_const.add (L.continuous.comp continuous_snd))))

/-- Joint continuity of iterated derivatives is preserved by adding two families. -/
theorem continuous_iteratedFDeriv_add {X : Type*} [TopologicalSpace X] {i : ℕ} {f g : X → E → F}
    (hf : ∀ x, ContDiff 𝕜 i (f x)) (hg : ∀ x, ContDiff 𝕜 i (g x))
    (hfc : Continuous fun q : X × E => iteratedFDeriv 𝕜 i (f q.1) q.2)
    (hgc : Continuous fun q : X × E => iteratedFDeriv 𝕜 i (g q.1) q.2) :
    Continuous fun q : X × E => iteratedFDeriv 𝕜 i (fun y => f q.1 y + g q.1 y) q.2 := by
  have h : ∀ q : X × E, iteratedFDeriv 𝕜 i (fun y => f q.1 y + g q.1 y) q.2 =
      iteratedFDeriv 𝕜 i (f q.1) q.2 + iteratedFDeriv 𝕜 i (g q.1) q.2 := fun q =>
    iteratedFDeriv_add_apply (f := f q.1) (g := g q.1) (hf _).contDiffAt (hg _).contDiffAt
  simp_rw [h]
  exact hfc.add hgc

/-- `p·(·)` as a combination of the coordinate functions. -/
theorem lin_eq (p : ℝ × ℝ) :
    lin p = p.1 • (fun k : ℝ × ℝ => k.1) + p.2 • (fun k : ℝ × ℝ => k.2) := by
  funext k; simp [lin]

/-- The iterated derivative of `p·(·)` is linear in `p`. -/
theorem iteratedFDeriv_lin (j : ℕ) (p k : ℝ × ℝ) :
    iteratedFDeriv ℝ j (lin p) k = p.1 • iteratedFDeriv ℝ j (fun k : ℝ × ℝ => k.1) k +
      p.2 • iteratedFDeriv ℝ j (fun k : ℝ × ℝ => k.2) k := by
  have h1 : ContDiff ℝ j (fun k : ℝ × ℝ => k.1) := contDiff_fst
  have h2 : ContDiff ℝ j (fun k : ℝ × ℝ => k.2) := contDiff_snd
  rw [lin_eq, iteratedFDeriv_add_apply (f := p.1 • fun k : ℝ × ℝ => k.1)
    (g := p.2 • fun k : ℝ × ℝ => k.2)
    (h1.const_smul p.1 : ContDiff ℝ j (p.1 • fun k : ℝ × ℝ => k.1)).contDiffAt
    (h2.const_smul p.2 : ContDiff ℝ j (p.2 • fun k : ℝ × ℝ => k.2)).contDiffAt,
    iteratedFDeriv_const_smul_apply h1.contDiffAt, iteratedFDeriv_const_smul_apply h2.contDiffAt]

/-- `p·(·)` is smooth. -/
theorem contDiff_lin {n : WithTop ℕ∞} (p : ℝ × ℝ) : ContDiff ℝ n (lin p) := by
  unfold lin; fun_prop

/-- `(p, k) ↦ Dʲ(p·)(k)` is jointly continuous. -/
theorem continuous_iteratedFDeriv_lin (j : ℕ) :
    Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => iteratedFDeriv ℝ j (lin q.1) q.2 := by
  simp_rw [iteratedFDeriv_lin]
  have h1 := (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := ⊤)).continuous_iteratedFDeriv
    (m := j) (by exact_mod_cast le_top)
  have h2 := (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := ⊤)).continuous_iteratedFDeriv
    (m := j) (by exact_mod_cast le_top)
  fun_prop

end OscInt.StationaryPhase.FamilyAux

namespace OscInt.StationaryPhase

open Set OscInt.Statements FamilyAux

/-- **F1a** Adding a linear term `p·(·)`, `p ∈ P`, keeps a family of class `Cⁿ`. -/
theorem familyAddLinear : OscInt.Blueprint.FamilyAddLinearFacts := by
  intro Λ _ n Ψ P ⟨hΨ, hc⟩
  refine ⟨fun q => (hΨ q.1).add (contDiff_lin _), fun j hj => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  exact continuous_iteratedFDeriv_add (f := fun q : Λ × P => Ψ q.1) (g := fun q => lin q.2.1)
    (fun q => (hΨ q.1).of_le hj') (fun q => contDiff_lin _)
    ((hc j hj).comp (continuous_fst.fst.prodMk continuous_snd))
    ((continuous_iteratedFDeriv_lin j).comp
      ((continuous_subtype_val.comp continuous_fst.snd).prodMk continuous_snd))

/-- **F1b** Precomposing a family of class `Cⁿ` with a fixed affine map keeps class `Cⁿ`. -/
theorem familyAffine : OscInt.Blueprint.FamilyAffineFacts := by
  intro Λ _ n Ψ k₀ L ⟨hΨ, hc⟩
  exact ⟨fun σ => (hΨ σ).comp (contDiff_const.add L.contDiff), fun j hj =>
    continuous_iteratedFDeriv_comp_affine hΨ k₀ L (by exact_mod_cast hj) (hc j hj)⟩

/-- **F1d** Amplitude bounds under an affine change of variables. -/
theorem ampBoundAffine : OscInt.Blueprint.AmpBoundAffineFacts := by
  intro n K A M k₀ L ⟨hA, hK, hM⟩
  set L' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  refine ⟨hA.comp (contDiff_const.add L'.contDiff), ?_, fun j hj k => ?_⟩
  · exact (tsupport_comp_subset_preimage A (continuous_const.add L'.continuous)).trans (preimage_mono hK)
  · have hL : ‖L'‖ ^ j ≤ max 1 ‖L'‖ ^ n :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    calc ‖iteratedFDeriv ℝ j (fun k => A (k₀ + L' k)) k‖
        ≤ ‖iteratedFDeriv ℝ j A (k₀ + L' k)‖ * ‖L'‖ ^ j :=
          norm_iteratedFDeriv_comp_affine_le hA k₀ L' k (by exact_mod_cast hj)
      _ ≤ M * max 1 ‖L'‖ ^ n := mul_le_mul (hM j hj _) hL (by positivity) hM0
      _ = max 1 ‖L'‖ ^ n * M := mul_comm _ _

end OscInt.StationaryPhase
