/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Family

namespace OscInt.API.FamilyAux

/-- The `j`-th derivative of the slice `k' ↦ f (σ, k')` is the `j`-th derivative of `f` at `(σ, k)` restricted to
the second factor (composition with `inr` in every argument), for `j ≤ n` and `f` of class `Cⁿ`. -/
theorem iteratedFDeriv_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E × (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ n f) (σ : E) (k : ℝ × ℝ) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun k' => f (σ, k')) k =
      (iteratedFDeriv ℝ j f (σ, k)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ E (ℝ × ℝ)) := by
  have hg : ContDiff ℝ n (fun z : E × (ℝ × ℝ) => f ((σ, 0) + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun k' : ℝ × ℝ => f (σ, k')) =
      (fun z : E × (ℝ × ℝ) => f ((σ, 0) + z)) ∘ ContinuousLinearMap.inr ℝ E (ℝ × ℝ) := by
    funext k'; simp
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast hj),
    iteratedFDeriv_comp_add_left]
  simp

end OscInt.API.FamilyAux

namespace OscInt.API

/-- **C10** A family that is `Cⁿ` jointly in a real normed parameter and the point is `FamilyCk n` on every
parameter set. -/
theorem familyCk_of_uncurry : OscInt.Statements.FamilyCkOfUncurryStatement := by
  intro E _ _ n Ψ hΨ S
  refine ⟨fun σ => ?_, fun j hj => ?_⟩
  · have : ContDiff ℝ n (fun k' : ℝ × ℝ => Function.uncurry Ψ ((σ : E), k')) :=
      hΨ.comp (contDiff_const.prodMk contDiff_id)
    simpa using this
  · have hc : Continuous fun q : S × (ℝ × ℝ) =>
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => ContinuousLinearMap.inr ℝ E (ℝ × ℝ))
          (iteratedFDeriv ℝ j (Function.uncurry Ψ) ((q.1 : E), q.2)) :=
      (ContinuousLinearMap.continuous _).comp
        ((hΨ.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    refine hc.congr fun q => ?_
    rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ← FamilyAux.iteratedFDeriv_slice hΨ (q.1 : E) q.2 hj]
    rfl

end OscInt.API
