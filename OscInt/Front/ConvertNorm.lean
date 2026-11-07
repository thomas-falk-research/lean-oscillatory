import OscInt.Statements.Convert
import OscInt.Front.Core

/-!
# Front-end batch 2, P-Norm: `GradLower` as a norm bound (C8) and `AmpBound` in Mathlib's idiom (C9)

Route: `docs/proof-API2.md`, P-Norm.
-/

namespace OscInt.API.NormAux

open OscInt.Statements

/-- A functional on `ℝ × ℝ` is `lin` of its values on the standard basis. -/
theorem lin_apply_functional (L : (ℝ × ℝ) →L[ℝ] ℝ) (x : ℝ × ℝ) : lin (L (1, 0), L (0, 1)) x = L x := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_rhs => rw [hx]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [lin]
  ring

/-- Derivative of `Ψ` plus the linear term of a functional. -/
theorem fderiv_add_lin {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (h : DifferentiableAt ℝ Ψ k) (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    fderiv ℝ (fun x => Ψ x + lin (L (1, 0), L (0, 1)) x) k = fderiv ℝ Ψ k + L := by
  have hf : (fun x => Ψ x + lin (L (1, 0), L (0, 1)) x) = fun x => Ψ x + L x := by
    funext x; rw [lin_apply_functional]
  rw [hf]; exact (h.hasFDerivAt.add L.hasFDerivAt).fderiv

/-- The operator norm of a functional on `ℝ × ℝ` (max norm) is `|L e₀| + |L e₁|`. -/
theorem norm_prod_functional (L : (ℝ × ℝ) →L[ℝ] ℝ) : ‖L‖ = |L (1, 0)| + |L (0, 1)| := by
  set a := L (1, 0)
  set b := L (0, 1)
  have hL : ∀ x : ℝ × ℝ, L x = a * x.1 + b * x.2 := fun x => by
    rw [← lin_apply_functional]; rfl
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [hL, Real.norm_eq_abs, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |a * x.1 + b * x.2| ≤ |a| * |x.1| + |b| * |x.2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * max |x.1| |x.2| + |b| * max |x.1| |x.2| := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = (|a| + |b|) * max |x.1| |x.2| := by ring
  · set v : ℝ × ℝ := (if 0 ≤ a then 1 else -1, if 0 ≤ b then 1 else -1)
    have hv : ‖v‖ ≤ 1 := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      apply max_le <;> simp only [v] <;> split_ifs <;> simp
    have hLv : L v = |a| + |b| := by
      rw [hL]
      simp only [v]
      split_ifs with ha hb hb
      · rw [abs_of_nonneg ha, abs_of_nonneg hb]; ring
      · rw [abs_of_nonneg ha, abs_of_neg (not_le.mp hb)]; ring
      · rw [abs_of_neg (not_le.mp ha), abs_of_nonneg hb]; ring
      · rw [abs_of_neg (not_le.mp ha), abs_of_neg (not_le.mp hb)]; ring
    calc |a| + |b| = L v := hLv.symm
      _ ≤ ‖L v‖ := Real.le_norm_self _
      _ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
      _ ≤ ‖L‖ * 1 := by gcongr
      _ = ‖L‖ := mul_one _

/-- The coordinate map `x ↦ (x 0, x 1)` from the Euclidean plane to `ℝ × ℝ`. -/
noncomputable def coordProd : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

theorem coordProd_apply (x : EuclideanSpace ℝ (Fin 2)) : coordProd x = (x 0, x 1) := rfl

theorem coordProd_toEuclid (k : ℝ × ℝ) : coordProd (toEuclid k) = k := by
  rw [coordProd_apply, (sanity_toEuclid k).1, (sanity_toEuclid k).2]

/-- The Euclidean norm of `G ∘ coordProd` is `√(G(e₀)² + G(e₁)²)`. -/
theorem norm_comp_coordProd (G : (ℝ × ℝ) →L[ℝ] ℝ) :
    ‖G.comp coordProd‖ = Real.sqrt (G (1, 0) ^ 2 + G (0, 1) ^ 2) := by
  set a := G (1, 0)
  set b := G (0, 1)
  have hG : ∀ x : EuclideanSpace ℝ (Fin 2), G.comp coordProd x = a * x 0 + b * x 1 := fun x => by
    rw [ContinuousLinearMap.comp_apply, coordProd_apply, ← lin_apply_functional]; rfl
  have hn : ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := fun x => by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    rw [hG, hn, Real.norm_eq_abs, ← Real.sqrt_mul (by positivity)]
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (a * x 1 - b * x 0)]
  · set v := toEuclid (a, b)
    have hv0 : v 0 = a := (sanity_toEuclid (a, b)).1
    have hv1 : v 1 = b := (sanity_toEuclid (a, b)).2
    have hnv : ‖v‖ = Real.sqrt (a ^ 2 + b ^ 2) := by rw [hn, hv0, hv1]
    have hGv : G.comp coordProd v = a ^ 2 + b ^ 2 := by rw [hG, hv0, hv1]; ring
    have hs : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) = a ^ 2 + b ^ 2 :=
      Real.mul_self_sqrt (by positivity)
    rcases (Real.sqrt_nonneg (a ^ 2 + b ^ 2)).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · have h1 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) ≤
          ‖G.comp coordProd‖ * Real.sqrt (a ^ 2 + b ^ 2) := by
        calc _ = G.comp coordProd v := by rw [hGv, hs]
          _ ≤ ‖G.comp coordProd v‖ := Real.le_norm_self _
          _ ≤ ‖G.comp coordProd‖ * ‖v‖ := (G.comp coordProd).le_opNorm v
          _ = _ := by rw [hnv]
      exact le_of_mul_le_mul_right h1 hpos

/-- The functional `x ↦ lin p x`. -/
noncomputable def linCLM (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem linCLM_basis (p : ℝ × ℝ) : (linCLM p (1, 0), linCLM p (0, 1)) = p := by
  simp [linCLM]

theorem fderiv_add_lin' {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (h : DifferentiableAt ℝ Ψ k) (p : ℝ × ℝ) :
    fderiv ℝ (fun x => Ψ x + lin p x) k = fderiv ℝ Ψ k + linCLM p := by
  have := fderiv_add_lin h (linCLM p)
  rwa [linCLM_basis] at this

theorem differentiableAt_add_lin {Ψ : ℝ × ℝ → ℝ} {k : ℝ × ℝ} (h : DifferentiableAt ℝ Ψ k) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun x => Ψ x + lin p x) k := by
  have hf : (fun x => Ψ x + lin p x) = fun x => Ψ x + linCLM p x := by
    funext x
    have := lin_apply_functional (linCLM p) x
    rw [linCLM_basis] at this
    rw [this]
  rw [hf]; exact h.add (linCLM p).differentiableAt

end OscInt.API.NormAux

namespace OscInt.API

open OscInt.Statements OscInt.API.NormAux

/-- **C8** `GradLower` as a norm bound. -/
theorem gradLower_iff : GradLowerIffStatement := by
  intro Ψ p k c hΨ hc
  set G := fderiv ℝ (fun x => Ψ x + lin p x) k with hGdef
  have hG : G = fderiv ℝ Ψ k + linCLM p := fderiv_add_lin' hΨ p
  have ha : G (1, 0) = fderiv ℝ Ψ k (1, 0) + p.1 := by
    rw [hG]; simp [linCLM]
  have hb : G (0, 1) = fderiv ℝ Ψ k (0, 1) + p.2 := by
    rw [hG]; simp [linCLM]
  have hGL : ∀ c' : ℝ, GradLower Ψ p k c' ↔ c' ^ 2 ≤ G (1, 0) ^ 2 + G (0, 1) ^ 2 := by
    intro c'; rw [ha, hb]; rfl
  -- the Euclidean derivative
  have hE : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 2) => Ψ (x 0, x 1) + lin p (x 0, x 1)) (toEuclid k) =
      G.comp coordProd := by
    have hd : DifferentiableAt ℝ (fun x => Ψ x + lin p x) (coordProd (toEuclid k)) := by
      rw [coordProd_toEuclid]; exact differentiableAt_add_lin hΨ p
    have := (hd.hasFDerivAt.comp (toEuclid k) coordProd.hasFDerivAt).fderiv
    rw [coordProd_toEuclid] at this
    exact this
  have hnormE : ‖G.comp coordProd‖ = Real.sqrt (G (1, 0) ^ 2 + G (0, 1) ^ 2) := norm_comp_coordProd G
  have hnormM : ‖G‖ = |G (1, 0)| + |G (0, 1)| := norm_prod_functional G
  have hsq_le : Real.sqrt (G (1, 0) ^ 2 + G (0, 1) ^ 2) ≤ |G (1, 0)| + |G (0, 1)| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg (G (1, 0)), abs_nonneg (G (0, 1)), sq_abs (G (1, 0)), sq_abs (G (0, 1)),
      mul_nonneg (abs_nonneg (G (1, 0))) (abs_nonneg (G (0, 1)))]
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, hnormE, hGL, Real.le_sqrt hc (by positivity)]
  · intro h
    rw [hnormM]
    rw [hGL, ← Real.le_sqrt hc (by positivity)] at h
    exact h.trans hsq_le
  · intro h
    rw [hnormM] at h
    rw [hGL]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_pow, h2, div_le_iff₀ (by norm_num)]
    have hc2 : c ^ 2 ≤ (|G (1, 0)| + |G (0, 1)|) ^ 2 := pow_le_pow_left₀ hc h 2
    nlinarith [sq_abs (G (1, 0)), sq_abs (G (0, 1)), sq_nonneg (|G (1, 0)| - |G (0, 1)|)]

/-- **C9** `AmpBound` and Mathlib's idiom. -/
theorem ampBound_conv : AmpBoundConvStatement := by
  refine ⟨fun n K A M hK hA => ⟨hA.1, hK.of_isClosed_subset (isClosed_tsupport A) hA.2.1⟩, fun n A hA hcs => ?_⟩
  exact ampBoundOfContDiff n (tsupport A) A hcs hA subset_rfl

end OscInt.API
