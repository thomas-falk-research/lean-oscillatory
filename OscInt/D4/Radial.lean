import Blueprint.D4LimitS42
import OscInt.D4.CosMoment

/-!
# S4.2, part E1a: the radial identity

`OscInt.D4.radialIdentity : OscInt.Blueprint.RadialIdentityFacts`. For a `C¹` profile `ψ` with `ψ = 1` on `[0, 1]`,
`ψ = 0` on `[K, ∞)` and `l > 0`,
`l^{2/3} ∫₀^K cos(l r³) ψ(r) r dr = −(1/3) ∫₁^K ψ′(ρ) cosMomentPartial(l ρ³) dρ`.

Proof (route `docs/proof-S42.md`, revision; brief S4.2 Task Y, integration by parts variant): the function
`G ρ = (1/3) l^{-2/3} cosMomentPartial(l ρ³)` is a primitive of `cos(l ρ³) ρ` on `(0, ∞)` (FTC for
`cosMomentPartial` at `u > 0` and the chain rule, `(l ρ³)^{-1/3} = l^{-1/3} ρ⁻¹`) and is continuous on `[0, 1]` with
`G 0 = 0`. Split `∫₀^K` at `1`: on `[0, 1]` `ψ = 1` and the FTC gives `G 1`; on `[1, K]` integrate by parts
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`) with `ψ K = 0`, `ψ 1 = 1`, giving
`−G 1 − ∫₁^K ψ′ G`. Multiply by `l^{2/3}`.
-/

namespace OscInt.D4.RadialAux

open Set MeasureTheory Filter Topology OscInt.Statements

/-- `cosMomentPartial` has derivative `cos u · u^{-1/3}` at every `u > 0`. -/
theorem hasDerivAt_cosMomentPartial {u : ℝ} (hu : 0 < u) :
    HasDerivAt cosMomentPartial (Real.cos u * u ^ (-(1 : ℝ) / 3)) u := by
  have hc : ContinuousOn (fun v : ℝ => Real.cos v * v ^ (-(1 : ℝ) / 3)) (Ioi 0) := fun v hv =>
    (Real.continuous_cos.continuousAt.mul
      (Real.continuousAt_rpow_const v _ (Or.inl (ne_of_gt hv)))).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right
    (OscInt.D4.CosMomentAux.intervalIntegrable_cos_mul_rpow u hu.le)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi u hu)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hu))

/-- `(l ρ³)^{-1/3} = l^{-1/3} ρ⁻¹` for `l, ρ > 0`. -/
theorem rpow_cube_neg_third {l ρ : ℝ} (hl : 0 < l) (hρ : 0 < ρ) :
    (l * ρ ^ 3) ^ (-(1 : ℝ) / 3) = l ^ (-(1 : ℝ) / 3) * ρ⁻¹ := by
  rw [Real.mul_rpow hl.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num [Real.rpow_neg_one]

/-- `l^{-2/3} · l^{-1/3} · l = 1` for `l > 0`. -/
theorem rpow_two_thirds_cancel {l : ℝ} (hl : 0 < l) :
    l ^ (-(2 : ℝ) / 3) * l ^ (-(1 : ℝ) / 3) * l = 1 := by
  rw [← Real.rpow_add hl, ← Real.rpow_add_one hl.ne']
  norm_num

/-- The primitive `G ρ = (1/3) l^{-2/3} cosMomentPartial (l ρ³)` of `cos(l ρ³) ρ`. -/
noncomputable def radialPrim (l ρ : ℝ) : ℝ := (1 / 3) * l ^ (-(2 : ℝ) / 3) * cosMomentPartial (l * ρ ^ 3)

/-- `G` is a primitive of `cos(l ρ³) ρ` on `(0, ∞)`. -/
theorem hasDerivAt_radialPrim {l ρ : ℝ} (hl : 0 < l) (hρ : 0 < ρ) :
    HasDerivAt (radialPrim l) (Real.cos (l * ρ ^ 3) * ρ) ρ := by
  have h1 : HasDerivAt (fun x : ℝ => l * x ^ 3) (l * (3 * ρ ^ 2)) ρ := by
    simpa using (hasDerivAt_pow 3 ρ).const_mul l
  have h2 := ((hasDerivAt_cosMomentPartial (by positivity : 0 < l * ρ ^ 3)).comp ρ h1).const_mul
    ((1 / 3) * l ^ (-(2 : ℝ) / 3))
  convert h2 using 1
  · rfl
  rw [rpow_cube_neg_third hl hρ]
  have hX := rpow_two_thirds_cancel hl
  have hY : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ.ne'
  linear_combination (-(Real.cos (l * ρ ^ 3) * ρ * (ρ⁻¹ * ρ))) * hX - Real.cos (l * ρ ^ 3) * ρ * hY

/-- `G` is continuous on `[0, 1]`. -/
theorem continuousOn_radialPrim {l : ℝ} (hl : 0 < l) : ContinuousOn (radialPrim l) (Icc 0 1) := by
  have hP : ContinuousOn cosMomentPartial (uIcc 0 l) :=
    intervalIntegral.continuousOn_primitive_interval'
      (OscInt.D4.CosMomentAux.intervalIntegrable_cos_mul_rpow l hl.le) left_mem_uIcc
  refine continuousOn_const.mul (hP.comp (continuousOn_const.mul (continuousOn_pow 3)) ?_)
  intro x hx
  rw [uIcc_of_le hl.le]
  refine ⟨by have := hx.1; positivity, ?_⟩
  have : x ^ 3 ≤ 1 := pow_le_one₀ hx.1 hx.2
  nlinarith

end OscInt.D4.RadialAux

namespace OscInt.D4

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint OscInt.D4.RadialAux

/-- **E1a** The radial identity (`OscInt.Blueprint.RadialIdentityFacts`). -/
theorem radialIdentity : RadialIdentityFacts := by
  intro ψ hψ K hK h1 hK0 l hl
  have hψc : Continuous ψ := hψ.continuous
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable one_ne_zero) x).hasDerivAt
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hf : Continuous fun r : ℝ => Real.cos (l * r ^ 3) * ψ r * r := by fun_prop
  have hg : Continuous fun r : ℝ => Real.cos (l * r ^ 3) * r := by fun_prop
  -- split at `1`
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  -- the piece on `[0, 1]`
  have hA : ∫ r in (0 : ℝ)..1, Real.cos (l * r ^ 3) * ψ r * r = radialPrim l 1 := by
    have : ∫ r in (0 : ℝ)..1, Real.cos (l * r ^ 3) * ψ r * r =
        ∫ r in (0 : ℝ)..1, Real.cos (l * r ^ 3) * r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le zero_le_one] at hr
      simp only [h1 r hr, mul_one]
    rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_radialPrim hl) (fun x hx => hasDerivAt_radialPrim hl hx.1)
      (hg.intervalIntegrable _ _)]
    simp [radialPrim, cosMomentPartial]
  -- the piece on `[1, K]`, by parts
  have hB : ∫ r in (1 : ℝ)..K, Real.cos (l * r ^ 3) * ψ r * r =
      - radialPrim l 1 - ∫ r in (1 : ℝ)..K, deriv ψ r * radialPrim l r := by
    have hpos : ∀ x ∈ uIcc 1 K, 0 < x := fun x hx => by
      rw [uIcc_of_le hK] at hx; linarith [hx.1]
    have hGc : ContinuousOn (radialPrim l) (uIcc 1 K) := fun x hx =>
      (hasDerivAt_radialPrim hl (hpos x hx)).continuousAt.continuousWithinAt
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hψc.continuousOn hGc (fun x _ => hψd x)
      (fun x hx => hasDerivAt_radialPrim hl (hpos x (Ioo_subset_Icc_self hx)))
      (hψ'.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    rw [hK0 K le_rfl, h1 1 ⟨zero_le_one, le_rfl⟩] at hibp
    rw [← sub_eq_zero]
    have : ∫ r in (1 : ℝ)..K, Real.cos (l * r ^ 3) * ψ r * r =
        ∫ x in (1 : ℝ)..K, ψ x * (Real.cos (l * x ^ 3) * x) :=
      intervalIntegral.integral_congr fun x _ => by ring
    rw [this, hibp]
    ring
  have hC : ∫ r in (1 : ℝ)..K, deriv ψ r * radialPrim l r =
      (1 / 3) * l ^ (-(2 : ℝ) / 3) * ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (l * ρ ^ 3) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by simp only [radialPrim]; ring
  rw [hA, hB, hC]
  have hcancel : l ^ ((2 : ℝ) / 3) * l ^ (-(2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hl]; norm_num
  linear_combination (-(1 / 3) * ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (l * ρ ^ 3)) * hcancel

end OscInt.D4
