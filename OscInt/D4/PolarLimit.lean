import Blueprint.D4LimitS42
import OscInt.D4.Angular
import OscInt.D4.CosMoment
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

/-!
# S4.2, parts E1c and E1d: zeros on the circle, and the polar limit of the cubic cut-off integral

* `circleZerosNull : OscInt.Blueprint.CircleZerosNullFacts` (E1c). By C3 (`circleNondeg`) every zero `θ` of
  `g = circleCubic q` has `g′(θ) ≠ 0`, so `g ≠ 0` on a punctured neighbourhood (`HasDerivAt.eventually_ne`):
  the zero set is discrete, hence countable (`IsLindelof.countable_of_isDiscrete`), hence null.
* `cubicCutoffLimit_of : OscInt.Blueprint.CubicCutoffLimitCombineFacts` (E1d). Given E1a (radial identity),
  E1b (polar reduction) and E1c: pick `K₀ ≥ 1` with `χ = 0` outside the max-norm ball of radius `K₀`; for
  `R > 0` and `g(θ) ≠ 0` the substitution `r = Rρ` and E1a for the profile `ψ_θ(ρ) = χ(ρ cos θ, ρ sin θ)`
  (`1` on `[0, 1]`, `0` on `[2K₀, ∞)`) give inner integral `= |g|^{-2/3} · J(R, θ)` with
  `J = −(1/3) ∫₁^{2K₀} ψ_θ′(ρ) cosMomentPartial(R³|g|ρ³) dρ`. `|J|` is bounded uniformly (sup‖Dχ‖ and
  `cosMomentPartial` bounded on `[0, ∞)`), and `J → cosMoment/3` (dominated convergence in `ρ`, FTC). Dominated
  convergence in `θ` (bound `const · |g|^{-2/3}`, integrable on `[−π, π]` by periodicity) and the periodic
  shift `∫_{−π}^{π} = ∫₀^{2π}` give the limit `d4Constant q`.

Route: `docs/proof-S42.md` with its route-referee revision (`review/2026-11-06-S42-proof-route.md`, §3).
-/

namespace OscInt.D4.PolarLimitAux

open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint
open scoped ContDiff

/-- For `disc q ≠ 0` the zeros of the cubic on the circle are isolated. -/
theorem isDiscrete_zeros (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    IsDiscrete {θ : ℝ | circleCubic q θ = 0} := by
  refine IsDiscrete.of_nhdsWithin fun θ hθ => ?_
  have hd := (AngularAux.hasDerivAt_circleCubic q θ).differentiableAt.hasDerivAt
  have h : ∀ᶠ z in 𝓝[≠] θ, circleCubic q z ≠ 0 := hd.eventually_ne (circleNondeg q hq θ hθ)
  rw [eventually_nhdsWithin_iff] at h
  rw [le_pure_iff, mem_nhdsWithin_iff_eventually]
  filter_upwards [h] with z hz hzs
  by_contra hne
  exact hz hne hzs

theorem continuous_circleCubic (q : ℝ × ℝ × ℝ × ℝ) : Continuous (circleCubic q) := by
  unfold circleCubic cubicForm; fun_prop

/-- `‖ρ ω(θ)‖ ≤ ρ` in the max norm. -/
theorem norm_polar_le {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : ‖(ρ * Real.cos θ, ρ * Real.sin θ)‖ ≤ ρ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρ]
  exact max_le (mul_le_of_le_one_right hρ (Real.abs_cos_le_one θ))
    (mul_le_of_le_one_right hρ (Real.abs_sin_le_one θ))

/-- `ρ/2 ≤ ‖ρ ω(θ)‖` in the max norm. -/
theorem half_le_norm_polar (ρ θ : ℝ) :
    ρ / 2 ≤ ‖(ρ * Real.cos θ, ρ * Real.sin θ)‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  by_contra h
  push Not at h
  have h1 := (le_max_left _ _).trans_lt h
  have h2 := (le_max_right _ _).trans_lt h
  have hp := Real.sin_sq_add_cos_sq θ
  have e1 : (ρ * Real.cos θ) ^ 2 < (ρ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
  have e2 : (ρ * Real.sin θ) ^ 2 < (ρ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h2 (abs_nonneg _) (by norm_num)
  nlinarith

/-- A compactly supported function vanishes outside some max-norm ball of radius `K₀ ≥ 1`. -/
theorem exists_vanish_radius {χ : ℝ × ℝ → ℝ} (hcs : HasCompactSupport χ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ z, K₀ ≤ ‖z‖ → χ z = 0 := by
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 0 + 1, by linarith [le_max_right r 0], fun z hz => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hzs => ?_
  have := hr hzs
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left r 0]


/-- The radial profile of `χ` in direction `θ`. -/
noncomputable def psi (χ : ℝ × ℝ → ℝ) (θ ρ : ℝ) : ℝ := χ (ρ * Real.cos θ, ρ * Real.sin θ)

theorem hasDerivAt_psi {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ ρ : ℝ) :
    HasDerivAt (psi χ θ) (fderiv ℝ χ (ρ * Real.cos θ, ρ * Real.sin θ) (Real.cos θ, Real.sin θ)) ρ := by
  have hl : HasDerivAt (fun r : ℝ => r • (Real.cos θ, Real.sin θ)) ((1 : ℝ) • (Real.cos θ, Real.sin θ)) ρ :=
    (hasDerivAt_id ρ).smul_const _
  rw [one_smul] at hl
  have hf : HasFDerivAt χ (fderiv ℝ χ (ρ • (Real.cos θ, Real.sin θ))) (ρ • (Real.cos θ, Real.sin θ)) :=
    ((hχ.differentiable (by simp)) _).hasFDerivAt
  have := hf.comp_hasDerivAt ρ hl
  simp only [Function.comp_def, Prod.smul_mk, smul_eq_mul] at this
  exact this

theorem contDiff_psi {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ : ℝ) : ContDiff ℝ 1 (psi χ θ) := by
  unfold psi
  exact (hχ.of_le (by simp)).comp (by fun_prop)

theorem psi_eq_one {χ : ℝ × ℝ → ℝ} (h1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1) (θ : ℝ) :
    ∀ ρ ∈ Icc (0 : ℝ) 1, psi χ θ ρ = 1 := fun _ hρ =>
  h1 _ ((norm_polar_le hρ.1 θ).trans hρ.2)

theorem psi_eq_zero {χ : ℝ × ℝ → ℝ} {K₀ : ℝ} (hv : ∀ z, K₀ ≤ ‖z‖ → χ z = 0) (θ : ℝ) :
    ∀ ρ, 2 * K₀ ≤ ρ → psi χ θ ρ = 0 := fun ρ hρ =>
  hv _ (by have := half_le_norm_polar ρ θ; linarith)

/-- The radial derivatives are bounded uniformly in `θ`. -/
theorem exists_deriv_psi_bound {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ρ, |deriv (psi χ θ) ρ| ≤ B := by
  obtain ⟨C, hC⟩ := (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  refine ⟨max C 0, le_max_right _ _, fun θ ρ => ?_⟩
  rw [(hasDerivAt_psi hχ θ ρ).deriv, ← Real.norm_eq_abs]
  refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
  have hω : ‖(Real.cos θ, Real.sin θ)‖ ≤ 1 := by simpa using norm_polar_le zero_le_one θ
  calc _ ≤ max C 0 * 1 := mul_le_mul ((hC _).trans (le_max_left _ _)) hω (norm_nonneg _)
          (le_max_right _ _)
    _ = max C 0 := mul_one _

/-- `cosMomentPartial` is continuous on `[0, ∞)`. -/
theorem continuousOn_cosMomentPartial : ContinuousOn cosMomentPartial (Ici 0) := by
  intro x hx
  have h := intervalIntegral.continuousOn_primitive_interval'
    (CosMomentAux.intervalIntegrable_cos_mul_rpow (x + 1) (by simp at hx; linarith))
    (left_mem_uIcc (a := (0 : ℝ)) (b := x + 1))
  have hx' : x ∈ uIcc 0 (x + 1) := by
    rw [uIcc_of_le (by simp at hx; linarith)]; exact ⟨hx, by linarith⟩
  refine (h x hx').mono_of_mem_nhdsWithin ?_
  rw [uIcc_of_le (by simp at hx; linarith)]
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- A convergent `cosMomentPartial` is bounded on `[0, ∞)`. -/
theorem exists_cosMomentPartial_bound (hcm : Tendsto cosMomentPartial atTop (𝓝 cosMoment)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, 0 ≤ x → |cosMomentPartial x| ≤ C := by
  have hev : ∀ᶠ x in atTop, |cosMomentPartial x| ≤ |cosMoment| + 1 := by
    have := (continuous_abs.tendsto _).comp hcm
    exact this.eventually (eventually_le_nhds (by linarith : |cosMoment| < |cosMoment| + 1))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_cosMomentPartial.mono (fun y (hy : y ∈ Icc 0 (max T 0)) => hy.1))
  refine ⟨max C₁ (|cosMoment| + 1), le_max_of_le_right (by positivity), fun x hx => ?_⟩
  rcases le_total x (max T 0) with h | h
  · exact (by simpa using hC₁ x ⟨hx, h⟩ : |cosMomentPartial x| ≤ C₁).trans (le_max_left _ _)
  · exact (hT x ((le_max_left _ _).trans h)).trans (le_max_right _ _)

theorem cos_mul_abs (x g : ℝ) : Real.cos (x * |g|) = Real.cos (x * g) := by
  rcases abs_choice g with h | h <;> rw [h]
  rw [mul_neg, Real.cos_neg]

theorem rpow_two_thirds {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) :
    (R ^ 3 * a) ^ ((2 : ℝ) / 3) = R ^ 2 * a ^ ((2 : ℝ) / 3) := by
  rw [Real.mul_rpow (by positivity) ha, ← Real.rpow_natCast R 3, ← Real.rpow_mul hR.le]
  norm_num

/-- The substitution `r = Rρ` in the inner radial integral. -/
theorem inner_rescale (χ : ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ × ℝ) (K₀ : ℝ) {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ∫ r in (0 : ℝ)..(2 * K₀ * R),
        Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r =
      R ^ 2 * ∫ ρ in (0 : ℝ)..(2 * K₀),
        Real.cos (R ^ 3 * |circleCubic q θ| * ρ ^ 3) * psi χ θ ρ * ρ := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * K₀)
    (fun r => Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r)
    hR.ne'
  rw [mul_zero, mul_comm R] at h
  rw [smul_eq_mul] at h
  rw [eq_inv_mul_iff_mul_eq₀ hR.ne'] at h
  rw [← h, pow_two, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have e1 : R⁻¹ • (R * x * Real.cos θ, R * x * Real.sin θ) = (x * Real.cos θ, x * Real.sin θ) := by
    simp only [Prod.smul_mk, smul_eq_mul]; congr 1 <;> field_simp
  have e2 : (R * x) ^ 3 * circleCubic q θ = R ^ 3 * x ^ 3 * circleCubic q θ := by ring
  simp only [e1, e2, psi]
  rw [show R ^ 3 * |circleCubic q θ| * x ^ 3 = R ^ 3 * x ^ 3 * |circleCubic q θ| by ring, cos_mul_abs]
  ring

/-- The angular-radial factorisation: inner integral `= |g|^{-2/3} · J`. -/
theorem inner_eq (hA : RadialIdentityFacts) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1) (q : ℝ × ℝ × ℝ × ℝ) {K₀ : ℝ} (hK₀ : 1 ≤ K₀)
    (hv : ∀ z, K₀ ≤ ‖z‖ → χ z = 0) {R : ℝ} (hR : 0 < R) {θ : ℝ} (hg : circleCubic q θ ≠ 0) :
    ∫ r in (0 : ℝ)..(2 * K₀ * R),
        Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r =
      |circleCubic q θ| ^ (-(2 : ℝ) / 3) * (-(1 / 3) * ∫ ρ in (1 : ℝ)..(2 * K₀),
        deriv (psi χ θ) ρ * cosMomentPartial (R ^ 3 * |circleCubic q θ| * ρ ^ 3)) := by
  have hga : 0 < |circleCubic q θ| := abs_pos.2 hg
  have hE := hA (psi χ θ) (contDiff_psi hχ θ) (2 * K₀) (by linarith) (psi_eq_one h1 θ)
    (psi_eq_zero hv θ) (R ^ 3 * |circleCubic q θ|) (by positivity)
  rw [inner_rescale χ q K₀ hR θ, ← hE, rpow_two_thirds hR hga.le, neg_div,
    Real.rpow_neg hga.le, ← mul_assoc, ← mul_assoc, mul_comm _ (R ^ 2), mul_assoc (R ^ 2),
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hga _).ne', mul_one]

theorem pos_of_mem_uIoc {K ρ : ℝ} (hK : 1 ≤ K) (hρ : ρ ∈ uIoc 1 K) : 0 < ρ := by
  rw [uIoc_of_le hK] at hρ; linarith [hρ.1]

/-- The θ-uniform bound on the radial factor `J`. -/
theorem abs_J_le {ψ : ℝ → ℝ} {B : ℝ} (hB : ∀ ρ, |deriv ψ ρ| ≤ B) {Cp : ℝ}
    (hCp : ∀ x, 0 ≤ x → |cosMomentPartial x| ≤ Cp) {K : ℝ} (hK : 1 ≤ K) {R a : ℝ} (hR : 0 ≤ R)
    (ha : 0 ≤ a) :
    |-(1 / 3) * ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (R ^ 3 * a * ρ ^ 3)| ≤
      1 / 3 * (B * Cp * |K - 1|) := by
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
  gcongr
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun ρ hρ => ?_
  have := pos_of_mem_uIoc hK hρ
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (hB ρ) (hCp _ (by positivity)) (abs_nonneg _) ((abs_nonneg _).trans (hB ρ))

/-- The radial factor tends to `cosMoment / 3` (dominated convergence in `ρ`, then FTC). -/
theorem tendsto_J {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {B : ℝ} (hB : ∀ ρ, |deriv ψ ρ| ≤ B) {Cp : ℝ}
    (hCp : ∀ x, 0 ≤ x → |cosMomentPartial x| ≤ Cp) (hcm : Tendsto cosMomentPartial atTop (𝓝 cosMoment))
    {K : ℝ} (hK : 1 ≤ K) (hψ1 : ψ 1 = 1) (hψK : ψ K = 0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R => -(1 / 3) * ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (R ^ 3 * a * ρ ^ 3))
      atTop (𝓝 (cosMoment / 3)) := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hlim : Tendsto (fun R => ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMomentPartial (R ^ 3 * a * ρ ^ 3))
      atTop (𝓝 (∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMoment)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B * Cp) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [eventually_ge_atTop 0] with R hR
      refine ContinuousOn.aestronglyMeasurable (hd.continuousOn.mul
        (continuousOn_cosMomentPartial.comp (by fun_prop) fun ρ hρ => ?_)) measurableSet_uIoc
      have := pos_of_mem_uIoc hK hρ
      exact mem_Ici.2 (by positivity)
    · filter_upwards [eventually_ge_atTop 0] with R hR
      refine Eventually.of_forall fun ρ hρ => ?_
      have := pos_of_mem_uIoc hK hρ
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hB ρ) (hCp _ (by positivity)) (abs_nonneg _) ((abs_nonneg _).trans (hB ρ))
    · refine Eventually.of_forall fun ρ hρ => ?_
      have := pos_of_mem_uIoc hK hρ
      have ht : Tendsto (fun R : ℝ => R ^ 3 * a * ρ ^ 3) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).atTop_mul_const
          (by positivity : 0 < a * ρ ^ 3)).congr fun R => by ring
      exact (hcm.comp ht).const_mul _
  have hF : ∫ ρ in (1 : ℝ)..K, deriv ψ ρ * cosMoment = -cosMoment := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hψ.differentiable one_ne_zero) x) (hd.intervalIntegrable _ _), hψ1, hψK]
    ring
  rw [hF] at hlim
  convert hlim.const_mul (-(1 / 3)) using 2
  ring

/-- The inner radial integral is continuous in `θ`. -/
theorem continuous_inner {χ : ℝ × ℝ → ℝ} (hχ : Continuous χ) (q : ℝ × ℝ × ℝ × ℝ) (b R : ℝ) :
    Continuous fun θ => ∫ r in (0 : ℝ)..b,
      Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r := by
  have := continuous_circleCubic q
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _

theorem periodic_abs_rpow (q : ℝ × ℝ × ℝ × ℝ) :
    Function.Periodic (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) (2 * Real.pi) := fun θ => by
  simp [circleCubic, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The limit, written over `(-π, π)`, is `d4Constant q` (periodic shift). -/
theorem d4Constant_eq (q : ℝ × ℝ × ℝ × ℝ) :
    d4Constant q = ∫ θ in (-Real.pi)..Real.pi, |circleCubic q θ| ^ (-(2 : ℝ) / 3) * (cosMoment / 3) := by
  have h := (periodic_abs_rpow q).intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h
  rw [intervalIntegral.integral_mul_const, h, d4Constant, angularMoment]
  simp only [circleCubic]
  ring

/-- Dominated convergence in `θ` for the iterated polar integral. -/
theorem tendsto_angular (hA : RadialIdentityFacts) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h1 : ∀ z, ‖z‖ ≤ 1 → χ z = 1) (q : ℝ × ℝ × ℝ × ℝ) {K₀ : ℝ} (hK₀ : 1 ≤ K₀)
    (hv : ∀ z, K₀ ≤ ‖z‖ → χ z = 0) {B : ℝ} (hBd : ∀ θ ρ, |deriv (psi χ θ) ρ| ≤ B) {Cp : ℝ}
    (hCp : ∀ x, 0 ≤ x → |cosMomentPartial x| ≤ Cp) (hcm : Tendsto cosMomentPartial atTop (𝓝 cosMoment))
    (hnull : volume {θ : ℝ | circleCubic q θ = 0} = 0)
    (hint : IntervalIntegrable (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3)) volume 0 (2 * Real.pi)) :
    Tendsto (fun R : ℝ => ∫ θ in (-Real.pi)..Real.pi, ∫ r in (0 : ℝ)..(2 * K₀ * R),
        Real.cos (r ^ 3 * circleCubic q θ) * χ (R⁻¹ • (r * Real.cos θ, r * Real.sin θ)) * r)
      atTop (𝓝 (d4Constant q)) := by
  have hint' := (periodic_abs_rpow q).intervalIntegrable₀ (by positivity) hint (-Real.pi) Real.pi
  have hae : ∀ᵐ θ ∂volume, θ ∉ {θ : ℝ | circleCubic q θ = 0} := measure_eq_zero_iff_ae_notMem.1 hnull
  rw [d4Constant_eq]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => |circleCubic q θ| ^ (-(2 : ℝ) / 3) * (1 / 3 * (B * Cp * |2 * K₀ - 1|))) ?_ ?_
    (hint'.mul_const _) ?_
  · exact Eventually.of_forall fun R => (continuous_inner hχ.continuous q _ R).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with R hR
    filter_upwards [hae] with θ hθ _
    rw [inner_eq hA hχ h1 q hK₀ hv hR hθ, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    gcongr
    exact abs_J_le (hBd θ) hCp (by linarith) hR.le (abs_nonneg _)
  · filter_upwards [hae] with θ hθ _
    refine ((tendsto_J (contDiff_psi hχ θ) (hBd θ) hCp hcm (by linarith : (1 : ℝ) ≤ 2 * K₀)
      (psi_eq_one h1 θ 1 ⟨zero_le_one, le_rfl⟩) (psi_eq_zero hv θ _ le_rfl)
      (abs_pos.2 hθ)).const_mul _).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (inner_eq hA hχ h1 q hK₀ hv hR hθ).symm

end OscInt.D4.PolarLimitAux

namespace OscInt.D4
open Set MeasureTheory Filter Topology OscInt.Statements OscInt.Blueprint

/-- **E1c** The zeros of the cubic on the circle form a null set. -/
theorem circleZerosNull : CircleZerosNullFacts := fun q hq =>
  ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (PolarLimitAux.isDiscrete_zeros q hq)).measure_zero _


/-- **E1d** E1 from E1a–E1c. -/
theorem cubicCutoffLimit_of : CubicCutoffLimitCombineFacts := by
  intro hA hB hC q hq hcm hint χ hχ hcs heven h1
  obtain ⟨K₀, hK₀, hv⟩ := PolarLimitAux.exists_vanish_radius hcs
  obtain ⟨B, -, hBd⟩ := PolarLimitAux.exists_deriv_psi_bound hχ hcs
  obtain ⟨Cp, -, hCp⟩ := PolarLimitAux.exists_cosMomentPartial_bound hcm
  have hreal := PolarLimitAux.tendsto_angular hA hχ h1 q hK₀ hv hBd hCp hcm (hC q hq) hint
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (hB q χ hχ.continuous heven K₀ (by linarith) hv R hR).symm

end OscInt.D4
