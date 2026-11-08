import OscInt.Statements.Global
import OscInt.Front.ConvertSanity

/-! # Sanity theorems through the batch-GD statement constants

Every theorem below about a frozen statement of `OscInt/Statements/Global.lean` takes that statement constant as its
only statement hypothesis, discharges all of the constant's hypotheses on explicit, closed data, and concludes the
constant's conclusion on those data (lessons 33; the conditions of the step-5 rule referee, F.1 (b)). Planted copies:
`docs/replay/plants/2026-11-08-GD/` with compiler output. Structural limit: such a theorem detects a plant that makes a
hypothesis harder to discharge or the conclusion weaker; a plant that weakens a hypothesis or strengthens the
conclusion is not detected, and rests on the blind fidelity reviews.

Data (generic where the statement has roles to separate, lessons 17):
* `E = x³ − 3xy²` (elliptic umbilic, `disc = 108 > 0`): its only degenerate point is `0`, a D4 point; on
  `K = B̄(0, 1)` with `D = {0}` it is classified (nondegenerate off `0`). Used for GD and GD-C.
* `F = x³ + y²`: fold on `x = 0`, nondegenerate elsewhere, no D4 point (GD-F).
* `Q = x² + 3xy + 5y²`: nondegenerate everywhere, `det H = 11` (GD-N).
* The lattice kernel at `t = 0`: `K(0, 0) = (2π)²`, `K(0, (1, 0)) = 0` (pins the box and the sign/scale of `x·k`).
-/

namespace OscInt.API.GlobalSanity

open OscInt.Statements OscInt.D4 OscInt.API.ConvertSanity Filter Topology

/-! ## The elliptic umbilic `x³ − 3xy²` -/

/-- `E = x³ − 3xy²`. -/
noncomputable def ellPhase : ℝ × ℝ → ℝ := genCubic 1 0 (-3) 0

theorem ellPhase_contDiff : ContDiff ℝ 4 ellPhase := genCubic_contDiff 1 0 (-3) 0

theorem hessian_ell (k : ℝ × ℝ) :
    hessianMatrix ellPhase k = !![6 * k.1, -6 * k.2; -6 * k.2, -6 * k.1] := by
  unfold ellPhase
  have h := iteratedFDeriv_two_eq_dd (f := genCubic 1 0 (-3) 0) ((genCubic_contDiff 1 0 (-3) 0).of_le (by norm_num)) k
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, dd_genCubic, coordVec] <;> ring_nf <;> simp

theorem det_hessian_ell (k : ℝ × ℝ) : (hessianMatrix ellPhase k).det = -36 * (k.1 ^ 2 + k.2 ^ 2) := by
  rw [hessian_ell, Matrix.det_fin_two]; simp; ring

/-- Off the origin `E` is nondegenerate. -/
theorem ell_nondeg (k : ℝ × ℝ) (hk : k ≠ 0) : (hessianMatrix ellPhase k).det ≠ 0 := by
  rw [det_hessian_ell]
  have : 0 < k.1 ^ 2 + k.2 ^ 2 := by
    rcases k with ⟨x, y⟩
    have : x ≠ 0 ∨ y ≠ 0 := by
      by_contra h; simp only [not_or, not_not] at h; exact hk (Prod.ext h.1 h.2)
    rcases this with h | h
    · have := pow_pos (abs_pos.mpr h) 2; simp only [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.mpr h) 2; simp only [sq_abs] at this; positivity
  linarith

/-- The origin is a D4 point of `E` (cubic part `x³ − 3xy²`, `discr = 108`). -/
theorem ell_isD4 : IsD4Point ellPhase 0 := by
  obtain ⟨-, h2, h3, hd⟩ := d4FE_hyps_elliptic
  exact ⟨h2, 1, 0, -3, 0, h3, hd⟩

/-- Bite: `E` is not fold-or-nondegenerate at the origin (zero Hessian). -/
theorem not_foldOrNondegMatrix_ell_zero : ¬ FoldOrNondegMatrix ellPhase 0 := by
  unfold FoldOrNondegMatrix FoldCondSpan
  have hH : hessianMatrix ellPhase 0 = 0 := by
    rw [hessian_ell]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hH]
  rintro (h | ⟨e, he, hker, -⟩)
  · simp at h
  · have h1 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ LinearMap.ker (Matrix.toLin' (0 : Matrix (Fin 2) (Fin 2) ℝ)) := by simp
    have h2 : (Pi.single 1 1 : Fin 2 → ℝ) ∈ LinearMap.ker (Matrix.toLin' (0 : Matrix (Fin 2) (Fin 2) ℝ)) := by simp
    rw [hker, Submodule.mem_span_singleton] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have ha0 := congrFun ha 0; have ha1 := congrFun ha 1
    have hb0 := congrFun hb 0; have hb1 := congrFun hb 1
    simp at ha0 ha1 hb0 hb1
    -- a e₀ = 1, a e₁ = 0, b e₀ = 0, b e₁ = 1: then a ≠ 0, so e₁ = 0, contradicting b e₁ = 1
    have : e 1 = 0 := by
      rcases ha1 with h | h
      · rw [h, zero_mul] at ha0; exact absurd ha0 (by norm_num)
      · exact h
    rw [this, mul_zero] at hb1; exact absurd hb1 (by norm_num)

theorem ell_classified : Classified ellPhase (Metric.closedBall 0 1) {0} :=
  ⟨fun k _ hk => Or.inl (ell_nondeg k (by simpa using hk)), fun k₀ hk₀ => by
    rw [Finset.mem_singleton] at hk₀; subst hk₀; exact ell_isD4⟩

/-- **GD through the statement constant.** `Ψ = E`, `K = B̄(0, 1)`, `U = ℝ²`, `D = {0}`; all linear terms.
Plants this detects (planted copies recorded): the exception `k ∉ D` dropped (then `0 ∈ K` must be fold-or-nondegenerate,
false by `not_foldOrNondegMatrix_ell_zero`); `discr ≠ 0` strengthened to `discr < 0` (`E` has `discr = 108`); the rate
weakened (`-(2/3) ↦ -(1/2)`). Not detected: weakening plants (a dropped `↑D ⊆ U`, `C⁴ ↦ C³`). -/
theorem globalDecay_ell (h : GlobalDecayStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (ellPhase k + L k)) * Complex.I) * A k‖ ≤
        C * M * m ^ (-(2 : ℝ) / 3) :=
  h ellPhase (Metric.closedBall 0 1) Set.univ {0} (isCompact_closedBall _ _) isOpen_univ (Set.subset_univ _)
    (Set.subset_univ _) ellPhase_contDiff.contDiffOn ell_classified

/-- `L₁ = 3·fst`: the critical points of `E + L₁` are `(±1/√… )`-free: `3x² − 3y² + 3 = 0`, `xy = 0` forces `x = 0`,
`y = ±1`, both nondegenerate. -/
noncomputable def L₁ : (ℝ × ℝ) →L[ℝ] ℝ := (3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- **GD-C through the statement constant.** `Ψ = E`, `K = B̄(0, 1)`, `U = ℝ²`, `K′ = {0, L₁}`, `D = {0}`. Plants
detected: `k ∉ D` dropped (with `L = 0` the origin is a critical point in `K`, not fold-or-nondegenerate); the rate
weakened. Not detected: weakening plants (`∀ L ∈ K′ ↦ ∀ L`, which the data satisfy as well). -/
theorem globalDecayCrit_ell (h : GlobalDecayCritStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ ({0, L₁} : Set ((ℝ × ℝ) →L[ℝ] ℝ)) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (ellPhase k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3) :=
  h ellPhase (Metric.closedBall 0 1) Set.univ {0, L₁} {0} (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (Set.subset_univ _) ((Set.finite_singleton _).insert _).isCompact
    ellPhase_contDiff.contDiffOn
    ⟨fun _ _ k _ hk _ => Or.inl (ell_nondeg k (by simpa using hk)), ell_classified.2⟩

/-! ## GD-F: the fold `x³ + y²` -/

/-- `F = x³ + y²`. -/
def foldPhase (k : ℝ × ℝ) : ℝ := k.1 ^ 3 + k.2 ^ 2

/-- `Q = x² + 3xy + 5y²`. -/
def quadPhase (k : ℝ × ℝ) : ℝ := k.1 ^ 2 + 3 * k.1 * k.2 + 5 * k.2 ^ 2

/-- **GD-F through the statement constant.** `Ψ = x³ + y²` (a fold along `x = 0`), `K = B̄(0, 1)`, `U = ℝ²`, all
linear terms. Plants detected: `FoldOrNondegMatrix ↦ det ≠ 0` (fails on `x = 0`, `hessian_fold`); the rate weakened.
Not detected: weakening plants. -/
theorem globalFold_fold (h : GlobalFoldStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (foldPhase k + L k)) * Complex.I) * A k‖ ≤
        C * M * m ^ (-(5 : ℝ) / 6) :=
  h foldPhase (Metric.closedBall 0 1) Set.univ (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (by unfold foldPhase; fun_prop) (fun k _ => foldOrNondegMatrix_fold k)

/-- The data of `globalFold_fold` violate the strengthened (planted) hypothesis `det ≠ 0` at the origin. -/
theorem fold_det_zero : (hessianMatrix foldPhase 0).det = 0 := by
  unfold foldPhase; rw [hessian_fold, Matrix.det_fin_two]; simp

/-! ## GD-N: the quadratic `x² + 3xy + 5y²` -/

/-- **GD-N through the statement constant.** `Ψ = x² + 3xy + 5y²` (`det H = 11`, mixed term nonzero), `K = B̄(0, 1)`,
`U = B(0, 2)` (open, `≠ ℝ²`), all linear terms. Plants detected: `K ⊆ U` reversed (`B(0, 2) ⊄ B̄(0, 1)`); the
rate weakened (`/ m ↦ / m ^ (1/2)`). Not detected: weakening plants. -/
theorem globalNondeg_quad (h : GlobalNondegStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (quadPhase k + L k)) * Complex.I) * A k‖ ≤ C * M / m :=
  h quadPhase (Metric.closedBall 0 1) (Metric.ball 0 2)
    (isCompact_closedBall _ _) Metric.isOpen_ball (Metric.closedBall_subset_ball (by norm_num))
    (by unfold quadPhase; fun_prop : ContDiff ℝ 4 quadPhase).contDiffOn
    (fun k _ => by unfold quadPhase; rw [(hessian_mixed k).2]; norm_num)

/-! ## SH: the sharpness lemma on `m^{-1/2}` -/

/-- **SH through the statement constant.** `I(m) = m^{-1/2}` satisfies `m^{1/2} I(m) → 1`, so SH gives the lower bound
`m^{-1/2}/2 ≤ |I(m)|` eventually and excludes the rate `m^{-1}`. Plants detected: `c ≠ 0 ↦ c = 0`-type strengthenings of
the hypothesis (the data have `c = 1`); the lower bound weakened in form (`‖c‖ / 2 ↦ ‖c‖ / 4` is a weakening of the
conclusion and is detected because the conclusion below has `1 / 2`). -/
theorem sharpness_sqrt (h : SharpnessStatement) :
    (∀ᶠ m : ℝ in atTop, 1 / 2 * m ^ (-(1 / 2 : ℝ)) ≤ ‖((m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖) ∧
      ¬ ∃ C : ℝ, ∀ᶠ m : ℝ in atTop, ‖((m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ C * m ^ (-(1 : ℝ)) := by
  have ht : Tendsto (fun m : ℝ => ((m ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    rw [← Complex.ofReal_mul, ← Real.rpow_add hm]; norm_num
  obtain ⟨h1, h2⟩ := h.1 _ _ _ ht one_ne_zero
  refine ⟨by simpa using h1, fun hC => h2 1 (by norm_num) ?_⟩
  simpa using hC

/-! ## T1 and the lattice kernel: the box, the period and the linear term -/

theorem volume_torusBox : MeasureTheory.volume torusBox = ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
  rw [torusBox, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith [Real.pi_pos])]
  congr 1; ring

theorem integral_one_torusBox : ∫ _ in torusBox, (1 : ℂ) = ((2 * Real.pi) ^ 2 : ℝ) := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, volume_torusBox,
    ENNReal.toReal_ofReal (by positivity)]
  simp

/-- `∫_{[−π, π]} e^{i n s} ds = 0` for an integer `n ≠ 0`. -/
theorem integral_exp_int_mul (n : ℤ) (hn : n ≠ 0) :
    ∫ s in (-Real.pi)..Real.pi, Complex.exp (↑((n : ℝ) * s) * Complex.I) = 0 := by
  have hc : ((n : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
  have : (fun s : ℝ => Complex.exp (↑((n : ℝ) * s) * Complex.I)) =
      fun s : ℝ => Complex.exp (((n : ℂ) * Complex.I) * s) := by
    funext s; congr 1; push_cast; ring
  rw [this, integral_exp_mul_complex hc]
  have h1 : Complex.exp ((n : ℂ) * Complex.I * Real.pi) = Complex.exp ((n : ℂ) * Complex.I * (-Real.pi : ℝ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨n, by push_cast; ring⟩
  rw [h1, sub_self, zero_div]

/-- `K(0, (0, 0)) = (2π)²`: the box has area `(2π)²`. -/
theorem latticeKernel_zero_zero : latticeKernel 0 (0, 0) = ((2 * Real.pi) ^ 2 : ℝ) := by
  rw [← integral_one_torusBox, latticeKernel]
  congr 1; funext k; simp

/-- `K(0, (1, 0)) = 0`: the linear term is `x·k` with integer `x`, and the box is a full period. -/
theorem latticeKernel_zero_one : latticeKernel 0 (1, 0) = 0 := by
  have hint : MeasureTheory.IntegrableOn (fun k : ℝ × ℝ => Complex.exp (↑(k.1) * Complex.I)) torusBox := by
    exact (by fun_prop : Continuous fun k : ℝ × ℝ => Complex.exp (↑(k.1) * Complex.I)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [latticeKernel, torusBox, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod _ (by simpa [torusBox, MeasureTheory.Measure.volume_eq_prod] using hint)]
  have h0 := integral_exp_int_mul 1 one_ne_zero
  simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero, zero_add] at h0 ⊢
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp only [MeasureTheory.setIntegral_const]
  rw [intervalIntegral.integral_smul, h0, smul_zero]

/-- **T1 through the statement constant.** With `g = 1`: `∫ η = (2π)²`; with `g = e^{ik₁}`: `∫ η e^{ik₁} = 0`.
Plants detected: the period `2π ↦ π` (then `e^{ik₁}` is not admissible: `e^{i(k₁ + π)} = −e^{ik₁}`, so the discharge of
the period hypothesis fails); `torusBox ↦ [0, π]²` is detected by `integral_one_torusBox` only through the constant
`(2π)²` in the conclusion. Not detected: weakening plants (e.g. `Continuous g` dropped). -/
theorem torusUnfold_moments (h : TorusUnfoldStatement) :
    ∃ η : ℝ × ℝ → ℝ, ∫ k : ℝ × ℝ, (η k : ℂ) * 1 = ((2 * Real.pi) ^ 2 : ℝ) ∧
      ∫ k : ℝ × ℝ, (η k : ℂ) * Complex.exp (↑(k.1) * Complex.I) = 0 := by
  obtain ⟨η, -, -, hη⟩ := h
  refine ⟨η, ?_, ?_⟩
  · rw [← hη (fun _ => 1) continuous_const (fun _ => rfl) (fun _ => rfl), integral_one_torusBox]
  · have h0 := latticeKernel_zero_one
    rw [latticeKernel] at h0
    simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero, zero_add] at h0
    rw [← hη (fun k : ℝ × ℝ => Complex.exp (↑(k.1) * Complex.I)) (by fun_prop) (fun k => ?_) (fun _ => rfl), h0]
    have : Complex.exp (↑(k.1 + 2 * Real.pi) * Complex.I) = Complex.exp (↑k.1 * Complex.I) * 1 := by
      rw [← Complex.exp_two_pi_mul_I, ← Complex.exp_add]; congr 1; push_cast; ring
    simpa using this

/-- **T6 through the statement constant**, on the diagonal `x = (n, n)` at time `n ≥ 1` (where T6L shows the rate is
attained). Plants detected: the rate weakened (`-(2/3) ↦ -(1/2)`); the uniformity over `x` restricted (e.g. `x = 0`
only). Not detected: a strengthened rate (false by T6L and SH, `latticeLaplacian_sharp`, but not a discharge failure). -/
theorem latticeLaplacianDecay_diag (h : LatticeLaplacianDecayStatement) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖latticeKernel n ((n : ℤ), (n : ℤ))‖ ≤ C * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun n hn => hC n _ (by exact_mod_cast hn)⟩

/-! ## T6, T6L and SH together: the rate `t^{-2/3}` cannot be improved -/

theorem d4ClosedConstant_lattice_pos : 0 < d4ClosedConstant (-1 / 48) := by
  unfold d4ClosedConstant
  rw [if_pos (by norm_num : (-1 / 48 : ℝ) < 0)]
  have hg : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

/-- **T6L and SH through the constants.** If the diagonal limit holds, no bound `C t^{-3/4}` uniform in `x` holds:
T6's rate is sharp. Plants detected: in T6L, a limit `0` (the constant `0` instead of `d4ClosedConstant (−1/48)`)
would make `c ≠ 0` fail. Not detected: a different nonzero constant (the pre-registered numeric check is the only
test of its value, `numerics/results-classify-2026-11-08.txt`, part B). -/
theorem latticeLaplacian_sharp (hS : SharpnessStatement) (hL : LatticeLaplacianLimitStatement) :
    ¬ ∃ C : ℝ, ∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t → ‖latticeKernel t x‖ ≤ C * t ^ (-(3 : ℝ) / 4) := by
  rintro ⟨C, hC⟩
  have hL' : Tendsto (fun n : ℕ => (((n : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ n * latticeKernel n ((n : ℤ), (n : ℤ)))) atTop (𝓝 (d4ClosedConstant (-1 / 48) : ℂ)) := by
    unfold LatticeLaplacianLimitStatement at hL
    simpa only [mul_assoc] using hL
  obtain ⟨-, h2⟩ := hS.2 _ _ _ hL' (by exact_mod_cast d4ClosedConstant_lattice_pos.ne')
  refine h2 (3 / 4) (by norm_num) ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := hC n ((n : ℤ), (n : ℤ)) (by exact_mod_cast hn)
  convert this using 2; norm_num

end OscInt.API.GlobalSanity
