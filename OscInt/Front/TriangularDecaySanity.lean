/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.TriangularDecay
import OscInt.Front.TriangularAnisoSanity

/-! # Sanity theorems for batch K2 (K2-L, K2-MA, K2-ML, K2-F, K2-U, K2-D)

Draft, written before the statements are stamped; no proof of a batch-K2 statement exists in this file or is used
by it, and no statement is derived from another. Two forms (`docs/lessons.md`, rules 8 and 9).

A. Unconditional, on closed data, through the definitions of `OscInt/Statements/TriangularDecay.lean`:
* `triKernel`: `triKernel 0 = latticeKernel` (`triKernel_zero`); `triKernel α 0 (0, 0) = (2π)²` for every `α`
  (`triKernel_time_zero`); `‖triKernel α t n‖ ≤ (2π)²` (`norm_triKernel_le`).
* `triRate`: `2/3` at `0`, `a*`, `−a*`; `3/4` at `1/4`, `1`, `−2` and at every `α ∉ {0, ±a*}` (`triRate_generic`).
* `PlateauCutoff`: satisfied by `plat r R = smoothTransition ((R² − x²)/(R² − r²))` for every `0 < r < R`
  (`plat_plateau`); bites: the constant `1` fails only compact support, the shifted `plat 1 2 (· − 1/4)` with
  `r = 1/2` fails only evenness.
* K2-L's hypotheses: on `x^m + y²/2` at `0` (`v = (1, 0)`, `w = (0, 1)`, `h = 0`, reduced `m`-th derivative `m!`) for
  every `m ≥ 2` (`modelL_hyps`); on the sheared `y²/2 + y x² + x⁴` with the genuine curve `h(u) = −u²` (reduced
  fourth derivative `12`, straight-line fourth derivative along `v` equal to `24`, `D²[v, v] = 0`); bites: `x⁶ + y²/2`
  at order `4` (reduced fourth derivative `0`); for the spanning condition, `v = w = (0, 1)`, where the reduced
  function is identically `0` (`modelL_parallel`); in general the spanning condition is implied by the other
  hypotheses (`span_of_hyps`), so no datum fails it alone.
* The bite of `D²Ψ(k₀)[w, w] ≠ 0`: `x²` at `0` satisfies every other hypothesis of K2-L at `m = 2`
  (`modelX_hyps`); its integral against `b(κ₁) b(κ₂)` factorises (`oscInt2_modelX_prodAmp`).
* K2-F's hypotheses: `χ₁` (a `ContDiffBump` at `0` of outer radius `1`); bites: `χ_π` (outer radius `π`, support
  closure reaching `(π, 0)`) and the constant `1`. The lattice coefficients of the zero phase vanish off `n = 0`
  (`lattice_coeff_zero_phase`); `∫_{[−π, π]²} χ₁ ≠ 0`; `triPhase α` is continuous and biperiodic.
* Bites of hypotheses, exact: K2-ML's threshold (`ml_threshold_bite`, `t = 1/200²`), K2-MA's `0 < t`
  (`ma_time_zero_bite`), K2-U's `1 ≤ t` (`u_time_zero_bite`, at `t = 0`).
* Helpers: `rate_separation` (two rates separate), `integral_plat_ge`, `norm_integral_plat_le`, real powers.

B. Conditional, each statement constant as the only statement hypothesis (consistency theorems use two): K2-U at
`α = 0` (gives batch GD's `LatticeLaplacianDecayStatement`), `±a*`, `1/4`, `1`, `−2` and generic `α`; K2-D at the same
`α`; K2-MA with `plat r R` for every `m ≥ 2`, `σ = ±1`, and at `m = 2, 3, 4, 6`; the bound `‖C‖ ≤ 2R + 4/(m r^{m−1})`;
K2-ML at `t = s^m` with `(s r)^{m−1} ≥ 96`, and at `m = 2, 3, 4, 6`; K2-L on the model (`m = 3, 6`, exponents `5/6`,
`2/3`) and on the sheared datum (exponent `3/4`); K2-F with `χ₁`, also at the zero phase; consistency K2-U with K2-D
(`c ≤ C`) and K2-F with K2-U (the localised `triPhase` integral at every real velocity).

Planted copies: `plants/README.md` of the scratch work directory of the sanity agent (not in the repository).
-/

namespace OscInt.API.TriangularDecaySanity

open OscInt.Statements OscInt.API.Poly OscInt.API.CuspSanity OscInt.API.TriangularAnisoSanity MeasureTheory
open scoped ContDiff Topology
open Filter

/-! ## A. The kernel -/

theorem triKernel_zero : triKernel 0 = latticeKernel := by
  funext t n
  simp only [triKernel, latticeKernel, triPhase, zero_mul, add_zero]

theorem volume_torusBox : volume torusBox = ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
  rw [torusBox, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith [Real.pi_pos])]
  congr 1; ring

theorem volume_real_torusBox : volume.real torusBox = (2 * Real.pi) ^ 2 := by
  rw [Measure.real, volume_torusBox, ENNReal.toReal_ofReal (by positivity)]

theorem triKernel_time_zero (α : ℝ) : triKernel α 0 (0, 0) = (((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
  simp only [triKernel, zero_mul, Int.cast_zero, add_zero, Complex.ofReal_zero, Complex.exp_zero]
  rw [setIntegral_const, volume_real_torusBox]
  simp

theorem norm_triKernel_le (α t : ℝ) (n : ℤ × ℤ) : ‖triKernel α t n‖ ≤ (2 * Real.pi) ^ 2 := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := torusBox) (C := 1)
    (f := fun k : ℝ × ℝ => Complex.exp (↑(t * triPhase α k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I))
    (by rw [volume_torusBox]; exact ENNReal.ofReal_lt_top) (fun k _ => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [volume_real_torusBox, one_mul] at h
  exact h

/-! ## A. The exponent -/

theorem quarter_ne_exceptional : (1 / 4 : ℝ) ≠ triExceptional := by
  intro h
  have := triExceptional_sq
  rw [← h] at this
  norm_num at this

theorem triRate_zero : triRate 0 = 2 / 3 := by simp [triRate]

theorem triRate_exceptional : triRate triExceptional = 2 / 3 := by
  simp [triRate, abs_of_pos triExceptional_pos]

theorem triRate_neg_exceptional : triRate (-triExceptional) = 2 / 3 := by
  simp [triRate, abs_neg, abs_of_pos triExceptional_pos]

/-- Off the exceptional set the exponent is `3/4`. -/
theorem triRate_generic (α : ℝ) (h0 : α ≠ 0) (h1 : |α| ≠ triExceptional) : triRate α = 3 / 4 := by
  unfold triRate
  split_ifs with h
  · rcases h with h | h
    · exact absurd h h0
    · exact absurd h h1
  · rfl

theorem triRate_quarter : triRate (1 / 4) = 3 / 4 :=
  triRate_generic _ (by norm_num) (by rw [abs_of_pos (by norm_num)]; exact quarter_ne_exceptional)

theorem triRate_one : triRate 1 = 3 / 4 :=
  triRate_generic _ one_ne_zero (by rw [abs_one]; linarith [triExceptional_lt_half])

theorem triRate_neg_two : triRate (-2) = 3 / 4 :=
  triRate_generic _ (by norm_num) (by rw [abs_of_neg (by norm_num)]; linarith [triExceptional_lt_half])

/-- The two values of the exponent. -/
theorem triRate_cases (α : ℝ) : triRate α = 2 / 3 ∨ triRate α = 3 / 4 := by
  unfold triRate; split_ifs <;> simp

/-! ## A. Plateau cutoffs -/

/-- `plat r R x = smoothTransition ((R² − x²)/(R² − r²))`: `1` on `[−r, r]`, `0` off `(−R, R)`. -/
noncomputable def plat (r R : ℝ) (x : ℝ) : ℝ := Real.smoothTransition ((R ^ 2 - x ^ 2) / (R ^ 2 - r ^ 2))

theorem plat_contDiff (r R : ℝ) : ContDiff ℝ ∞ (plat r R) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem plat_contDiff_one (r R : ℝ) : ContDiff ℝ 1 (plat r R) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem plat_nonneg (r R x : ℝ) : 0 ≤ plat r R x := Real.smoothTransition.nonneg _

theorem plat_le_one (r R x : ℝ) : plat r R x ≤ 1 := Real.smoothTransition.le_one _

theorem plat_eq_one {r R x : ℝ} (hrR : r < R) (hx : |x| ≤ r) : plat r R x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hr : 0 ≤ r := (abs_nonneg x).trans hx
  have hd : 0 < R ^ 2 - r ^ 2 := by nlinarith
  rw [one_le_div hd]
  have : x ^ 2 ≤ r ^ 2 := by
    have := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    exact this
  linarith

theorem plat_eq_zero {r R x : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hx : R ≤ |x|) : plat r R x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0 < R ^ 2 - r ^ 2 := by nlinarith
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  have hR : 0 ≤ R := hr.trans hrR.le
  have : R ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hR hx 2
  rw [sq_abs] at this
  linarith

theorem plat_even (r R x : ℝ) : plat r R (-x) = plat r R x := by simp [plat]

theorem plat_hasCompactSupport {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) : HasCompactSupport (plat r R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => plat_eq_zero hr hrR ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem plat_antitoneOn {r R : ℝ} (hrR : r < R) (hr : 0 ≤ r) : AntitoneOn (plat r R) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply Real.smoothTransition.monotone
  have hd : 0 < R ^ 2 - r ^ 2 := by nlinarith
  apply div_le_div_of_nonneg_right _ hd.le
  have hx0 : (0 : ℝ) ≤ x := hx
  nlinarith

/-- **`PlateauCutoff` is satisfiable**, for every `0 < r < R`. -/
theorem plat_plateau {r R : ℝ} (hr : 0 < r) (hrR : r < R) : PlateauCutoff (plat r R) r :=
  ⟨plat_contDiff_one r R, plat_hasCompactSupport hr.le hrR, hr, plat_even r R, fun _ hx => plat_eq_one hrR hx,
    plat_antitoneOn hrR hr.le⟩

/-- The support lies in `[−R, R]`. -/
theorem plat_eq_zero_of_notMem {r R x : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hx : x ∉ Set.Icc (-R) R) :
    plat r R x = 0 := by
  apply plat_eq_zero hr hrR
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **Bite**: the constant `1` satisfies every conjunct except compact support. -/
theorem const_one_not_plateau (r : ℝ) : ¬ PlateauCutoff (fun _ => (1 : ℝ)) r := by
  rintro ⟨-, h, -⟩
  apply noncompact_univ ℝ
  have : tsupport (fun _ : ℝ => (1 : ℝ)) = Set.univ := by
    rw [tsupport, Function.support_const one_ne_zero, closure_univ]
  rw [HasCompactSupport, this] at h
  exact h

theorem const_one_other_conjuncts (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) ∧ 0 < r ∧ (∀ x : ℝ, (fun _ : ℝ => (1 : ℝ)) (-x) = (fun _ => (1 : ℝ)) x) ∧
      (∀ x : ℝ, |x| ≤ r → (fun _ : ℝ => (1 : ℝ)) x = 1) ∧ AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici 0) :=
  ⟨contDiff_const, hr, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => le_rfl⟩

/-- **Bite**: the shifted cutoff `x ↦ plat 1 2 (x − 1/4)` with `r = 1/2` is not even. -/
theorem shifted_not_even : plat 1 2 (-1 - 1 / 4) ≠ plat 1 2 (1 - 1 / 4) := by
  rw [plat_eq_one (x := 1 - 1 / 4) (by norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)]
  apply ne_of_lt
  unfold plat
  apply Real.smoothTransition.lt_one_of_lt_one
  norm_num

theorem shifted_not_plateau : ¬ PlateauCutoff (fun x => plat 1 2 (x - 1 / 4)) (1 / 2) := by
  rintro ⟨-, -, -, h, -⟩
  exact shifted_not_even (h 1)

/-- The shifted cutoff satisfies the other conjuncts (so evenness is what fails). -/
theorem shifted_other_conjuncts :
    ContDiff ℝ 1 (fun x => plat 1 2 (x - 1 / 4)) ∧ HasCompactSupport (fun x => plat 1 2 (x - 1 / 4)) ∧
      (∀ x : ℝ, |x| ≤ 1 / 2 → plat 1 2 (x - 1 / 4) = 1) ∧
      AntitoneOn (fun x => plat 1 2 (x - 1 / 4)) (Set.Ici 0) := by
  refine ⟨(plat_contDiff_one 1 2).comp (by fun_prop), ?_, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · exact (plat_hasCompactSupport (by norm_num) (by norm_num)).comp_homeomorph (Homeomorph.subRight (1 / 4))
  · apply plat_eq_one (by norm_num)
    rw [abs_le] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  · have hx0 : (0 : ℝ) ≤ x := hx
    simp only
    by_cases hc : |x - 1 / 4| ≤ 1
    · rw [plat_eq_one (by norm_num) hc]; exact plat_le_one _ _ _
    · have h1 : 5 / 4 < x := by
        rw [not_le, abs_of_nonneg (by by_contra h; rw [abs_of_neg (by linarith)] at hc; linarith)] at hc
        linarith
      rw [← plat_even 1 2 (x - 1 / 4) |>.symm.trans (plat_even 1 2 _) |>.symm]
      exact plat_antitoneOn (by norm_num) (by norm_num) (show (0 : ℝ) ≤ x - 1 / 4 by linarith)
        (show (0 : ℝ) ≤ y - 1 / 4 by linarith) (by linarith)

/-- The `L¹` size of a plateau cutoff: `‖∫ b(x) e^{iφ(x)} dx‖ ≤ 2R` for every real phase. -/
theorem norm_integral_plat_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (φ : ℝ → ℝ) :
    ‖∫ x : ℝ, (plat r R x : ℂ) * Complex.exp (↑(φ x) * Complex.I)‖ ≤ 2 * R := by
  have hR : 0 ≤ R := hr.trans hrR.le
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-R) R)
    (fun x hx => by rw [plat_eq_zero_of_notMem hr hrR hx]; simp)]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-R) R) (C := 1)
    (f := fun x : ℝ => (plat r R x : ℂ) * Complex.exp (↑(φ x) * Complex.I))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (plat_nonneg _ _ _)]
      exact plat_le_one _ _ _)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), one_mul] at h
  linarith

/-! ## A. Data for K2-L -/

/-- The model phase `x^m + y²/2`. -/
noncomputable def modelL (m : ℕ) (k : ℝ × ℝ) : ℝ := k.1 ^ m + k.2 ^ 2 / 2

theorem modelL_contDiff (m : ℕ) : ContDiff ℝ ω (modelL m) := by unfold modelL; fun_prop

theorem modelL_hasFDerivAt (m : ℕ) (x : ℝ × ℝ) :
    HasFDerivAt (modelL m)
      ((m * x.1 ^ (m - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ + x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have h1 := (hasFDerivAt_fst (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)).pow m
  have h2 := ((hasFDerivAt_snd (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)).pow 2).mul_const (1 / 2 : ℝ)
  have := h1.add h2
  convert this using 1
  · funext k; simp only [modelL, Pi.add_apply]; ring
  · refine ContinuousLinearMap.ext fun v => ?_
    simp; ring

theorem modelL_fderiv (m : ℕ) (x w : ℝ × ℝ) :
    fderiv ℝ (modelL m) x w = m * x.1 ^ (m - 1) * w.1 + x.2 * w.2 := by
  rw [(modelL_hasFDerivAt m x).fderiv]
  simp

theorem modelL_fderiv_zero (m : ℕ) (hm : 2 ≤ m) (w : ℝ × ℝ) : fderiv ℝ (modelL m) 0 w = 0 := by
  rw [modelL_fderiv]
  simp [zero_pow (show m - 1 ≠ 0 by omega)]

theorem modelL_d2w (m : ℕ) (hm : 2 ≤ m) : iteratedFDeriv ℝ 2 (modelL m) 0 ![(0, 1), (0, 1)] = 1 := by
  rw [vec2_const, iteratedFDeriv_diag_eq ((modelL_contDiff m).of_le le_top)]
  have e : (fun t : ℝ => modelL m (0 + t • ((0 : ℝ), (1 : ℝ)))) = fun t => (1 / 2 : ℝ) * t ^ 2 := by
    funext t; simp [modelL, zero_pow (show m ≠ 0 by omega)]; ring
  rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  norm_num

theorem modelL_reducedCurve (m : ℕ) (ε : ℝ) :
    ReducedCurve (modelL m) 0 (1, 0) (0, 1) ε (fun _ => 0) := by
  refine ⟨contDiff_const, rfl, fun u _ => ?_⟩
  rw [modelL_fderiv, modelL_fderiv]
  simp

theorem modelL_reducedFn (m : ℕ) (hm : 2 ≤ m) :
    reducedFn (modelL m) 0 (1, 0) (0, 1) (fun _ => 0) = fun u => u ^ m := by
  funext u
  rw [reducedFn, modelL_fderiv_zero m hm]
  simp [modelL]

/-- The reduced `m`-th derivative of the model is `m!`. -/
theorem modelL_reduced_deriv (m : ℕ) (hm : 2 ≤ m) :
    iteratedDeriv m (reducedFn (modelL m) 0 (1, 0) (0, 1) (fun _ => 0)) 0 = m.factorial := by
  rw [modelL_reducedFn m hm, iteratedDeriv_fun_pow_zero]
  simp

/-- `(1, 0)` and `(0, 1)` span `ℝ²`. -/
theorem span_e1_e2 : ((1 : ℝ), (0 : ℝ)).1 * ((0 : ℝ), (1 : ℝ)).2 - ((1 : ℝ), (0 : ℝ)).2 * ((0 : ℝ), (1 : ℝ)).1 ≠ 0 := by
  norm_num

/-- **K2-L's hypotheses hold** on the model `x^m + y²/2` at `0` (`v = (1, 0)`, `w = (0, 1)`, `h = 0`), every `m ≥ 2`. -/
theorem modelL_hyps (m : ℕ) (hm : 2 ≤ m) :
    ContDiff ℝ ∞ (modelL m) ∧ ((1 : ℝ), (0 : ℝ)).1 * ((0 : ℝ), (1 : ℝ)).2 - ((1 : ℝ), (0 : ℝ)).2 * ((0 : ℝ), (1 : ℝ)).1 ≠ 0 ∧
      iteratedFDeriv ℝ 2 (modelL m) 0 ![(0, 1), (0, 1)] ≠ 0 ∧
      ReducedCurve (modelL m) 0 (1, 0) (0, 1) 1 (fun _ => 0) ∧
      iteratedDeriv m (reducedFn (modelL m) 0 (1, 0) (0, 1) (fun _ => 0)) 0 ≠ 0 := by
  refine ⟨(modelL_contDiff m).of_le le_top, span_e1_e2, by rw [modelL_d2w m hm]; norm_num,
    modelL_reducedCurve m 1, ?_⟩
  rw [modelL_reduced_deriv m hm]
  exact_mod_cast (Nat.factorial_pos m).ne'

/-- **Bite**: `x⁶ + y²/2` at order `4`: the reduced fourth derivative vanishes. -/
theorem modelL6_order4 : iteratedDeriv 4 (reducedFn (modelL 6) 0 (1, 0) (0, 1) (fun _ => 0)) 0 = 0 := by
  rw [modelL_reducedFn 6 (by norm_num), iteratedDeriv_fun_pow_zero]
  simp

/-- The sheared phase `y²/2 + y x² + x⁴ = (y + x²)²/2 + x⁴/2`. -/
noncomputable def shear (k : ℝ × ℝ) : ℝ := k.2 ^ 2 / 2 + k.2 * k.1 ^ 2 + k.1 ^ 4

theorem shear_contDiff : ContDiff ℝ ω shear := by unfold shear; fun_prop

theorem shear_hasFDerivAt (x : ℝ × ℝ) :
    HasFDerivAt shear
      ((2 * x.2 * x.1 + 4 * x.1 ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (x.2 + x.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hf := hasFDerivAt_fst (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)
  have hs := hasFDerivAt_snd (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)
  have := ((hs.pow 2).mul_const (1 / 2 : ℝ)).add ((hs.mul (hf.pow 2)).add (hf.pow 4))
  convert this using 1
  · funext k; simp only [shear, Pi.add_apply, Pi.mul_apply]; ring
  · refine ContinuousLinearMap.ext fun v => ?_
    simp; ring

theorem shear_fderiv (x w : ℝ × ℝ) :
    fderiv ℝ shear x w = (2 * x.2 * x.1 + 4 * x.1 ^ 3) * w.1 + (x.2 + x.1 ^ 2) * w.2 := by
  rw [(shear_hasFDerivAt x).fderiv]
  simp

theorem shear_reducedCurve (ε : ℝ) : ReducedCurve shear 0 (1, 0) (0, 1) ε (fun u => -u ^ 2) := by
  refine ⟨by fun_prop, by simp, fun u _ => ?_⟩
  rw [shear_fderiv, shear_fderiv]
  simp

theorem shear_reducedFn : reducedFn shear 0 (1, 0) (0, 1) (fun u => -u ^ 2) = fun u => (1 / 2 : ℝ) * u ^ 4 := by
  funext u
  rw [reducedFn, shear_fderiv]
  simp [shear]; ring

/-- The genuine reduced fourth derivative of the sheared datum is `12`. -/
theorem shear_reduced_deriv : iteratedDeriv 4 (reducedFn shear 0 (1, 0) (0, 1) (fun u => -u ^ 2)) 0 = 12 := by
  rw [shear_reducedFn, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  norm_num [Nat.factorial]

/-- The straight-line fourth derivative along `v = (1, 0)` is `24` (not the reduced value). -/
theorem shear_d4v : iteratedFDeriv ℝ 4 shear 0 ![(1, 0), (1, 0), (1, 0), (1, 0)] = 24 := by
  rw [vec4_const, iteratedFDeriv_diag_eq (shear_contDiff.of_le le_top)]
  have e : (fun t : ℝ => shear (0 + t • ((1 : ℝ), (0 : ℝ)))) = fun t => t ^ 4 := by
    funext t; simp [shear]
  rw [e, iteratedDeriv_fun_pow_zero]
  norm_num [Nat.factorial]

theorem shear_d2w : iteratedFDeriv ℝ 2 shear 0 ![(0, 1), (0, 1)] = 1 := by
  rw [vec2_const, iteratedFDeriv_diag_eq (shear_contDiff.of_le le_top)]
  have e : (fun t : ℝ => shear (0 + t • ((0 : ℝ), (1 : ℝ)))) = fun t => (1 / 2 : ℝ) * t ^ 2 := by
    funext t; simp [shear]; ring
  rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  norm_num

/-- `v = (1, 0)` is in the Hessian kernel of the sheared datum: `D²[v, v] = 0` (a degenerate point). -/
theorem shear_d2v : iteratedFDeriv ℝ 2 shear 0 ![(1, 0), (1, 0)] = 0 := by
  rw [vec2_const, iteratedFDeriv_diag_eq (shear_contDiff.of_le le_top)]
  have e : (fun t : ℝ => shear (0 + t • ((1 : ℝ), (0 : ℝ)))) = fun t => t ^ 4 := by
    funext t; simp [shear]
  rw [e, iteratedDeriv_fun_pow_zero]
  norm_num

/-- **K2-L's hypotheses hold** on the sheared datum at order `4` with the curve `h(u) = −u²`. -/
theorem shear_hyps :
    ContDiff ℝ ∞ shear ∧ iteratedFDeriv ℝ 2 shear 0 ![(0, 1), (0, 1)] ≠ 0 ∧
      ReducedCurve shear 0 (1, 0) (0, 1) 1 (fun u => -u ^ 2) ∧
      iteratedDeriv 4 (reducedFn shear 0 (1, 0) (0, 1) (fun u => -u ^ 2)) 0 ≠ 0 :=
  ⟨shear_contDiff.of_le le_top, by rw [shear_d2w]; norm_num, shear_reducedCurve 1,
    by rw [shear_reduced_deriv]; norm_num⟩

/-- **Bite (spanning)**: with `v = w = (0, 1)` the vectors do not span; `h(u) = −u` is a reduced curve, and the
reduced function is identically `0`, so the derivative hypothesis fails too (see the report: the spanning
condition is implied by the other hypotheses). -/
theorem modelL_parallel (m : ℕ) (hm : 2 ≤ m) :
    ((0 : ℝ), (1 : ℝ)).1 * ((0 : ℝ), (1 : ℝ)).2 - ((0 : ℝ), (1 : ℝ)).2 * ((0 : ℝ), (1 : ℝ)).1 = 0 ∧
      ReducedCurve (modelL m) 0 (0, 1) (0, 1) 1 (fun u => -u) ∧
      reducedFn (modelL m) 0 (0, 1) (0, 1) (fun u => -u) = (fun _ => 0) ∧
      ∀ j : ℕ, 1 ≤ j → iteratedDeriv j (reducedFn (modelL m) 0 (0, 1) (0, 1) (fun u => -u)) 0 = 0 := by
  have hr : reducedFn (modelL m) 0 (0, 1) (0, 1) (fun u => -u) = fun _ => 0 := by
    funext u
    rw [reducedFn, modelL_fderiv_zero m hm]
    simp [modelL, zero_pow (show m ≠ 0 by omega)]
  refine ⟨by norm_num, ⟨by fun_prop, by simp, fun u _ => ?_⟩, hr, fun j hj => ?_⟩
  · rw [modelL_fderiv, modelL_fderiv]; simp
  · rw [hr]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [iteratedDeriv_succ']
    simp

/-- The spanning hypothesis of K2-L is implied by the others: if `D²Ψ(k₀)[w, w] ≠ 0`, `h` is a reduced curve and some
reduced derivative of order `m ≥ 1` is nonzero, then `v` and `w` span `ℝ²`. -/
theorem span_of_hyps (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (ε : ℝ) (h : ℝ → ℝ) (m : ℕ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hm : 1 ≤ m) (hw : iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] ≠ 0) (hε : 0 < ε) (hc : ReducedCurve Ψ k₀ v w ε h)
    (hd : iteratedDeriv m (reducedFn Ψ k₀ v w h) 0 ≠ 0) : v.1 * w.2 - v.2 * w.1 ≠ 0 := by
  intro hpar
  -- `w ≠ 0`
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hw
    exact (iteratedFDeriv ℝ 2 Ψ k₀).map_coord_zero 0 (by simp)
  -- `v = λ w`
  obtain ⟨l, hl⟩ : ∃ l : ℝ, v = l • w := by
    by_cases h1 : w.1 = 0
    · have h2 : w.2 ≠ 0 := fun h2 => hw0 (Prod.ext h1 h2)
      refine ⟨v.2 / w.2, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul, h1, mul_zero]
        rw [h1, mul_zero, sub_zero] at hpar
        exact (mul_eq_zero.mp hpar).resolve_right h2
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp
    · refine ⟨v.1 / w.1, Prod.ext ?_ ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp; linarith
  -- the transverse derivative along the line through `k₀` in direction `w`
  set φ : ℝ → ℝ := fun s => fderiv ℝ Ψ (k₀ + s • w) w with hφ
  have hdiff : Differentiable ℝ (fderiv ℝ Ψ) :=
    ((contDiff_infty.mp hΨ 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => k₀ + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add k₀
  have hF : HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (k₀ + s • w)) (fderiv ℝ (fderiv ℝ Ψ) k₀ w) 0 :=
    (hdiff k₀).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hφd : HasDerivAt φ (fderiv ℝ (fderiv ℝ Ψ) k₀ w w) 0 := by
    have := hF.clm_apply (hasDerivAt_const (0 : ℝ) w)
    simpa using this
  have hne : fderiv ℝ (fderiv ℝ Ψ) k₀ w w ≠ 0 := by
    rwa [iteratedFDeriv_two_apply] at hw
  have hev := hφd.eventually_ne (c := φ 0) hne
  rw [eventually_nhdsWithin_iff] at hev
  -- `s(u) = l u + h u` tends to `0`
  set S : ℝ → ℝ := fun u => u * l + h u with hS
  have hScont : Continuous S := (continuous_id.mul continuous_const).add hc.1.continuous
  have hS0 : S 0 = 0 := by simp [hS, hc.2.1]
  have hStend : Tendsto S (𝓝 0) (𝓝 0) := by
    have := hScont.tendsto 0; rwa [hS0] at this
  have hpt : ∀ u : ℝ, k₀ + u • v + h u • w = k₀ + S u • w := by
    intro u; rw [hl, smul_smul, add_assoc, ← add_smul]
  have hzero : ∀ᶠ u in 𝓝 (0 : ℝ), S u = 0 := by
    have h1 := hStend.eventually hev
    have h2 : ∀ᶠ u in 𝓝 (0 : ℝ), |u| < ε := by
      have : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
      filter_upwards [this] with u hu
      simpa [Real.dist_eq] using hu
    filter_upwards [h1, h2] with u hu1 hu2
    by_contra hSu
    apply hu1 hSu
    have := hc.2.2 u hu2
    rw [hpt] at this
    simp only [hφ, zero_smul, add_zero]
    exact this
  have hred : reducedFn Ψ k₀ v w h =ᶠ[𝓝 0] fun _ => Ψ k₀ := by
    filter_upwards [hzero] with u hu
    rw [reducedFn, hpt, hu, show u • v + h u • w = S u • w by rw [hl, smul_smul, ← add_smul], hu]
    simp
  apply hd
  rw [hred.iteratedDeriv_eq, iteratedDeriv_const]
  simp; omega

/-! ## A. Data for K2-F -/

/-- A smooth bump at `0` of outer radius `1` (sup norm). -/
noncomputable def bump1 : ContDiffBump (0 : ℝ × ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `χ₁ = bump1` as a complex function. -/
noncomputable def chi1 (k : ℝ × ℝ) : ℂ := (bump1 k : ℂ)

theorem chi1_contDiff : ContDiff ℝ ∞ chi1 :=
  Complex.ofRealCLM.contDiff.comp bump1.contDiff

theorem tsupport_ofReal_comp (f : ℝ × ℝ → ℝ) : tsupport (fun k => (f k : ℂ)) = tsupport f := by
  have : Function.support (fun k => (f k : ℂ)) = Function.support f :=
    Function.support_comp_eq (fun x : ℝ => (x : ℂ)) (fun {x} => Complex.ofReal_eq_zero) f
  rw [tsupport, tsupport, this]

theorem chi1_tsupport : tsupport chi1 ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  intro k hk
  change k ∈ tsupport (fun k => ((bump1 k : ℝ) : ℂ)) at hk
  rw [tsupport_ofReal_comp, ContDiffBump.tsupport_eq] at hk
  have hk' : ‖k‖ ≤ 1 := by simpa [bump1] using hk
  rw [Prod.norm_def] at hk'
  have h1 : |k.1| ≤ 1 := (le_max_left _ _).trans hk'
  have h2 : |k.2| ≤ 1 := (le_max_right _ _).trans hk'
  have hpi := Real.pi_gt_three
  rw [abs_le] at h1 h2
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **K2-F's hypotheses hold** for `χ₁`. -/
theorem chi1_hyps : ContDiff ℝ ∞ chi1 ∧
    tsupport chi1 ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi :=
  ⟨chi1_contDiff, chi1_tsupport⟩

/-- A bump of outer radius `π`: smooth, but its support reaches the boundary of the box. -/
noncomputable def bumpPi : ContDiffBump (0 : ℝ × ℝ) := ⟨1, Real.pi, one_pos, by linarith [Real.pi_gt_three]⟩

noncomputable def chiPi (k : ℝ × ℝ) : ℂ := (bumpPi k : ℂ)

/-- **Bite**: `χ_π` is smooth and `(π, 0)` lies in its support closure, not in the open box. -/
theorem chiPi_bite : ContDiff ℝ ∞ chiPi ∧
    ¬ tsupport chiPi ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  refine ⟨Complex.ofRealCLM.contDiff.comp bumpPi.contDiff, fun h => ?_⟩
  have hm : ((Real.pi, 0) : ℝ × ℝ) ∈ tsupport chiPi := by
    change _ ∈ tsupport (fun k => ((bumpPi k : ℝ) : ℂ))
    rw [tsupport_ofReal_comp, ContDiffBump.tsupport_eq]
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_zero]
    rw [abs_of_pos Real.pi_pos]
    simp [bumpPi, Real.pi_pos.le]
  exact lt_irrefl _ (h hm).1.2

/-- **Bite**: the constant `1` is smooth with support closure the whole plane. -/
theorem const_one_bite : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℂ)) ∧
    ¬ tsupport (fun _ : ℝ × ℝ => (1 : ℂ)) ⊆ Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  refine ⟨contDiff_const, fun h => ?_⟩
  have : ((Real.pi, 0) : ℝ × ℝ) ∈ tsupport (fun _ : ℝ × ℝ => (1 : ℂ)) :=
    subset_closure (by simp)
  exact lt_irrefl _ (h this).1.2

/-- `triPhase α` is continuous and `2π`-periodic in each variable (K2-F applies to it). -/
theorem triPhase_periodic (α : ℝ) : Continuous (triPhase α) ∧
    (∀ k : ℝ × ℝ, triPhase α (k.1 + 2 * Real.pi, k.2) = triPhase α k) ∧
    (∀ k : ℝ × ℝ, triPhase α (k.1, k.2 + 2 * Real.pi) = triPhase α k) := by
  refine ⟨(triPhase_contDiff α).continuous, fun k => ?_, fun k => ?_⟩
  · simp only [triPhase]
    rw [Real.cos_add_two_pi, show k.1 + 2 * Real.pi + k.2 = (k.1 + k.2) + 2 * Real.pi by ring, Real.cos_add_two_pi]
  · simp only [triPhase]
    rw [Real.cos_add_two_pi, show k.1 + (k.2 + 2 * Real.pi) = (k.1 + k.2) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]

/-- `∫_{−π}^{π} e^{ijx} dx = 0` for an integer `j ≠ 0`. -/
theorem integral_Icc_exp_int (j : ℤ) (hj : j ≠ 0) :
    ∫ x in Set.Icc (-Real.pi) Real.pi, Complex.exp (↑((j : ℝ) * x) * Complex.I) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
  have e : ∀ x : ℝ, Complex.exp (↑((j : ℝ) * x) * Complex.I) = Complex.exp ((j : ℂ) * Complex.I * x) := by
    intro x; congr 1; push_cast; ring
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h2 : Complex.exp ((j : ℂ) * Complex.I * (Real.pi : ℝ)) =
      Complex.exp ((j : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) * Complex.exp (j * (2 * Real.pi * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [Complex.exp_int_mul_two_pi_mul_I, mul_one] at h2
  rw [h2, sub_self, zero_div]

/-- The lattice coefficients of the zero phase: `∫_{[−π, π]²} e^{i n·k} dk = 0` for `n ≠ 0`. -/
theorem lattice_coeff_zero_phase (t : ℝ) (n : ℤ × ℤ) (hn : n ≠ 0) :
    ∫ k in torusBox, Complex.exp (↑(t * (fun _ : ℝ × ℝ => (0 : ℝ)) k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) *
      Complex.I) = 0 := by
  have e : ∀ k : ℝ × ℝ, Complex.exp (↑(t * (fun _ : ℝ × ℝ => (0 : ℝ)) k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) *
      Complex.I) = Complex.exp (↑((n.1 : ℝ) * k.1) * Complex.I) * Complex.exp (↑((n.2 : ℝ) * k.2) * Complex.I) := by
    intro k; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [torusBox, Measure.volume_eq_prod, setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun x : ℝ => Complex.exp (↑((n.1 : ℝ) * x) * Complex.I)) (fun y : ℝ => Complex.exp (↑((n.2 : ℝ) * y) * Complex.I))]
  by_cases h1 : n.1 = 0
  · have h2 : n.2 ≠ 0 := fun h2 => hn (Prod.ext h1 h2)
    rw [integral_Icc_exp_int _ h2, mul_zero]
  · rw [integral_Icc_exp_int _ h1, zero_mul]

theorem integral_chi1_eq : ∫ k in torusBox, chi1 k = ((∫ k, bump1 k : ℝ) : ℂ) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_ofReal
  · intro k hk
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hk (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self (chi1_tsupport h))

theorem integral_chi1_ne_zero : ∫ k in torusBox, chi1 k ≠ 0 := by
  rw [integral_chi1_eq]
  exact_mod_cast (bump1.integral_pos (μ := volume)).ne'

/-! ## A. Real-variable helpers (powers, separation of rates, the integral of a cutoff) -/

/-- `(s^m)^{1 − 1/m} = s^{m−1}`. -/
theorem pow_rpow_one_sub {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) :
    (s ^ m) ^ (1 - 1 / (m : ℝ)) = s ^ (m - 1) := by
  rw [← Real.rpow_natCast_mul hs.le, ← Real.rpow_natCast]
  congr 1
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Nat.cast_sub hm]; field_simp; push_cast; ring

/-- `(s^m)^{−1/m} = s⁻¹`. -/
theorem pow_rpow_neg_inv {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) : (s ^ m) ^ (-(1 : ℝ) / (m : ℝ)) = s⁻¹ := by
  rw [← Real.rpow_natCast_mul hs.le]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [show (m : ℝ) * (-(1 : ℝ) / (m : ℝ)) = -1 by field_simp, Real.rpow_neg_one]

/-- `r^{1−m} = (r^{m−1})⁻¹`. -/
theorem rpow_one_sub_nat {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) : r ^ (1 - (m : ℝ)) = (r ^ (m - 1))⁻¹ := by
  rw [show (1 : ℝ) - m = -((m - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hm]; push_cast; ring, Real.rpow_neg hr.le,
    Real.rpow_natCast]

/-- Two rates separate: for `a < b` and `c > 0`, some `t ≥ max T 1` has `C t^{−b} < c t^{−a}`. -/
theorem rate_separation (a b c C T : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ t : ℝ, T ≤ t ∧ 1 ≤ t ∧ C * t ^ (-b) < c * t ^ (-a) := by
  set K := (|C| / c + 1) ^ (1 / (b - a)) with hK
  have hba : 0 < b - a := by linarith
  have hK0 : 0 < |C| / c + 1 := by positivity
  refine ⟨max (max T 1) K, le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _), ?_⟩
  set t := max (max T 1) K
  have ht1 : 1 ≤ t := le_max_of_le_left (le_max_right _ _)
  have ht0 : 0 < t := by linarith
  have htK : K ≤ t := le_max_right _ _
  have hpow : |C| / c + 1 ≤ t ^ (b - a) := by
    have e : (|C| / c + 1) = K ^ (b - a) := by
      rw [hK, ← Real.rpow_mul hK0.le, show 1 / (b - a) * (b - a) = 1 by field_simp, Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow (by positivity) htK hba.le
  have hsplit : t ^ (-a) = t ^ (-b) * t ^ (b - a) := by
    rw [← Real.rpow_add ht0]; ring_nf
  rw [hsplit]
  have hb : 0 < t ^ (-b) := Real.rpow_pos_of_pos ht0 _
  have h1 : C < c * t ^ (b - a) := by
    have : c * (|C| / c + 1) ≤ c * t ^ (b - a) := mul_le_mul_of_nonneg_left hpow hc.le
    have e2 : c * (|C| / c + 1) = |C| + c := by field_simp
    linarith [le_abs_self C]
  nlinarith

theorem plat_continuous (r R : ℝ) : Continuous (plat r R) := (plat_contDiff r R).continuous

theorem plat_integrable {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) : Integrable (plat r R) :=
  (plat_continuous r R).integrable_of_hasCompactSupport (plat_hasCompactSupport hr hrR)

/-- `∫ plat r R ≥ 2r`. -/
theorem integral_plat_ge {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) : 2 * r ≤ ∫ x, plat r R x := by
  have h := setIntegral_le_integral (s := Set.Icc (-r) r) (plat_integrable hr hrR)
    (Filter.Eventually.of_forall fun x => plat_nonneg r R x)
  have e : ∫ x in Set.Icc (-r) r, plat r R x = ∫ x in Set.Icc (-r) r, (1 : ℝ) :=
    setIntegral_congr_fun measurableSet_Icc fun x hx => plat_eq_one hrR (abs_le.mpr hx)
  rw [e, setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
    mul_one] at h
  linarith

/-- **Bite of K2-ML's threshold** (unconditional): at `m = 2`, `t = (1/200)²`, `b = plat 1 2` the lower bound
`t^{−1/m}/(24m) = 200/48` fails, since `‖∫ b e^{itx²}‖ ≤ 4`. -/
theorem ml_threshold_bite :
    ¬ (((1 / 200 : ℝ) ^ 2) ^ (-(1 : ℝ) / ((2 : ℕ) : ℝ)) / (24 * ((2 : ℕ) : ℝ)) ≤
        ‖∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp ((((1 / 200 : ℝ) ^ 2 * 1 * x ^ 2 : ℝ) : ℂ) * Complex.I)‖) := by
  intro h
  rw [pow_rpow_neg_inv (by norm_num) (by norm_num)] at h
  have h2 := norm_integral_plat_le (r := 1) (R := 2) (by norm_num) (by norm_num)
    (fun x => (1 / 200 : ℝ) ^ 2 * 1 * x ^ 2)
  beta_reduce at h2
  have e : (1 / 200 : ℝ)⁻¹ / (24 * ((2 : ℕ) : ℝ)) = 200 / 48 := by norm_num
  rw [e] at h
  linarith

/-- **Bite of K2-MA's hypothesis `0 < t`** (unconditional): at `t = 0` the remainder bound reads `‖∫ b‖ ≤ 0`, but
`∫ plat r R ≥ 2r > 0`. -/
theorem ma_time_zero_bite (m : ℕ) (hm : 2 ≤ m) (σ : ℝ) (C : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ¬ ‖(∫ x : ℝ, (plat r R x : ℂ) * Complex.exp (↑(0 * σ * x ^ m) * Complex.I)) -
        (((0 : ℝ) ^ (-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) * C‖ ≤ 4 / ((m : ℝ) * 0 * r ^ (m - 1)) := by
  intro h
  have hm0 : (-(1 : ℝ) / (m : ℝ)) ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact div_ne_zero (by norm_num) this
  rw [Real.zero_rpow hm0] at h
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, sub_zero, mul_zero, div_zero] at h
  have e : ∫ x, ((plat r R x : ℝ) : ℂ) = ((∫ x, plat r R x : ℝ) : ℂ) := integral_ofReal
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  have := integral_plat_ge hr.le hrR
  have h0 : |∫ x, plat r R x| = 0 := le_antisymm h (abs_nonneg _)
  rw [abs_eq_zero] at h0
  linarith

/-- **Bite of K2-U's hypothesis `1 ≤ t`** (unconditional): at `t = 0`, `‖triKernel α 0 (0, 0)‖ = (2π)²` while
`C · 0^{−triRate α} = 0` for every `C`. -/
theorem u_time_zero_bite (α C : ℝ) : ¬ ‖triKernel α 0 (0, 0)‖ ≤ C * (0 : ℝ) ^ (-triRate α) := by
  have hr : -triRate α ≠ 0 := by rcases triRate_cases α with h | h <;> rw [h] <;> norm_num
  rw [triKernel_time_zero, Real.zero_rpow hr, mul_zero, Complex.norm_real, Real.norm_eq_abs]
  intro h
  have : 0 < (2 * Real.pi) ^ 2 := by positivity
  linarith [abs_nonneg ((2 * Real.pi) ^ 2), le_abs_self ((2 * Real.pi) ^ 2)]


/-! ## A. The bite of `D²Ψ(k₀)[w, w] ≠ 0` in K2-L: the phase `x²` -/

/-- `x²`: constant in the direction `w = (0, 1)`. -/
noncomputable def modelX (k : ℝ × ℝ) : ℝ := k.1 ^ 2

theorem modelX_contDiff : ContDiff ℝ ω modelX := by unfold modelX; fun_prop

theorem modelX_fderiv (x w : ℝ × ℝ) : fderiv ℝ modelX x w = 2 * x.1 * w.1 := by
  have h := (hasFDerivAt_fst (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)).pow 2
  rw [show modelX = fun k : ℝ × ℝ => k.1 ^ 2 from rfl, h.fderiv]
  simp

/-- **Bite**: `x²` at `0` (`v = (1, 0)`, `w = (0, 1)`, `h = 0`, `m = 2`) satisfies every hypothesis of K2-L except
`D²Ψ(0)[w, w] ≠ 0`. -/
theorem modelX_hyps :
    ContDiff ℝ ∞ modelX ∧ ((1 : ℝ), (0 : ℝ)).1 * ((0 : ℝ), (1 : ℝ)).2 - ((1 : ℝ), (0 : ℝ)).2 * ((0 : ℝ), (1 : ℝ)).1 ≠ 0 ∧
      iteratedFDeriv ℝ 2 modelX 0 ![(0, 1), (0, 1)] = 0 ∧
      ReducedCurve modelX 0 (1, 0) (0, 1) 1 (fun _ => 0) ∧
      iteratedDeriv 2 (reducedFn modelX 0 (1, 0) (0, 1) (fun _ => 0)) 0 = 2 := by
  refine ⟨modelX_contDiff.of_le le_top, span_e1_e2, ?_, ⟨contDiff_const, rfl, fun u _ => ?_⟩, ?_⟩
  · rw [vec2_const, iteratedFDeriv_diag_eq (modelX_contDiff.of_le le_top)]
    have e : (fun t : ℝ => modelX (0 + t • ((0 : ℝ), (1 : ℝ)))) = fun _ => 0 := by
      funext t; simp [modelX]
    rw [e, iteratedDeriv_const]; simp
  · rw [modelX_fderiv, modelX_fderiv]; simp
  · have e : reducedFn modelX 0 (1, 0) (0, 1) (fun _ => 0) = fun u => u ^ 2 := by
      funext u; rw [reducedFn, modelX_fderiv]; simp [modelX]
    rw [e, iteratedDeriv_fun_pow_zero]; norm_num

/-- The product amplitude `b(κ₁) b(κ₂)`. -/
noncomputable def prodAmp (b : ℝ → ℝ) (κ : ℝ × ℝ) : ℂ := ((b κ.1 * b κ.2 : ℝ) : ℂ)

/-- For `x²` the integral factorises: `∫ e^{itκ₁²} b(κ₁) b(κ₂) = (∫ b e^{itx²}) (∫ b)`. -/
theorem oscInt2_modelX_prodAmp (b : ℝ → ℝ) (t : ℝ) :
    oscInt2 (fun κ => t * modelX κ + lin 0 κ) (prodAmp b) =
      (∫ x : ℝ, (b x : ℂ) * Complex.exp (((t * 1 * x ^ 2 : ℝ) : ℂ) * Complex.I)) * ∫ y : ℝ, (b y : ℂ) := by
  rw [oscInt2, Measure.volume_eq_prod, ← integral_prod_mul (μ := volume) (ν := volume)
    (fun x : ℝ => (b x : ℂ) * Complex.exp (((t * 1 * x ^ 2 : ℝ) : ℂ) * Complex.I)) (fun y : ℝ => (b y : ℂ))]
  congr 1
  funext κ
  simp only [modelX, lin, prodAmp, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, mul_one]
  push_cast; ring

theorem prodAmp_tsupport {c R : ℝ} (hc : 0 ≤ c) (hcR : c < R) :
    tsupport (prodAmp (plat c R)) ⊆ Metric.closedBall 0 R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro κ hκ
  have hR : 0 ≤ R := hc.trans hcR.le
  rw [Function.mem_support, prodAmp, Complex.ofReal_ne_zero, mul_ne_zero_iff] at hκ
  have h1 : |κ.1| < R := by
    by_contra h; exact hκ.1 (plat_eq_zero hc hcR (not_lt.mp h))
  have h2 : |κ.2| < R := by
    by_contra h; exact hκ.2 (plat_eq_zero hc hcR (not_lt.mp h))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le h1.le h2.le

theorem prodAmp_contDiff (r R : ℝ) : ContDiff ℝ ∞ (prodAmp (plat r R)) :=
  Complex.ofRealCLM.contDiff.comp (((plat_contDiff r R).comp contDiff_fst).mul ((plat_contDiff r R).comp contDiff_snd))


/-! ## B. Through the statement constants (each the only statement hypothesis; consistency theorems use two) -/

/-- **K2-U** at `α = 0` is the lattice Laplacian bound of batch GD (`triKernel 0 = latticeKernel`, rate `2/3`). -/
theorem triU_zero (h : TriDecayUpperStatement) : LatticeLaplacianDecayStatement := by
  obtain ⟨C, hC⟩ := h 0
  refine ⟨C, fun t x ht => ?_⟩
  have := hC t x ht
  rw [triKernel_zero, triRate_zero] at this
  rw [show -(2 : ℝ) / 3 = -(2 / 3) by ring]
  exact this

/-- **K2-U** at `±a*`: rate `2/3`. -/
theorem triU_exceptional (h : TriDecayUpperStatement) :
    (∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel triExceptional t n‖ ≤ C * t ^ (-(2 / 3 : ℝ))) ∧
      ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel (-triExceptional) t n‖ ≤ C * t ^ (-(2 / 3 : ℝ)) := by
  have h1 := h triExceptional
  have h2 := h (-triExceptional)
  rw [triRate_exceptional] at h1
  rw [triRate_neg_exceptional] at h2
  exact ⟨h1, h2⟩

/-- **K2-U** at `α = 1/4`, `1`, `−2`: rate `3/4`. -/
theorem triU_generic (h : TriDecayUpperStatement) (α : ℝ) (hα : α = 1 / 4 ∨ α = 1 ∨ α = -2) :
    ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel α t n‖ ≤ C * t ^ (-(3 / 4 : ℝ)) := by
  have h1 := h α
  rcases hα with rfl | rfl | rfl
  · rwa [triRate_quarter] at h1
  · rwa [triRate_one] at h1
  · rwa [triRate_neg_two] at h1

/-- **K2-U** off the exceptional set (generic `α`): rate `3/4`. -/
theorem triU_off (h : TriDecayUpperStatement) (α : ℝ) (h0 : α ≠ 0) (h1 : |α| ≠ triExceptional) :
    ∃ C : ℝ, ∀ (t : ℝ) (n : ℤ × ℤ), 1 ≤ t → ‖triKernel α t n‖ ≤ C * t ^ (-(3 / 4 : ℝ)) := by
  have h2 := h α
  rwa [triRate_generic α h0 h1] at h2

/-- **K2-D** at `α = 0`: a lower bound `c t^{−2/3}` for the lattice Laplacian kernel at some site. -/
theorem triD_zero (h : TriDecayLowerStatement) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-(2 / 3 : ℝ)) ≤ ‖latticeKernel t n‖ := by
  have h1 := h 0
  rw [triKernel_zero, triRate_zero] at h1
  exact h1

/-- **K2-D** at `±a*`: rate `2/3`. -/
theorem triD_exceptional (h : TriDecayLowerStatement) :
    (∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ,
        c * t ^ (-(2 / 3 : ℝ)) ≤ ‖triKernel triExceptional t n‖) ∧
      ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-(2 / 3 : ℝ)) ≤ ‖triKernel (-triExceptional) t n‖ := by
  have h1 := h triExceptional
  have h2 := h (-triExceptional)
  rw [triRate_exceptional] at h1
  rw [triRate_neg_exceptional] at h2
  exact ⟨h1, h2⟩

/-- **K2-D** at `α = 1/4`, `1`, `−2`: rate `3/4`. -/
theorem triD_generic (h : TriDecayLowerStatement) (α : ℝ) (hα : α = 1 / 4 ∨ α = 1 ∨ α = -2) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ n : ℤ × ℤ, c * t ^ (-(3 / 4 : ℝ)) ≤ ‖triKernel α t n‖ := by
  have h1 := h α
  rcases hα with rfl | rfl | rfl
  · rwa [triRate_quarter] at h1
  · rwa [triRate_one] at h1
  · rwa [triRate_neg_two] at h1

/-- **K2-D** with the trivial bound: `c t^{−triRate α} ≤ (2π)²` for `t ≥ T`. -/
theorem triD_trivial (h : TriDecayLowerStatement) (α : ℝ) :
    ∃ c > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → c * t ^ (-triRate α) ≤ (2 * Real.pi) ^ 2 := by
  obtain ⟨c, hc, T, hT⟩ := h α
  refine ⟨c, hc, T, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := hT t ht
  exact hn.trans (norm_triKernel_le α t n)

/-- **Consistency K2-U with K2-D** at every `α`: the constants satisfy `c ≤ C`. -/
theorem triU_triD_consistent (hU : TriDecayUpperStatement) (hD : TriDecayLowerStatement) (α : ℝ) :
    ∃ c > 0, ∃ C : ℝ, c ≤ C := by
  obtain ⟨C, hC⟩ := hU α
  obtain ⟨c, hc, T, hT⟩ := hD α
  refine ⟨c, hc, C, ?_⟩
  set t := max T 1
  obtain ⟨n, hn⟩ := hT t (le_max_left _ _)
  have h1 := hC t n (le_max_right _ _)
  have hp : 0 < t ^ (-triRate α) := Real.rpow_pos_of_pos (by positivity) _
  have := hn.trans h1
  exact le_of_mul_le_mul_right this hp

/-- **K2-MA** with the cutoff `plat r R` (any `0 < r < R`), every `m ≥ 2` and `σ = ±1`. -/
theorem triMA_plat (h : MonomialAsymptoticStatement) (m : ℕ) (hm : 2 ≤ m) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℂ, 1 / (12 * (m : ℝ)) ≤ C.re ∧ ∀ t : ℝ, 0 < t →
      ‖(∫ x : ℝ, (plat r R x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)) -
          ((t ^ (-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) * C‖ ≤ 4 / ((m : ℝ) * t * r ^ (m - 1)) := by
  obtain ⟨C, hC, -, hb⟩ := h m σ hm hσ
  exact ⟨C, hC, fun t ht => hb (plat r R) r t (plat_plateau hr hrR) ht⟩

/-- **K2-MA** at `m = 2, 3, 4, 6`, `σ = ±1`, cutoff `plat 1 2`: remainder `4/(m t)`. -/
theorem triMA_instances (h : MonomialAsymptoticStatement) :
    ∀ m ∈ ({2, 3, 4, 6} : Finset ℕ), ∀ σ ∈ ({1, -1} : Finset ℝ), ∃ C : ℂ, 1 / (12 * (m : ℝ)) ≤ C.re ∧
      ∀ t : ℝ, 0 < t → ‖(∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp (↑(t * σ * x ^ m) * Complex.I)) -
          ((t ^ (-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) * C‖ ≤ 4 / ((m : ℝ) * t) := by
  intro m hm σ hσ
  have hm2 : 2 ≤ m := by simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  have hσ' : σ = 1 ∨ σ = -1 := by simpa using hσ
  obtain ⟨C, hC, hb⟩ := triMA_plat h m hm2 σ hσ' (r := 1) (R := 2) one_pos (by norm_num)
  exact ⟨C, hC, fun t ht => by simpa using hb t ht⟩

/-- **K2-MA**, the constant is bounded: `‖C‖ ≤ 2R + 4/(m r^{m−1})` (from the remainder at `t = 1`). -/
theorem triMA_norm_le (h : MonomialAsymptoticStatement) (m : ℕ) (hm : 2 ≤ m) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℂ, 1 / (12 * (m : ℝ)) ≤ C.re ∧ ‖C‖ ≤ 2 * R + 4 / ((m : ℝ) * r ^ (m - 1)) := by
  obtain ⟨C, hC, hb⟩ := triMA_plat h m hm σ hσ hr hrR
  refine ⟨C, hC, ?_⟩
  have h1 := hb 1 one_pos
  simp only [Real.one_rpow, Complex.ofReal_one, one_mul, mul_one] at h1
  have h2 := norm_integral_plat_le hr.le hrR (fun x => σ * x ^ m)
  beta_reduce at h2
  have := norm_sub_norm_le C (∫ x : ℝ, (plat r R x : ℂ) * Complex.exp (↑(σ * x ^ m) * Complex.I))
  rw [norm_sub_rev] at this
  linarith

/-- **K2-ML** with `plat r R` at `t = s^m`: once `(s r)^{m−1} ≥ 96`, `‖∫ b e^{i s^m σ x^m}‖ ≥ s⁻¹/(24m)`. -/
theorem triML_plat (h : MonomialLowerStatement) (m : ℕ) (hm : 2 ≤ m) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (s : ℝ) (hs : 0 < s) (hth : 96 ≤ (s * r) ^ (m - 1)) :
    s⁻¹ / (24 * (m : ℝ)) ≤ ‖∫ x : ℝ, (plat r R x : ℂ) * Complex.exp (↑(s ^ m * σ * x ^ m) * Complex.I)‖ := by
  have h1 := h m σ (plat r R) r (s ^ m) hm hσ (plat_plateau hr hrR) (by positivity)
  rw [pow_rpow_neg_inv hs (by omega)] at h1
  apply h1
  rw [pow_rpow_one_sub hs (by omega), rpow_one_sub_nat hr (by omega)]
  have hr' : 0 < r ^ (m - 1) := by positivity
  rw [mul_pow] at hth
  rw [← div_eq_mul_inv, div_le_iff₀ hr']
  linarith

/-- **K2-ML** at `m = 2` (`s = 96`), `m = 3` (`s = 10`), `m = 4` (`s = 5`), `m = 6` (`s = 5/2`), `σ = ±1`, cutoff
`plat 1 2`. -/
theorem triML_instances (h : MonomialLowerStatement) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (96 : ℝ)⁻¹ / 48 ≤ ‖∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp (((((96 : ℝ) ^ 2 * σ * x ^ 2 : ℝ)) : ℂ) * Complex.I)‖ ∧
    (10 : ℝ)⁻¹ / 72 ≤ ‖∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp (((((10 : ℝ) ^ 3 * σ * x ^ 3 : ℝ)) : ℂ) * Complex.I)‖ ∧
    (5 : ℝ)⁻¹ / 96 ≤ ‖∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp (((((5 : ℝ) ^ 4 * σ * x ^ 4 : ℝ)) : ℂ) * Complex.I)‖ ∧
    (5 / 2 : ℝ)⁻¹ / 144 ≤
      ‖∫ x : ℝ, (plat 1 2 x : ℂ) * Complex.exp (((((5 / 2 : ℝ) ^ 6 * σ * x ^ 6 : ℝ)) : ℂ) * Complex.I)‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := triML_plat h 2 le_rfl σ hσ (r := 1) (R := 2) one_pos (by norm_num) 96 (by norm_num) (by norm_num)
    norm_num at this ⊢; exact this
  · have := triML_plat h 3 (by norm_num) σ hσ (r := 1) (R := 2) one_pos (by norm_num) 10 (by norm_num)
      (by norm_num)
    norm_num at this ⊢; exact this
  · have := triML_plat h 4 (by norm_num) σ hσ (r := 1) (R := 2) one_pos (by norm_num) 5 (by norm_num)
      (by norm_num)
    norm_num at this ⊢; exact this
  · have := triML_plat h 6 (by norm_num) σ hσ (r := 1) (R := 2) one_pos (by norm_num) (5 / 2) (by norm_num)
      (by norm_num)
    norm_num at this ⊢; exact this

/-- **K2-L** on the model `x^m + y²/2` (every `m ≥ 2`): decay `t^{−(1/2 + 1/m)}` near `0`, uniformly in `y`. -/
theorem triL_model (h : ReducedOrderBoundStatement) (m : ℕ) (hm : 2 ≤ m) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * modelL m κ + lin y κ) A‖ ≤ C * M * t ^ (-(1 / 2 + 1 / (m : ℝ))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := modelL_hyps m hm
  exact h (modelL m) 0 (1, 0) (0, 1) 1 (fun _ => 0) m h1 hm h2 h3 one_pos h4 h5

/-- **K2-L** on the model at `m = 3` and `m = 6`, with the exponent substituted (`5/6`, `2/3`). -/
theorem triL_model_36 (h : ReducedOrderBoundStatement) :
    (∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * modelL 3 κ + lin y κ) A‖ ≤ C * M * t ^ (-(5 / 6 : ℝ))) ∧
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * modelL 6 κ + lin y κ) A‖ ≤ C * M * t ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨δ₃, hδ₃, C₃, h3⟩ := triL_model h 3 (by norm_num)
  obtain ⟨δ₆, hδ₆, C₆, h6⟩ := triL_model h 6 (by norm_num)
  refine ⟨⟨δ₃, hδ₃, C₃, fun A M y t hA ht => ?_⟩, ⟨δ₆, hδ₆, C₆, fun A M y t hA ht => ?_⟩⟩
  · have := h3 A M y t hA ht
    rwa [show -(1 / 2 + 1 / ((3 : ℕ) : ℝ)) = -(5 / 6 : ℝ) by norm_num] at this
  · have := h6 A M y t hA ht
    rwa [show -(1 / 2 + 1 / ((6 : ℕ) : ℝ)) = -(2 / 3 : ℝ) by norm_num] at this

/-- **K2-L** on the sheared datum at order `4` (reduced curve `h(u) = −u²`): decay `t^{−3/4}`. -/
theorem triL_shear (h : ReducedOrderBoundStatement) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (y : ℝ × ℝ) (t : ℝ),
      AmpBound 2 (Metric.closedBall 0 δ) A M → 1 ≤ t →
        ‖oscInt2 (fun κ => t * shear κ + lin y κ) A‖ ≤ C * M * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := shear_hyps
  obtain ⟨δ, hδ, C, hC⟩ := h shear 0 (1, 0) (0, 1) 1 (fun u => -u ^ 2) 4 h1 (by norm_num) span_e1_e2 h2 one_pos h3 h4
  refine ⟨δ, hδ, C, fun A M y t hA ht => ?_⟩
  have := hC A M y t hA ht
  rwa [show -(1 / 2 + 1 / ((4 : ℕ) : ℝ)) = -(3 / 4 : ℝ) by norm_num] at this

/-- **K2-F** with `χ₁`: one constant `D` for every continuous biperiodic phase, time and velocity. -/
theorem triF_chi1 (h : TorusLocalizationStatement) :
    ∃ D : ℝ, ∀ (Ψ : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) (B : ℝ), Continuous Ψ →
      (∀ k : ℝ × ℝ, Ψ (k.1 + 2 * Real.pi, k.2) = Ψ k) → (∀ k : ℝ × ℝ, Ψ (k.1, k.2 + 2 * Real.pi) = Ψ k) →
      (∀ n : ℤ × ℤ, ‖∫ k in torusBox,
          Complex.exp (↑(t * Ψ k + ((n.1 : ℝ) * k.1 + (n.2 : ℝ) * k.2)) * Complex.I)‖ ≤ B) →
        ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * (Ψ k + lin p k)) * Complex.I)‖ ≤ D * B :=
  h chi1 chi1_contDiff chi1_tsupport

/-- **K2-F** with `χ₁` and the zero phase: `‖∫ χ₁ e^{it p·k}‖ ≤ D (2π)²` (the zero mode is `(2π)²`). -/
theorem triF_chi1_zero (h : TorusLocalizationStatement) :
    ∃ D : ℝ, ∀ (t : ℝ) (p : ℝ × ℝ),
      ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * ((fun _ : ℝ × ℝ => (0 : ℝ)) k + lin p k)) * Complex.I)‖ ≤
        D * (2 * Real.pi) ^ 2 := by
  obtain ⟨D, hD⟩ := triF_chi1 h
  refine ⟨D, fun t p => hD _ t p _ continuous_const (fun _ => rfl) (fun _ => rfl) fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    simp only [mul_zero, Int.cast_zero, zero_mul, add_zero, Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero,
      Complex.exp_zero, setIntegral_const, volume_real_torusBox, Complex.real_smul, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact le_of_eq (abs_of_pos (by positivity))
  · rw [lattice_coeff_zero_phase t n hn, norm_zero]; positivity

/-- **Consistency K2-F with K2-U**: the lattice coefficients of `triPhase α` are `triKernel α t n`, so the
`χ₁`-localised integral at every real velocity decays at the rate `triRate α`. -/
theorem triF_triU_consistent (hF : TorusLocalizationStatement) (hU : TriDecayUpperStatement) (α : ℝ) :
    ∃ D C : ℝ, ∀ (t : ℝ) (p : ℝ × ℝ), 1 ≤ t →
      ‖∫ k in torusBox, chi1 k * Complex.exp (↑(t * (triPhase α k + lin p k)) * Complex.I)‖ ≤
        D * (C * t ^ (-triRate α)) := by
  obtain ⟨D, hD⟩ := triF_chi1 hF
  obtain ⟨C, hC⟩ := hU α
  obtain ⟨h1, h2, h3⟩ := triPhase_periodic α
  exact ⟨D, C, fun t p ht => hD _ t p _ h1 h2 h3 fun n => hC t n ht⟩

end OscInt.API.TriangularDecaySanity
