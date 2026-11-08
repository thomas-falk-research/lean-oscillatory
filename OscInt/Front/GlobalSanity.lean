/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

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
open scoped ContDiff

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

/-- The zero matrix satisfies no fold condition: its kernel is the whole plane, not a line. -/
theorem not_foldCondSpan_zero (T : (Fin 2 → ℝ) → ℝ) : ¬ FoldCondSpan (0 : Matrix (Fin 2) (Fin 2) ℝ) T := by
  rintro (h | ⟨e, -, hker, -⟩)
  · simp at h
  · have h1 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ Submodule.span ℝ {e} := by rw [← hker]; simp
    have h2 : (Pi.single 1 1 : Fin 2 → ℝ) ∈ Submodule.span ℝ {e} := by rw [← hker]; simp
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h2
    have ha0 := congrFun ha 0; have ha1 := congrFun ha 1; have hb1 := congrFun hb 1
    simp at ha0 ha1 hb1
    rcases ha1 with h | h
    · rw [h, zero_mul] at ha0; exact absurd ha0 (by norm_num)
    · rw [h, mul_zero] at hb1; exact absurd hb1 (by norm_num)

/-- Bite: `E` is not fold-or-nondegenerate at the origin (zero Hessian). -/
theorem not_foldOrNondegMatrix_ell_zero : ¬ FoldOrNondegMatrix ellPhase 0 := by
  unfold FoldOrNondegMatrix
  rw [show hessianMatrix ellPhase 0 = 0 by rw [hessian_ell]; ext i j; fin_cases i <;> fin_cases j <;> simp]
  exact not_foldCondSpan_zero _

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

/-- `L₁ = 3·fst`: the critical points of `E + L₁` solve `3x² − 3y² + 3 = 0`, `xy = 0`, so they are `(0, ±1)`, both
nondegenerate. -/
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

/-! ## The hyperbolic umbilic `x³ + y³`: fold lines on the axes (pre-proof referee A, m1) -/

/-- `H = x³ + y³`. -/
noncomputable def hypPhase : ℝ × ℝ → ℝ := genCubic 1 0 0 1

theorem hessian_hyp (k : ℝ × ℝ) : hessianMatrix hypPhase k = !![6 * k.1, 0; 0, 6 * k.2] := by
  unfold hypPhase
  have h := iteratedFDeriv_two_eq_dd (f := genCubic 1 0 0 1) ((genCubic_contDiff 1 0 0 1).of_le (by norm_num)) k
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, dd_genCubic, coordVec] <;> ring_nf <;> simp

theorem third_hyp (k : ℝ × ℝ) (e : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 3 hypPhase k ![ofFin2 e, ofFin2 e, ofFin2 e] = 6 * e 0 ^ 3 + 6 * e 1 ^ 3 := by
  unfold hypPhase
  rw [iteratedFDeriv_three_diag ((genCubic_contDiff 1 0 0 1).of_le (by norm_num)), ddd_genCubic]
  simp [ofFin2]; ring

/-- The kernel of `diag(a, b)` with `a = 0 ≠ b` is the first axis. -/
theorem ker_diag_left (b : ℝ) (hb : b ≠ 0) :
    LinearMap.ker (Matrix.toLin' !![(0 : ℝ), 0; 0, b]) = Submodule.span ℝ {(![1, 0] : Fin 2 → ℝ)} := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp [h1.resolve_left hb]
  · rintro ⟨a, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The kernel of `diag(a, b)` with `a ≠ 0 = b` is the second axis. -/
theorem ker_diag_right (a : ℝ) (ha : a ≠ 0) :
    LinearMap.ker (Matrix.toLin' !![a, 0; 0, (0 : ℝ)]) = Submodule.span ℝ {(![0, 1] : Fin 2 → ℝ)} := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨v 1, ?_⟩
    ext i; fin_cases i <;> simp [h0.resolve_left ha]
  · rintro ⟨a, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Off the origin `x³ + y³` is nondegenerate (`xy ≠ 0`) or a fold (on the axes). -/
theorem hyp_foldOrNondeg (k : ℝ × ℝ) (hk : k ≠ 0) : FoldOrNondegMatrix hypPhase k := by
  unfold FoldOrNondegMatrix FoldCondSpan
  rw [hessian_hyp]
  simp only [third_hyp]
  by_cases h1 : k.1 = 0
  · have h2 : k.2 ≠ 0 := fun h2 => hk (Prod.ext h1 h2)
    right
    refine ⟨![1, 0], by simp, ?_, by norm_num⟩
    rw [h1, mul_zero]; exact ker_diag_left _ (mul_ne_zero (by norm_num) h2)
  · by_cases h2 : k.2 = 0
    · right
      refine ⟨![0, 1], by simp, ?_, by norm_num⟩
      rw [h2, mul_zero]; exact ker_diag_right _ (mul_ne_zero (by norm_num) h1)
    · left
      rw [Matrix.det_fin_two]; simp
      exact ⟨h1, h2⟩

/-- Bite: `x³ + y³` is degenerate (not nondegenerate) on the axes: `det H = 0` at `(0, 1/2)`. -/
theorem hyp_det_zero_axis : (hessianMatrix hypPhase (0, 1 / 2)).det = 0 := by
  rw [hessian_hyp, Matrix.det_fin_two]; simp

theorem hyp_isD4 : IsD4Point hypPhase 0 := by
  refine ⟨?_, 1, 0, 0, 1, ?_, ?_⟩
  · unfold hypPhase; exact iteratedFDeriv_two_genCubic_zero 1 0 0 1
  · intro x y; unfold hypPhase; exact third_genCubic 1 0 0 1 x y
  · rw [Cubic.discr]; norm_num

theorem hyp_classified : Classified hypPhase (Metric.closedBall 0 1) {0} :=
  ⟨fun k _ hk => hyp_foldOrNondeg k (by simpa using hk), fun k₀ hk₀ => by
    rw [Finset.mem_singleton] at hk₀; subst hk₀; exact hyp_isD4⟩

/-- **GD through the statement constant, with fold points.** `Ψ = x³ + y³` (hyperbolic umbilic, `discr = −27`),
`K = B̄(0, 1)`, `U = B(0, 2)` (so `↑D ⊆ U` and `K ⊆ U` are not discharged by `univ`), `D = {0}`. Plants detected
(recorded): `FoldOrNondegMatrix ↦ det ≠ 0` in `Classified` (fails on the axes, `hyp_det_zero_axis`). -/
theorem globalDecay_hyp (h : GlobalDecayStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (hypPhase k + L k)) * Complex.I) * A k‖ ≤
        C * M * m ^ (-(2 : ℝ) / 3) :=
  h hypPhase (Metric.closedBall 0 1) (Metric.ball 0 2) {0} (isCompact_closedBall _ _) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by norm_num)) (by simp)
    (genCubic_contDiff 1 0 0 1).contDiffOn hyp_classified

/-- **GD-C through the statement constant, with fold points**: same data, `K′ = {0}` (the origin is critical). -/
theorem globalDecayCrit_hyp (h : GlobalDecayCritStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ ({0} : Set ((ℝ × ℝ) →L[ℝ] ℝ)) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (hypPhase k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3) :=
  h hypPhase (Metric.closedBall 0 1) (Metric.ball 0 2) {0} {0} (isCompact_closedBall _ _) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by norm_num)) (by simp) isCompact_singleton
    (genCubic_contDiff 1 0 0 1).contDiffOn
    ⟨fun _ _ k _ hk _ => hyp_foldOrNondeg k (by simpa using hk), hyp_classified.2⟩

/-- On `K = B̄((3/4, 3/4), 1/4)` (the square `[1/2, 1]²`) `x³ + y³` is nondegenerate; the D4 point `0` lies in
`U = B(0, 2)` but not in `K`. -/
theorem hyp_classified_offK : Classified hypPhase (Metric.closedBall (3 / 4, 3 / 4) (1 / 4)) {0} := by
  refine ⟨fun k hk _ => ?_, hyp_classified.2⟩
  have hk' := hk
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le] at hk'
  left
  rw [hessian_hyp, Matrix.det_fin_two]; simp
  constructor <;> linarith [hk'.1.1, hk'.2.1]

theorem zero_not_mem_offK : (0 : ℝ × ℝ) ∉ Metric.closedBall ((3 : ℝ) / 4, (3 : ℝ) / 4) (1 / 4) := by
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]; norm_num [Real.dist_eq, abs_of_neg]

/-- **GD through the statement constant, D4 point outside `K`.** Plants detected (recorded): `↑D ⊆ U ↦ ↑D ⊆ K`
(`zero_not_mem_offK`) — pre-proof referee A, m3. -/
theorem globalDecay_hyp_offK (h : GlobalDecayStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall (3 / 4, 3 / 4) (1 / 4) →
      (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (hypPhase k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3) :=
  h hypPhase (Metric.closedBall (3 / 4, 3 / 4) (1 / 4)) (Metric.ball 0 2) {0} (isCompact_closedBall _ _)
    Metric.isOpen_ball (fun k hk => by
      rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le] at hk
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hk.1.1, hk.1.2, hk.2.1, hk.2.2])
    (by simp) (genCubic_contDiff 1 0 0 1).contDiffOn hyp_classified_offK

/-! ## Critical points only (pre-proof referee B, m1) and a D4 point away from the origin (B, m2) -/

/-- `L₃ = −3 fst − 3 snd`: the critical points of `x³ + y³ + L₃` are `(±1, ±1)`, all nondegenerate, while
`0 ∈ B̄(0, 2)` is degenerate and not a fold (so the pointwise classification fails there). -/
noncomputable def L₃ : (ℝ × ℝ) →L[ℝ] ℝ := (-3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (-3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hyp_crit_nondeg (k : ℝ × ℝ) (hc : fderiv ℝ hypPhase k + L₃ = 0) : (hessianMatrix hypPhase k).det ≠ 0 := by
  have h1 := congrArg (fun f => f (1, 0)) hc
  have h2 := congrArg (fun f => f (0, 1)) hc
  simp only [hypPhase, add_apply, fd_genCubic, L₃, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, zero_apply] at h1 h2
  have hx : k.1 ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  have hy : k.2 ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  rw [hessian_hyp, Matrix.det_fin_two]; simp; exact ⟨hx, hy⟩

/-- Bite: `0` is not fold-or-nondegenerate for `x³ + y³` (zero Hessian). -/
theorem not_foldOrNondegMatrix_hyp_zero : ¬ FoldOrNondegMatrix hypPhase 0 := by
  unfold FoldOrNondegMatrix
  rw [show hessianMatrix hypPhase 0 = 0 by rw [hessian_hyp]; ext i j; fin_cases i <;> fin_cases j <;> simp]
  exact not_foldCondSpan_zero _

/-- **GD-C through the statement constant, critical points only.** `Ψ = x³ + y³`, `K = B̄(0, 2)`, `U = ℝ²`,
`K′ = {L₃}`, `D = ∅`: the classification holds at the critical points `(±1, ±1)` but not pointwise (`0 ∈ K`,
`not_foldOrNondegMatrix_hyp_zero`). Plants detected (recorded): dropping `fderiv ℝ Ψ k + L = 0 →` in
`ClassifiedCrit`. -/
theorem globalDecayCrit_hyp_crit (h : GlobalDecayCritStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      L ∈ ({L₃} : Set ((ℝ × ℝ) →L[ℝ] ℝ)) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (hypPhase k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3) :=
  h hypPhase (Metric.closedBall 0 2) Set.univ {L₃} ∅ (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (by simp) isCompact_singleton (genCubic_contDiff 1 0 0 1).contDiffOn
    ⟨fun L hL k _ _ hc => by
      rw [Set.mem_singleton_iff] at hL; subst hL; exact Or.inl (hyp_crit_nondeg k hc), by simp⟩

/-- `x³ + y³` moved to `(1, 1)`: `Ψ(k) = (k₁ − 1)³ + (k₂ − 1)³`, written as `hypPhase (k + (−1, −1))`. -/
noncomputable def hypShift (k : ℝ × ℝ) : ℝ := hypPhase (k + (-1, -1))

theorem hessian_hypShift (k : ℝ × ℝ) : hessianMatrix hypShift k = hessianMatrix hypPhase (k + (-1, -1)) := by
  unfold hessianMatrix hypShift; rw [iteratedFDeriv_comp_add_right]

theorem foldOrNondegMatrix_hypShift (k : ℝ × ℝ) :
    FoldOrNondegMatrix hypShift k ↔ FoldOrNondegMatrix hypPhase (k + (-1, -1)) := by
  unfold FoldOrNondegMatrix; rw [hessian_hypShift]; unfold hypShift; rw [iteratedFDeriv_comp_add_right]

theorem hypShift_isD4 : IsD4Point hypShift (1, 1) := by
  have h0 : ((1, 1) : ℝ × ℝ) + (-1, -1) = 0 := by ext <;> norm_num
  obtain ⟨h2, a, b, c, d, h3, hd⟩ := hyp_isD4
  refine ⟨?_, a, b, c, d, fun x y => ?_, hd⟩
  · unfold hypShift; rw [iteratedFDeriv_comp_add_right, h0]; exact h2
  · unfold hypShift; rw [iteratedFDeriv_comp_add_right, h0]; exact h3 x y

/-- Bite for a plant evaluating `IsD4Point`'s derivatives at `0` instead of `k₀`: the Hessian of `hypShift` at `0`
is `diag(−6, −6) ≠ 0`. -/
theorem hypShift_hessian_zero_ne : hessianMatrix hypShift 0 ≠ 0 := by
  rw [hessian_hypShift, hessian_hyp]; intro h
  have := congrFun (congrFun h 0) 0; simp at this

/-- **GD through the statement constant, D4 point at `(1, 1)`.** `Ψ = hypShift`, `K = B̄((1, 1), 1)`, `U = ℝ²`,
`D = {(1, 1)}`. Plants detected (recorded): `IsD4Point Ψ k₀ ↦ IsD4Point Ψ 0`-type plants (Hessian at `0` instead of
`k₀`, `hypShift_hessian_zero_ne`). -/
theorem globalDecay_hypShift (h : GlobalDecayStatement) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall (1, 1) 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (hypShift k + L k)) * Complex.I) * A k‖ ≤
        C * M * m ^ (-(2 : ℝ) / 3) :=
  h hypShift (Metric.closedBall (1, 1) 1) Set.univ {(1, 1)} (isCompact_closedBall _ _) isOpen_univ
    (Set.subset_univ _) (Set.subset_univ _)
    ((genCubic_contDiff 1 0 0 1).comp (contDiff_id.add contDiff_const)).contDiffOn
    ⟨fun k _ hk => (foldOrNondegMatrix_hypShift k).2 (hyp_foldOrNondeg _ (by
        intro h0; apply hk; rw [Finset.mem_singleton]
        have := congrArg (· + ((1 : ℝ), (1 : ℝ))) h0; simp only [zero_add] at this
        rw [← this]; ext <;> simp)),
      fun k₀ hk₀ => by rw [Finset.mem_singleton] at hk₀; subst hk₀; exact hypShift_isD4⟩

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
The smoothness and support conjuncts are kept in the conclusion (adversarial review b1: weakening them to
`Continuous η` or to `closedBall 0 400` is then detected). Plants detected: the period `2π ↦ π` (then `e^{ik₁}` is not admissible: `e^{i(k₁ + π)} = −e^{ik₁}`, so the discharge of
the period hypothesis fails); `torusBox ↦ [0, π]²` is detected by `integral_one_torusBox` only through the constant
`(2π)²` in the conclusion. Not detected: weakening plants (e.g. `Continuous g` dropped). -/
theorem torusUnfold_moments (h : TorusUnfoldStatement) :
    ∃ η : ℝ × ℝ → ℝ, ContDiff ℝ ∞ η ∧ tsupport η ⊆ Metric.closedBall 0 4 ∧
      ∫ k : ℝ × ℝ, (η k : ℂ) * 1 = ((2 * Real.pi) ^ 2 : ℝ) ∧
      ∫ k : ℝ × ℝ, (η k : ℂ) * Complex.exp (↑(k.1) * Complex.I) = 0 := by
  obtain ⟨η, hs, hsupp, hη⟩ := h
  refine ⟨η, hs, hsupp, ?_, ?_⟩
  · rw [← hη (fun _ => 1) continuous_const (fun _ => rfl) (fun _ => rfl), integral_one_torusBox]
  · have h0 := latticeKernel_zero_one
    rw [latticeKernel] at h0
    simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero, zero_add] at h0
    rw [← hη (fun k : ℝ × ℝ => Complex.exp (↑(k.1) * Complex.I)) (by fun_prop) (fun k => ?_) (fun _ => rfl), h0]
    have : Complex.exp (↑(k.1 + 2 * Real.pi) * Complex.I) = Complex.exp (↑k.1 * Complex.I) * 1 := by
      rw [← Complex.exp_two_pi_mul_I, ← Complex.exp_add]; congr 1; push_cast; ring
    simpa using this

/-- **T6 through the statement constant**, on the diagonal `x = (n, n)` at time `n ≥ 1` (where T6L shows the rate is
attained). Plants detected: the rate weakened (`-(2/3) ↦ -(1/2)`); the uniformity over `x` restricted so that it misses the
diagonal (e.g. `x = 0` only). Not detected: a restriction to the diagonal itself; a strengthened rate (false by T6L and SH, `latticeLaplacian_sharp`, but not a discharge failure). -/
theorem latticeLaplacianDecay_diag (h : LatticeLaplacianDecayStatement) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖latticeKernel n ((n : ℤ), (n : ℤ))‖ ≤ C * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun n hn => hC n _ (by exact_mod_cast hn)⟩

/-! ## T6, T6L and SH together: the rate `t^{-2/3}` cannot be improved -/

theorem d4ClosedConstant_lattice_pos : 0 < d4ClosedConstant (-1 / 48) := by
  unfold d4ClosedConstant
  rw [ite_eq_left_iff.mpr (fun h => absurd (by norm_num : (-1 / 48 : ℝ) < 0) h)]
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

/-- **T6L and SH through the constants, every faster rate** (adversarial review d1): if the diagonal limit holds, no
bound `C t^{-σ′}` uniform in `x` holds for any `σ′ > 2/3`. -/
theorem latticeLaplacian_sharp_all (hS : SharpnessStatement) (hL : LatticeLaplacianLimitStatement) :
    ∀ σ' > (2 : ℝ) / 3, ¬ ∃ C : ℝ, ∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t → ‖latticeKernel t x‖ ≤ C * t ^ (-σ') := by
  intro σ' hσ ⟨C, hC⟩
  have hL' : Tendsto (fun n : ℕ => (((n : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ n * latticeKernel n ((n : ℤ), (n : ℤ)))) atTop (𝓝 (d4ClosedConstant (-1 / 48) : ℂ)) := by
    unfold LatticeLaplacianLimitStatement at hL
    simpa only [mul_assoc] using hL
  obtain ⟨-, h2⟩ := hS.2 _ _ _ hL' (by exact_mod_cast d4ClosedConstant_lattice_pos.ne')
  refine h2 σ' hσ ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hC n ((n : ℤ), (n : ℤ)) (by exact_mod_cast hn)

end OscInt.API.GlobalSanity
