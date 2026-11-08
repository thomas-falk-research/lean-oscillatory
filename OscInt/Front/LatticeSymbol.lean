/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.GlobalSanity
import Blueprint.Global

/-!
# GD-P3: the lattice symbol `cos k₁ + cos k₂` (route R7) and the diagonal phase data (route R9)

* `latticeSymbolFacts : Blueprint.GD.LatticeSymbolFacts`: on `B̄(0, 4)` the symbol is nondegenerate or a fold off
  `latticeD4`, and the four points `(±π/2, ±π/2)` are D4 points.
* `diagPhaseFacts : Blueprint.GD.DiagPhaseFacts`: the translated phase `−sin κ₁ − sin κ₂ + κ₁ + κ₂`.
* `fderiv_latticeSymbol`: the derivative of the symbol.

All derivatives go through one separable-phase lemma (`Ψ k = g k.1 + h k.2`), applied three times.
-/

namespace OscInt.API.LatticeSymbolAux

open OscInt.Statements OscInt.API.ConvertSanity OscInt.API.GlobalSanity

/-- The derivative of a separable phase `g k.1 + h k.2`. -/
theorem fderiv_sep {g h g' h' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hh : ∀ x, HasDerivAt h (h' x) x)
    (y v : ℝ × ℝ) : fderiv ℝ (fun k : ℝ × ℝ => g k.1 + h k.2) y v = g' y.1 * v.1 + h' y.2 * v.2 := by
  have H : HasFDerivAt (fun k : ℝ × ℝ => g k.1 + h k.2)
      (g' y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + h' y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    ((hg y.1).comp_hasFDerivAt y (hasFDerivAt_fst (𝕜 := ℝ) (p := y))).add
      ((hh y.2).comp_hasFDerivAt y (hasFDerivAt_snd (𝕜 := ℝ) (p := y)))
  rw [H.fderiv]; simp

/-- Second derivative of a separable phase. -/
theorem dd_sep {g h g' h' g'' h'' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hh : ∀ x, HasDerivAt h (h' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hh' : ∀ x, HasDerivAt h' (h'' x) x) (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => g k.1 + h k.2) y v w = g'' y.1 * v.1 * w.1 + h'' y.2 * v.2 * w.2 := by
  have e : (fun z : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => g k.1 + h k.2) z v) =
      fun z => (fun x => g' x * v.1) z.1 + (fun x => h' x * v.2) z.2 := by
    funext z; exact fderiv_sep hg hh z v
  rw [dd, e, fderiv_sep (fun x => (hg' x).mul_const v.1) (fun x => (hh' x).mul_const v.2)]

/-- Third derivative of a separable phase. -/
theorem ddd_sep {g h g' h' g'' h'' g''' h''' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hh : ∀ x, HasDerivAt h (h' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hh' : ∀ x, HasDerivAt h' (h'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x) (hh'' : ∀ x, HasDerivAt h'' (h''' x) x) (y u v w : ℝ × ℝ) :
    ddd (fun k : ℝ × ℝ => g k.1 + h k.2) y u v w =
      g''' y.1 * u.1 * v.1 * w.1 + h''' y.2 * u.2 * v.2 * w.2 := by
  have e : (fun z : ℝ × ℝ => dd (fun k : ℝ × ℝ => g k.1 + h k.2) z u v) =
      fun z => (fun x => g'' x * (u.1 * v.1)) z.1 + (fun x => h'' x * (u.2 * v.2)) z.2 := by
    funext z; rw [dd_sep hg hh hg' hh']; ring
  rw [ddd, e, fderiv_sep (fun x => (hg'' x).mul_const _) (fun x => (hh'' x).mul_const _)]; ring

/-- The lattice symbol. -/
noncomputable def ω : ℝ × ℝ → ℝ := fun k => Real.cos k.1 + Real.cos k.2

theorem hd_cos : ∀ x, HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos

theorem hd_negsin : ∀ x, HasDerivAt (fun x => -Real.sin x) (-Real.cos x) x :=
  fun x => (Real.hasDerivAt_sin x).neg

theorem hd_negcos : ∀ x, HasDerivAt (fun x => -Real.cos x) (Real.sin x) x :=
  fun x => by
    have := (Real.hasDerivAt_cos x).neg
    rw [neg_neg] at this
    exact this

theorem fderiv_ω (y v : ℝ × ℝ) : fderiv ℝ ω y v = -Real.sin y.1 * v.1 - Real.sin y.2 * v.2 := by
  unfold ω; rw [fderiv_sep hd_cos hd_cos]; ring

theorem dd_ω (y v w : ℝ × ℝ) : dd ω y v w = -Real.cos y.1 * v.1 * w.1 - Real.cos y.2 * v.2 * w.2 := by
  unfold ω; rw [dd_sep hd_cos hd_cos hd_negsin hd_negsin]; ring

theorem ddd_ω (y u v w : ℝ × ℝ) :
    ddd ω y u v w = Real.sin y.1 * u.1 * v.1 * w.1 + Real.sin y.2 * u.2 * v.2 * w.2 := by
  unfold ω; rw [ddd_sep hd_cos hd_cos hd_negsin hd_negsin hd_negcos hd_negcos]

theorem ω_contDiff : ContDiff ℝ 3 ω := by unfold ω; fun_prop

theorem hessian_ω (y : ℝ × ℝ) : hessianMatrix ω y = !![-Real.cos y.1, 0; 0, -Real.cos y.2] := by
  have h := iteratedFDeriv_two_eq_dd (ω_contDiff.of_le (by norm_num)) y
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessianMatrix, h, dd_ω, coordVec]

theorem third_ω (y : ℝ × ℝ) (e : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 3 ω y ![ofFin2 e, ofFin2 e, ofFin2 e] =
      Real.sin y.1 * e 0 ^ 3 + Real.sin y.2 * e 1 ^ 3 := by
  rw [iteratedFDeriv_three_diag ω_contDiff, ddd_ω]; simp [ofFin2]; ring

theorem sin_ne_zero_of_cos_eq_zero {x : ℝ} (h : Real.cos x = 0) : Real.sin x ≠ 0 := by
  intro hs
  have := Real.sin_sq_add_cos_sq x
  rw [h, hs] at this; norm_num at this

/-- In `[−4, 4]`, `cos x = 0` only at `±π/2`. -/
theorem cos_eq_zero_bounded {x : ℝ} (hx : |x| ≤ 4) (h : Real.cos x = 0) :
    x = Real.pi / 2 ∨ x = -(Real.pi / 2) := by
  obtain ⟨n, rfl⟩ := Real.cos_eq_zero_iff.mp h
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have hp := Real.pi_gt_three
  have a1 : (n : ℝ) < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have a2 : (-2 : ℝ) < n := by
    by_contra hc; push Not at hc; nlinarith
  have b1 : n < 1 := by exact_mod_cast a1
  have b2 : -2 < n := by exact_mod_cast a2
  rcases (show n = 0 ∨ n = -1 by omega) with rfl | rfl
  · left; simp
  · right; push_cast; ring

theorem isD4_ω (y : ℝ × ℝ) (h1 : Real.cos y.1 = 0) (h2 : Real.cos y.2 = 0) : IsD4Point ω y := by
  refine ⟨?_, Real.sin y.1 / 6, 0, 0, Real.sin y.2 / 6, ?_, ?_⟩
  · ext m
    have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
    rw [hm, iteratedFDeriv_two_eq_dd (ω_contDiff.of_le (by norm_num)), dd_ω, h1, h2]
    simp
  · intro x z
    rw [iteratedFDeriv_three_diag ω_contDiff, ddd_ω]; ring
  · have s1 := sin_ne_zero_of_cos_eq_zero h1
    have s2 := sin_ne_zero_of_cos_eq_zero h2
    rw [Cubic.discr]
    have : (Real.sin y.1 / 6) ^ 2 * (Real.sin y.2 / 6) ^ 2 ≠ 0 := by positivity
    intro hc; apply this; linarith

theorem foldOrNondeg_ω (y : ℝ × ℝ) (h : ¬ (Real.cos y.1 = 0 ∧ Real.cos y.2 = 0)) : FoldOrNondegMatrix ω y := by
  unfold FoldOrNondegMatrix FoldCondSpan
  rw [hessian_ω]
  simp only [third_ω]
  by_cases h1 : Real.cos y.1 = 0
  · have h2 : Real.cos y.2 ≠ 0 := fun h2 => h ⟨h1, h2⟩
    right
    refine ⟨![1, 0], by simp, ?_, by simpa using sin_ne_zero_of_cos_eq_zero h1⟩
    rw [h1, neg_zero]; exact ker_diag_left _ (neg_ne_zero.mpr h2)
  · by_cases h2 : Real.cos y.2 = 0
    · right
      refine ⟨![0, 1], by simp, ?_, by simpa using sin_ne_zero_of_cos_eq_zero h2⟩
      rw [h2, neg_zero]; exact ker_diag_right _ (neg_ne_zero.mpr h1)
    · left
      rw [Matrix.det_fin_two]; simp
      exact ⟨h1, h2⟩

/-- The translated diagonal phase of R9, in separable form. -/
noncomputable def φ : ℝ × ℝ → ℝ := fun κ => (fun x => -Real.sin x + x) κ.1 + (fun x => -Real.sin x + x) κ.2

theorem φ_eq : (fun κ : ℝ × ℝ => -Real.sin κ.1 - Real.sin κ.2 + κ.1 + κ.2) = φ := by
  funext κ; simp only [φ]; ring

theorem hd_φ₀ : ∀ x, HasDerivAt (fun x => -Real.sin x + x) (-Real.cos x + 1) x :=
  fun x => (Real.hasDerivAt_sin x).neg.add (hasDerivAt_id x)

theorem hd_φ₁ : ∀ x, HasDerivAt (fun x => -Real.cos x + 1) (Real.sin x) x :=
  fun x => by simpa using (Real.hasDerivAt_cos x).neg.add_const 1

theorem hd_φ₂ : ∀ x, HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin

end OscInt.API.LatticeSymbolAux

namespace OscInt.API.LatticeSymbol

open OscInt.Statements OscInt.Blueprint.GD OscInt.API.LatticeSymbolAux

/-- The derivative of the lattice symbol. -/
theorem fderiv_latticeSymbol (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2) y v = -Real.sin y.1 * v.1 - Real.sin y.2 * v.2 :=
  fderiv_ω y v

/-- **R7.** The lattice symbol is classified on `B̄(0, 4)` with exceptional set `latticeD4`. -/
theorem latticeSymbolFacts : LatticeSymbolFacts := by
  show Classified ω (Metric.closedBall 0 4) latticeD4
  refine ⟨fun k hk hkD => foldOrNondeg_ω k ?_, fun k₀ hk₀ => ?_⟩
  · rintro ⟨h1, h2⟩
    rw [mem_closedBall_zero_iff] at hk
    have a1 : |k.1| ≤ 4 := (norm_fst_le k).trans hk
    have a2 : |k.2| ≤ 4 := (norm_snd_le k).trans hk
    apply hkD
    rcases cos_eq_zero_bounded a1 h1 with e1 | e1 <;> rcases cos_eq_zero_bounded a2 h2 with e2 | e2 <;>
      · have : k = (k.1, k.2) := rfl
        rw [this, e1, e2]; simp [latticeD4]
  · apply isD4_ω
    · simp only [latticeD4, Finset.mem_insert, Finset.mem_singleton] at hk₀
      rcases hk₀ with rfl | rfl | rfl | rfl <;> simp
    · simp only [latticeD4, Finset.mem_insert, Finset.mem_singleton] at hk₀
      rcases hk₀ with rfl | rfl | rfl | rfl <;> simp

/-- **R9 data.** The translated diagonal phase `−sin κ₁ − sin κ₂ + κ₁ + κ₂`. -/
theorem diagPhaseFacts : DiagPhaseFacts := by
  unfold DiagPhaseFacts
  dsimp only
  rw [φ_eq]
  refine ⟨by unfold φ; fun_prop, by simp, ?_, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    unfold φ; rw [fderiv_sep hd_φ₀ hd_φ₀]; simp
  · intro v w; unfold φ; rw [dd_sep hd_φ₀ hd_φ₀ hd_φ₁ hd_φ₁]; simp
  · unfold cubicCoeffs φ
    simp only [ddd_sep hd_φ₀ hd_φ₀ hd_φ₁ hd_φ₁ hd_φ₂ hd_φ₂]
    norm_num [disc]
  · intro κ
    simp only [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

end OscInt.API.LatticeSymbol
