/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.Convert

/-!
# P-Fold: the fold condition in matrix form (core) and C7′

Route: `docs/proof-API2.md`, P-Fold.
-/

namespace OscInt.API

open OscInt.Statements

namespace FoldAux

/-- A continuous linear map on `ℝ × ℝ` through its values on the standard basis. -/
theorem decomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : (ℝ × ℝ) →L[ℝ] F)
    (w : ℝ × ℝ) : L w = w.1 • L (1, 0) + w.2 • L (0, 1) := by
  conv_lhs => rw [show w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) by ext <;> simp]
  rw [map_add, map_smul, map_smul]

/-- A symmetric bilinear form on `ℝ × ℝ` in coordinates. -/
theorem bil (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (v w : ℝ × ℝ) :
    B v w = v.1 * w.1 * B (1, 0) (1, 0) + (v.1 * w.2 + v.2 * w.1) * B (1, 0) (0, 1) +
      v.2 * w.2 * B (0, 1) (0, 1) := by
  rw [decomp B v]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [decomp (B (1, 0)) w, decomp (B (0, 1)) w, hB (0, 1) (1, 0)]
  simp only [smul_eq_mul]
  ring

/-- The matrix of a symmetric bilinear form. -/
theorem mat_eq (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) :
    (Matrix.of fun i j => B (coordVec i) (coordVec j)) =
      !![B (1, 0) (1, 0), B (1, 0) (0, 1); B (1, 0) (0, 1), B (0, 1) (0, 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordVec, hB (0, 1) (1, 0)]

/-- Membership in the kernel of `!![a, b; b, c]`. -/
theorem mem_ker (a b c : ℝ) (x : Fin 2 → ℝ) :
    x ∈ LinearMap.ker (Matrix.toLin' !![a, b; b, c]) ↔ a * x 0 + b * x 1 = 0 ∧ b * x 0 + c * x 1 = 0 := by
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

/-- A kernel that is a line gives rank one. -/
theorem rank_of_ker (M : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → ℝ) (he : e ≠ 0)
    (hker : LinearMap.ker (Matrix.toLin' M) = Submodule.span ℝ {e}) : M.rank = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  rw [hker, finrank_span_singleton he, Module.finrank_fin_fun] at h
  rw [Matrix.rank]
  have : LinearMap.range M.mulVecLin = LinearMap.range (Matrix.toLin' M) := rfl
  rw [this]
  omega

/-- On a line, a cubic-homogeneous function is nonzero off `0` iff it is nonzero at a spanning vector. -/
theorem line_iff (T : (Fin 2 → ℝ) → ℝ) (hT : ∀ (t : ℝ) x, T (t • x) = t ^ 3 * T x)
    (e : Fin 2 → ℝ) (he : e ≠ 0) :
    (∀ x ∈ Submodule.span ℝ {e}, x ≠ 0 → T x ≠ 0) ↔ T e ≠ 0 := by
  constructor
  · intro h
    exact h e (Submodule.mem_span_singleton_self e) he
  · intro h x hx hx0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ht : t ≠ 0 := by rintro rfl; simp at hx0
    rw [hT]
    exact mul_ne_zero (pow_ne_zero 3 ht) h

/-- The kernel of `!![a, b; b, c]` with `ac = b²`, not all zero, is a line. -/
theorem ker_line (a b c : ℝ) (hdet : a * c - b ^ 2 = 0) (hz : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    ∃ e : Fin 2 → ℝ, e ≠ 0 ∧ LinearMap.ker (Matrix.toLin' !![a, b; b, c]) = Submodule.span ℝ {e} := by
  by_cases ha : a = 0
  · have hb : b = 0 := by subst ha; nlinarith [sq_nonneg b]
    have hc : c ≠ 0 := fun hc => hz ⟨ha, hb, hc⟩
    refine ⟨![1, 0], by simp, ?_⟩
    ext x
    rw [mem_ker, Submodule.mem_span_singleton]
    subst ha hb
    constructor
    · rintro ⟨-, h1⟩
      have : x 1 = 0 := by simpa [hc] using h1
      refine ⟨x 0, ?_⟩
      ext i; fin_cases i <;> simp [this]
    · rintro ⟨t, rfl⟩
      simp
  · refine ⟨![-b, a], by simp [ha], ?_⟩
    ext x
    rw [mem_ker, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨h0, -⟩
      refine ⟨x 1 / a, ?_⟩
      ext i; fin_cases i
      · simp; field_simp; linarith
      · simp; field_simp
    · rintro ⟨t, rfl⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
      constructor
      · ring
      · linear_combination t * hdet

/-- The span form on a line: any spanning vector of the line will do. -/
theorem span_iff (T : (Fin 2 → ℝ) → ℝ) (hT : ∀ (t : ℝ) x, T (t • x) = t ^ 3 * T x)
    (e : Fin 2 → ℝ) (he : e ≠ 0) :
    (∃ e' : Fin 2 → ℝ, e' ≠ 0 ∧ Submodule.span ℝ {e} = Submodule.span ℝ {e'} ∧ T e' ≠ 0) ↔ T e ≠ 0 := by
  constructor
  · rintro ⟨e', he', hs, h⟩
    have hmem : e ∈ Submodule.span ℝ {e'} := hs ▸ Submodule.mem_span_singleton_self e
    exact (line_iff T hT e' he').2 h e hmem he
  · intro h
    exact ⟨e, he, rfl, h⟩

/-- The zero matrix has no line as kernel. -/
theorem not_ker_line_zero (e : Fin 2 → ℝ) (he : e ≠ 0) :
    LinearMap.ker (Matrix.toLin' !![(0 : ℝ), 0; 0, 0]) ≠ Submodule.span ℝ {e} := by
  intro h
  have h1 := rank_of_ker _ e he h
  have h0 : !![(0 : ℝ), 0; 0, 0] = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [h0, Matrix.rank_zero] at h1
  exact zero_ne_one h1

/-- The kernel condition `∀ w, B v w = 0` in matrix form. -/
theorem kerB_iff (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (a b c : ℝ)
    (hbil : ∀ v w, B v w = v.1 * w.1 * a + (v.1 * w.2 + v.2 * w.1) * b + v.2 * w.2 * c)
    (x : Fin 2 → ℝ) : (∀ w, B (ofFin2 x) w = 0) ↔ x ∈ LinearMap.ker (Matrix.toLin' !![a, b; b, c]) := by
  rw [mem_ker]
  simp only [hbil, ofFin2]
  constructor
  · intro h
    have h0 := h (1, 0)
    have h1 := h (0, 1)
    simp only [mul_one, mul_zero, add_zero, zero_add] at h0 h1
    constructor <;> linarith
  · rintro ⟨h0, h1⟩ w
    linear_combination w.1 * h0 + w.2 * h1

/-- The left-hand side's kernel clause in matrix form. -/
theorem lhs_iff (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (T : ℝ × ℝ → ℝ) (S : Submodule ℝ (Fin 2 → ℝ))
    (hk : ∀ x : Fin 2 → ℝ, (∀ w, B (ofFin2 x) w = 0) ↔ x ∈ S) :
    (∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0) ↔
      ∀ x ∈ S, x ≠ 0 → T (ofFin2 x) ≠ 0 := by
  constructor
  · intro h x hx hx0
    refine h (ofFin2 x) ?_ ((hk x).2 hx)
    intro h0
    apply hx0
    have e0 : x 0 = 0 := congrArg Prod.fst h0
    have e1 : x 1 = 0 := congrArg Prod.snd h0
    ext i; fin_cases i <;> simp [e0, e1]
  · intro h v hv hBv
    have hx : (![v.1, v.2] : Fin 2 → ℝ) ∈ S := (hk _).1 hBv
    have hx0 : (![v.1, v.2] : Fin 2 → ℝ) ≠ 0 := by
      intro h0
      apply hv
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      simp at e0 e1
      exact Prod.ext e0 e1
    exact h _ hx hx0

end FoldAux

open FoldAux in
/-- The P-Fold core: the fold condition for a symmetric bilinear form `B` and a cubic-homogeneous `T` is the span
form and the rank form for the matrix of `B`. -/
theorem FoldAux.foldCore (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (T : ℝ × ℝ → ℝ) (hB : ∀ v w, B v w = B w v)
    (hT : ∀ (c : ℝ) v, T (c • v) = c ^ 3 * T v) :
    ((B (1, 0) (1, 0) * B (0, 1) (0, 1) - B (1, 0) (0, 1) ^ 2 ≠ 0 ∨
        ((∃ v w, B v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0)) ↔
      FoldCondSpan (Matrix.of fun i j => B (coordVec i) (coordVec j)) (fun e => T (ofFin2 e))) ∧
    ((B (1, 0) (1, 0) * B (0, 1) (0, 1) - B (1, 0) (0, 1) ^ 2 ≠ 0 ∨
        ((∃ v w, B v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0)) ↔
      FoldCondRank (Matrix.of fun i j => B (coordVec i) (coordVec j)) (fun e => T (ofFin2 e))) := by
  have hbil := bil B hB
  rw [mat_eq B hB]
  generalize B (1, 0) (1, 0) = a at hbil ⊢
  generalize B (1, 0) (0, 1) = b at hbil ⊢
  generalize B (0, 1) (0, 1) = c at hbil ⊢
  have hdetM : (!![a, b; b, c]).det = a * c - b ^ 2 := by rw [Matrix.det_fin_two_of]; ring
  have hTe : ∀ (t : ℝ) (x : Fin 2 → ℝ), T (ofFin2 (t • x)) = t ^ 3 * T (ofFin2 x) :=
    fun t x => hT t (ofFin2 x)
  unfold FoldCondSpan FoldCondRank
  rw [hdetM, lhs_iff B T _ (kerB_iff B a b c hbil)]
  by_cases h0 : a * c - b ^ 2 = 0
  swap
  · simp only [ne_eq, h0, not_false_eq_true, true_or, and_self]
  by_cases hz : a = 0 ∧ b = 0 ∧ c = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hz
    have hB0 : ¬ ∃ v w, B v w ≠ 0 := by
      push Not; intro v w; rw [hbil]; ring
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rintro (h | ⟨h, -⟩)
      · exact absurd h0 h
      · exact absurd h hB0
    · rintro (h | ⟨e, he, hk, -⟩)
      · exact absurd h0 h
      · exact absurd hk (not_ker_line_zero e he)
    · rintro (h | ⟨h, -⟩)
      · exact absurd h0 h
      · exact absurd h hB0
    · rintro (h | ⟨h, -⟩)
      · exact absurd h0 h
      · have h00 : !![(0 : ℝ), 0; 0, 0] = 0 := by
          ext i j; fin_cases i <;> fin_cases j <;> rfl
        rw [h00, Matrix.rank_zero] at h
        exact (zero_ne_one h).elim
  · obtain ⟨e, he, hker⟩ := ker_line a b c h0 hz
    have hB0 : ∃ v w, B v w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hz
      refine ⟨?_, ?_, ?_⟩
      · simpa [hbil] using hcon (1, 0) (1, 0)
      · simpa [hbil] using hcon (1, 0) (0, 1)
      · simpa [hbil] using hcon (0, 1) (0, 1)
    rw [rank_of_ker _ e he hker, hker, line_iff _ hTe e he, span_iff _ hTe e he]
    simp only [h0, ne_eq, not_true_eq_false, false_or, hB0, true_and, and_self]

namespace FoldAux

/-- Second derivatives from derivative data: `dd Ψ y v w = D₂ y w v`. -/
theorem dd_of_hasFDeriv (Ψ : ℝ × ℝ → ℝ) (D₁ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (D₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (hΨ : ∀ y, HasFDerivAt Ψ (D₁ y) y)
    (hD₁ : ∀ y, HasFDerivAt D₁ (D₂ y) y) (y v w : ℝ × ℝ) : dd Ψ y v w = D₂ y w v := by
  have hf : fderiv ℝ Ψ = D₁ := funext fun y => (hΨ y).fderiv
  have h := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt (x := D₁ y)).comp y (hD₁ y)
  simp only [dd, hf]
  rw [show (fun y => D₁ y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ D₁ from rfl, h.fderiv]
  rfl

/-- Third derivatives from derivative data: `ddd Ψ k u v w = D₃ w v u`. -/
theorem ddd_of_hasFDeriv (Ψ : ℝ × ℝ → ℝ) (D₁ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (D₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ)
    (D₃ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (k : ℝ × ℝ)
    (hΨ : ∀ y, HasFDerivAt Ψ (D₁ y) y) (hD₁ : ∀ y, HasFDerivAt D₁ (D₂ y) y) (hD₂ : HasFDerivAt D₂ D₃ k)
    (u v w : ℝ × ℝ) : ddd Ψ k u v w = D₃ w v u := by
  have hfun : (fun y => dd Ψ y u v) = fun y => D₂ y v u :=
    funext fun y => dd_of_hasFDeriv Ψ D₁ D₂ hΨ hD₁ y u v
  have h := (hD₂.clm_apply (hasFDerivAt_const v k)).clm_apply (hasFDerivAt_const u k)
  simp only [ddd, hfun, h.fderiv]
  simp

end FoldAux

open FoldAux in
/-- **C7′** `FoldOrNondeg` from derivative data, by the core with `B = D₂ k` and `T v = D₃ v v v`. -/
theorem foldOrNondeg_of_hasFDeriv : FoldOrNondegOfHasFDerivStatement := by
  intro Ψ D₁ D₂ D₃ k hΨ hD₁ hD₂
  have hsymm : ∀ v w, D₂ k v w = D₂ k w v := second_derivative_symmetric hΨ (hD₁ k)
  have hdd : ∀ v w, dd Ψ k v w = D₂ k v w := fun v w => by
    rw [dd_of_hasFDeriv Ψ D₁ D₂ hΨ hD₁, hsymm]
  have hddd : ∀ v, ddd Ψ k v v v = D₃ v v v := fun v => ddd_of_hasFDeriv Ψ D₁ D₂ D₃ k hΨ hD₁ hD₂ v v v
  have hT : ∀ (c : ℝ) (v : ℝ × ℝ), D₃ (c • v) (c • v) (c • v) = c ^ 3 * D₃ v v v := by
    intro c v
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have := (foldCore (D₂ k) (fun v => D₃ v v v) hsymm hT).1
  simp only [FoldOrNondeg, hessDet, hdd, hddd]
  exact this

end OscInt.API
