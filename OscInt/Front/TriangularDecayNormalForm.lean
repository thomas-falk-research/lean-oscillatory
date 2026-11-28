/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.StationaryPhase.Change
import OscInt.StationaryPhase.Local
import OscInt.Front.TriangularDecaySanity

/-!
# Batch K2, parts P11 and P12: exact product normal forms (under P9)

Route: `docs/proof-K2.md`, section 5 ("P11", "P12"), with section 8, items 3 and 4 (N3, N5); section 8
supersedes the cutoff of section 5. Blueprint: `Blueprint/TriangularDecay.lean`.

* `OscInt.K2.productNormalForm (hP9 : ParamIntegralSmoothFacts) : ProductNormalFormFacts`.
* `OscInt.K2.squareNormalForm (hP9 : ParamIntegralSmoothFacts) : SquareNormalFormFacts`.

P9 is used only as the hypothesis `hP9`, with one-variable remainders composed with `u ↦ (u, 0)` (N3).

Helpers (namespace `OscInt.K2.ProductNormalFormAux`):
* `exists_subst`, `exists_root`: globally smooth substitutes for `y ↦ y` and `y ↦ y^{1/n}` on `[a, ∞)`,
  bounded below by a positive constant (section 8, item 3: smooth substitutes on the sign-fixed range).
* `hadamard`, `iteratedDeriv_mul_id`, `monomial_factor`: iterated Hadamard lemma with smooth quotients (P9).
* `monomial_coord` (N5, shared by P11 and P12): `G = G(0) + σ z^m` near 0 with `z(u) = u q(u)`, `q ≥ c₁ > 0`.
* `taylor2`, `hasDerivAt_snd`, `transverse`: `F(u, s) = F(u, S) + (s − S) F_s(u, S) + (s − S)² R(u, s)`,
  `R` smooth (P9), `R(u, S u) = F_ss(u, S u)/2`.
* `subst_line`: the one-dimensional substitution (`intervalIntegral.integral_deriv_smul_comp`, complex integrand)
  for a coordinate `φ(x) = (x − x₀) q(x)` with `q ≥ c₀ > 0` against a cutoff vanishing off `[−ρ, ρ]`.

Cutoff. Since `|z(u)| ≥ c₁ |u|` and `|w(u, s)| ≥ c₀ |s − S(u)|` globally, the product
`b₁(z) z′ · b₂(w) ∂ₛw` is itself supported where `|u| < A` and `|s − S(u)| < θ/4`; the radii are chosen so that
this set lies inside the box where the normal-form identities hold and inside `closedBall k₀ δ`. No separate
spatial plateau ζ is needed (it would be identically 1 on that support).
-/

open Set MeasureTheory OscInt.Statements OscInt.Blueprint.K2
open scoped ContDiff

namespace OscInt.K2.ProductNormalFormAux

/-- A smooth substitute for the identity on `[a, ∞)`, bounded below by `a / 2`. -/
theorem exists_subst (a : ℝ) (ha : 0 < a) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, a / 2 ≤ g y) ∧ ∀ y, a ≤ y → g y = y := by
  refine ⟨fun y => a / 2 + (y - a / 2) * Real.smoothTransition ((y - a / 2) / (a / 2)), ?_, ?_, ?_⟩
  · exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).div_const _)))
  · intro y
    dsimp only
    by_cases hy : y ≤ a / 2
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))]
      simp
    · have := Real.smoothTransition.nonneg ((y - a / 2) / (a / 2))
      have : 0 ≤ (y - a / 2) * Real.smoothTransition ((y - a / 2) / (a / 2)) :=
        mul_nonneg (by linarith) this
      linarith
  · intro y hy
    dsimp only
    rw [Real.smoothTransition.one_of_one_le]
    · ring
    · rw [le_div_iff₀ (by linarith)]; linarith

/-- A smooth substitute for `y ↦ y^{1/n}` on `[a, ∞)`, bounded below by a positive constant. -/
theorem exists_root (n : ℕ) (hn : n ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∃ c > 0, ∀ y, c ≤ ρ y) ∧ ∀ y, a ≤ y → ρ y ^ n = y := by
  obtain ⟨g, hg, hglb, hgeq⟩ := exists_subst a ha
  have hgpos : ∀ y, 0 < g y := fun y => lt_of_lt_of_le (by linarith) (hglb y)
  refine ⟨fun y => g y ^ ((n : ℝ)⁻¹), hg.rpow_const_of_ne (fun y => (hgpos y).ne'),
    ⟨(a / 2) ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos (by linarith) _,
      fun y => Real.rpow_le_rpow (by linarith) (hglb y) (by positivity)⟩, fun y hy => ?_⟩
  simp only
  rw [Real.rpow_inv_natCast_pow (hgpos y).le hn, hgeq y hy]

/-- Hadamard's lemma in one variable, with a smooth quotient (via P9). -/
theorem hadamard (hP9 : ParamIntegralSmoothFacts) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (h0 : f 0 = 0) :
    ∃ f₁ : ℝ → ℝ, ContDiff ℝ ∞ f₁ ∧ ∀ u, f u = u * f₁ u := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hF : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv f (p.2 * p.1.1)) := hd.comp (by fun_prop)
  have h1 := hP9 ⊤ _ hF
  refine ⟨fun u => ∫ θ in (0 : ℝ)..1, deriv f (θ * u), ?_, ?_⟩
  · exact h1.comp (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => ((u, 0) : ℝ × ℝ)))
  · intro u
    have hder : ∀ θ ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun θ => f (θ * u)) (u * deriv f (θ * u)) θ := by
      intro θ _
      have := ((hf.differentiable (by simp)) (θ * u)).hasDerivAt.comp θ ((hasDerivAt_id' θ).mul_const u)
      exact this.congr_deriv (by ring)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (continuous_const.mul (hd.continuous.comp (by fun_prop))) _ _)
    rw [intervalIntegral.integral_const_mul] at hint
    simp only [one_mul, zero_mul, h0, sub_zero] at hint
    exact hint.symm

/-- `(u f₁)^{(j+1)} = (j+1) f₁^{(j)} + u f₁^{(j+1)}`. -/
theorem iteratedDeriv_mul_id (f₁ : ℝ → ℝ) (hf : ContDiff ℝ ∞ f₁) (j : ℕ) :
    iteratedDeriv (j + 1) (fun u => u * f₁ u) =
      fun u => ((j : ℝ) + 1) * iteratedDeriv j f₁ u + u * iteratedDeriv (j + 1) f₁ u := by
  have hdi : ∀ i u, HasDerivAt (fun u => iteratedDeriv i f₁ u) (iteratedDeriv (i + 1) f₁ u) u := by
    intro i u
    rw [iteratedDeriv_succ]
    exact ((hf.differentiable_iteratedDeriv i (by exact_mod_cast WithTop.coe_lt_top _)) u).hasDerivAt
  induction j with
  | zero =>
    funext u
    rw [iteratedDeriv_one]
    have := (hasDerivAt_id' u).mul ((hf.differentiable (by simp)) u).hasDerivAt
    apply HasDerivAt.deriv
    convert this using 1
    simp [iteratedDeriv_one]
  | succ j ih =>
    funext u
    rw [iteratedDeriv_succ, ih]
    have := ((hdi j u).const_mul ((j : ℝ) + 1)).add ((hasDerivAt_id' u).mul (hdi (j + 1) u))
    apply HasDerivAt.deriv
    convert this using 1
    push_cast
    ring

/-- Iterated Hadamard: vanishing jets of order `< k` give `f = u^k g` with `k! g(0) = f^{(k)}(0)`. -/
theorem monomial_factor (hP9 : ParamIntegralSmoothFacts) (k : ℕ) :
    ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → (∀ j < k, iteratedDeriv j f 0 = 0) →
      ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ u, f u = u ^ k * g u) ∧
        (k.factorial : ℝ) * g 0 = iteratedDeriv k f 0 := by
  induction k with
  | zero => intro f hf _; exact ⟨f, hf, by simp, by simp⟩
  | succ k ih =>
    intro f hf hj
    have h0 : f 0 = 0 := by simpa using hj 0 (Nat.succ_pos k)
    obtain ⟨f₁, hf₁, hff₁⟩ := hadamard hP9 f hf h0
    have hfeq : f = fun u => u * f₁ u := funext hff₁
    have hrel : ∀ j, iteratedDeriv (j + 1) f 0 = ((j : ℝ) + 1) * iteratedDeriv j f₁ 0 := by
      intro j; rw [hfeq, iteratedDeriv_mul_id f₁ hf₁ j]; simp
    obtain ⟨g, hg, hfg, hg0⟩ := ih f₁ hf₁ (fun j hj' => by
      have := hj (j + 1) (by omega)
      rw [hrel] at this
      exact (mul_eq_zero.mp this).resolve_left (by positivity))
    refine ⟨g, hg, fun u => by rw [hff₁, hfg]; ring, ?_⟩
    rw [hrel k, ← hg0, Nat.factorial_succ]
    push_cast
    ring

/-- **Monomial coordinate** (route section 8, N5; shared by P11 and P12): a smooth `G` with `G^{(j)}(0) = 0` for
`1 ≤ j < m` and `G^{(m)}(0) ≠ 0` is `G(0) + σ z^m` near 0, with `z(u) = u q(u)` smooth and `q ≥ c₁ > 0`. -/
theorem monomial_coord (hP9 : ParamIntegralSmoothFacts) (G : ℝ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hG : ContDiff ℝ ∞ G) (hj : ∀ j ∈ Finset.Icc 1 (m - 1), iteratedDeriv j G 0 = 0)
    (hmne : iteratedDeriv m G 0 ≠ 0) :
    ∃ (σ : ℝ) (z q : ℝ → ℝ) (η c₁ : ℝ), (σ = 1 ∨ σ = -1) ∧ (0 < iteratedDeriv m G 0 → σ = 1) ∧
      ContDiff ℝ ∞ z ∧ 0 < η ∧ 0 < c₁ ∧ (∀ u, z u = u * q u) ∧ (∀ u, c₁ ≤ q u) ∧
      ∀ u, |u| < η → G u = G 0 + σ * z u ^ m := by
  set f : ℝ → ℝ := fun u => G u - G 0 with hfdef
  have hf : ContDiff ℝ ∞ f := hG.sub contDiff_const
  have hdf : ∀ j, 1 ≤ j → iteratedDeriv j f = iteratedDeriv j G := by
    intro j hj1
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    congr 1
    funext x
    exact deriv_sub_const _
  obtain ⟨g, hg, hfg, hg0⟩ := monomial_factor hP9 m f hf (fun j hj' => by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp [hfdef]
    · rw [hdf j h]; exact hj j (Finset.mem_Icc.mpr ⟨h, by omega⟩))
  rw [hdf m hm] at hg0
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hg0' : g 0 = iteratedDeriv m G 0 / m.factorial := by
    field_simp; linarith
  have hg0ne : g 0 ≠ 0 := by rw [hg0']; exact div_ne_zero hmne hfac.ne'
  set σ : ℝ := if 0 < g 0 then 1 else -1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by by_cases h : 0 < g 0 <;> simp [hσdef, h]
  have hσsq : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσg : σ * g 0 = |g 0| := by
    by_cases h : 0 < g 0
    · simp [hσdef, h, abs_of_pos h]
    · have h' : g 0 < 0 := lt_of_le_of_ne (not_lt.mp h) hg0ne
      simp [hσdef, h, abs_of_neg h']
  set a := |g 0| with hadef
  have ha : 0 < a := abs_pos.mpr hg0ne
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.mp (hg.continuous.continuousAt (x := 0)) (a / 2)
    (by linarith)
  have hsign : ∀ u, |u| < η → a / 2 ≤ σ * g u := by
    intro u hu
    have h1 := hηg (show dist u 0 < η by simpa [Real.dist_eq] using hu)
    rw [Real.dist_eq] at h1
    have h2 : |σ * g u - σ * g 0| < a / 2 := by
      rw [← mul_sub, abs_mul]
      rcases hσ with h | h <;> rw [h] <;> simpa using h1
    have := (abs_lt.mp h2).1
    linarith
  obtain ⟨ρ, hρ, ⟨c, hc, hρc⟩, hρpow⟩ := exists_root m (by omega) (a / 2) (by linarith)
  refine ⟨σ, fun u => u * ρ (σ * g u), fun u => ρ (σ * g u), η, c, hσ, fun hpos => ?_,
    contDiff_id.mul (hρ.comp (contDiff_const.mul hg)), hη, hc, fun u => rfl, fun u => hρc _,
    fun u hu => ?_⟩
  · have : 0 < g 0 := by rw [hg0']; exact div_pos hpos hfac
    simp [hσdef, this]
  · have h1 : G u = G 0 + f u := by simp [hfdef]
    rw [h1, hfg u, mul_pow, hρpow _ (hsign u hu)]
    have : σ * (u ^ m * (σ * g u)) = (σ * σ) * (u ^ m * g u) := by ring
    rw [this, hσsq, one_mul]

/-- An integral over `ℝ` of a function vanishing off `[a, b]` is the interval integral. -/
theorem integral_eq_interval (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (hf : ∀ x, x ∉ Icc a b → f x = 0) :
    ∫ x, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hf]

/-- One-dimensional substitution for a coordinate `φ(x) = (x − x₀) q(x)` with `q ≥ c₀ > 0`, against a cutoff
vanishing off `[−ρ, ρ]` (`intervalIntegral.integral_deriv_smul_comp`). -/
theorem subst_line (φ φ' q b : ℝ → ℝ) (E : ℝ → ℂ) (x₀ c₀ ρ : ℝ) (hc₀ : 0 < c₀) (hρ : 0 < ρ)
    (hφ : ∀ x, φ x = (x - x₀) * q x) (hq : ∀ x, c₀ ≤ q x) (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') (hb : Continuous b) (hb0 : ∀ y, ρ < |y| → b y = 0) (hE : Continuous E) :
    ∫ x, (b (φ x) : ℂ) * (φ' x : ℂ) * E (φ x) = ∫ y, (b y : ℂ) * E y := by
  have hrc : 0 < ρ / c₀ := div_pos hρ hc₀
  have hρeq : ρ / c₀ * c₀ = ρ := div_mul_cancel₀ ρ hc₀.ne'
  have hAB : x₀ - ρ / c₀ ≤ x₀ + ρ / c₀ := by linarith
  have hφA : φ (x₀ - ρ / c₀) ≤ -ρ := by
    rw [hφ]
    have := hq (x₀ - ρ / c₀)
    nlinarith
  have hφB : ρ ≤ φ (x₀ + ρ / c₀) := by
    rw [hφ]
    have := hq (x₀ + ρ / c₀)
    nlinarith
  have hbig : ∀ x, x ∉ Icc (x₀ - ρ / c₀) (x₀ + ρ / c₀) → ρ < |φ x| := by
    intro x hx
    have hx' : ρ / c₀ < |x - x₀| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hqx := hq x
    rw [hφ, abs_mul, abs_of_pos (by linarith : 0 < q x)]
    have : ρ / c₀ * c₀ < |x - x₀| * q x := by
      calc ρ / c₀ * c₀ < |x - x₀| * c₀ := by exact mul_lt_mul_of_pos_right hx' hc₀
        _ ≤ |x - x₀| * q x := by exact mul_le_mul_of_nonneg_left hqx (abs_nonneg _)
    linarith
  rw [integral_eq_interval _ hAB (fun x hx => by simp [hb0 _ (hbig x hx)])]
  have key := intervalIntegral.integral_deriv_smul_comp (a := x₀ - ρ / c₀) (b := x₀ + ρ / c₀)
    (f := φ) (f' := φ') (g := fun y => (b y : ℂ) * E y) (fun x _ => hd x) hφ'.continuousOn
    ((Complex.continuous_ofReal.comp hb).mul hE)
  have hfun : (fun x => (b (φ x) : ℂ) * (φ' x : ℂ) * E (φ x)) =
      fun x => φ' x • ((fun y => (b y : ℂ) * E y) ∘ φ) x := by
    funext x; simp only [Function.comp, Complex.real_smul]; ring
  rw [hfun, key, integral_eq_interval _ (by linarith : φ (x₀ - ρ / c₀) ≤ φ (x₀ + ρ / c₀))]
  intro y hy
  have : ρ < |y| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [hb0 _ this]

/-- Taylor's formula of order 2 with integral remainder. -/
theorem taylor2 (φ φ' φ'' : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (φ' x) x) (hd' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hc : Continuous φ'') (a b : ℝ) :
    φ b = φ a + (b - a) * φ' a + (b - a) ^ 2 * ∫ θ in (0 : ℝ)..1, (1 - θ) * φ'' (a + θ * (b - a)) := by
  have hψ : ∀ θ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun θ => φ (a + θ * (b - a)) + (1 - θ) * (b - a) * φ' (a + θ * (b - a)))
        ((b - a) ^ 2 * ((1 - θ) * φ'' (a + θ * (b - a)))) θ := by
    intro θ _
    have hl : HasDerivAt (fun θ : ℝ => a + θ * (b - a)) (b - a) θ := by
      simpa using ((hasDerivAt_id' θ).mul_const (b - a)).const_add a
    have h1 := (hd (a + θ * (b - a))).comp θ hl
    have h2 := (hd' (a + θ * (b - a))).comp θ hl
    have h3 : HasDerivAt (fun θ : ℝ => (1 - θ) * (b - a)) (-(b - a)) θ := by
      simpa using ((hasDerivAt_id' θ).const_sub 1).mul_const (b - a)
    convert h1.add (h3.mul h2) using 1
    · rfl
    · simp only [Function.comp]
      ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hψ
    (Continuous.intervalIntegrable (continuous_const.mul ((continuous_const.sub continuous_id).mul
      (hc.comp (continuous_const.add (continuous_id.mul continuous_const))))) _ _)
  rw [intervalIntegral.integral_const_mul] at hint
  simp only [one_mul, zero_mul, add_zero, sub_self, sub_zero] at hint
  have : a + (b - a) = b := by ring
  rw [this] at hint
  linarith

/-- The partial derivative in the second variable along a horizontal line. -/
theorem hasDerivAt_snd (H : ℝ × ℝ → ℝ) (hH : Differentiable ℝ H) (u s : ℝ) :
    HasDerivAt (fun s => H (u, s)) (fderiv ℝ H (u, s) (0, 1)) s := by
  have hl : HasDerivAt (fun s : ℝ => ((u, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) s :=
    (hasDerivAt_const s u).prodMk (hasDerivAt_id s)
  exact (hH (u, s)).hasFDerivAt.comp_hasDerivAt s hl

/-- **Transverse factorisation**: `F(u, s) = F(u, S u) + (s − S u) F_s(u, S u) + (s − S u)² R(u, s)` with `R`
smooth (P9) and `R(u, S u) = F_ss(u, S u)/2`. -/
theorem transverse (hP9 : ParamIntegralSmoothFacts) (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (S : ℝ → ℝ)
    (hS : ContDiff ℝ ∞ S) :
    ∃ R : ℝ × ℝ → ℝ, ContDiff ℝ ∞ R ∧
      (∀ u s, F (u, s) = F (u, S u) + (s - S u) * fderiv ℝ F (u, S u) (0, 1) + (s - S u) ^ 2 * R (u, s)) ∧
      ∀ u, R (u, S u) = fderiv ℝ (fun p => fderiv ℝ F p (0, 1)) (u, S u) (0, 1) / 2 := by
  set Fs : ℝ × ℝ → ℝ := fun p => fderiv ℝ F p (0, 1) with hFsdef
  have hFs : ContDiff ℝ ∞ Fs := (hF.fderiv_right le_rfl).clm_apply contDiff_const
  set Fss : ℝ × ℝ → ℝ := fun p => fderiv ℝ Fs p (0, 1) with hFssdef
  have hFss : ContDiff ℝ ∞ Fss := (hFs.fderiv_right le_rfl).clm_apply contDiff_const
  have hf : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
      (1 - p.2) * Fss (p.1.1, S p.1.1 + p.2 * (p.1.2 - S p.1.1))) := by
    have hS1 : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => S p.1.1) := hS.comp (by fun_prop)
    exact (contDiff_const.sub contDiff_snd).mul (hFss.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (hS1.add (contDiff_snd.mul ((contDiff_snd.comp contDiff_fst).sub hS1)))))
  refine ⟨fun x => ∫ θ in (0 : ℝ)..1, (1 - θ) * Fss (x.1, S x.1 + θ * (x.2 - S x.1)), hP9 ⊤ _ hf,
    fun u s => ?_, fun u => ?_⟩
  · exact taylor2 (fun s => F (u, s)) (fun s => Fs (u, s)) (fun s => Fss (u, s))
      (fun s => hasDerivAt_snd F (hF.differentiable (by simp)) u s)
      (fun s => hasDerivAt_snd Fs (hFs.differentiable (by simp)) u s)
      (hFss.continuous.comp (by fun_prop)) (S u) s
  · simp only [sub_self, mul_zero, add_zero]
    rw [intervalIntegral.integral_mul_const]
    have : ∫ θ in (0 : ℝ)..1, (1 - θ) = 1 / 2 := by
      rw [intervalIntegral.integral_sub (by simp) (by simp)]
      simp
      norm_num
    rw [this]
    ring

end OscInt.K2.ProductNormalFormAux

open OscInt.K2.ProductNormalFormAux OscInt.API.TriangularDecaySanity in
/-- **P11** The exact product normal form (route section 5, "P11", with the cutoff of section 8, item 3). -/
theorem OscInt.K2.productNormalForm (hP9 : ParamIntegralSmoothFacts) : ProductNormalFormFacts := by
  intro Ψ k₀ v w ε₀ h m δ hΨ hm hdet hww hε₀ hcurve hjets hmne hδ
  obtain ⟨hh, hh0, hcrit⟩ := hcurve
  obtain ⟨e, he1, he2⟩ := OscInt.StationaryPhase.LocalAux.exists_equiv_cols v w hdet
  have he : ∀ x : ℝ × ℝ, e x = x.1 • v + x.2 • w := by
    intro x
    have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, he1, he2]
  set eL : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) with heL
  have heL' : ∀ x, eL x = e x := fun x => rfl
  -- the chart phase
  set F : ℝ × ℝ → ℝ := fun x => Ψ (k₀ + e x) - fderiv ℝ Ψ k₀ (e x) with hFdef
  have hF : ContDiff ℝ ∞ F :=
    (hΨ.comp (contDiff_const.add e.contDiff)).sub ((fderiv ℝ Ψ k₀).contDiff.comp e.contDiff)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hD2 : Differentiable ℝ (fderiv ℝ Ψ) := (hΨ.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hlin : ∀ x, HasFDerivAt (fun x => k₀ + e x) eL x := fun x => eL.hasFDerivAt.const_add k₀
  have hFd : ∀ x, HasFDerivAt F ((fderiv ℝ Ψ (k₀ + e x)).comp eL - (fderiv ℝ Ψ k₀).comp eL) x := by
    intro x
    exact ((hΨd (k₀ + e x)).hasFDerivAt.comp x (hlin x)).sub ((fderiv ℝ Ψ k₀).hasFDerivAt.comp x
      eL.hasFDerivAt)
  have hFs : (fun x => fderiv ℝ F x (0, 1)) = fun x => fderiv ℝ Ψ (k₀ + e x) w - fderiv ℝ Ψ k₀ w := by
    funext x
    rw [(hFd x).fderiv]
    simp [heL', he2]
  have hFss : fderiv ℝ (fun x => fderiv ℝ F x (0, 1)) (0, 0) (0, 1) = iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] := by
    rw [hFs, iteratedFDeriv_two_apply]
    have h2 := ((hD2 (k₀ + e (0, 0))).hasFDerivAt.comp ((0 : ℝ), (0 : ℝ)) (hlin (0, 0))).clm_apply
      (hasFDerivAt_const w ((0 : ℝ), (0 : ℝ)))
    have h3 : HasFDerivAt (fun x => fderiv ℝ Ψ (k₀ + e x) w - fderiv ℝ Ψ k₀ w) _ ((0 : ℝ), (0 : ℝ)) :=
      h2.sub_const (fderiv ℝ Ψ k₀ w)
    rw [h3.fderiv]
    simp [heL', he2, Prod.mk_zero_zero]
  have hFs0 : ∀ u, |u| < ε₀ → fderiv ℝ F (u, h u) (0, 1) = 0 := by
    intro u hu
    have := congrFun hFs (u, h u)
    rw [this, he]
    try simp only
    rw [← add_assoc, hcrit u hu, sub_self]
  have hG : reducedFn Ψ k₀ v w h = fun u => F (u, h u) := by
    funext u
    simp only [reducedFn, hFdef, he, add_assoc]
  have hGs : ContDiff ℝ ∞ (fun u => F (u, h u)) := hF.comp (contDiff_id.prodMk hh)
  -- the longitudinal coordinate
  obtain ⟨σ, z, q, η₁, c₁, hσ, -, hz, hη₁, hc₁, hzq, hq, hGz⟩ :=
    monomial_coord hP9 (fun u => F (u, h u)) m (by omega) hGs (by rw [← hG]; exact hjets)
      (by rw [← hG]; exact hmne)
  have hzd : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  -- the transverse coordinate
  obtain ⟨R, hR, hFR, hRS⟩ := transverse hP9 F hF h hh
  have hR0 : R (0, 0) = iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] / 2 := by
    have := hRS 0
    rw [hh0] at this
    rw [this, hFss]
  have hR0ne : R (0, 0) ≠ 0 := by rw [hR0]; exact div_ne_zero hww two_ne_zero
  set ε : ℝ := if 0 < R (0, 0) then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases h' : 0 < R (0, 0) <;> simp [hεdef, h']
  have hεsq : ε * ε = 1 := by rcases hε with h' | h' <;> rw [h'] <;> norm_num
  have hεR : ε * R (0, 0) = |R (0, 0)| := by
    by_cases h' : 0 < R (0, 0)
    · simp [hεdef, h', abs_of_pos h']
    · have h'' : R (0, 0) < 0 := lt_of_le_of_ne (not_lt.mp h') hR0ne
      simp [hεdef, h', abs_of_neg h'']
  set a₀ := |R (0, 0)| with ha₀def
  have ha₀ : 0 < a₀ := abs_pos.mpr hR0ne
  obtain ⟨η₀, hη₀, hη₀R⟩ := Metric.continuousAt_iff.mp
    (hR.continuous.continuousAt (x := ((0 : ℝ), (0 : ℝ)))) (a₀ / 2) (by linarith)
  have hsignR : ∀ x : ℝ × ℝ, dist x (0, 0) < η₀ → a₀ / 2 ≤ ε * R x := by
    intro x hx
    have h1 := hη₀R hx
    rw [Real.dist_eq] at h1
    have h2 : |ε * R x - ε * R (0, 0)| < a₀ / 2 := by
      rw [← mul_sub, abs_mul]
      rcases hε with h' | h' <;> rw [h'] <;> simpa using h1
    have := (abs_lt.mp h2).1
    linarith
  obtain ⟨ρ, hρ, ⟨c₀, hc₀, hρc⟩, hρsq⟩ := exists_root 2 (by norm_num) (a₀ / 2) (by linarith)
  set W : ℝ × ℝ → ℝ := fun x => (x.2 - h x.1) * ρ (ε * R x) with hWdef
  have hW : ContDiff ℝ ∞ W :=
    (contDiff_snd.sub (hh.comp contDiff_fst)).mul (hρ.comp (contDiff_const.mul hR))
  set Wd : ℝ × ℝ → ℝ := fun x => fderiv ℝ W x (0, 1) with hWddef
  have hWd : ContDiff ℝ ∞ Wd := (hW.fderiv_right le_rfl).clm_apply contDiff_const
  -- the radii
  set N := ‖v‖ + ‖w‖ + 1 with hNdef
  have hN : 0 < N := by positivity
  set θ := min (min η₀ η₁) (min ε₀ (δ / N)) with hθdef
  have hθ : 0 < θ := lt_min (lt_min hη₀ hη₁) (lt_min hε₀ (div_pos hδ hN))
  have hθη₀ : θ ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hθη₁ : θ ≤ η₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hθε₀ : θ ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hθδ : θ ≤ δ / N := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η₂, hη₂, hη₂h⟩ := Metric.continuousAt_iff.mp (hh.continuous.continuousAt (x := 0)) (θ / 4)
    (by linarith)
  have hhs : ∀ u, |u| < η₂ → |h u| < θ / 4 := by
    intro u hu
    have := hη₂h (show dist u 0 < η₂ by simpa [Real.dist_eq] using hu)
    simpa [Real.dist_eq, hh0] using this
  set A := min (θ / 2) (η₂ / 2) with hAdef
  have hA : 0 < A := lt_min (by linarith) (by linarith)
  have hAθ : A ≤ θ / 2 := min_le_left _ _
  have hAη₂ : A < η₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set ρ₁ := c₁ * A with hρ₁def
  have hρ₁ : 0 < ρ₁ := mul_pos hc₁ hA
  set ρ₂ := c₀ * (θ / 4) with hρ₂def
  have hρ₂ : 0 < ρ₂ := mul_pos hc₀ (by linarith)
  set b₁ := plat (ρ₁ / 2) ρ₁ with hb₁def
  set b₂ := plat (ρ₂ / 2) ρ₂ with hb₂def
  have hb₁0' : ∀ y, ρ₁ ≤ |y| → b₁ y = 0 := fun y hy => plat_eq_zero (by positivity) (by linarith) hy
  have hb₂0' : ∀ y, ρ₂ ≤ |y| → b₂ y = 0 := fun y hy => plat_eq_zero (by positivity) (by linarith) hy
  -- the cutoff in the chart
  set χt : ℝ × ℝ → ℝ := fun x => b₁ (z x.1) * deriv z x.1 * (b₂ (W x) * Wd x) with hχtdef
  have hχt : ContDiff ℝ ∞ χt :=
    ((((plat_contDiff _ _).comp hz).comp contDiff_fst).mul (hzd.comp contDiff_fst)).mul
      (((plat_contDiff _ _).comp hW).mul hWd)
  have hsupp : ∀ x, χt x ≠ 0 → |x.1| < A ∧ |x.2 - h x.1| < θ / 4 := by
    intro x hx
    have hx1 : b₁ (z x.1) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
    have hx2 : b₂ (W x) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hx)
    constructor
    · by_contra hA'
      have hA' := not_lt.mp hA'
      apply hx1
      apply hb₁0'
      rw [hzq, abs_mul, abs_of_pos (lt_of_lt_of_le hc₁ (hq _)), hρ₁def, mul_comm c₁]
      exact mul_le_mul hA' (hq _) hc₁.le (abs_nonneg _)
    · by_contra hB'
      have hB' := not_lt.mp hB'
      apply hx2
      apply hb₂0'
      rw [hWdef]
      simp only
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le hc₀ (hρc _)), hρ₂def, mul_comm c₀]
      exact mul_le_mul hB' (hρc _) hc₀.le (abs_nonneg _)
  have hsupp' : ∀ x, χt x ≠ 0 →
      |x.1| < θ / 2 ∧ |x.2| < θ / 2 ∧ |x.1| < η₁ ∧ |x.1| < ε₀ ∧ dist x (0, 0) < η₀ := by
    intro x hx
    obtain ⟨h1, h2⟩ := hsupp x hx
    have h3 : |h x.1| < θ / 4 := hhs _ (lt_trans h1 hAη₂)
    have h4 : |x.2| < θ / 2 := by
      have : |x.2| ≤ |x.2 - h x.1| + |h x.1| := by
        calc |x.2| = |(x.2 - h x.1) + h x.1| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    refine ⟨by linarith, h4, by linarith, by linarith, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact max_lt (by linarith) (by linarith)
  have hphase : ∀ x, χt x ≠ 0 → F x = F (0, h 0) + σ * z x.1 ^ m + ε * W x ^ 2 := by
    intro x hx
    obtain ⟨-, -, h3, h4, h5⟩ := hsupp' x hx
    have hT := hFR x.1 x.2
    have hGx := hGz x.1 h3
    rw [hFs0 x.1 h4, mul_zero, add_zero, hGx, Prod.mk.eta] at hT
    have hWsq : ε * W x ^ 2 = (x.2 - h x.1) ^ 2 * R x := by
      calc ε * W x ^ 2 = ε * ((x.2 - h x.1) ^ 2 * (ρ (ε * R x)) ^ 2) := by rw [hWdef]; ring
        _ = ε * ((x.2 - h x.1) ^ 2 * (ε * R x)) := by rw [hρsq _ (hsignR x h5)]
        _ = (ε * ε) * ((x.2 - h x.1) ^ 2 * R x) := by ring
        _ = _ := by rw [hεsq, one_mul]
    rw [hWsq]
    exact hT
  -- the cutoff in `k`
  set χ : ℝ × ℝ → ℝ := fun k => χt (e.symm (k - k₀)) with hχdef
  have hdetne : LinearMap.det (e : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' (e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ))).ne_zero
  set d := |LinearMap.det (e : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))| with hddef
  have hd : 0 < d := abs_pos.mpr hdetne
  set K := fderiv ℝ Ψ k₀ k₀ with hKdef
  set c := F (0, h 0) - K with hcdef
  have hb₁c : Continuous b₁ := (plat_contDiff _ _).continuous
  have hb₂c : Continuous b₂ := (plat_contDiff _ _).continuous
  refine ⟨χ, hχt.comp (e.symm.contDiff.comp (contDiff_id.sub contDiff_const)), ?_, c, σ, ε, d⁻¹,
    ρ₁ / 2, ρ₂ / 2, b₁, b₂, hσ, hε, inv_pos.mpr hd, plat_plateau (by positivity) (by linarith),
    plat_plateau (by positivity) (by linarith), plat_contDiff _ _, plat_contDiff _ _, fun t => ?_⟩
  · refine closure_minimal (fun k hk => ?_) Metric.isClosed_closedBall
    have hk' : χt (e.symm (k - k₀)) ≠ 0 := hk
    obtain ⟨h1, h2, -⟩ := hsupp' _ hk'
    have hk_eq : k - k₀ = (e.symm (k - k₀)).1 • v + (e.symm (k - k₀)).2 • w := by
      rw [← he, ContinuousLinearEquiv.apply_symm_apply]
    rw [Metric.mem_closedBall, dist_eq_norm, hk_eq]
    set x := e.symm (k - k₀)
    have hθN : θ * N ≤ δ := (le_div_iff₀ hN).mp hθδ
    calc ‖x.1 • v + x.2 • w‖ ≤ ‖x.1 • v‖ + ‖x.2 • w‖ := norm_add_le _ _
      _ = |x.1| * ‖v‖ + |x.2| * ‖w‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (θ / 2) * ‖v‖ + (θ / 2) * ‖w‖ := by gcongr
      _ ≤ δ := by nlinarith [norm_nonneg v, norm_nonneg w]
  · set P₁ : ℝ → ℂ := fun u => (b₁ (z u) : ℂ) * ((deriv z u : ℝ) : ℂ) *
      Complex.exp (↑(t * σ * z u ^ m) * Complex.I) with hP₁def
    set P₂ : ℝ × ℝ → ℂ := fun x => (b₂ (W x) : ℂ) * (Wd x : ℂ) *
      Complex.exp (↑(t * ε * W x ^ 2) * Complex.I) with hP₂def
    have hprod : ∀ x : ℝ × ℝ, P₁ x.1 * P₂ x = (χt x : ℂ) *
        (Complex.exp (↑(t * σ * z x.1 ^ m) * Complex.I) * Complex.exp (↑(t * ε * W x ^ 2) * Complex.I)) := by
      intro x; simp only [hP₁def, hP₂def, hχtdef]; push_cast; ring
    have hpt : ∀ x : ℝ × ℝ, ((χ (k₀ + e x) : ℝ) : ℂ) *
        Complex.exp (↑(t * (Ψ (k₀ + e x) - fderiv ℝ Ψ k₀ (k₀ + e x))) * Complex.I) =
        Complex.exp (↑(t * c) * Complex.I) * (P₁ x.1 * P₂ x) := by
      intro x
      have hχx : χ (k₀ + e x) = χt x := by simp [hχdef]
      have hFx : Ψ (k₀ + e x) - fderiv ℝ Ψ k₀ (k₀ + e x) = F x - K := by
        simp only [hFdef, hKdef, map_add]; ring
      rw [hprod x, hχx, hFx]
      by_cases hx : χt x = 0
      · simp [hx]
      · rw [hphase x hx]
        have : (↑(t * (F (0, h 0) + σ * z x.1 ^ m + ε * W x ^ 2 - K)) : ℂ) * Complex.I =
            ↑(t * c) * Complex.I +
              (↑(t * σ * z x.1 ^ m) * Complex.I + ↑(t * ε * W x ^ 2) * Complex.I) := by
          rw [hcdef]; push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_add]
        ring
    have hP₁c : Continuous P₁ := by
      have := hzd.continuous; have := hz.continuous; fun_prop
    have hP₂c : Continuous P₂ := by
      have := hWd.continuous; have := hW.continuous; fun_prop
    have hInt : Integrable (fun x : ℝ × ℝ => P₁ x.1 * P₂ x) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      refine ((hP₁c.comp continuous_fst).mul hP₂c).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) θ) (fun x hx => ?_)
      show P₁ x.1 * P₂ x = 0
      rw [hprod x]
      by_cases hx' : χt x = 0
      · simp [hx']
      · exfalso; apply hx
        obtain ⟨h1, h2, -⟩ := hsupp' x hx'
        rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
        exact max_le (by linarith) (by linarith)
    have hin : ∀ u : ℝ, ∫ s : ℝ, P₁ (u, s).1 * P₂ (u, s) =
        P₁ u * ∫ y : ℝ, (b₂ y : ℂ) * Complex.exp (↑(t * ε * y ^ 2) * Complex.I) := by
      intro u
      show ∫ s : ℝ, P₁ u * P₂ (u, s) = _
      rw [integral_const_mul]
      congr 1
      exact subst_line (fun s => W (u, s)) (fun s => Wd (u, s)) (fun s => ρ (ε * R (u, s))) b₂
        (fun y => Complex.exp (↑(t * ε * y ^ 2) * Complex.I)) (h u) c₀ ρ₂ hc₀ hρ₂ (fun s => rfl)
        (fun s => hρc _) (fun s => hasDerivAt_snd W (hW.differentiable (by simp)) u s)
        (hWd.continuous.comp (by fun_prop)) hb₂c (fun y hy => hb₂0' y hy.le) (by fun_prop)
    have hout : ∫ u : ℝ, P₁ u = ∫ y : ℝ, (b₁ y : ℂ) * Complex.exp (↑(t * σ * y ^ m) * Complex.I) :=
      subst_line z (deriv z) q b₁ (fun y => Complex.exp (↑(t * σ * y ^ m) * Complex.I)) 0 c₁ ρ₁ hc₁ hρ₁
        (fun x => by rw [hzq, sub_zero]) hq (fun x => (hz.differentiable (by simp) x).hasDerivAt)
        hzd.continuous hb₁c (fun y hy => hb₁0' y hy.le) (by fun_prop)
    calc ∫ k, ((χ k : ℝ) : ℂ) * Complex.exp (↑(t * (Ψ k - fderiv ℝ Ψ k₀ k)) * Complex.I)
        = d • ∫ x : ℝ × ℝ, ((χ (k₀ + e x) : ℝ) : ℂ) *
            Complex.exp (↑(t * (Ψ (k₀ + e x) - fderiv ℝ Ψ k₀ (k₀ + e x))) * Complex.I) :=
          OscInt.StationaryPhase.ChangeAux.integral_eq_abs_det_smul_integral_comp_affine volume e k₀ _
      _ = d • ∫ x : ℝ × ℝ, Complex.exp (↑(t * c) * Complex.I) * (P₁ x.1 * P₂ x) := by
          rw [integral_congr_ae (ae_of_all _ hpt)]
      _ = d • (Complex.exp (↑(t * c) * Complex.I) * ((∫ u : ℝ, P₁ u) *
            ∫ y : ℝ, (b₂ y : ℂ) * Complex.exp (↑(t * ε * y ^ 2) * Complex.I))) := by
          rw [integral_const_mul, Measure.volume_eq_prod, integral_prod _ hInt,
            integral_congr_ae (ae_of_all _ hin), integral_mul_const]
      _ = _ := by
          rw [hout, Complex.real_smul]
          push_cast
          rw [inv_inv]
          ring

open OscInt.K2.ProductNormalFormAux OscInt.API.TriangularDecaySanity in
/-- **P12** The square case (route section 5, "P12"). -/
theorem OscInt.K2.squareNormalForm (hP9 : ParamIntegralSmoothFacts) : SquareNormalFormFacts := by
  intro δ hδ
  set f : ℝ → ℝ := fun a => a - Real.sin a with hfdef
  have hf : ContDiff ℝ ∞ f := contDiff_id.sub Real.contDiff_sin
  have h1 : deriv f = fun a => 1 - Real.cos a :=
    funext fun a => ((hasDerivAt_id' a).sub (Real.hasDerivAt_sin a)).deriv
  have h2 : deriv (fun a => 1 - Real.cos a) = Real.sin := funext fun a => by simp
  have hi1 : iteratedDeriv 1 f 0 = 0 := by rw [iteratedDeriv_one, h1]; simp
  have hi2 : iteratedDeriv 2 f 0 = 0 := by rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]; simp
  have hi3 : iteratedDeriv 3 f 0 = 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, Real.deriv_sin]; simp
  obtain ⟨σ, z, q, η, c₁, -, hσ1, hz, hη, hc₁, hzq, hq, hfz⟩ := monomial_coord hP9 f 3 (by norm_num) hf
    (by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
      exacts [hi1, hi2])
    (by rw [hi3]; norm_num)
  have hσ : σ = 1 := hσ1 (by rw [hi3]; norm_num)
  subst hσ
  have hf0 : f 0 = 0 := by simp [hfdef]
  set A := min (η / 2) (δ / 2) with hAdef
  have hA : 0 < A := lt_min (by linarith) (by linarith)
  have hAη : A < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hAδ : A ≤ δ / 2 := min_le_right _ _
  set ρ := c₁ * A with hρdef
  have hρ : 0 < ρ := mul_pos hc₁ hA
  set b := plat (ρ / 2) ρ with hbdef
  have hb0' : ∀ y, ρ ≤ |y| → b y = 0 := fun y hy => plat_eq_zero (by positivity) (by linarith) hy
  have hb0 : ∀ y, ρ < |y| → b y = 0 := fun y hy => hb0' y hy.le
  have hbc : Continuous b := (plat_contDiff _ _).continuous
  have hzd : ContDiff ℝ ∞ (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  set χ₁ : ℝ → ℝ := fun a => b (z a) * deriv z a with hχ₁def
  have hχ₁ : ContDiff ℝ ∞ χ₁ := ((plat_contDiff _ _).comp hz).mul hzd
  have hsupp : ∀ a, χ₁ a ≠ 0 → |a| < A := by
    intro a ha
    have hb : b (z a) ≠ 0 := left_ne_zero_of_mul ha
    by_contra hA'
    have hA' := not_lt.mp hA'
    apply hb
    apply hb0'
    rw [hzq, abs_mul, abs_of_pos (lt_of_lt_of_le hc₁ (hq a)), hρdef, mul_comm c₁]
    exact mul_le_mul hA' (hq a) hc₁.le (abs_nonneg _)
  have hpi : (Real.pi / 2, Real.pi / 2).1 = Real.pi / 2 := rfl
  refine ⟨fun k => χ₁ (k.1 - Real.pi / 2) * χ₁ (k.2 - Real.pi / 2),
    (hχ₁.comp (contDiff_fst.sub contDiff_const)).mul (hχ₁.comp (contDiff_snd.sub contDiff_const)), ?_,
    Real.pi, ρ / 2, b, plat_plateau (by positivity) (by linarith), plat_contDiff _ _, fun t => ?_⟩
  · refine closure_minimal (fun k hk => ?_) Metric.isClosed_closedBall
    have hk' : χ₁ (k.1 - Real.pi / 2) * χ₁ (k.2 - Real.pi / 2) ≠ 0 := hk
    have ha1 := hsupp _ (left_ne_zero_of_mul hk')
    have ha2 := hsupp _ (right_ne_zero_of_mul hk')
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (by linarith) (by linarith)
  · -- the separated phase and the factorisation
    set g : ℝ → ℂ := fun x => (χ₁ (x - Real.pi / 2) : ℂ) *
      Complex.exp (↑(t * (Real.cos x + x)) * Complex.I) with hgdef
    have hpt : ∀ k : ℝ × ℝ, ((χ₁ (k.1 - Real.pi / 2) * χ₁ (k.2 - Real.pi / 2) : ℝ) : ℂ) *
        Complex.exp (↑(t * (triPhase 0 k + k.1 + k.2)) * Complex.I) = g k.1 * g k.2 := by
      intro k
      have hph : t * (triPhase 0 k + k.1 + k.2) = t * (Real.cos k.1 + k.1) + t * (Real.cos k.2 + k.2) := by
        simp [triPhase]; ring
      rw [hph, Complex.ofReal_add, add_mul, Complex.exp_add, hgdef]
      push_cast
      ring
    have hg : ∫ x, g x = Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) *
        ∫ y, (b y : ℂ) * Complex.exp (↑(t * y ^ 3) * Complex.I) := by
      have hpt2 : ∀ a, g (a + Real.pi / 2) = Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) *
          ((b (z a) : ℂ) * ((deriv z a : ℝ) : ℂ) * Complex.exp (↑(t * z a ^ 3) * Complex.I)) := by
        intro a
        simp only [hgdef, add_sub_cancel_right]
        by_cases ha : χ₁ a = 0
        · have : (b (z a) : ℂ) * ((deriv z a : ℝ) : ℂ) = 0 := by
            rw [← Complex.ofReal_mul]; exact_mod_cast ha
          rw [ha, Complex.ofReal_zero, zero_mul]
          linear_combination (-(Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) *
            Complex.exp (↑(t * z a ^ 3) * Complex.I))) * this
        · have hfa : f a = z a ^ 3 := by
            rw [hfz a (lt_trans (hsupp a ha) hAη), hf0]; ring
          have hcos : Real.cos (a + Real.pi / 2) + (a + Real.pi / 2) = Real.pi / 2 + z a ^ 3 := by
            rw [Real.cos_add_pi_div_two, ← hfa, hfdef]; ring
          rw [hcos, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add, hχ₁def]
          push_cast
          ring
      calc ∫ x, g x = ∫ a, g (a + Real.pi / 2) := (integral_add_right_eq_self g (Real.pi / 2)).symm
        _ = ∫ a, Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) *
            ((b (z a) : ℂ) * ((deriv z a : ℝ) : ℂ) * Complex.exp (↑(t * z a ^ 3) * Complex.I)) :=
          integral_congr_ae (ae_of_all _ hpt2)
        _ = _ := by
          rw [integral_const_mul]
          congr 1
          exact subst_line z (deriv z) q b (fun y => Complex.exp (↑(t * y ^ 3) * Complex.I)) 0 c₁ ρ hc₁ hρ
            (fun x => by rw [hzq, sub_zero]) hq (fun x => (hz.differentiable (by simp) x).hasDerivAt)
            hzd.continuous hbc hb0 (by fun_prop)
    rw [integral_congr_ae (ae_of_all _ hpt), Measure.volume_eq_prod, integral_prod_mul, hg]
    have hexp : Complex.exp (↑(t * Real.pi) * Complex.I) = Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) *
        Complex.exp (↑(t * (Real.pi / 2)) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    ring

