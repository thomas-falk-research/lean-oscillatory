/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4
import OscInt.StationaryPhase.Implicit
import OscInt.StationaryPhase.Local

/-!
# S4.1, parts D3 and D4: the fold gauge

* `cubicGauge : OscInt.Blueprint.CubicGaugeFacts` (D3). For `C = cubicPoly (a, b, c, d)` the second and third
  directional derivatives are computed explicitly (`HasFDerivAt` terms, then `dd`, then `ddd`). At `z = (x, y)`
  the Hessian entries are `p = 6ax + 2by`, `r = 2bx + 2cy`, `s = 2cx + 6dy` and `D³C[v³] = 6 C(v)`. Every
  failure of the gauge produces a vector `v ≠ 0` with `H(z) v = 0` and `C(v) = 0` (`v = z` if `H(z) = 0`, by
  Euler's identity; otherwise one of the kernel vectors `(-r, p)`, `(s, -r)`). Writing `v = v₂ (t, 1)` and applying
  the shear `(X, Y) ↦ (X + tY, Y)` (which preserves the discriminant, checked by `ring`), the cubic has no `Y³`
  term, and the kernel equations force its `XY²` coefficient to vanish, so `disc = 0` (`disc_eq_zero`).
* `gaugeFold : OscInt.Blueprint.GaugeFoldFacts` (D4). If `det H = 0` and `H ≠ 0`, every kernel vector is a
  multiple `λ u` of a kernel vector `u ∈ {(-r, p), (s, -r)}` with `D³Ψ[u³] ≠ 0`, and `D³Ψ[(λu)³] = λ³ D³Ψ[u³]`.
  Uses the symmetric coordinate formula `dd_eq_coord` and `ddd_eq_iteratedFDeriv`.

Route: `docs/proof-S4.md`, Step 3 (case argument, as revised after the route referee).
-/

open OscInt.Statements OscInt.Blueprint

namespace OscInt.D4.GaugeAux

/-! ## Derivatives of a binary cubic -/

theorem fd_cubicPoly (a b c d : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (cubicPoly (a, b, c, d)) y v =
      (3 * a * v.1 + b * v.2) * y.1 ^ 2 + (2 * b * v.1 + 2 * c * v.2) * y.1 * y.2 +
        (c * v.1 + 3 * d * v.2) * y.2 ^ 2 := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h : HasFDerivAt (cubicPoly (a, b, c, d))
      ((3 * a * y.1 ^ 2 + 2 * b * y.1 * y.2 + c * y.2 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (b * y.1 ^ 2 + 2 * c * y.1 * y.2 + 3 * d * y.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    have he : cubicPoly (a, b, c, d) =
        fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.1 ^ 2 * k.2 + c * k.1 * k.2 ^ 2 + d * k.2 ^ 3 := rfl
    rw [he]
    convert ((((h1.pow 3).const_mul a).add (((h1.pow 2).const_mul b).mul h2)).add
      (((h1.const_mul c).mul (h2.pow 2)))).add ((h2.pow 3).const_mul d) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp; ring

theorem fd_quad (p q r : ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => p * k.1 ^ 2 + q * k.1 * k.2 + r * k.2 ^ 2) y w =
      (2 * p * w.1 + q * w.2) * y.1 + (q * w.1 + 2 * r * w.2) * y.2 := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h : HasFDerivAt (fun k : ℝ × ℝ => p * k.1 ^ 2 + q * k.1 * k.2 + r * k.2 ^ 2)
      ((2 * p * y.1 + q * y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (q * y.1 + 2 * r * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((h1.pow 2).const_mul p).add ((h1.const_mul q).mul h2)).add ((h2.pow 2).const_mul r) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp; ring

theorem dd_cubicPoly (a b c d : ℝ) (y u v : ℝ × ℝ) :
    dd (cubicPoly (a, b, c, d)) y u v =
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * y.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * y.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (cubicPoly (a, b, c, d)) y u) = fun y =>
      (3 * a * u.1 + b * u.2) * y.1 ^ 2 + (2 * b * u.1 + 2 * c * u.2) * y.1 * y.2 +
        (c * u.1 + 3 * d * u.2) * y.2 ^ 2 := by
    funext y; rw [fd_cubicPoly]
  rw [dd, this, fd_quad]

theorem ddd_cubicPoly (a b c d : ℝ) (y u v w : ℝ × ℝ) :
    ddd (cubicPoly (a, b, c, d)) y u v w =
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * w.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * w.2 := by
  have : (fun y : ℝ × ℝ => dd (cubicPoly (a, b, c, d)) y u v) = fun y =>
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * y.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * y.2 := by
    funext y; rw [dd_cubicPoly]
  rw [ddd, this, sanity_fd_lin]

/-! ## The algebraic core -/

/-- Shear case: a kernel vector `(t, 1)` of `H(x, y)` on which the cubic vanishes forces `disc = 0`. -/
theorem disc_eq_zero_shear (a b c d x y t : ℝ) (hz : x ≠ 0 ∨ y ≠ 0)
    (h1 : (6 * a * x + 2 * b * y) * t + (2 * b * x + 2 * c * y) = 0)
    (h2 : (2 * b * x + 2 * c * y) * t + (2 * c * x + 6 * d * y) = 0)
    (h3 : a * t ^ 3 + b * t ^ 2 + c * t + d = 0) : disc (a, b, c, d) = 0 := by
  obtain rfl : d = -(a * t ^ 3 + b * t ^ 2 + c * t) := by linarith
  have hd : disc (a, b, c, -(a * t ^ 3 + b * t ^ 2 + c * t)) =
      (3 * a * t ^ 2 + 2 * b * t + c) ^ 2 * ((3 * a * t + b) ^ 2 - 4 * a * (3 * a * t ^ 2 + 2 * b * t + c)) := by
    simp only [disc]; ring
  have hc : (3 * a * t ^ 2 + 2 * b * t + c) * (x - t * y) = 0 := by linear_combination (t * h1 + h2) / 2
  have hb : (3 * a * t + b) * (x - t * y) + (3 * a * t ^ 2 + 2 * b * t + c) * y = 0 := by
    linear_combination h1 / 2
  rw [hd]
  rcases mul_eq_zero.1 hc with h | h
  · rw [h]; ring
  · rw [h, mul_zero, zero_add] at hb
    rcases mul_eq_zero.1 hb with h' | h'
    · rw [h']; ring
    · exfalso; rw [h', mul_zero, sub_zero] at h; tauto

/-- A nonzero vector `v` with `H(x, y) v = 0` and `C(v) = 0` at `(x, y) ≠ 0` forces `disc = 0`. -/
theorem disc_eq_zero (a b c d x y v₁ v₂ : ℝ) (hz : x ≠ 0 ∨ y ≠ 0) (hv : v₁ ≠ 0 ∨ v₂ ≠ 0)
    (h1 : (6 * a * x + 2 * b * y) * v₁ + (2 * b * x + 2 * c * y) * v₂ = 0)
    (h2 : (2 * b * x + 2 * c * y) * v₁ + (2 * c * x + 6 * d * y) * v₂ = 0)
    (h3 : a * v₁ ^ 3 + b * v₁ ^ 2 * v₂ + c * v₁ * v₂ ^ 2 + d * v₂ ^ 3 = 0) : disc (a, b, c, d) = 0 := by
  by_cases hv₂ : v₂ = 0
  · subst hv₂
    have hv₁ : v₁ ≠ 0 := by tauto
    have ha : a = 0 := by
      have : a * v₁ ^ 3 = 0 := by linear_combination h3
      simpa [hv₁] using this
    subst ha
    have hb : b * y = 0 := by
      have : (2 * b * y) * v₁ = 0 := by linear_combination h1
      simpa [hv₁] using this
    have hbc : b * x + c * y = 0 := by
      have : (2 * (b * x + c * y)) * v₁ = 0 := by linear_combination h2
      simpa [hv₁] using this
    simp only [disc]
    by_cases hb0 : b = 0
    · rw [hb0]; ring
    · exfalso
      have hy : y = 0 := by simpa [hb0] using hb
      rw [hy, mul_zero, add_zero] at hbc
      have hx : x = 0 := by simpa [hb0] using hbc
      tauto
  · obtain ⟨t, rfl⟩ : ∃ t, v₁ = t * v₂ := ⟨v₁ / v₂, by field_simp⟩
    refine disc_eq_zero_shear a b c d x y t hz ?_ ?_ ?_
    · have : ((6 * a * x + 2 * b * y) * t + (2 * b * x + 2 * c * y)) * v₂ = 0 := by linear_combination h1
      simpa [hv₂] using this
    · have : ((2 * b * x + 2 * c * y) * t + (2 * c * x + 6 * d * y)) * v₂ = 0 := by linear_combination h2
      simpa [hv₂] using this
    · have : (a * t ^ 3 + b * t ^ 2 + c * t + d) * v₂ ^ 3 = 0 := by linear_combination h3
      simpa [hv₂] using this

/-- `D³C[v³] = 6 C(v)`. -/
theorem ddd_cubicPoly_diag (a b c d : ℝ) (y v : ℝ × ℝ) :
    ddd (cubicPoly (a, b, c, d)) y v v v =
      6 * (a * v.1 ^ 3 + b * v.1 ^ 2 * v.2 + c * v.1 * v.2 ^ 2 + d * v.2 ^ 3) := by
  rw [ddd_cubicPoly]; ring

/-- The Hessian of the cubic at `z ≠ 0` is nonzero when `disc ≠ 0`. -/
theorem hessNorm_pos (a b c d x y : ℝ) (hdisc : disc (a, b, c, d) ≠ 0) (hz : x ≠ 0 ∨ y ≠ 0) :
    0 < hessNorm (cubicPoly (a, b, c, d)) (x, y) := by
  simp only [hessNorm, dd_cubicPoly]
  norm_num
  by_contra hle
  have h0 := not_lt.1 hle
  have h1 := sq_nonneg (2 * (3 * a) * x + 2 * b * y)
  have h2 := sq_nonneg (2 * b * x + 2 * c * y)
  have h3 := sq_nonneg (2 * c * x + 2 * (3 * d) * y)
  have hp : 6 * a * x + 2 * b * y = 0 := by
    have := pow_eq_zero_iff (n := 2) (a := 2 * (3 * a) * x + 2 * b * y) two_ne_zero
    linarith [this.1 (by linarith)]
  have hr : 2 * b * x + 2 * c * y = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith)
  have hs : 2 * c * x + 6 * d * y = 0 := by
    have := pow_eq_zero_iff (n := 2) (a := 2 * c * x + 2 * (3 * d) * y) two_ne_zero
    linarith [this.1 (by linarith)]
  refine hdisc (disc_eq_zero a b c d x y x y hz hz ?_ ?_ ?_)
  · rw [hp, hr]; ring
  · rw [hr, hs]; ring
  · linear_combination (x ^ 2 * hp + 2 * x * y * hr + y ^ 2 * hs) / 6

/-- Three squares summing to at most `0` all vanish. -/
theorem sq_three_eq_zero {u v w : ℝ} (h : u ^ 2 + v ^ 2 + w ^ 2 ≤ 0) : u = 0 ∧ v = 0 ∧ w = 0 := by
  have hu := sq_nonneg u
  have hv := sq_nonneg v
  have hw := sq_nonneg w
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 (by linarith), pow_eq_zero_iff two_ne_zero |>.1 (by linarith),
    pow_eq_zero_iff two_ne_zero |>.1 (by linarith)⟩

/-- The fold gauge of the cubic at `z ≠ 0` is positive when `disc ≠ 0`. -/
theorem foldGauge_pos (a b c d x y : ℝ) (hdisc : disc (a, b, c, d) ≠ 0) (hz : x ≠ 0 ∨ y ≠ 0) :
    0 < foldGauge (cubicPoly (a, b, c, d)) (x, y) := by
  have hH := hessNorm_pos a b c d x y hdisc hz
  have hP : dd (cubicPoly (a, b, c, d)) (x, y) (1, 0) (1, 0) = 6 * a * x + 2 * b * y := by
    rw [dd_cubicPoly]; ring
  have hR : dd (cubicPoly (a, b, c, d)) (x, y) (1, 0) (0, 1) = 2 * b * x + 2 * c * y := by
    rw [dd_cubicPoly]; ring
  have hS : dd (cubicPoly (a, b, c, d)) (x, y) (0, 1) (0, 1) = 2 * c * x + 6 * d * y := by
    rw [dd_cubicPoly]; ring
  rw [hessNorm, hP, hR, hS] at hH
  rw [foldGauge, hessDet, kerVec₁, kerVec₂, hP, hR, hS, ddd_cubicPoly_diag, ddd_cubicPoly_diag]
  by_contra hle
  obtain ⟨hdet, hF1, hF2⟩ := sq_three_eq_zero (not_lt.1 hle)
  simp only at hF1 hF2
  by_cases hv : -(2 * b * x + 2 * c * y) ≠ 0 ∨ 6 * a * x + 2 * b * y ≠ 0
  · refine hdisc (disc_eq_zero a b c d x y _ _ hz hv ?_ ?_ ?_)
    · ring
    · linear_combination hdet
    · linear_combination hF1 / 6
  · rw [not_or, not_ne_iff, not_ne_iff] at hv
    obtain ⟨hr, hp⟩ := hv
    have hr' : 2 * b * x + 2 * c * y = 0 := by linarith
    have hs : 2 * c * x + 6 * d * y ≠ 0 := by
      intro hs; rw [hp, hr', hs] at hH; norm_num at hH
    refine hdisc (disc_eq_zero a b c d x y (2 * c * x + 6 * d * y) (-(2 * b * x + 2 * c * y)) hz
      (Or.inl hs) ?_ ?_ ?_)
    · rw [hp, hr']; ring
    · rw [hr']; ring
    · linear_combination hF2 / 6

/-! ## The gauge implies the fold condition -/

/-- `D³Ψ[(tu)³] = t³ D³Ψ[u³]` for `Ψ ∈ C³`. -/
theorem ddd_smul_diag {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (k u : ℝ × ℝ) (t : ℝ) :
    ddd Ψ k (t • u) (t • u) (t • u) = t ^ 3 * ddd Ψ k u u u := by
  rw [OscInt.StationaryPhase.ImplicitAux.ddd_eq_iteratedFDeriv hΨ le_rfl,
    OscInt.StationaryPhase.ImplicitAux.ddd_eq_iteratedFDeriv hΨ le_rfl]
  have h : (![t • u, t • u, t • u] : Fin 3 → ℝ × ℝ) = fun i => t • (![u, u, u] : Fin 3 → ℝ × ℝ) i := by
    funext i; fin_cases i <;> rfl
  rw [h, ContinuousMultilinearMap.map_smul_univ]
  simp [smul_eq_mul]

/-- Two vectors of the plane with vanishing cross product, the first nonzero, are proportional. -/
theorem exists_smul_of_cross {u v : ℝ × ℝ} (hu : u ≠ 0) (h : u.1 * v.2 - u.2 * v.1 = 0) :
    ∃ t : ℝ, v = t • u := by
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    refine ⟨v.2 / u.2, Prod.ext ?_ ?_⟩
    · have : u.2 * v.1 = 0 := by rw [h1] at h; linarith
      simp [h1, (mul_eq_zero.1 this).resolve_left h2]
    · simp; field_simp
  · refine ⟨v.1 / u.1, Prod.ext ?_ ?_⟩
    · simp; field_simp
    · simp; field_simp; linarith

/-- If `D³Ψ[u³] ≠ 0` and `v ≠ 0` is parallel to `u`, then `D³Ψ[v³] ≠ 0`. -/
theorem ddd_ne_zero_of_cross {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiff ℝ 3 Ψ) {k u v : ℝ × ℝ}
    (hT : ddd Ψ k u u u ≠ 0) (hv : v ≠ 0) (h : u.1 * v.2 - u.2 * v.1 = 0) : ddd Ψ k v v v ≠ 0 := by
  have hu : u ≠ 0 := by
    rintro rfl
    apply hT
    have := ddd_smul_diag hΨ k (0 : ℝ × ℝ) 0
    simpa using this
  obtain ⟨t, rfl⟩ := exists_smul_of_cross hu h
  have ht : t ≠ 0 := by rintro rfl; exact hv (zero_smul _ _)
  rw [ddd_smul_diag hΨ]
  exact mul_ne_zero (pow_ne_zero 3 ht) hT

end OscInt.D4.GaugeAux

namespace OscInt.D4

open OscInt.D4.GaugeAux

/-- **D3** For a binary cubic with nonzero discriminant, the Hessian norm and the fold gauge are positive at
every `z ≠ 0`. -/
theorem cubicGauge : CubicGaugeFacts := by
  rintro ⟨a, b, c, d⟩ hdisc ⟨x, y⟩ hz
  have hz' : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; rw [not_or, not_ne_iff, not_ne_iff] at h; obtain ⟨rfl, rfl⟩ := h; exact hz rfl
  exact ⟨foldGauge_pos a b c d x y hdisc hz', hessNorm_pos a b c d x y hdisc hz'⟩

/-- **D4** A positive fold gauge and a nonzero Hessian give the fold-or-nondegenerate condition. -/
theorem gaugeFold : GaugeFoldFacts := by
  intro Ψ hΨ k hg hh
  by_cases hdet : hessDet Ψ k ≠ 0
  · exact Or.inl hdet
  rw [not_ne_iff] at hdet
  refine Or.inr ⟨?_, fun v hv hker => ?_⟩
  · by_contra hall
    simp only [not_exists, not_not] at hall
    simp [hessNorm, hall] at hh
  · have hΨ2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
    have e1 := hker (1, 0)
    have e2 := hker (0, 1)
    rw [OscInt.StationaryPhase.LocalAux.dd_eq_coord hΨ2] at e1 e2
    simp only [mul_one, mul_zero, add_zero, zero_add] at e1 e2
    have hT : ddd Ψ k (kerVec₁ Ψ k) (kerVec₁ Ψ k) (kerVec₁ Ψ k) ≠ 0 ∨
        ddd Ψ k (kerVec₂ Ψ k) (kerVec₂ Ψ k) (kerVec₂ Ψ k) ≠ 0 := by
      by_contra h
      rw [not_or, not_ne_iff, not_ne_iff] at h
      simp [foldGauge, hdet, h.1, h.2] at hg
    rcases hT with hT | hT
    · refine ddd_ne_zero_of_cross hΨ hT hv ?_
      simp only [kerVec₁]; linear_combination -e1
    · refine ddd_ne_zero_of_cross hΨ hT hv ?_
      simp only [kerVec₂]; linear_combination e2

end OscInt.D4
