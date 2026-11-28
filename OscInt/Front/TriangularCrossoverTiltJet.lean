/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.TriangularCrossoverBaseData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Batch A5U, part A11: the tilt jets (`A5TiltJetFacts`)

Route `docs/proof-A5U.md`, section 2; blueprint `A5TiltJetFacts`. Deviation from the blueprint's sketch: the
jets are computed directly in the fixed chart instead of through TRI-Q, P6 and the reduced bridge (the values are
the same; TRI-Q's quartic `12(8α*² − 1)/(4α*) = 24α* − 3/α*` is what the computation below reproduces).

With `θ = θ₀`, `φ(u) = θ + ys(u)` and A8:
* `∂_sQ_{α,q}(u, s) = −2 sin(θ + s) cos u + 2 sin θ + q` (`a5uW_dQs`), so the curve equation is
  `sin φ(u) cos u = sin θ + q/2` on `[−a, a]`; differentiating twice at `0` gives `φ′(0) = 0` and
  `cos φ(0) φ″(0) = sin φ(0)` (`a5uW_constraint_core`), since `cos φ(0) ≠ 0` for `|ys 0| < π/4`.
* `g′(u) = −2 cos φ(u) sin u − 2α sin 2u` on `(−a, a)` (`a5uW_red_hasDeriv`, the curve equation kills the
  `ys′` terms); three more derivatives at `0` give `g″(0) = −2 cos φ(0) − 4α` and
  `g⁗(0) = 6 sin φ(0) φ″(0) + 2 cos φ(0) + 16α` (`a5uW_jet_core`).
* With `C = cos φ(0) = −2α*`, `S² = 1 − C²`: `g″(0) = 4(α* − α)` and `g⁗(0) = 8α* − 3/α* + 16α
  = 24α* − 3/α* − 4g″(0)`; and `24α* − 3/α* = (α* − a₀)(24 + 3/(α* a₀))` (`a₀² = 1/8`) gives the inequality
  (`a5uW_alg`).
-/

open Set Filter Topology OscInt.Statements OscInt.Blueprint OscInt.Blueprint.A5U
  OscInt.StationaryPhase.ImplicitAux
open scoped ContDiff

namespace OscInt.A5UAux

/-! ## The chart phase, explicitly -/

/-- `∂_sQ_{α,q}(x, s) = −2 sin(θ₀ + s) cos x + 2 sin θ₀ + q` (A8). -/
theorem a5uW_dQs (h8 : A5FixedChartFacts) (a₀ α q x s : ℝ) :
    fderiv ℝ (a5Q a₀ α q) (x, s) (0, 1) =
      -2 * Real.sin (a5Theta a₀ + s) * Real.cos x + 2 * Real.sin (a5Theta a₀) + q := by
  have e : a5Q a₀ α q = fun k : ℝ × ℝ => 2 * Real.cos (a5Theta a₀ + k.2) * Real.cos k.1 -
      2 * Real.cos (a5Theta a₀) + α * (Real.cos (2 * k.1) - 1) + 2 * k.2 * Real.sin (a5Theta a₀) + q * k.2 := by
    funext k; simp only [a5Q]; rw [h8]
  have hd : Differentiable ℝ (a5Q a₀ α q) := by rw [e]; fun_prop
  have h1 := hasDerivAt_slice (hd (x, s))
  have e2 : (fun t => a5Q a₀ α q (x, t)) = fun t => 2 * Real.cos (a5Theta a₀ + t) * Real.cos x -
      2 * Real.cos (a5Theta a₀) + α * (Real.cos (2 * x) - 1) + 2 * t * Real.sin (a5Theta a₀) + q * t := by
    rw [e]
  rw [e2] at h1
  have hc := (((hasDerivAt_id' s).const_add (a5Theta a₀)).cos.const_mul 2).mul_const (Real.cos x)
  have hl := ((hasDerivAt_id' s).const_mul 2).mul_const (Real.sin (a5Theta a₀))
  have h2 := (((hc.sub_const (2 * Real.cos (a5Theta a₀))).add_const (α * (Real.cos (2 * x) - 1))).add hl).add
    ((hasDerivAt_id' s).const_mul q)
  rw [h1.unique h2]
  ring

/-- Along a critical curve, `g′ = −2 cos(θ₀ + ys u) sin u − 2α sin 2u` (A8 and the curve equation). -/
theorem a5uW_red_hasDeriv (h8 : A5FixedChartFacts) {a₀ α q u d : ℝ} {ys : ℝ → ℝ} (hys : HasDerivAt ys d u)
    (hK : 2 * Real.sin (a5Theta a₀ + ys u) * Real.cos u = 2 * Real.sin (a5Theta a₀) + q) :
    HasDerivAt (a5Red a₀ α q ys)
      (-2 * Real.cos (a5Theta a₀ + ys u) * Real.sin u - 2 * α * Real.sin (2 * u)) u := by
  have e : a5Red a₀ α q ys = fun u => 2 * Real.cos (a5Theta a₀ + ys u) * Real.cos u -
      2 * Real.cos (a5Theta a₀) + α * (Real.cos (2 * u) - 1) + 2 * ys u * Real.sin (a5Theta a₀) + q * ys u := by
    funext u; simp only [a5Red, a5Q]; rw [h8]
  rw [e]
  have hc := (((hys.const_add (a5Theta a₀)).cos.const_mul 2).mul (Real.hasDerivAt_cos u)).sub_const
    (2 * Real.cos (a5Theta a₀))
  have hα := (((hasDerivAt_id' u).const_mul 2).cos.sub_const 1).const_mul α
  have h := ((hc.add hα).add ((hys.const_mul 2).mul_const (Real.sin (a5Theta a₀)))).add (hys.const_mul q)
  refine h.congr_deriv ?_
  linear_combination (-d) * hK

/-! ## One-variable jet computations -/

/-- The curve equation `sin p(u) cos u = c₀` near `0` gives `p′(0) = 0` and `cos p(0) p″(0) = sin p(0)`. -/
theorem a5uW_constraint_core {p p1 p2 : ℝ → ℝ} {a c₀ : ℝ} (ha : 0 < a)
    (hp : ∀ u ∈ Ioo (-a) a, HasDerivAt p (p1 u) u) (hp1 : HasDerivAt p1 (p2 0) 0)
    (hK : ∀ u ∈ Ioo (-a) a, Real.sin (p u) * Real.cos u = c₀) (hC : Real.cos (p 0) ≠ 0) :
    p1 0 = 0 ∧ Real.cos (p 0) * p2 0 = Real.sin (p 0) := by
  have hn : ∀ u ∈ Ioo (-a) a, Ioo (-a) a ∈ 𝓝 u := fun u hu => isOpen_Ioo.mem_nhds hu
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hK1 : ∀ u ∈ Ioo (-a) a,
      Real.cos (p u) * p1 u * Real.cos u - Real.sin (p u) * Real.sin u = 0 := by
    intro u hu
    have h1 : HasDerivAt (fun u => Real.sin (p u) * Real.cos u)
        (Real.cos (p u) * p1 u * Real.cos u - Real.sin (p u) * Real.sin u) u := by
      refine ((hp u hu).sin.mul (Real.hasDerivAt_cos u)).congr_deriv ?_; ring
    have h2 : HasDerivAt (fun u => Real.sin (p u) * Real.cos u) 0 u :=
      (hasDerivAt_const u c₀).congr_of_eventuallyEq (by filter_upwards [hn u hu] with v hv; exact hK v hv)
    exact h1.unique h2
  have h10 : p1 0 = 0 := by
    have := hK1 0 h0
    simp only [Real.sin_zero, Real.cos_zero, mul_zero, mul_one, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hC
  refine ⟨h10, ?_⟩
  have h3 := (((hp 0 h0).cos.mul hp1).mul (Real.hasDerivAt_cos 0)).sub ((hp 0 h0).sin.mul (Real.hasDerivAt_sin 0))
  have h4 : HasDerivAt (fun u => Real.cos (p u) * p1 u * Real.cos u - Real.sin (p u) * Real.sin u) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (by filter_upwards [hn 0 h0] with v hv; exact hK1 v hv)
  have := h3.unique h4
  simp only [Real.sin_zero, Real.cos_zero, h10] at this
  linarith

/-- The jets of `g` with `g′ = −2 cos p(u) sin u − 2α sin 2u` near `0` and `p′(0) = 0`. -/
theorem a5uW_jet_core {p p1 p2 g : ℝ → ℝ} {a α d : ℝ} (ha : 0 < a)
    (hp : ∀ u ∈ Ioo (-a) a, HasDerivAt p (p1 u) u) (hp1 : ∀ u ∈ Ioo (-a) a, HasDerivAt p1 (p2 u) u)
    (hp2 : HasDerivAt p2 d 0) (h10 : p1 0 = 0)
    (hg : ∀ u ∈ Ioo (-a) a,
      HasDerivAt g (-2 * Real.cos (p u) * Real.sin u - 2 * α * Real.sin (2 * u)) u) :
    iteratedDeriv 2 g 0 = -2 * Real.cos (p 0) - 4 * α ∧
      iteratedDeriv 4 g 0 = 6 * Real.sin (p 0) * p2 0 + 2 * Real.cos (p 0) + 16 * α := by
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hn : Ioo (-a) a ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds h0
  have d1 : ∀ u ∈ Ioo (-a) a,
      HasDerivAt (fun u => -2 * Real.cos (p u) * Real.sin u - 2 * α * Real.sin (2 * u))
        (2 * Real.sin (p u) * p1 u * Real.sin u - 2 * Real.cos (p u) * Real.cos u -
          4 * α * Real.cos (2 * u)) u := by
    intro u hu
    refine ((((hp u hu).cos.const_mul (-2)).mul (Real.hasDerivAt_sin u)).sub
      (((hasDerivAt_id' u).const_mul 2).sin.const_mul (2 * α))).congr_deriv ?_
    ring
  have d2 : ∀ u ∈ Ioo (-a) a,
      HasDerivAt (fun u => 2 * Real.sin (p u) * p1 u * Real.sin u - 2 * Real.cos (p u) * Real.cos u -
          4 * α * Real.cos (2 * u))
        (2 * Real.cos (p u) * p1 u ^ 2 * Real.sin u + 2 * Real.sin (p u) * p2 u * Real.sin u +
          4 * Real.sin (p u) * p1 u * Real.cos u + 2 * Real.cos (p u) * Real.sin u +
          8 * α * Real.sin (2 * u)) u := by
    intro u hu
    refine (((((((hp u hu).sin.const_mul 2).mul (hp1 u hu)).mul (Real.hasDerivAt_sin u)).sub
      (((hp u hu).cos.const_mul 2).mul (Real.hasDerivAt_cos u))).sub
      (((hasDerivAt_id' u).const_mul 2).cos.const_mul (4 * α)))).congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have d3 : HasDerivAt (fun u => 2 * Real.cos (p u) * p1 u ^ 2 * Real.sin u + 2 * Real.sin (p u) * p2 u * Real.sin u +
      4 * Real.sin (p u) * p1 u * Real.cos u + 2 * Real.cos (p u) * Real.sin u + 8 * α * Real.sin (2 * u))
      (6 * Real.sin (p 0) * p2 0 + 2 * Real.cos (p 0) + 16 * α) 0 := by
    refine ((((((((hp 0 h0).cos.const_mul 2).mul ((hp1 0 h0).pow 2)).mul (Real.hasDerivAt_sin 0)).add
      ((((hp 0 h0).sin.const_mul 2).mul hp2).mul (Real.hasDerivAt_sin 0))).add
      ((((hp 0 h0).sin.const_mul 4).mul (hp1 0 h0)).mul (Real.hasDerivAt_cos 0))).add
      (((hp 0 h0).cos.const_mul 2).mul (Real.hasDerivAt_sin 0))).add
      (((hasDerivAt_id' (0 : ℝ)).const_mul 2).sin.const_mul (8 * α))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Real.sin_zero, Real.cos_zero, h10, mul_zero]
    ring
  have e1 : deriv g =ᶠ[𝓝 0] fun u => -2 * Real.cos (p u) * Real.sin u - 2 * α * Real.sin (2 * u) := by
    filter_upwards [hn] with u hu; exact (hg u hu).deriv
  have e2 : deriv (fun u => -2 * Real.cos (p u) * Real.sin u - 2 * α * Real.sin (2 * u)) =ᶠ[𝓝 0]
      fun u => 2 * Real.sin (p u) * p1 u * Real.sin u - 2 * Real.cos (p u) * Real.cos u -
        4 * α * Real.cos (2 * u) := by
    filter_upwards [hn] with u hu; exact (d1 u hu).deriv
  have e3 : deriv (fun u => 2 * Real.sin (p u) * p1 u * Real.sin u - 2 * Real.cos (p u) * Real.cos u -
      4 * α * Real.cos (2 * u)) =ᶠ[𝓝 0] fun u => 2 * Real.cos (p u) * p1 u ^ 2 * Real.sin u +
        2 * Real.sin (p u) * p2 u * Real.sin u + 4 * Real.sin (p u) * p1 u * Real.cos u +
        2 * Real.cos (p u) * Real.sin u + 8 * α * Real.sin (2 * u) := by
    filter_upwards [hn] with u hu; exact (d2 u hu).deriv
  constructor
  · rw [iteratedDeriv_succ', e1.iteratedDeriv_eq, iteratedDeriv_one, (d1 0 h0).deriv]
    simp [h10]
  · rw [iteratedDeriv_succ', e1.iteratedDeriv_eq, iteratedDeriv_succ', e2.iteratedDeriv_eq, iteratedDeriv_succ',
      e3.iteratedDeriv_eq, iteratedDeriv_one, d3.deriv]

/-! ## The moving coupling and the algebra -/

/-- `α* a₀ > 0` for `|ys 0| < π/4`: `θ₀ = 3π/4` for `a₀ > 0` and `θ₀ = π/4` for `a₀ < 0`. -/
theorem a5uW_moving_pos {a₀ y : ℝ} (ha₀ : |a₀| = triExceptional) (hy : |y| < Real.pi / 4) :
    0 < -Real.cos (a5Theta a₀ + y) / 2 * a₀ := by
  have hpi := Real.pi_pos
  have hy' := abs_lt.mp hy
  rcases lt_or_gt_of_ne (a5uW_ne_zero ha₀) with hl | hl
  · have e : a₀ = -triExceptional := by rw [← ha₀, abs_of_neg hl, neg_neg]
    have hθ : a5Theta a₀ = Real.pi / 4 := by
      rw [a5Theta, e, show -2 * -triExceptional = 2 * triExceptional by ring,
        OscInt.API.TriDeriv.arccos_two_triExceptional]
    have : 0 < Real.cos (a5Theta a₀ + y) :=
      Real.cos_pos_of_mem_Ioo ⟨by rw [hθ]; linarith, by rw [hθ]; linarith⟩
    nlinarith
  · have e : a₀ = triExceptional := by rw [← ha₀, abs_of_pos hl]
    have hθ : a5Theta a₀ = 3 * Real.pi / 4 := by
      rw [a5Theta, e, OscInt.API.TriDeriv.arccos_neg_two_triExceptional]
    have : Real.cos (a5Theta a₀ + y) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by rw [hθ]; linarith) (by rw [hθ]; linarith)
    nlinarith

/-- `|α* − a₀| ≤ |y|/2`. -/
theorem a5uW_moving_close {a₀ y : ℝ} (ha₀ : |a₀| = triExceptional) :
    |-Real.cos (a5Theta a₀ + y) / 2 - a₀| ≤ |y| / 2 := by
  have hc := a5uW_cos_theta ha₀
  have e : -Real.cos (a5Theta a₀ + y) / 2 - a₀ = (Real.cos (a5Theta a₀) - Real.cos (a5Theta a₀ + y)) / 2 := by
    rw [hc]; ring
  rw [e, abs_div, abs_two]
  have := Real.abs_cos_sub_cos_le (a5Theta a₀) (a5Theta a₀ + y)
  rw [show a5Theta a₀ - (a5Theta a₀ + y) = -y by ring, abs_neg] at this
  linarith

theorem a5uW_B0 {a₀ m : ℝ} (ha : a₀ ^ 2 = 1 / 8) (hm0 : m ≠ 0) (ha0 : a₀ ≠ 0) :
    24 * m - 3 / m = (m - a₀) * (24 + 3 / (m * a₀)) := by
  field_simp
  linear_combination (24 * m) * ha

/-- The jets in terms of `α* = −C/2` and the separation inequality. -/
theorem a5uW_alg {a₀ C S d α : ℝ} (ha : a₀ ^ 2 = 1 / 8) (hpos : 0 < -C / 2 * a₀) (hCS : S ^ 2 + C ^ 2 = 1)
    (hd : C * d = S) :
    -2 * C - 4 * α = 4 * (-C / 2 - α) ∧
      6 * S * d + 2 * C + 16 * α = 24 * (-C / 2) - 3 / (-C / 2) - 4 * (-2 * C - 4 * α) ∧
      24 * |α - a₀| - 10 * |-2 * C - 4 * α| ≤ |6 * S * d + 2 * C + 16 * α| := by
  have hC : C ≠ 0 := by rintro rfl; simp at hpos
  have ha0 : a₀ ≠ 0 := by rintro rfl; simp at hpos
  have h2 : 6 * S * d + 2 * C + 16 * α = 24 * (-C / 2) - 3 / (-C / 2) - 4 * (-2 * C - 4 * α) := by
    field_simp
    linear_combination (12 * S) * hd + 12 * hCS
  refine ⟨by ring, h2, ?_⟩
  set m := -C / 2 with hm
  have hm0 : m ≠ 0 := by rw [hm]; intro h; apply hC; linarith
  have hB0 := a5uW_B0 ha hm0 ha0
  have hpos' : 0 < 24 + 3 / (m * a₀) := by have := div_pos (by norm_num : (0 : ℝ) < 3) hpos; linarith
  have hB0abs : 24 * |m - a₀| ≤ |24 * m - 3 / m| := by
    rw [hB0, abs_mul, abs_of_pos hpos']
    have := div_pos (by norm_num : (0 : ℝ) < 3) hpos
    nlinarith [abs_nonneg (m - a₀)]
  rw [h2]
  have hA : -2 * C - 4 * α = 4 * (m - α) := by rw [hm]; ring
  rw [hA]
  have t1 := abs_sub_abs_le_abs_sub (24 * m - 3 / m) (4 * (4 * (m - α)))
  have t2 := abs_sub_le α m a₀
  have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  simp only [abs_mul, h4] at t1 ⊢
  rw [abs_sub_comm α m] at t2
  linarith

/-! ## A11 -/

theorem a5uW_hasDerivAt {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s) {u : ℝ}
    (hu : u ∈ s) : HasDerivAt f (deriv f u) u :=
  ((hf.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hu)).hasDerivAt

/-- **A11** The tilt jets, from A8. -/
theorem a5TiltJet : OscInt.Blueprint.A5U.A5TiltJetFacts := by
  intro h8 a₀ ha₀ q a ys ha hys hcrit hy
  have hU : IsOpen (Ioo (-2 * a) (2 * a)) := isOpen_Ioo
  have hys1 : ContDiffOn ℝ ∞ (deriv ys) (Ioo (-2 * a) (2 * a)) := hys.deriv_of_isOpen hU (by simp)
  have hys2 : ContDiffOn ℝ ∞ (deriv (deriv ys)) (Ioo (-2 * a) (2 * a)) := hys1.deriv_of_isOpen hU (by simp)
  have hsub : ∀ u ∈ Ioo (-a) a, u ∈ Ioo (-2 * a) (2 * a) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hd0 : ∀ u ∈ Ioo (-a) a, HasDerivAt (fun u => a5Theta a₀ + ys u) (deriv ys u) u := fun u hu =>
    (a5uW_hasDerivAt hys hU (hsub u hu)).const_add _
  have hd1 : ∀ u ∈ Ioo (-a) a, HasDerivAt (deriv ys) (deriv (deriv ys) u) u := fun u hu =>
    a5uW_hasDerivAt hys1 hU (hsub u hu)
  have hd2 := a5uW_hasDerivAt hys2 hU (hsub 0 h0)
  have hK : ∀ u ∈ Ioo (-a) a,
      2 * Real.sin (a5Theta a₀ + ys u) * Real.cos u = 2 * Real.sin (a5Theta a₀) + q := by
    intro u hu
    have := hcrit u (Ioo_subset_Icc_self hu)
    rw [a5uW_dQs h8] at this
    linarith
  have hpos := a5uW_moving_pos ha₀ hy
  have hCne : Real.cos (a5Theta a₀ + ys 0) ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  obtain ⟨h10, h20⟩ := a5uW_constraint_core (p := fun u => a5Theta a₀ + ys u) (p1 := deriv ys)
    (p2 := deriv (deriv ys)) (c₀ := Real.sin (a5Theta a₀) + q / 2) ha hd0 (hd1 0 h0)
    (fun u hu => by
      show Real.sin (a5Theta a₀ + ys u) * Real.cos u = _
      have := hK u hu; linarith) hCne
  refine ⟨hpos, a5uW_moving_close ha₀, fun α => ?_⟩
  obtain ⟨j2, j4⟩ := a5uW_jet_core (g := a5Red a₀ α q ys) (α := α) ha hd0 hd1 hd2 h10
    (fun u hu => a5uW_red_hasDeriv h8 (a5uW_hasDerivAt hys hU (hsub u hu)) (hK u hu))
  have ha2 : a₀ ^ 2 = 1 / 8 := by rw [← sq_abs, ha₀, OscInt.API.TriDeriv.triExceptional_sq]
  have hCS := Real.sin_sq_add_cos_sq (a5Theta a₀ + ys 0)
  rw [j2, j4, a5Moving]
  exact a5uW_alg ha2 hpos hCS h20

end OscInt.A5UAux
