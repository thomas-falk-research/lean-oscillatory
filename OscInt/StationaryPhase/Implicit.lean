/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.StationaryPhase

/-!
# S2/S3, parts L3–L5: from a normal point to the core hypotheses

`normalizedData : OscInt.Blueprint.NormalizedDataFacts`. Route: `docs/proof-S2S3.md` (L3), (L4) with the
revision items 1 and 3, simplified as follows. Every uniform bound is obtained from continuity at the single
point `(τ₀, 0)` of finitely many jointly continuous functions of `(τ, k)` (product neighbourhood
`U × ball 0 r`, `exists_prod_ball`); the box is then chosen inside the ball, so no tube lemma is needed.

* Directional derivatives `fderiv`, `dd`, `ddd` are iterated derivatives applied to fixed vectors
  (`dd_eq_iteratedFDeriv`, `ddd_eq_iteratedFDeriv`), hence jointly continuous for a family of class `C⁴`.
* One phase (`SliceHyps`): if `|∂²_yQ − c| ≤ |c|/2` on `[-2a, 2a] × [-2b, 2b]` and `|∂_yQ(x, 0)| < |c| b/2`,
  then `y ↦ c ∂_yQ(x, y)` grows at rate `c²/2`, so `∂_yQ(x, ·)` has exactly one zero in `[-2b, 2b]`, lying in
  `(-b, b)` (intermediate value theorem). This zero is `implicitCurve Q b x`. It is `C³` on `(-2a, 2a)`
  because it agrees near each point with the implicit function of Mathlib's `C³` implicit function theorem
  (`ContDiffAt.contDiffAt_implicitFunction`), by uniqueness.
* Explicit formulas `ys′ = Y1`, `ys″ = Y2`, `g″ = G2`, `g‴ = G3` at `(x, ys x)` for `g(x) = Q(x, ys x)`
  (chain rule along the graph). At `(τ₀, 0)` the normal-point conditions give `Y1 = 0`, `G2 = ∂²_xQ(0)`,
  `G3 = ∂³_xQ(0)` (using the symmetry `∂_x∂_yQ = ∂_y∂_xQ`), which yields `ν`; `D` bounds `|ys|`, `|Y1|`, `|Y2|`
  and `‖DⁱQ‖`, `i ≤ 4`, near `(τ₀, 0)`.

The contraction-mapping construction of the route is replaced by the intermediate value theorem; continuity of
`ys` in `τ` is never needed.
-/

open Set Filter Topology OscInt.Statements
open scoped ContDiff

namespace OscInt.StationaryPhase.ImplicitAux

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The directional derivative of `y ↦ Dⁿf(y) m` in direction `w` is `Dⁿ⁺¹f(k) (w, m)`. -/
theorem fderiv_iteratedFDeriv_apply {N : ℕ} {f : E → F} (hf : ContDiff ℝ N f) {n : ℕ} (hn : n < N)
    (m : Fin n → E) (k w : E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ n f y m) k w = iteratedFDeriv ℝ (n + 1) f k (Fin.cons w m) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) k :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast hn) k
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]

/-- `y ↦ Df(y) v` is `Cⁿ` if `f` is `Cⁿ⁺¹`. -/
theorem contDiff_fderiv_apply {n : ℕ} {f : E → F} (hf : ContDiff ℝ (n + 1) f) (v : E) :
    ContDiff ℝ n (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := n) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- A continuous linear endomorphism of `ℝ` with `L 1 ≠ 0` is invertible. -/
theorem isInvertible_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : L.IsInvertible :=
  ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L 1) h), ContinuousLinearMap.ext_ring (by simp)⟩

end General

/-! ## Directional derivatives on `ℝ²` as iterated derivatives -/

theorem fderiv_eq_iteratedFDeriv (f : ℝ × ℝ → ℝ) (k v : ℝ × ℝ) :
    fderiv ℝ f k v = iteratedFDeriv ℝ 1 f k ![v] := by
  simp [iteratedFDeriv_one_apply]

/-- `∂_w∂_vf(k) = D²f(k) (w, v)` for `f ∈ C²`. -/
theorem dd_eq_iteratedFDeriv {N : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ N f) (hN : 2 ≤ N) (k v w : ℝ × ℝ) :
    dd f k v w = iteratedFDeriv ℝ 2 f k ![w, v] := by
  have : (fun y => fderiv ℝ f y v) = fun y => iteratedFDeriv ℝ 1 f y ![v] :=
    funext fun y => fderiv_eq_iteratedFDeriv f y v
  rw [dd, this, fderiv_iteratedFDeriv_apply hf (by omega)]
  rfl

/-- `∂_w∂_v∂_uf(k) = D³f(k) (w, v, u)` for `f ∈ C³`. -/
theorem ddd_eq_iteratedFDeriv {N : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ N f) (hN : 3 ≤ N)
    (k u v w : ℝ × ℝ) : ddd f k u v w = iteratedFDeriv ℝ 3 f k ![w, v, u] := by
  have : (fun y => dd f y u v) = fun y => iteratedFDeriv ℝ 2 f y ![v, u] :=
    funext fun y => dd_eq_iteratedFDeriv hf (by omega) y u v
  rw [ddd, this, fderiv_iteratedFDeriv_apply hf (by omega)]
  rfl

theorem contDiff_dd {n : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (n + 2) f) (v w : ℝ × ℝ) :
    ContDiff ℝ n (fun k => dd f k v w) :=
  contDiff_fderiv_apply (contDiff_fderiv_apply (n := n + 1) (by exact_mod_cast hf) v) w

theorem contDiff_ddd {n : ℕ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (n + 3) f) (u v w : ℝ × ℝ) :
    ContDiff ℝ n (fun k => ddd f k u v w) :=
  contDiff_fderiv_apply (contDiff_dd (n := n + 1) (by exact_mod_cast hf) u v) w

/-- Symmetry of second directional derivatives of a `C²` function. -/
theorem dd_comm {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k v w : ℝ × ℝ) : dd f k v w = dd f k w v := by
  have hd : ∀ y, DifferentiableAt ℝ (fderiv ℝ f) y := fun y =>
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y
  have h : ∀ v w, dd f k v w = fderiv ℝ (fderiv ℝ f) k w v := fun v w => by
    rw [dd, fderiv_clm_apply (hd k) (differentiableAt_const v)]
    simp
  rw [h, h]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) w v

/-! ## Joint continuity in a parameter -/

section Family
variable {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ}

theorem continuous_fderiv_apply {n : ℕ} (hQ : FamilyCk n Q) (hn : 1 ≤ n) (v : ℝ × ℝ) :
    Continuous fun q : T × (ℝ × ℝ) => fderiv ℝ (Q q.1) q.2 v := by
  simp_rw [fderiv_eq_iteratedFDeriv]
  exact (continuous_eval_const _).comp (hQ.2 1 hn)

/-- Second directional derivatives of a `Cⁿ` family (`n ≥ 2`) are jointly continuous. -/
theorem continuous_dd {n : ℕ} (hQ : FamilyCk n Q) (hn : 2 ≤ n) (v w : ℝ × ℝ) :
    Continuous fun q : T × (ℝ × ℝ) => dd (Q q.1) q.2 v w := by
  simp_rw [dd_eq_iteratedFDeriv (hQ.1 _) hn]
  exact (continuous_eval_const _).comp (hQ.2 2 hn)

theorem continuous_ddd {n : ℕ} (hQ : FamilyCk n Q) (hn : 3 ≤ n) (u v w : ℝ × ℝ) :
    Continuous fun q : T × (ℝ × ℝ) => ddd (Q q.1) q.2 u v w := by
  simp_rw [ddd_eq_iteratedFDeriv (hQ.1 _) hn]
  exact (continuous_eval_const _).comp (hQ.2 3 hn)

end Family


/-! ## Chain rule along a graph -/

/-- Chain rule along a graph: `(R(t, f t))′ = ∂_xR + f′ ∂_yR`. -/
theorem hasDerivAt_comp_graph {R : ℝ × ℝ → ℝ} {f : ℝ → ℝ} {x d : ℝ} (hR : DifferentiableAt ℝ R (x, f x))
    (hf : HasDerivAt f d x) :
    HasDerivAt (fun t => R (t, f t)) (fderiv ℝ R (x, f x) (1, 0) + d * fderiv ℝ R (x, f x) (0, 1)) x := by
  have h := hR.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk hf)
  have e : ((1 : ℝ), d) = (1, 0) + d • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [e, map_add, map_smul, smul_eq_mul] at h
  exact h

theorem hasDerivAt_slice {R : ℝ × ℝ → ℝ} {x y : ℝ} (hR : DifferentiableAt ℝ R (x, y)) :
    HasDerivAt (fun t => R (x, t)) (fderiv ℝ R (x, y) (0, 1)) y :=
  hR.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

/-! ## One phase: the implicit critical curve -/

/-- Hypotheses for one phase `Q` on the box `[-2a, 2a] × [-2b, 2b]`: `∂²_yQ` stays within `|c|/2` of
`c ≠ 0`, and `|∂_yQ(x, 0)| < |c| b / 2`. -/
structure SliceHyps (Q : ℝ × ℝ → ℝ) (a b c : ℝ) : Prop where
  smooth : ContDiff ℝ 4 Q
  hb : 0 < b
  hc : c ≠ 0
  yy : ∀ x ∈ Icc (-2 * a) (2 * a), ∀ y ∈ Icc (-2 * b) (2 * b), |dd Q (x, y) (0, 1) (0, 1) - c| ≤ |c| / 2
  y0 : ∀ x ∈ Icc (-2 * a) (2 * a), |fderiv ℝ Q (x, 0) (0, 1)| < |c| / 2 * b

/-- The critical point of `y ↦ Q(x, y)` in `(-b, b)` (any value if there is none). -/
noncomputable def implicitCurve (Q : ℝ × ℝ → ℝ) (b x : ℝ) : ℝ :=
  Classical.epsilon fun y => y ∈ Ioo (-b) b ∧ fderiv ℝ Q (x, y) (0, 1) = 0

theorem sq_half_le_mul_of_abs_sub_le {t c : ℝ} (h : |t - c| ≤ |c| / 2) : c ^ 2 / 2 ≤ c * t := by
  have h1 := neg_abs_le (c * (t - c))
  rw [abs_mul] at h1
  have h2 : |c| * |t - c| ≤ |c| * (|c| / 2) := mul_le_mul_of_nonneg_left h (abs_nonneg c)
  have h3 : |c| * |c| = c ^ 2 := by rw [abs_mul_abs_self, sq]
  nlinarith

theorem half_abs_le_abs_of_abs_sub_le {t c : ℝ} (h : |t - c| ≤ |c| / 2) : |c| / 2 ≤ |t| := by
  have := abs_sub_abs_le_abs_sub c t
  rw [abs_sub_comm] at this
  linarith

section Slice
variable {Q : ℝ × ℝ → ℝ} {a b c : ℝ}

theorem SliceHyps.differentiableAt_dy (h : SliceHyps Q a b c) (k : ℝ × ℝ) :
    DifferentiableAt ℝ (fun k => fderiv ℝ Q k (0, 1)) k :=
  (contDiff_fderiv_apply (n := 3) (by exact_mod_cast h.smooth) _).differentiable (by norm_num) k

/-- `y ↦ c ∂_yQ(x, y)` grows at rate at least `c²/2` on `[-2b, 2b]`. -/
theorem SliceHyps.growth (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Icc (-2 * a) (2 * a)) {y z : ℝ}
    (hy : y ∈ Icc (-2 * b) (2 * b)) (hz : z ∈ Icc (-2 * b) (2 * b)) (hyz : y ≤ z) :
    c ^ 2 / 2 * (z - y) ≤ c * fderiv ℝ Q (x, z) (0, 1) - c * fderiv ℝ Q (x, y) (0, 1) := by
  have hd : ∀ t, HasDerivAt (fun t => c * fderiv ℝ Q (x, t) (0, 1)) (c * dd Q (x, t) (0, 1) (0, 1)) t :=
    fun t => (hasDerivAt_slice (h.differentiableAt_dy (x, t))).const_mul c
  refine (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) y hy z hz hyz
  rw [interior_Icc] at ht
  rw [(hd t).deriv]
  exact sq_half_le_mul_of_abs_sub_le (h.yy x hx t (Ioo_subset_Icc_self ht))

/-- Uniqueness of the critical point of `Q(x, ·)` in `[-2b, 2b]`. -/
theorem SliceHyps.unique (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Icc (-2 * a) (2 * a)) {y z : ℝ}
    (hy : y ∈ Icc (-2 * b) (2 * b)) (hz : z ∈ Icc (-2 * b) (2 * b)) (hy0 : fderiv ℝ Q (x, y) (0, 1) = 0)
    (hz0 : fderiv ℝ Q (x, z) (0, 1) = 0) : y = z := by
  have hc2 : 0 < c ^ 2 / 2 := by have := h.hc; positivity
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h.growth hx hy hz hlt.le
    rw [hy0, hz0] at this
    nlinarith
  · have := h.growth hx hz hy hlt.le
    rw [hy0, hz0] at this
    nlinarith

/-- Existence of a critical point of `Q(x, ·)` in `(-b, b)` (intermediate value theorem). -/
theorem SliceHyps.exists_zero (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Icc (-2 * a) (2 * a)) :
    ∃ y ∈ Ioo (-b) b, fderiv ℝ Q (x, y) (0, 1) = 0 := by
  have hb := h.hb
  have hmem : ∀ t ∈ Icc (-b) b, t ∈ Icc (-2 * b) (2 * b) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0 : (0 : ℝ) ∈ Icc (-2 * b) (2 * b) := ⟨by linarith, by linarith⟩
  have hup := h.growth hx h0 (hmem b ⟨by linarith, le_rfl⟩) hb.le
  have hlo := h.growth hx (hmem (-b) ⟨le_rfl, by linarith⟩) h0 (by linarith)
  have hP := h.y0 x hx
  have hcP : |c * fderiv ℝ Q (x, 0) (0, 1)| < c ^ 2 / 2 * b := by
    rw [abs_mul]
    have h2 : |c| * |fderiv ℝ Q (x, 0) (0, 1)| < |c| * (|c| / 2 * b) :=
      mul_lt_mul_of_pos_left hP (abs_pos.mpr h.hc)
    have h3 : |c| * |c| = c ^ 2 := by rw [abs_mul_abs_self, sq]
    nlinarith
  rw [abs_lt] at hcP
  have hcont : ContinuousOn (fun t => c * fderiv ℝ Q (x, t) (0, 1)) (Icc (-b) b) := fun t _ =>
    ((hasDerivAt_slice (h.differentiableAt_dy (x, t))).const_mul c).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by linarith : -b ≤ b) hcont
    (show (0 : ℝ) ∈ Ioo _ _ from ⟨by nlinarith, by nlinarith⟩)
  exact ⟨y, hy, (mul_eq_zero.mp hy0).resolve_left h.hc⟩

theorem SliceHyps.spec (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Icc (-2 * a) (2 * a)) :
    implicitCurve Q b x ∈ Ioo (-b) b ∧ fderiv ℝ Q (x, implicitCurve Q b x) (0, 1) = 0 := by
  obtain ⟨y, hy⟩ := h.exists_zero hx
  exact Classical.epsilon_spec (p := fun y => y ∈ Ioo (-b) b ∧ fderiv ℝ Q (x, y) (0, 1) = 0) ⟨y, hy⟩

end Slice


section Smooth
variable {Q : ℝ × ℝ → ℝ} {a b c : ℝ}

theorem SliceHyps.dd_ne_zero (h : SliceHyps Q a b c) {x y : ℝ} (hx : x ∈ Icc (-2 * a) (2 * a))
    (hy : y ∈ Icc (-2 * b) (2 * b)) : dd Q (x, y) (0, 1) (0, 1) ≠ 0 := by
  have := half_abs_le_abs_of_abs_sub_le (h.yy x hx y hy)
  have hc := abs_pos.mpr h.hc
  intro h0; rw [h0, abs_zero] at this; linarith

theorem mem_Icc_two_of_mem_Ioo {b y : ℝ} (hy : y ∈ Ioo (-b) b) : y ∈ Icc (-2 * b) (2 * b) := by
  have : 0 < b := by linarith [hy.1, hy.2]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The implicit curve is `C³` on `(-2a, 2a)`: it agrees near each point with the implicit function
given by Mathlib's `C³` implicit function theorem, by uniqueness of the critical point. -/
theorem SliceHyps.contDiffAt (h : SliceHyps Q a b c) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (-2 * a) (2 * a)) :
    ContDiffAt ℝ 3 (implicitCurve Q b) x₀ := by
  set P : ℝ × ℝ → ℝ := fun k => fderiv ℝ Q k (0, 1) with hPdef
  set u : ℝ × ℝ := (x₀, implicitCurve Q b x₀) with hu
  have hx₀' := Ioo_subset_Icc_self hx₀
  obtain ⟨hys, hP0⟩ := h.spec hx₀'
  have cdf : ContDiffAt ℝ 3 P u :=
    (contDiff_fderiv_apply (n := 3) (by exact_mod_cast h.smooth) _).contDiffAt
  have if₂ : (fderiv ℝ P u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply isInvertible_of_apply_one_ne_zero
    simpa [P, dd] using h.dd_ne_zero hx₀' (mem_Icc_two_of_mem_Ioo hys)
  have pn : (3 : ℕ∞ω) ≠ 0 := by norm_num
  set ψ := cdf.implicitFunction pn if₂
  have hψ0 : ψ x₀ = implicitCurve Q b x₀ := cdf.implicitFunction_apply_self pn if₂
  have hψc : ContDiffAt ℝ 3 ψ x₀ := cdf.contDiffAt_implicitFunction pn if₂
  have hev : ∀ᶠ x in 𝓝 x₀, ψ x ∈ Ioo (-2 * b) (2 * b) := by
    apply hψc.continuousAt.eventually_mem
    rw [hψ0]
    exact isOpen_Ioo.mem_nhds ⟨by linarith [hys.1, h.hb], by linarith [hys.2, h.hb]⟩
  refine hψc.congr_of_eventuallyEq ?_
  filter_upwards [cdf.eventually_apply_implicitFunction pn if₂, hev, isOpen_Ioo.mem_nhds hx₀]
    with x h1 h2 h3
  have h3' := Ioo_subset_Icc_self h3
  obtain ⟨hy1, hy2⟩ := h.spec h3'
  refine h.unique h3' (mem_Icc_two_of_mem_Ioo hy1) (Ioo_subset_Icc_self h2) hy2 ?_
  exact h1.trans hP0

theorem SliceHyps.contDiffOn (h : SliceHyps Q a b c) :
    ContDiffOn ℝ 3 (implicitCurve Q b) (Ioo (-2 * a) (2 * a)) :=
  fun _ hx => (h.contDiffAt hx).contDiffWithinAt

end Smooth


/-! ## Derivative formulas along the curve -/

/-- `ys′ = −∂_x∂_yQ / ∂²_yQ` at `(x, ys x)`. -/
noncomputable def Y1 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  -(dd Q k (0, 1) (1, 0) / dd Q k (0, 1) (0, 1))

/-- `ys″` at `(x, ys x)`: the derivative of `Y1` along the curve. -/
noncomputable def Y2 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  -(((ddd Q k (0, 1) (1, 0) (1, 0) + Y1 Q k * ddd Q k (0, 1) (1, 0) (0, 1)) * dd Q k (0, 1) (0, 1) -
      dd Q k (0, 1) (1, 0) * (ddd Q k (0, 1) (0, 1) (1, 0) + Y1 Q k * ddd Q k (0, 1) (0, 1) (0, 1))) /
    dd Q k (0, 1) (0, 1) ^ 2)

/-- `g″` for `g(x) = Q(x, ys x)`. -/
noncomputable def G2 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  dd Q k (1, 0) (1, 0) + Y1 Q k * dd Q k (1, 0) (0, 1)

/-- `g‴` for `g(x) = Q(x, ys x)`. -/
noncomputable def G3 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  ddd Q k (1, 0) (1, 0) (1, 0) + Y1 Q k * ddd Q k (1, 0) (1, 0) (0, 1) + Y2 Q k * dd Q k (1, 0) (0, 1) +
    Y1 Q k * (ddd Q k (1, 0) (0, 1) (1, 0) + Y1 Q k * ddd Q k (1, 0) (0, 1) (0, 1))

section Derivs
variable {Q : ℝ × ℝ → ℝ} {a b c : ℝ}

theorem hasDerivAt_fderiv_graph {f : ℝ → ℝ} {x d : ℝ} (hQ : ContDiff ℝ 4 Q) (hf : HasDerivAt f d x)
    (v : ℝ × ℝ) :
    HasDerivAt (fun t => fderiv ℝ Q (t, f t) v) (dd Q (x, f x) v (1, 0) + d * dd Q (x, f x) v (0, 1)) x :=
  hasDerivAt_comp_graph
    ((contDiff_fderiv_apply (n := 3) (by exact_mod_cast hQ) v).differentiable (by norm_num) _) hf

theorem hasDerivAt_dd_graph {f : ℝ → ℝ} {x d : ℝ} (hQ : ContDiff ℝ 4 Q) (hf : HasDerivAt f d x)
    (u v : ℝ × ℝ) :
    HasDerivAt (fun t => dd Q (t, f t) u v)
      (ddd Q (x, f x) u v (1, 0) + d * ddd Q (x, f x) u v (0, 1)) x :=
  hasDerivAt_comp_graph ((contDiff_dd (n := 2) (by exact_mod_cast hQ) u v).differentiable (by norm_num) _) hf

/-- `ys′(x) = −∂_x∂_yQ/∂²_yQ` at `(x, ys x)`, by differentiating `∂_yQ(x, ys x) = 0`. -/
theorem SliceHyps.hasDerivAt (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (implicitCurve Q b) (Y1 Q (x, implicitCurve Q b x)) x := by
  set ys := implicitCurve Q b
  have hd : HasDerivAt ys (deriv ys x) x :=
    ((h.contDiffAt hx).differentiableAt (by norm_num)).hasDerivAt
  have h1 := hasDerivAt_fderiv_graph h.smooth hd (0, 1)
  have h0 : HasDerivAt (fun t => fderiv ℝ Q (t, ys t) (0, 1)) 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact (h.spec (Ioo_subset_Icc_self ht)).2
  have he := h1.unique h0
  have hne : dd Q (x, ys x) (0, 1) (0, 1) ≠ 0 := h.dd_ne_zero (Ioo_subset_Icc_self hx)
    (mem_Icc_two_of_mem_Ioo (h.spec (Ioo_subset_Icc_self hx)).1)
  convert hd using 1
  rw [Y1]
  field_simp
  linarith

theorem SliceHyps.hasDerivAt_Y1 (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => Y1 Q (t, implicitCurve Q b t)) (Y2 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have hne := h.dd_ne_zero (Ioo_subset_Icc_self hx)
    (mem_Icc_two_of_mem_Ioo (h.spec (Ioo_subset_Icc_self hx)).1)
  exact ((hasDerivAt_dd_graph h.smooth hd (0, 1) (1, 0)).div (hasDerivAt_dd_graph h.smooth hd (0, 1) (0, 1))
    hne).neg

theorem SliceHyps.deriv_eq (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    deriv (implicitCurve Q b) x = Y1 Q (x, implicitCurve Q b x) :=
  (h.hasDerivAt hx).deriv

theorem SliceHyps.iteratedDeriv_two (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    iteratedDeriv 2 (implicitCurve Q b) x = Y2 Q (x, implicitCurve Q b x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (implicitCurve Q b) =ᶠ[𝓝 x] fun t => Y1 Q (t, implicitCurve Q b t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact h.deriv_eq ht
  rw [this.deriv_eq]
  exact (h.hasDerivAt_Y1 hx).deriv

/-- `g′(x) = ∂_xQ(x, ys x)` since `∂_yQ(x, ys x) = 0`. -/
theorem SliceHyps.deriv_reduced (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    deriv (fun t => Q (t, implicitCurve Q b t)) x = fderiv ℝ Q (x, implicitCurve Q b x) (1, 0) := by
  have h1 := hasDerivAt_comp_graph ((h.smooth.differentiable (by norm_num)) _) (h.hasDerivAt hx)
  rw [(h.spec (Ioo_subset_Icc_self hx)).2, mul_zero, add_zero] at h1
  exact h1.deriv

theorem SliceHyps.hasDerivAt_G2 (h : SliceHyps Q a b c) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => G2 Q (t, implicitCurve Q b t)) (G3 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have := (hasDerivAt_dd_graph h.smooth hd (1, 0) (1, 0)).fun_add
    ((h.hasDerivAt_Y1 hx).fun_mul (hasDerivAt_dd_graph h.smooth hd (1, 0) (0, 1)))
  convert this using 1
  · rfl
  · simp only [G3]; ring

/-- `g″ = G2` along the curve, for `g(x) = Q(x, ys x)`. -/
theorem SliceHyps.iteratedDeriv_two_reduced (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    iteratedDeriv 2 (fun t => Q (t, implicitCurve Q b t)) x = G2 Q (x, implicitCurve Q b x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (fun t => Q (t, implicitCurve Q b t)) =ᶠ[𝓝 x]
      fun t => fderiv ℝ Q (t, implicitCurve Q b t) (1, 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact h.deriv_reduced ht
  rw [this.deriv_eq]
  exact (hasDerivAt_fderiv_graph h.smooth (h.hasDerivAt hx) (1, 0)).deriv

/-- `g‴ = G3` along the curve, for `g(x) = Q(x, ys x)`. -/
theorem SliceHyps.iteratedDeriv_three_reduced (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    iteratedDeriv 3 (fun t => Q (t, implicitCurve Q b t)) x = G3 Q (x, implicitCurve Q b x) := by
  rw [iteratedDeriv_succ]
  have : iteratedDeriv 2 (fun t => Q (t, implicitCurve Q b t)) =ᶠ[𝓝 x]
      fun t => G2 Q (t, implicitCurve Q b t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact h.iteratedDeriv_two_reduced ht
  rw [this.deriv_eq]
  exact (h.hasDerivAt_G2 hx).deriv

end Derivs


/-! ## Joint continuity of the formulas at a point -/

section FamilyCont
variable {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {p₀ : T × (ℝ × ℝ)}

theorem continuousAt_Y1 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => Y1 (Q q.1) q.2) p₀ :=
  ((continuous_dd hQ (by norm_num) _ _).continuousAt.div (continuous_dd hQ (by norm_num) _ _).continuousAt
    hne).neg

theorem continuousAt_Y2 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => Y2 (Q q.1) q.2) p₀ := by
  have h2 : ∀ v w, ContinuousAt (fun q : T × (ℝ × ℝ) => dd (Q q.1) q.2 v w) p₀ :=
    fun v w => (continuous_dd hQ (by norm_num) v w).continuousAt
  have h3 : ∀ u v w, ContinuousAt (fun q : T × (ℝ × ℝ) => ddd (Q q.1) q.2 u v w) p₀ :=
    fun u v w => (continuous_ddd hQ (by norm_num) u v w).continuousAt
  have hY := continuousAt_Y1 hQ hne
  exact (((((h3 _ _ _).add (hY.mul (h3 _ _ _))).mul (h2 _ _)).sub
    ((h2 _ _).mul ((h3 _ _ _).add (hY.mul (h3 _ _ _))))).div ((h2 _ _).pow 2) (pow_ne_zero 2 hne)).neg

theorem continuousAt_G2 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => G2 (Q q.1) q.2) p₀ :=
  (continuous_dd hQ (by norm_num) _ _).continuousAt.add
    ((continuousAt_Y1 hQ hne).mul (continuous_dd hQ (by norm_num) _ _).continuousAt)

theorem continuousAt_G3 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => G3 (Q q.1) q.2) p₀ := by
  have h2 : ∀ v w, ContinuousAt (fun q : T × (ℝ × ℝ) => dd (Q q.1) q.2 v w) p₀ :=
    fun v w => (continuous_dd hQ (by norm_num) v w).continuousAt
  have h3 : ∀ u v w, ContinuousAt (fun q : T × (ℝ × ℝ) => ddd (Q q.1) q.2 u v w) p₀ :=
    fun u v w => (continuous_ddd hQ (by norm_num) u v w).continuousAt
  have hY := continuousAt_Y1 hQ hne
  exact (((h3 _ _ _).add (hY.mul (h3 _ _ _))).add ((continuousAt_Y2 hQ hne).mul (h2 _ _))).add
    (hY.mul ((h3 _ _ _).add (hY.mul (h3 _ _ _))))

theorem continuous_sum_norm (hQ : FamilyCk 4 Q) :
    Continuous fun q : T × (ℝ × ℝ) => ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q q.1) q.2‖ :=
  continuous_finsetSum _ fun i hi => (hQ.2 i (by simp at hi; omega)).norm

end FamilyCont

theorem eventually_abs_sub_lt {X : Type*} [TopologicalSpace X] {f : X → ℝ} {p : X} (hf : ContinuousAt f p)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q in 𝓝 p, |f q - f p| < ε := by
  filter_upwards [hf.eventually_mem (Metric.ball_mem_nhds _ hε)] with q hq
  rwa [Metric.mem_ball, Real.dist_eq] at hq

theorem dist_zero_lt {x y r : ℝ} (hx : |x| < r) (hy : |y| < r) : dist ((x, y) : ℝ × ℝ) 0 < r := by
  rw [Prod.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
  exact max_lt hx hy

/-- A product neighbourhood `U × ball 0 r` on which a property eventually true at `(τ₀, 0)` holds. -/
theorem exists_prod_ball {T : Type} [TopologicalSpace T] {τ₀ : T} {p : T × (ℝ × ℝ) → Prop}
    (h : ∀ᶠ q in 𝓝 (τ₀, (0 : ℝ × ℝ)), p q) :
    ∃ U ∈ 𝓝 τ₀, ∃ r > 0, ∀ τ ∈ U, ∀ x y : ℝ, |x| < r → |y| < r → p (τ, (x, y)) := by
  rw [nhds_prod_eq, eventually_prod_iff] at h
  obtain ⟨pa, ha, pb, hb, hab⟩ := h
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp hb
  exact ⟨{τ | pa τ}, ha, r, hr, fun τ hτ x y hx hy => hab hτ (hr' (dist_zero_lt hx hy))⟩


theorem abs_lt_add_one_of {t t₀ : ℝ} (h : |t - t₀| < 1) : |t| < |t₀| + 1 := by
  have := abs_sub_abs_le_abs_sub t t₀; linarith

theorem half_lt_abs_of {t t₀ : ℝ} (h : |t - t₀| < |t₀| / 2) : |t₀| / 2 < |t| := by
  have := abs_sub_abs_le_abs_sub t₀ t; rw [abs_sub_comm] at this; linarith

/-- The neighbourhood data, uniform near `τ₀`, from continuity at `(τ₀, 0)` of finitely many functions. -/
theorem exists_nbhd_data {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {τ₀ : T}
    {G : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ} (hQ : FamilyCk 4 Q)
    (hcont : ContinuousAt (fun q : T × (ℝ × ℝ) => G (Q q.1) q.2) (τ₀, 0)) (hG0 : G (Q τ₀) 0 ≠ 0)
    (hq0 : dd (Q τ₀) 0 (0, 1) (0, 1) ≠ 0) :
    ∃ U ∈ 𝓝 τ₀, ∃ r > 0, ∀ τ ∈ U, ∀ x y : ℝ, |x| < r → |y| < r →
      |dd (Q τ) (x, y) (0, 1) (0, 1) - dd (Q τ₀) 0 (0, 1) (0, 1)| ≤ |dd (Q τ₀) 0 (0, 1) (0, 1)| / 2 ∧
      ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q τ) (x, y)‖ <
        ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q τ₀) 0‖ + 1 ∧
      |Y1 (Q τ) (x, y)| < |Y1 (Q τ₀) 0| + 1 ∧ |Y2 (Q τ) (x, y)| < |Y2 (Q τ₀) 0| + 1 ∧
      |G (Q τ₀) 0| / 2 < |G (Q τ) (x, y)| := by
  refine exists_prod_ball (p := fun q =>
    |dd (Q q.1) q.2 (0, 1) (0, 1) - dd (Q τ₀) 0 (0, 1) (0, 1)| ≤ |dd (Q τ₀) 0 (0, 1) (0, 1)| / 2 ∧
      ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q q.1) q.2‖ <
        ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q τ₀) 0‖ + 1 ∧
      |Y1 (Q q.1) q.2| < |Y1 (Q τ₀) 0| + 1 ∧ |Y2 (Q q.1) q.2| < |Y2 (Q τ₀) 0| + 1 ∧
      |G (Q τ₀) 0| / 2 < |G (Q q.1) q.2|) ?_
  have e1 := eventually_abs_sub_lt (continuous_dd hQ (by norm_num) (0, 1) (0, 1)).continuousAt
    (half_pos (abs_pos.mpr hq0)) (p := (τ₀, 0))
  have e2 := eventually_abs_sub_lt (continuous_sum_norm hQ).continuousAt one_pos (p := (τ₀, 0))
  have e3 := eventually_abs_sub_lt (continuousAt_Y1 (p₀ := (τ₀, 0)) hQ hq0) one_pos
  have e4 := eventually_abs_sub_lt (continuousAt_Y2 (p₀ := (τ₀, 0)) hQ hq0) one_pos
  have e5 := eventually_abs_sub_lt hcont (half_pos (abs_pos.mpr hG0))
  filter_upwards [e1, e2, e3, e4, e5] with q h1 h2 h3 h4 h5
  refine ⟨h1.le, ?_, abs_lt_add_one_of h3, abs_lt_add_one_of h4, half_lt_abs_of h5⟩
  have := (abs_lt.mp h2).2
  linarith


theorem norm_iteratedFDeriv_le_sum (f : ℝ × ℝ → ℝ) (k : ℝ × ℝ) {i : ℕ} (hi : i ≤ 4) :
    ‖iteratedFDeriv ℝ i f k‖ ≤ ∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i f k‖ :=
  Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f k‖) (fun i _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

theorem abs_lt_of_mem_Icc {x l u r : ℝ} (hx : x ∈ Icc l u) (hl : -r < l) (hu : u < r) : |x| < r :=
  abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Assembly of the core hypotheses on a neighbourhood of `τ₀`, for any formula `G` for the `j`-th
derivative of the reduced phase which is continuous at `(τ₀, 0)` and nonzero there. -/
theorem exists_coreHyps (j : ℕ) (G : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ)
    (hG : ∀ (P : ℝ × ℝ → ℝ) (a b c : ℝ), SliceHyps P a b c → ∀ x ∈ Ioo (-2 * a) (2 * a),
      iteratedDeriv j (fun t => P (t, implicitCurve P b t)) x = G P (x, implicitCurve P b x))
    {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {τ₀ : T} (hQ : FamilyCk 4 Q)
    (hcont : ContinuousAt (fun q : T × (ℝ × ℝ) => G (Q q.1) q.2) (τ₀, 0)) (hG0 : G (Q τ₀) 0 ≠ 0)
    (hq0 : dd (Q τ₀) 0 (0, 1) (0, 1) ≠ 0) (hP0 : fderiv ℝ (Q τ₀) 0 (0, 1) = 0) :
    ∃ U ∈ 𝓝 τ₀, ∃ a b μ ν D : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : T → ℝ → ℝ, ∀ τ ∈ U, OscInt.Blueprint.CoreHyps j a b μ ν D (Q τ) (ys τ) := by
  obtain ⟨U₁, hU₁, r, hr, H⟩ := exists_nbhd_data hQ hcont hG0 hq0
  set q₀ := dd (Q τ₀) 0 (0, 1) (0, 1)
  set b := r / 4 with hbdef
  have hb : 0 < b := by positivity
  have hε : 0 < |q₀| / 2 * b := by have := abs_pos.mpr hq0; positivity
  obtain ⟨U₂, hU₂, r', hr', H'⟩ :=
    exists_prod_ball (p := fun q => |fderiv ℝ (Q q.1) q.2 (0, 1)| < |q₀| / 2 * b) (by
      have := eventually_abs_sub_lt (continuous_fderiv_apply hQ (by norm_num) (0, 1)).continuousAt hε
        (p := (τ₀, 0))
      filter_upwards [this] with q hq
      simpa [hP0] using hq)
  set a := min r r' / 4 with hadef
  have ha : 0 < a := by positivity
  have har : 2 * a < r := by have := min_le_left r r'; linarith
  have har' : 2 * a < r' := by have := min_le_right r r'; linarith
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, a, b, |q₀| / 2, |G (Q τ₀) 0| / 2,
    max (max b (|Y1 (Q τ₀) 0| + 1)) (max (|Y2 (Q τ₀) 0| + 1)
      (∑ i ∈ Finset.range 5, ‖iteratedFDeriv ℝ i (Q τ₀) 0‖ + 1)), ha, hb,
    by have := abs_pos.mpr hq0; positivity, by have := abs_pos.mpr hG0; positivity,
    fun τ => implicitCurve (Q τ) b, fun τ hτ => ?_⟩
  have hS : SliceHyps (Q τ) a b q₀ :=
    { smooth := by exact_mod_cast hQ.1 τ
      hb := hb
      hc := hq0
      yy := fun x hx y hy => (H τ hτ.1 x y (abs_lt_of_mem_Icc hx (by linarith) har)
        (abs_lt_of_mem_Icc hy (by linarith) (by linarith))).1
      y0 := fun x hx => H' τ hτ.2 x 0 (abs_lt_of_mem_Icc hx (by linarith) har') (by simpa using hr') }
  have hIoo : ∀ x ∈ Icc (-a) a, x ∈ Ioo (-2 * a) (2 * a) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxr : ∀ x ∈ Icc (-a) a, |x| < r := fun x hx => abs_lt_of_mem_Icc hx (by linarith) (by linarith)
  have hyr : ∀ x ∈ Icc (-a) a, |implicitCurve (Q τ) b x| < r := fun x hx =>
    abs_lt_of_mem_Icc (Ioo_subset_Icc_self (hS.spec (Ioo_subset_Icc_self (hIoo x hx))).1)
      (by linarith) (by linarith)
  refine ⟨hS.smooth, hS.contDiffOn, fun x hx => hS.spec (Ioo_subset_Icc_self (hIoo x hx)),
    fun x hx y hy => half_abs_le_abs_of_abs_sub_le (hS.yy x (Ioo_subset_Icc_self (hIoo x hx)) y hy),
    fun i hi x hx y hy => ?_, fun i hi x hx => ?_, fun x hx => ?_⟩
  · have h1 := (H τ hτ.1 x y (hxr x hx) (abs_lt_of_mem_Icc hy (by linarith) (by linarith))).2.1
    exact ((norm_iteratedFDeriv_le_sum _ _ hi).trans h1.le).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hH := H τ hτ.1 x _ (hxr x hx) (hyr x hx)
    interval_cases i
    · have h1 := (hS.spec (Ioo_subset_Icc_self (hIoo x hx))).1
      rw [iteratedDeriv_zero]
      exact (abs_lt.mpr ⟨h1.1, h1.2⟩).le.trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [iteratedDeriv_one, hS.deriv_eq (hIoo x hx)]
      exact hH.2.2.1.le.trans ((le_max_right _ _).trans (le_max_left _ _))
    · rw [hS.iteratedDeriv_two (hIoo x hx)]
      exact hH.2.2.2.1.le.trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hG _ _ _ _ hS x (hIoo x hx)]
    exact (H τ hτ.1 x _ (hxr x hx) (hyr x hx)).2.2.2.2.le

end OscInt.StationaryPhase.ImplicitAux

namespace OscInt.StationaryPhase

open ImplicitAux in
/-- **L3–L5** From a normal point to the core hypotheses (`NormalizedDataFacts`). -/
theorem normalizedData : OscInt.Blueprint.NormalizedDataFacts := by
  intro j hj T _ Q τ₀ hQ hN
  obtain ⟨-, hP0, hq0, hxy, h2, h3⟩ := hN
  have hsm : ContDiff ℝ 2 (Q τ₀) := (hQ.1 τ₀).of_le (by norm_num)
  have hyx : dd (Q τ₀) 0 (1, 0) (0, 1) = 0 := by rw [dd_comm hsm]; exact hxy
  have hY0 : Y1 (Q τ₀) 0 = 0 := by simp [Y1, hxy]
  rcases hj with rfl | rfl
  · exact exists_coreHyps 2 G2 (fun P a b c h x hx => h.iteratedDeriv_two_reduced hx) hQ
      (continuousAt_G2 (p₀ := (τ₀, 0)) hQ hq0) (by simpa [G2, hY0] using h2 rfl) hq0 hP0
  · exact exists_coreHyps 3 G3 (fun P a b c h x hx => h.iteratedDeriv_three_reduced hx) hQ
      (continuousAt_G3 (p₀ := (τ₀, 0)) hQ hq0) (by simpa [G3, hY0, hyx] using (h3 rfl).2) hq0 hP0

end OscInt.StationaryPhase

