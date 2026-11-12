/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Cusp
import OscInt.StationaryPhase.Implicit

/-! Batch A3, P3: explicit order-four extension of StationaryPhase.Implicit.
Every derivative below is in the spatial variables; the parameter is only topological.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`. -/

namespace OscInt.StationaryPhase.ImplicitAux

open Set Filter Topology MeasureTheory OscInt.Statements
open scoped ContDiff

/-- Differentiate the order-three directional derivative in one more direction. -/
noncomputable def dddd (Q : ℝ × ℝ → ℝ) (k u v w z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun s => ddd Q s u v w) k z

/-- The two inner differentiations commute by `dd_comm`, pointwise before differentiation. -/
theorem ddd_swap12 {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 3 Q) (k u v w : ℝ × ℝ) :
    ddd Q k u v w = ddd Q k v u w := by
  have he : (fun s => dd Q s u v) = fun s => dd Q s v u :=
    funext fun s => dd_comm (hQ.of_le (by norm_num)) s u v
  change fderiv ℝ (fun s => dd Q s u v) k w = fderiv ℝ (fun s => dd Q s v u) k w
  rw [he]

/-- The two outer differentiations commute by `dd_comm` applied to a directional derivative. -/
theorem ddd_swap23 {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 3 Q) (k u v w : ℝ × ℝ) :
    ddd Q k u v w = ddd Q k u w v := by
  exact dd_comm (contDiff_fderiv_apply (n := 2) hQ u) k v w

/-- The extra directional derivative is the fourth iterated derivative, with reversed slots. -/
theorem dddd_eq_iteratedFDeriv {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 4 Q)
    (k u v w z : ℝ × ℝ) :
    dddd Q k u v w z = iteratedFDeriv ℝ 4 Q k ![z, w, v, u] := by
  have he : (fun s => ddd Q s u v w) = fun s => iteratedFDeriv ℝ 3 Q s ![w, v, u] :=
    funext fun s => ddd_eq_iteratedFDeriv hQ (by norm_num) s u v w
  rw [dddd, he, fderiv_iteratedFDeriv_apply hQ (by norm_num)]
  rfl

/-- Chain rule for an order-three directional derivative along a differentiable graph. -/
theorem hasDerivAt_ddd_graph {Q : ℝ × ℝ → ℝ} {f : ℝ → ℝ} {x d : ℝ}
    (hQ : ContDiff ℝ 4 Q) (hf : HasDerivAt f d x) (u v w : ℝ × ℝ) :
    HasDerivAt (fun t => ddd Q (t, f t) u v w)
      (dddd Q (x, f x) u v w (1, 0) + d * dddd Q (x, f x) u v w (0, 1)) x :=
  hasDerivAt_comp_graph ((contDiff_ddd (n := 1) (by exact_mod_cast hQ) u v w).differentiable
    (by norm_num) _) hf

/-- Derivative of an order-three entry in the graph direction `(1,Y1)`. -/
noncomputable def d3Graph (Q : ℝ × ℝ → ℝ) (k u v w : ℝ × ℝ) : ℝ :=
  dddd Q k u v w (1, 0) + Y1 Q k * dddd Q k u v w (0, 1)

noncomputable def dyx1 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  ddd Q k (0, 1) (1, 0) (1, 0) + Y1 Q k * ddd Q k (0, 1) (1, 0) (0, 1)

noncomputable def dyy1 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  ddd Q k (0, 1) (0, 1) (1, 0) + Y1 Q k * ddd Q k (0, 1) (0, 1) (0, 1)

noncomputable def dyx2 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  d3Graph Q k (0, 1) (1, 0) (1, 0) + Y2 Q k * ddd Q k (0, 1) (1, 0) (0, 1) +
    Y1 Q k * d3Graph Q k (0, 1) (1, 0) (0, 1)

noncomputable def dyy2 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  d3Graph Q k (0, 1) (0, 1) (1, 0) + Y2 Q k * ddd Q k (0, 1) (0, 1) (0, 1) +
    Y1 Q k * d3Graph Q k (0, 1) (0, 1) (0, 1)

/-- Quotient rule for `Y2`; its denominator is nonzero wherever a slice is used. -/
noncomputable def Y3 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  -(((dyx2 Q k * dd Q k (0, 1) (0, 1) - dd Q k (0, 1) (1, 0) * dyy2 Q k) *
        dd Q k (0, 1) (0, 1) ^ 2 -
      (dyx1 Q k * dd Q k (0, 1) (0, 1) - dd Q k (0, 1) (1, 0) * dyy1 Q k) *
        (2 * dd Q k (0, 1) (0, 1) * dyy1 Q k)) / (dd Q k (0, 1) (0, 1) ^ 2) ^ 2)

/-- Explicit derivative of the repository's `G3` along its critical graph. -/
noncomputable def G4 (Q : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  d3Graph Q k (1, 0) (1, 0) (1, 0) +
    (Y2 Q k * ddd Q k (1, 0) (1, 0) (0, 1) + Y1 Q k * d3Graph Q k (1, 0) (1, 0) (0, 1)) +
    (Y3 Q k * dd Q k (1, 0) (0, 1) +
      Y2 Q k * (ddd Q k (1, 0) (0, 1) (1, 0) + Y1 Q k * ddd Q k (1, 0) (0, 1) (0, 1))) +
    (Y2 Q k * (ddd Q k (1, 0) (0, 1) (1, 0) + Y1 Q k * ddd Q k (1, 0) (0, 1) (0, 1)) +
      Y1 Q k * (d3Graph Q k (1, 0) (0, 1) (1, 0) +
        (Y2 Q k * ddd Q k (1, 0) (0, 1) (0, 1) + Y1 Q k * d3Graph Q k (1, 0) (0, 1) (0, 1))))

section Derivs
variable {Q : ℝ × ℝ → ℝ} {a b c : ℝ}

/-- Differentiate the numerator entry `Q_yx` twice along the critical graph. -/
theorem SliceHyps.hasDerivAt_dyx1 (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => dyx1 Q (t, implicitCurve Q b t)) (dyx2 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have hh := (hasDerivAt_ddd_graph h.smooth hd (0, 1) (1, 0) (1, 0)).fun_add
    ((h.hasDerivAt_Y1 hx).fun_mul (hasDerivAt_ddd_graph h.smooth hd (0, 1) (1, 0) (0, 1)))
  convert hh using 1
  · rfl
  · simp only [dyx2, d3Graph]; ring

/-- Differentiate the denominator entry `Q_yy` twice along the critical graph. -/
theorem SliceHyps.hasDerivAt_dyy1 (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => dyy1 Q (t, implicitCurve Q b t)) (dyy2 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have hh := (hasDerivAt_ddd_graph h.smooth hd (0, 1) (0, 1) (1, 0)).fun_add
    ((h.hasDerivAt_Y1 hx).fun_mul (hasDerivAt_ddd_graph h.smooth hd (0, 1) (0, 1) (0, 1)))
  convert hh using 1
  · rfl
  · simp only [dyy2, d3Graph]; ring

/-- Apply the quotient rule to `Y2`, using the transverse nonvanishing supplied by `SliceHyps`. -/
theorem SliceHyps.hasDerivAt_Y2 (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => Y2 Q (t, implicitCurve Q b t)) (Y3 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have hne := h.dd_ne_zero (Ioo_subset_Icc_self hx)
    (mem_Icc_two_of_mem_Ioo (h.spec (Ioo_subset_Icc_self hx)).1)
  have hA := hasDerivAt_dd_graph h.smooth hd (0, 1) (1, 0)
  have hB := hasDerivAt_dd_graph h.smooth hd (0, 1) (0, 1)
  have hh := ((((h.hasDerivAt_dyx1 hx).fun_mul hB).fun_sub
    (hA.fun_mul (h.hasDerivAt_dyy1 hx))).div (hB.pow 2) (pow_ne_zero 2 hne)).neg
  convert hh using 1
  · rfl
  · simp only [Y3, dyx1, dyy1]
    norm_num <;> ring

/-- Product rule on the four summands defining `G3`. -/
theorem SliceHyps.hasDerivAt_G3 (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    HasDerivAt (fun t => G3 Q (t, implicitCurve Q b t)) (G4 Q (x, implicitCurve Q b x)) x := by
  have hd := h.hasDerivAt hx
  have hY := h.hasDerivAt_Y1 hx
  have hh := (((hasDerivAt_ddd_graph h.smooth hd (1, 0) (1, 0) (1, 0)).fun_add
    (hY.fun_mul (hasDerivAt_ddd_graph h.smooth hd (1, 0) (1, 0) (0, 1)))).fun_add
    ((h.hasDerivAt_Y2 hx).fun_mul (hasDerivAt_dd_graph h.smooth hd (1, 0) (0, 1)))).fun_add
    (hY.fun_mul ((hasDerivAt_ddd_graph h.smooth hd (1, 0) (0, 1) (1, 0)).fun_add
      (hY.fun_mul (hasDerivAt_ddd_graph h.smooth hd (1, 0) (0, 1) (0, 1)))))
  convert hh using 1
  · rfl
  · simp only [G4, d3Graph]

/-- Differentiate the existing local identity for the reduced order-three derivative. -/
theorem SliceHyps.iteratedDeriv_four_reduced (h : SliceHyps Q a b c) {x : ℝ}
    (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    iteratedDeriv 4 (fun t => Q (t, implicitCurve Q b t)) x = G4 Q (x, implicitCurve Q b x) := by
  rw [iteratedDeriv_succ]
  have he : iteratedDeriv 3 (fun t => Q (t, implicitCurve Q b t)) =ᶠ[𝓝 x]
      fun t => G3 Q (t, implicitCurve Q b t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact h.iteratedDeriv_three_reduced ht
  rw [he.deriv_eq]
  exact (h.hasDerivAt_G3 hx).deriv

end Derivs

section FamilyCont
variable {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ} {p₀ : T × (ℝ × ℝ)}

/-- Evaluate the jointly continuous fourth iterated derivative at a fixed tuple. -/
theorem continuous_dddd (hQ : FamilyCk 4 Q) (u v w z : ℝ × ℝ) :
    Continuous fun q : T × (ℝ × ℝ) => dddd (Q q.1) q.2 u v w z := by
  simp_rw [dddd_eq_iteratedFDeriv (hQ.1 _)]
  exact (continuous_eval_const _).comp (hQ.2 4 (by norm_num))

theorem continuousAt_d3Graph (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0)
    (u v w : ℝ × ℝ) : ContinuousAt (fun q : T × (ℝ × ℝ) => d3Graph (Q q.1) q.2 u v w) p₀ :=
  (continuous_dddd hQ u v w (1, 0)).continuousAt.add
    ((continuousAt_Y1 hQ hne).mul (continuous_dddd hQ u v w (0, 1)).continuousAt)

/-- Continuity of the rational formula for `Y3` uses only nonvanishing of `Q_yy`. -/
theorem continuousAt_Y3 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => Y3 (Q q.1) q.2) p₀ := by
  have h2 := fun v w => (continuous_dd hQ (by norm_num) v w).continuousAt (x := p₀)
  have h3 := fun u v w => (continuous_ddd hQ (by norm_num) u v w).continuousAt (x := p₀)
  have hd := continuousAt_d3Graph (p₀ := p₀) hQ hne
  have hY := continuousAt_Y1 hQ hne
  have hZ := continuousAt_Y2 hQ hne
  have hA1 : ContinuousAt (fun q : T × (ℝ × ℝ) => dyx1 (Q q.1) q.2) p₀ :=
    (h3 _ _ _).add (hY.mul (h3 _ _ _))
  have hB1 : ContinuousAt (fun q : T × (ℝ × ℝ) => dyy1 (Q q.1) q.2) p₀ :=
    (h3 _ _ _).add (hY.mul (h3 _ _ _))
  have hA2 : ContinuousAt (fun q : T × (ℝ × ℝ) => dyx2 (Q q.1) q.2) p₀ :=
    ((hd _ _ _).add (hZ.mul (h3 _ _ _))).add (hY.mul (hd _ _ _))
  have hB2 : ContinuousAt (fun q : T × (ℝ × ℝ) => dyy2 (Q q.1) q.2) p₀ :=
    ((hd _ _ _).add (hZ.mul (h3 _ _ _))).add (hY.mul (hd _ _ _))
  exact (((((hA2.mul (h2 _ _)).sub ((h2 _ _).mul hB2)).mul ((h2 _ _).pow 2)).sub
    (((hA1.mul (h2 _ _)).sub ((h2 _ _).mul hB1)).mul
      ((continuousAt_const.mul (h2 _ _)).mul hB1))).div (((h2 _ _).pow 2).pow 2)
      (pow_ne_zero 2 (pow_ne_zero 2 hne))).neg

/-- `G4` is a finite algebraic expression in jointly continuous derivative entries and `Y1,Y2,Y3`. -/
theorem continuousAt_G4 (hQ : FamilyCk 4 Q) (hne : dd (Q p₀.1) p₀.2 (0, 1) (0, 1) ≠ 0) :
    ContinuousAt (fun q : T × (ℝ × ℝ) => G4 (Q q.1) q.2) p₀ := by
  have h2 := fun v w => (continuous_dd hQ (by norm_num) v w).continuousAt (x := p₀)
  have h3 := fun u v w => (continuous_ddd hQ (by norm_num) u v w).continuousAt (x := p₀)
  have hd := continuousAt_d3Graph (p₀ := p₀) hQ hne
  have hY := continuousAt_Y1 hQ hne
  have hZ := continuousAt_Y2 hQ hne
  have hW := continuousAt_Y3 hQ hne
  exact (((hd _ _ _).add ((hZ.mul (h3 _ _ _)).add (hY.mul (hd _ _ _)))).add
    ((hW.mul (h2 _ _)).add (hZ.mul ((h3 _ _ _).add (hY.mul (h3 _ _ _)))))).add
    ((hZ.mul ((h3 _ _ _).add (hY.mul (h3 _ _ _)))).add
      (hY.mul ((hd _ _ _).add ((hZ.mul (h3 _ _ _)).add (hY.mul (hd _ _ _))))))

end FamilyCont

/-- At a normal point, cancellation leaves precisely the reduced quartic. -/
theorem G4_eq_reduced {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 4 Q)
    (hne : dd Q 0 (0, 1) (0, 1) ≠ 0) (hxy : dd Q 0 (0, 1) (1, 0) = 0) :
    G4 Q 0 = iteratedFDeriv ℝ 4 Q 0 ![(1, 0), (1, 0), (1, 0), (1, 0)] -
      3 * ddd Q 0 (1, 0) (1, 0) (0, 1) ^ 2 / dd Q 0 (0, 1) (0, 1) := by
  have hQ3 : ContDiff ℝ 3 Q := hQ.of_le (by norm_num)
  have hyx : dd Q 0 (1, 0) (0, 1) = 0 := by
    rw [dd_comm (hQ.of_le (by norm_num))]; exact hxy
  have hT : ddd Q 0 (0, 1) (1, 0) (1, 0) = ddd Q 0 (1, 0) (1, 0) (0, 1) := by
    rw [ddd_swap12 hQ3, ddd_swap23 hQ3]
  have hS : ddd Q 0 (1, 0) (0, 1) (1, 0) = ddd Q 0 (1, 0) (1, 0) (0, 1) :=
    ddd_swap23 hQ3 _ _ _ _
  have hY : Y1 Q 0 = 0 := by simp [Y1, hxy]
  have hZ : Y2 Q 0 = -(ddd Q 0 (1, 0) (1, 0) (0, 1) / dd Q 0 (0, 1) (0, 1)) := by
    simp only [Y2, hY, hxy, hT, zero_mul, mul_zero, add_zero, sub_zero]
    field_simp [hne]
    <;> ring
  simp only [G4, d3Graph, hY, hZ, hyx, hS, zero_mul, mul_zero, add_zero, zero_add]
  rw [dddd_eq_iteratedFDeriv hQ]
  ring

end OscInt.StationaryPhase.ImplicitAux

namespace OscInt.Cusp

open OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase.ImplicitAux
open scoped ContDiff

/-- A3-P3: apply the existing generic neighbourhood construction to the explicit `G4`. -/
theorem normalizedData4 : NormalizedData4Facts := by
  intro T _ Q τ₀ hQ hN
  obtain ⟨hP0, hq0, hxy, hred⟩ := hN
  refine exists_coreHyps 4 G4 (fun P a b c h x hx => h.iteratedDeriv_four_reduced hx) hQ
    (continuousAt_G4 (p₀ := (τ₀, 0)) hQ hq0) ?_ hq0 hP0
  rw [G4_eq_reduced (hQ.1 τ₀) hq0 hxy]
  exact hred

end OscInt.Cusp
