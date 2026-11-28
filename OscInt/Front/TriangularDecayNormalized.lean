/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularDecay
import OscInt.StationaryPhase.Implicit
import OscInt.Front.ReducedBridge

/-!
# Batch K2, parts P2, P5, P6: normalized data of order m, existence of a reduced curve, the order-2 identity

Route: `docs/proof-K2.md`, section 1 ("P2"), section 2 ("P5", "P6") and section 8, items 1 and 4 (which supersede
section 1 for P2; option (a), the operator route).

* `OscInt.K2.normalizedDataM : NormalizedDataMFacts` (P2).
* `OscInt.K2.reducedCurveExists : ReducedCurveExistsFacts` (P5).
* `OscInt.K2.reducedOrderTwo : ReducedOrderTwoFacts` (P6).

Shared lemma (the `C^∞` slice root): under `SliceHyps Q a b c` with `Q` of class `C^∞`, the root
`implicitCurve Q b` is `C^∞` at every point of `(−2a, 2a)` (`contDiffAt_implicitCurve_top`), by the argument of
`SliceHyps.contDiffAt` with `n = ∞`.

P2, option (a). With `Y1 = −Q_xy/Q_yy` and `D f = f_x + Y1 f_y` (`Dop`), set `Gop Q 0 = Q_x` and
`Gop Q (j + 1) = D (Gop Q j)`. These are `C^∞` on the open set `{Q_yy ≠ 0}`. For any curve `y`, differentiable on an
open set `U` with `Q_y(t, y t) = 0` and `Q_yy(t, y t) ≠ 0` on `U`, `y′ = Y1(·, y ·)` and
`g^{(j+1)} = (Gop Q j)(·, y ·)` on `U` for `g t = Q(t, y t)` (`iteratedDeriv_reduced_eq`). For the family
`Q_q = F + q·s` the operator does not depend on `q` (`Gop_addq`). Along `h` this gives `Gop F (m − 1) 0 ≠ 0`; the
box, the constants and `q₀` come from continuity at `0` of finitely many functions of `k` alone.

P5. The slice root of `(u, s) ↦ Ψ(k₀ + uv + sw) − s DΨ(k₀)w` near `0`, composed with a smooth `ψ` equal to the
identity near `0` and with values in `[−a, a]` (the cutoff device of `OscInt.API.TriWitness.exists_cutoff`).

P6. `g″(0) = D²[v, v] + h′(0) D²[w, v]` from `ReducedBridge.hasDerivAt_reducedFn`, and
`D²[v, w] + h′(0) D²[w, w] = 0` from the curve equation.
-/

open Set Filter Topology OscInt.Statements OscInt.StationaryPhase.ImplicitAux
open scoped ContDiff

namespace OscInt.K2.NormalizedDataMAux

/-! ## Smoothness of directional derivatives -/

theorem contDiff_fderiv_apply_top {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun k => fderiv ℝ f k v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_dd_top {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (v w : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun k => dd f k v w) :=
  contDiff_fderiv_apply_top (contDiff_fderiv_apply_top hf v) w

/-! ## The `C^∞` slice root -/

section Slice
variable {Q : ℝ × ℝ → ℝ} {a b c : ℝ}

/-- The implicit curve of a `C^∞` phase is `C^∞` at every point of `(−2a, 2a)`. -/
theorem contDiffAt_implicitCurve_top (h : SliceHyps Q a b c) (hQ : ContDiff ℝ ∞ Q) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo (-2 * a) (2 * a)) : ContDiffAt ℝ ∞ (implicitCurve Q b) x₀ := by
  set P : ℝ × ℝ → ℝ := fun k => fderiv ℝ Q k (0, 1) with hPdef
  set u : ℝ × ℝ := (x₀, implicitCurve Q b x₀) with hu
  have hx₀' := Ioo_subset_Icc_self hx₀
  obtain ⟨hys, hP0⟩ := h.spec hx₀'
  have cdf : ContDiffAt ℝ ∞ P u := (contDiff_fderiv_apply_top hQ _).contDiffAt
  have if₂ : (fderiv ℝ P u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply isInvertible_of_apply_one_ne_zero
    simpa [P, dd] using h.dd_ne_zero hx₀' (mem_Icc_two_of_mem_Ioo hys)
  have pn : (∞ : ℕ∞ω) ≠ 0 := by simp
  set ψ := cdf.implicitFunction pn if₂
  have hψ0 : ψ x₀ = implicitCurve Q b x₀ := cdf.implicitFunction_apply_self pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ x₀ := cdf.contDiffAt_implicitFunction pn if₂
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

theorem contDiffOn_implicitCurve_top (h : SliceHyps Q a b c) (hQ : ContDiff ℝ ∞ Q) :
    ContDiffOn ℝ ∞ (implicitCurve Q b) (Ioo (-2 * a) (2 * a)) :=
  fun _ hx => (contDiffAt_implicitCurve_top h hQ hx).contDiffWithinAt

end Slice

/-! ## The operator `D f = f_x + Y1 f_y` -/

/-- `D f = ∂_x f + Y1 ∂_y f`, the derivative along the critical curve. -/
noncomputable def Dop (Q f : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  fderiv ℝ f k (1, 0) + Y1 Q k * fderiv ℝ f k (0, 1)

/-- `Gop Q j = D^j ∂_xQ`, the formula for the `(j + 1)`-th derivative of the reduced phase. -/
noncomputable def Gop (Q : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => fun k => fderiv ℝ Q k (1, 0)
  | j + 1 => Dop Q (Gop Q j)

/-- The open set where `∂²_yQ ≠ 0`. -/
def Wset (Q : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) := {k | dd Q k (0, 1) (0, 1) ≠ 0}

section Operator
variable {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ ∞ Q)
include hQ

theorem isOpen_Wset : IsOpen (Wset Q) :=
  isOpen_ne_fun (contDiff_dd_top hQ _ _).continuous continuous_const

theorem contDiffOn_Y1 : ContDiffOn ℝ ∞ (Y1 Q) (Wset Q) := by
  have := ((contDiff_dd_top hQ (0, 1) (1, 0)).contDiffOn.div (contDiff_dd_top hQ (0, 1) (0, 1)).contDiffOn
    (fun k hk => hk) (s := Wset Q)).neg
  exact this

theorem contDiffOn_Dop {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Wset Q)) :
    ContDiffOn ℝ ∞ (Dop Q f) (Wset Q) := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) (Wset Q) := hf.fderiv_of_isOpen (isOpen_Wset hQ) (by simp)
  have h1 : ∀ v : ℝ × ℝ, ContDiffOn ℝ ∞ (fun k => fderiv ℝ f k v) (Wset Q) :=
    fun v => hd.clm_apply contDiffOn_const
  exact (h1 _).add ((contDiffOn_Y1 hQ).mul (h1 _))

theorem contDiffOn_Gop : ∀ j : ℕ, ContDiffOn ℝ ∞ (Gop Q j) (Wset Q)
  | 0 => (contDiff_fderiv_apply_top hQ _).contDiffOn
  | j + 1 => contDiffOn_Dop hQ (contDiffOn_Gop j)

variable {U : Set ℝ} (hU : IsOpen U) {y : ℝ → ℝ} (hy : ∀ t ∈ U, DifferentiableAt ℝ y t)
  (h0 : ∀ t ∈ U, fderiv ℝ Q (t, y t) (0, 1) = 0) (hne : ∀ t ∈ U, dd Q (t, y t) (0, 1) (0, 1) ≠ 0)
include hU hy h0 hne

/-- `y′ = Y1(·, y ·)` along any differentiable curve of critical points with `∂²_yQ ≠ 0`. -/
theorem hasDerivAt_root {t : ℝ} (ht : t ∈ U) : HasDerivAt y (Y1 Q (t, y t)) t := by
  have hd := (hy t ht).hasDerivAt
  have h1 := hasDerivAt_comp_graph
    ((contDiff_fderiv_apply_top hQ (0, 1)).differentiable (by simp) (t, y t)) hd
  have h0' : HasDerivAt (fun s => fderiv ℝ Q (s, y s) (0, 1)) 0 t := by
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds ht] with s hs
    exact h0 s hs
  have he := h1.unique h0'
  change dd Q (t, y t) (0, 1) (1, 0) + deriv y t * dd Q (t, y t) (0, 1) (0, 1) = 0 at he
  have hn := hne t ht
  convert hd using 1
  rw [Y1, neg_eq_iff_eq_neg, div_eq_iff hn]
  linear_combination he

/-- The operator identity: `g^{(j+1)} = (Gop Q j)(·, y ·)` on `U`, for `g t = Q(t, y t)`. -/
theorem iteratedDeriv_reduced_eq (j : ℕ) :
    ∀ t ∈ U, iteratedDeriv (j + 1) (fun s => Q (s, y s)) t = Gop Q j (t, y t) := by
  induction j with
  | zero =>
    intro t ht
    rw [zero_add, iteratedDeriv_one]
    have := hasDerivAt_comp_graph ((hQ.differentiable (by simp)) (t, y t))
      (hasDerivAt_root hQ hU hy h0 hne ht)
    rw [h0 t ht, mul_zero, add_zero] at this
    exact this.deriv
  | succ j ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv (j + 1) (fun s => Q (s, y s)) =ᶠ[𝓝 t] fun s => Gop Q j (s, y s) := by
      filter_upwards [hU.mem_nhds ht] with s hs
      exact ih s hs
    rw [hev.deriv_eq]
    have hW : (t, y t) ∈ Wset Q := hne t ht
    have hdiff : DifferentiableAt ℝ (Gop Q j) (t, y t) :=
      ((contDiffOn_Gop hQ j).differentiableOn (by simp)).differentiableAt ((isOpen_Wset hQ).mem_nhds hW)
    exact (hasDerivAt_comp_graph hdiff (hasDerivAt_root hQ hU hy h0 hne ht)).deriv

end Operator

/-! ## The family `F + q·s` -/

section Family
variable {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (q : ℝ)
include hF

theorem fderiv_addq (k v : ℝ × ℝ) :
    fderiv ℝ (fun k => F k + q * k.2) k v = fderiv ℝ F k v + q * v.2 := by
  have := ((hF.differentiable (by simp)) k).hasFDerivAt.add (hasFDerivAt_snd.const_mul q)
  rw [show (fun k => F k + q * k.2) = (F + fun y => q * y.2) from rfl, this.fderiv]
  simp

theorem dd_addq (k v w : ℝ × ℝ) : dd (fun k => F k + q * k.2) k v w = dd F k v w := by
  unfold dd
  have : (fun y => fderiv ℝ (fun k => F k + q * k.2) y v) = fun y => fderiv ℝ F y v + q * v.2 :=
    funext fun y => fderiv_addq hF q y v
  rw [this, fderiv_add_const]

theorem Y1_addq : Y1 (fun k => F k + q * k.2) = Y1 F :=
  funext fun k => by simp only [Y1, dd_addq hF]

/-- The operator formulas do not depend on the transverse velocity `q`. -/
theorem Gop_addq : ∀ j : ℕ, Gop (fun k => F k + q * k.2) j = Gop F j
  | 0 => funext fun k => by simp [Gop, fderiv_addq hF q]
  | j + 1 => by
    show Dop _ (Gop _ j) = Dop F (Gop F j)
    rw [Gop_addq j]
    unfold Dop
    rw [Y1_addq hF]

theorem norm_iteratedFDeriv_addq_le (i : ℕ) (k : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun k => F k + q * k.2) k‖ ≤
      ‖iteratedFDeriv ℝ i F k‖ + |q| * ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) k‖ := by
  have hs : ContDiff ℝ ∞ (fun k : ℝ × ℝ => k.2) := contDiff_snd
  have e : (fun k : ℝ × ℝ => F k + q * k.2) = F + q • (fun k : ℝ × ℝ => k.2) := by
    funext k; simp
  have hsa : ContDiffAt ℝ i (q • fun k : ℝ × ℝ => k.2) k := (contDiff_infty.1 hs i).contDiffAt.const_smul q
  rw [e, iteratedFDeriv_add_apply (contDiff_infty.1 hF i).contDiffAt hsa,
    iteratedFDeriv_const_smul_apply (contDiff_infty.1 hs i).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]

end Family

/-! ## P5: the phase whose slice root is the reduced curve, and the cutoff -/

section Reduced
variable {Ψ : ℝ × ℝ → ℝ} {k₀ v w : ℝ × ℝ}

/-- The chart `(u, s) ↦ k₀ + u v + s w`. -/
def chartMap (k₀ v w : ℝ × ℝ) (k : ℝ × ℝ) : ℝ × ℝ := k₀ + k.1 • v + k.2 • w

theorem hasFDerivAt_chartMap (k : ℝ × ℝ) :
    HasFDerivAt (chartMap k₀ v w)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w) k :=
  ((hasFDerivAt_fst.smul_const v).const_add k₀).add (hasFDerivAt_snd.smul_const w)

theorem contDiff_chartMap : ContDiff ℝ ∞ (chartMap k₀ v w) :=
  (contDiff_const.add (contDiff_fst.smul contDiff_const)).add (contDiff_snd.smul contDiff_const)

/-- `∂_s f(k₀ + u v + s w) = Df(k₀ + u v + s w) w`. -/
theorem fderiv_comp_chartMap {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (k : ℝ × ℝ) :
    fderiv ℝ (fun k => f (chartMap k₀ v w k)) k (0, 1) = fderiv ℝ f (chartMap k₀ v w k) w := by
  rw [show (fun k => f (chartMap k₀ v w k)) = f ∘ chartMap k₀ v w from rfl,
    ((hf _).hasFDerivAt.comp k (hasFDerivAt_chartMap k)).fderiv]
  simp

/-- The phase `Q(u, s) = Ψ(k₀ + u v + s w) − s DΨ(k₀) w`, with `∂_sQ = DΨ(k₀ + u v + s w) w − DΨ(k₀) w`. -/
noncomputable def chartPhase (Ψ : ℝ × ℝ → ℝ) (k₀ v w : ℝ × ℝ) (k : ℝ × ℝ) : ℝ :=
  Ψ (chartMap k₀ v w k) - k.2 * fderiv ℝ Ψ k₀ w

variable (hΨ : ContDiff ℝ ∞ Ψ)
include hΨ

theorem contDiff_chartPhase : ContDiff ℝ ∞ (chartPhase Ψ k₀ v w) :=
  (hΨ.comp contDiff_chartMap).sub (contDiff_snd.mul contDiff_const)

theorem fderiv_chartPhase (k : ℝ × ℝ) :
    fderiv ℝ (chartPhase Ψ k₀ v w) k (0, 1) = fderiv ℝ Ψ (chartMap k₀ v w k) w - fderiv ℝ Ψ k₀ w := by
  have h1 := ((hΨ.comp (contDiff_chartMap (k₀ := k₀) (v := v) (w := w))).differentiable (by simp) k).hasFDerivAt.sub
    (hasFDerivAt_snd.mul_const (fderiv ℝ Ψ k₀ w))
  rw [show chartPhase Ψ k₀ v w = (Ψ ∘ chartMap k₀ v w) - fun y : ℝ × ℝ => y.2 * fderiv ℝ Ψ k₀ w from rfl,
    h1.fderiv, sub_apply,
    show fderiv ℝ (Ψ ∘ chartMap k₀ v w) k (0, 1) = fderiv ℝ Ψ (chartMap k₀ v w k) w from
      fderiv_comp_chartMap (hΨ.differentiable (by simp)) k]
  simp

theorem dd_chartPhase_zero : dd (chartPhase Ψ k₀ v w) 0 (0, 1) (0, 1) = iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] := by
  have e : (fun k => fderiv ℝ (chartPhase Ψ k₀ v w) k (0, 1)) =
      fun k => fderiv ℝ Ψ (chartMap k₀ v w k) w - fderiv ℝ Ψ k₀ w :=
    funext fun k => fderiv_chartPhase hΨ k
  rw [dd, e, fderiv_sub_const,
    fderiv_comp_chartMap ((contDiff_fderiv_apply_top hΨ w).differentiable (by simp)) 0]
  rw [← dd_eq_iteratedFDeriv (contDiff_infty.1 hΨ 2) le_rfl]
  simp [chartMap, dd]

end Reduced

/-- A smooth `ψ` with `ψ = id` on `|u| ≤ a/2` and `|ψ| ≤ a` (a `ContDiffBump` times the identity). -/
theorem exists_cutoff {a : ℝ} (ha : 0 < a) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ u, |u| ≤ a / 2 → ψ u = u) ∧ ∀ u, |ψ u| ≤ a := by
  let φ : ContDiffBump (0 : ℝ) := ⟨a / 2, a, by positivity, by linarith⟩
  refine ⟨fun u => u * φ u, contDiff_id.mul φ.contDiff, fun u hu => ?_, fun u => ?_⟩
  · show u * φ u = u
    rw [φ.one_of_mem_closedBall (by simpa [φ] using hu), mul_one]
  · show |u * φ u| ≤ a
    by_cases hu : |u| < a
    · rw [abs_mul, abs_of_nonneg φ.nonneg]
      calc |u| * φ u ≤ |u| * 1 := by gcongr; exact φ.le_one
        _ ≤ a := by linarith
    · rw [φ.zero_of_le_dist (by simp [φ]; linarith)]; simp; linarith

end OscInt.K2.NormalizedDataMAux

namespace OscInt.K2

open OscInt.K2.NormalizedDataMAux

/-- **P2** Normalized data of order m, uniformly over transverse velocities `|q| ≤ q₀`. -/
theorem normalizedDataM : OscInt.Blueprint.K2.NormalizedDataMFacts := by
  intro m F ε h hm hN
  obtain ⟨hF, hP0, hc0, hε, hh, h00, hcurve, hred⟩ := hN
  set c := dd F 0 (0, 1) (0, 1) with hcdef
  set G := Gop F (m - 1) with hGdef
  have hW0 : (0 : ℝ × ℝ) ∈ Wset F := hc0
  -- the operator identity along `h` gives `G 0 ≠ 0`
  set U : Set ℝ := {t | |t| < ε} ∩ {t | dd F (t, h t) (0, 1) (0, 1) ≠ 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_abs continuous_const).inter
      (isOpen_ne_fun ((contDiff_dd_top hF _ _).continuous.comp (continuous_id.prodMk hh.continuous))
        continuous_const)
  have h0U : (0 : ℝ) ∈ U := ⟨by simpa using hε, by show dd F (0, h 0) (0, 1) (0, 1) ≠ 0; rw [h00]; exact hc0⟩
  have hG0 : G 0 ≠ 0 := by
    have := iteratedDeriv_reduced_eq hF hUo (fun t _ => (hh.differentiable (by simp)) t)
      (fun t ht => hcurve t ht.1) (fun t ht => ht.2) (m - 1) 0 h0U
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at this
    rw [this, h00] at hred
    exact hred
  -- continuity at `0`
  set S : ℝ × ℝ → ℝ := fun k => ∑ i ∈ Finset.range 5,
    (‖iteratedFDeriv ℝ i F k‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) k‖) with hSdef
  have hSc : Continuous S := continuous_finsetSum _ fun i _ =>
    ((hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).add
      ((contDiff_snd.continuous_iteratedFDeriv (m := i) (n := ∞) (by exact_mod_cast le_top)).norm)
  have hGc : ContinuousAt G 0 :=
    (contDiffOn_Gop hF (m - 1)).continuousOn.continuousAt ((isOpen_Wset hF).mem_nhds hW0)
  have hcc : Continuous fun k => dd F k (0, 1) (0, 1) := (contDiff_dd_top hF _ _).continuous
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  have hGpos : 0 < |G 0| := abs_pos.mpr hG0
  have ev : ∀ᶠ k in 𝓝 (0 : ℝ × ℝ), |dd F k (0, 1) (0, 1) - c| ≤ |c| / 2 ∧ |G 0| / 2 < |G k| ∧
      S k < S 0 + 1 := by
    filter_upwards [eventually_abs_sub_lt hcc.continuousAt (half_pos hcpos),
      eventually_abs_sub_lt hGc (half_pos hGpos), eventually_abs_sub_lt hSc.continuousAt one_pos]
      with k h1 h2 h3
    exact ⟨h1.le, half_lt_abs_of h2, by have := (abs_lt.mp h3).2; linarith⟩
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.mp ev
  set b := r / 4 with hbdef
  have hb : 0 < b := by positivity
  have hcb : 0 < |c| * b / 4 := by positivity
  have hyc : Continuous fun x : ℝ => fderiv ℝ F (x, 0) (0, 1) :=
    (contDiff_fderiv_apply_top hF _).continuous.comp (continuous_id.prodMk continuous_const)
  have ev' : ∀ᶠ x in 𝓝 (0 : ℝ), |fderiv ℝ F (x, 0) (0, 1)| < |c| * b / 4 := by
    filter_upwards [eventually_abs_sub_lt hyc.continuousAt hcb] with x hx
    have e0 : fderiv ℝ F ((0 : ℝ), (0 : ℝ)) (0, 1) = 0 := hP0
    simpa [e0] using hx
  obtain ⟨r', hr', H'⟩ := Metric.eventually_nhds_iff.mp ev'
  set a := min r r' / 4 with hadef
  have ha : 0 < a := by positivity
  have har : 2 * a < r := by have := min_le_left r r'; linarith
  have har' : 2 * a < r' := by have := min_le_right r r'; linarith
  refine ⟨min 1 (|c| * b / 8), by positivity, a, b, |c| / 2, |G 0| / 2, S 0 + 1, ha, hb, half_pos hcpos,
    half_pos hGpos, fun q => implicitCurve (fun k => F k + q * k.2) b, fun q hq => ?_⟩
  have hq1 : |q| ≤ 1 := hq.trans (min_le_left _ _)
  have hq2 : |q| ≤ |c| * b / 8 := hq.trans (min_le_right _ _)
  set Q : ℝ × ℝ → ℝ := fun k => F k + q * k.2 with hQdef
  have hQ : ContDiff ℝ ∞ Q := hF.add (contDiff_const.mul contDiff_snd)
  have hS : SliceHyps Q a b c :=
    { smooth := contDiff_infty.1 hQ 4
      hb := hb
      hc := hc0
      yy := fun x hx y hy => by
        rw [hQdef, dd_addq hF]
        exact (H (dist_zero_lt (abs_lt_of_mem_Icc hx (by linarith) har)
          (abs_lt_of_mem_Icc hy (by linarith) (by linarith)))).1
      y0 := fun x hx => by
        rw [hQdef, fderiv_addq hF]
        have h1 := H' (show dist x 0 < r' by
          rw [Real.dist_eq, sub_zero]; exact abs_lt_of_mem_Icc hx (by linarith) har')
        have h2 := abs_add_le (fderiv ℝ F (x, 0) (0, 1)) (q * (1 : ℝ))
        rw [mul_one] at h2 ⊢
        have : |c| / 2 * b = |c| * b / 2 := by ring
        rw [this]
        linarith }
  have hIoo : ∀ x ∈ Icc (-a) a, x ∈ Ioo (-2 * a) (2 * a) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxr : ∀ x ∈ Icc (-a) a, |x| < r := fun x hx => abs_lt_of_mem_Icc hx (by linarith) (by linarith)
  have hyr : ∀ x ∈ Icc (-a) a, |implicitCurve Q b x| < r := fun x hx =>
    abs_lt_of_mem_Icc (Ioo_subset_Icc_self (hS.spec (Ioo_subset_Icc_self (hIoo x hx))).1)
      (by linarith) (by linarith)
  refine ⟨hQ, contDiffOn_implicitCurve_top hS hQ, fun x hx => hS.spec (Ioo_subset_Icc_self (hIoo x hx)),
    fun x hx y hy => half_abs_le_abs_of_abs_sub_le (hS.yy x (Ioo_subset_Icc_self (hIoo x hx)) y hy),
    fun i hi x hx y hy => ?_, fun x hx => ?_⟩
  · have hk := (H (dist_zero_lt (hxr x hx) (abs_lt_of_mem_Icc hy (by linarith) (by linarith)))).2.2
    have h1 := norm_iteratedFDeriv_addq_le hF q i (x, y)
    have h2 : |q| * ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hq1
    have h3 : ‖iteratedFDeriv ℝ i F (x, y)‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤ S (x, y) :=
      Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i F (x, y)‖ +
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖) (fun i _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    linarith
  · have hU2 : IsOpen (Ioo (-2 * a) (2 * a)) := isOpen_Ioo
    have hid := iteratedDeriv_reduced_eq hQ hU2
      (fun t ht => ((contDiffAt_implicitCurve_top hS hQ ht).differentiableAt (by simp)))
      (fun t ht => (hS.spec (Ioo_subset_Icc_self ht)).2)
      (fun t ht => hS.dd_ne_zero (Ioo_subset_Icc_self ht)
        (mem_Icc_two_of_mem_Ioo (hS.spec (Ioo_subset_Icc_self ht)).1)) (m - 1) x (hIoo x hx)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hQdef, Gop_addq hF q] at hid
    rw [hid]
    exact (H (dist_zero_lt (hxr x hx) (hyr x hx))).2.1.le

/-- **P5** A reduced curve exists when `D²Ψ(k₀)[w, w] ≠ 0`. -/
theorem reducedCurveExists : OscInt.Blueprint.K2.ReducedCurveExistsFacts := by
  intro Ψ k₀ v w hΨ hw
  set Q := chartPhase Ψ k₀ v w with hQdef
  have hQ : ContDiff ℝ ∞ Q := contDiff_chartPhase hΨ
  set c := dd Q 0 (0, 1) (0, 1) with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef, dd_chartPhase_zero hΨ]; exact hw
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  have hP : ∀ x : ℝ, fderiv ℝ Q (x, 0) (0, 1) = fderiv ℝ Ψ (k₀ + x • v) w - fderiv ℝ Ψ k₀ w := fun x => by
    rw [hQdef, fderiv_chartPhase hΨ]; simp [chartMap]
  have hcc : Continuous fun k => dd Q k (0, 1) (0, 1) := (contDiff_dd_top hQ _ _).continuous
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.mp
    (eventually_abs_sub_lt hcc.continuousAt (half_pos hcpos) (p := (0 : ℝ × ℝ)))
  set b := r / 4 with hbdef
  have hb : 0 < b := by positivity
  have hcb : 0 < |c| / 2 * b := by positivity
  have hyc : Continuous fun x : ℝ => fderiv ℝ Q (x, 0) (0, 1) :=
    (contDiff_fderiv_apply_top hQ _).continuous.comp (continuous_id.prodMk continuous_const)
  have hy0 : fderiv ℝ Q ((0 : ℝ), (0 : ℝ)) (0, 1) = 0 := by rw [hP]; simp
  obtain ⟨r', hr', H'⟩ := Metric.eventually_nhds_iff.mp (eventually_abs_sub_lt hyc.continuousAt hcb)
  set a := min r r' / 4 with hadef
  have ha : 0 < a := by positivity
  have har : 2 * a < r := by have := min_le_left r r'; linarith
  have har' : 2 * a < r' := by have := min_le_right r r'; linarith
  have hS : SliceHyps Q a b c :=
    { smooth := contDiff_infty.1 hQ 4
      hb := hb
      hc := hc0
      yy := fun x hx y hy => (H (dist_zero_lt (abs_lt_of_mem_Icc hx (by linarith) har)
          (abs_lt_of_mem_Icc hy (by linarith) (by linarith)))).le
      y0 := fun x hx => by
        have := H' (show dist x 0 < r' by
          rw [Real.dist_eq, sub_zero]; exact abs_lt_of_mem_Icc hx (by linarith) har')
        simpa [hy0] using this }
  set h₀ := implicitCurve Q b with hh₀
  have hmem : (0 : ℝ) ∈ Icc (-2 * a) (2 * a) := ⟨by linarith, by linarith⟩
  have h₀0 : h₀ 0 = 0 := by
    obtain ⟨hs1, hs2⟩ := hS.spec hmem
    exact hS.unique hmem (mem_Icc_two_of_mem_Ioo hs1) ⟨by linarith, by linarith⟩ hs2 hy0
  obtain ⟨ψ, hψ, hψid, hψb⟩ := exists_cutoff ha
  have hψmem : ∀ u, ψ u ∈ Ioo (-2 * a) (2 * a) := fun u => by
    have := abs_le.mp (hψb u); exact ⟨by linarith, by linarith⟩
  refine ⟨a / 2, by positivity, fun u => h₀ (ψ u), ?_, ?_, fun u hu => ?_⟩
  · exact contDiff_iff_contDiffAt.2 fun u =>
      (contDiffAt_implicitCurve_top hS hQ (hψmem u)).comp u hψ.contDiffAt
  · show h₀ (ψ 0) = 0
    rw [hψid 0 (by simp; positivity), h₀0]
  · show fderiv ℝ Ψ (k₀ + u • v + h₀ (ψ u) • w) w = fderiv ℝ Ψ k₀ w
    rw [hψid u hu.le]
    have hu' : u ∈ Icc (-2 * a) (2 * a) := by
      have := abs_lt.mp hu; exact ⟨by linarith, by linarith⟩
    have := (hS.spec hu').2
    rw [hQdef, fderiv_chartPhase hΨ, sub_eq_zero] at this
    exact this

open OscInt.API.ReducedBridge in
/-- **P6** Order 2: `g″(0) = D²Ψ[v, v] − D²Ψ[v, w]² / D²Ψ[w, w]` along any reduced curve. -/
theorem reducedOrderTwo : OscInt.Blueprint.K2.ReducedOrderTwoFacts := by
  intro Ψ k₀ v w ε h hΨ hw hε hred
  have hh := hred.1
  have h0 := hred.2.1
  set g := reducedFn Ψ k₀ v w h
  have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have hg : deriv g =ᶠ[𝓝 0] fun u => jet Ψ k₀ v w h 1 ![v] u - fderiv ℝ Ψ k₀ v := by
    filter_upwards [hball] with u hu
    exact (hasDerivAt_reducedFn hΨ hh hred (by simpa [Real.dist_eq] using hu)).deriv
  have g2 : iteratedDeriv 2 g 0 = slot₁ Ψ k₀ v w h v 0 := by
    rw [iteratedDeriv_succ', hg.iteratedDeriv_eq, iteratedDeriv_one, deriv_sub_const,
      deriv_jet_one hΨ hh]
  have hB : jet Ψ k₀ v w h 1 ![w] =ᶠ[𝓝 0] fun _ => fderiv ℝ Ψ k₀ w := by
    filter_upwards [hball] with u hu
    have := hred.2.2 u (by simpa [Real.dist_eq] using hu)
    simpa [jet, iteratedFDeriv_one_apply, curve] using this
  have hB1 : slot₁ Ψ k₀ v w h w 0 = 0 := by
    have := hB.iteratedDeriv_eq 1
    rwa [iteratedDeriv_one, iteratedDeriv_one, deriv_jet_one hΨ hh, deriv_const] at this
  simp only [slot₁, jet_zero h0] at hB1
  have hd : deriv h 0 = -iteratedFDeriv ℝ 2 Ψ k₀ ![v, w] / iteratedFDeriv ℝ 2 Ψ k₀ ![w, w] := by
    rw [eq_div_iff hw]; linarith
  rw [g2]
  simp only [slot₁, jet_zero h0]
  rw [hd, iteratedFDeriv_two_swap hΨ k₀ w v]
  ring

end OscInt.K2
