/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayNormalized
import OscInt.Front.TriangularDecayChart
import OscInt.Front.TriangularAnisoFinal

/-!
# Batch A5U, part A9: base data at `a₀`, uniformly in the tilt (`A5BaseDataFacts`)

Route `docs/proof-A5U.md`, sections 1 and 5; blueprint `A5BaseDataFacts`.

* The normal point: K2's P5 (`OscInt.K2.reducedCurveExists`) gives a reduced curve of `triPhase a₀` at
  `k* = a5Centre a₀` for `v = (1, 1)`, `w = (1, −1)` (`D²Ψ[w, w] = −2 cos θ₀ = 4a₀ ≠ 0`), TRI-W gives the
  reduced sixth derivative `−60√2 sign a₀ ≠ 0`, and K2's P3 (`OscInt.K2.chart`) turns these into
  `NormalPointM 6 (a5F a₀ a₀) ε h`.
* The data: a clone of the proof of K2's P2 (`OscInt.K2.normalizedDataM`), with the curve `ys q` the slice root
  `implicitCurve (F + q s) b`. Two more functions of `k` alone enter the continuity step at `0`: `Gop F 5` and
  `Gop F 7`. Since `g^{(j+1)} = (Gop F j)(·, ys q ·)` for every `q`
  (`NormalizedDataMAux.iteratedDeriv_reduced_eq`, `Gop_addq`), this bounds `g⁽⁶⁾` and `g⁽⁸⁾` uniformly in `q`.
* Evenness: `F` is even in `u` (A8), so `∂_sQ(−x, s) = ∂_sQ(x, s)`; `ys q (−x)` is then a critical point of
  `Q(x, ·)` in `(−b, b)`, equal to `ys q x` by uniqueness (`SliceHyps.unique`).
* The tilt bound: `∂_sQ(0, 0) = q`, `∂_sQ(0, ys q 0) = 0` and the growth estimate `SliceHyps.growth` give
  `|c|/2 · |ys q 0| ≤ |q|`.
-/

open Set Filter Topology OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
  OscInt.StationaryPhase.ImplicitAux OscInt.K2.NormalizedDataMAux
open scoped ContDiff

namespace OscInt.A5UAux

/-! ## The normal point at `k*` -/

theorem a5uW_ne_zero {a₀ : ℝ} (ha₀ : |a₀| = triExceptional) : a₀ ≠ 0 := by
  intro h; rw [h, abs_zero] at ha₀; exact (OscInt.API.TriDeriv.triExceptional_pos).ne ha₀

theorem a5uW_cos_theta {a₀ : ℝ} (ha₀ : |a₀| = triExceptional) : Real.cos (a5Theta a₀) = -2 * a₀ := by
  have h1 := OscInt.API.TriDeriv.triExceptional_lt_half
  have h2 : |(-2 * a₀)| ≤ 1 := by rw [abs_mul, ha₀]; norm_num; linarith
  exact Real.cos_arccos (by linarith [neg_abs_le (-2 * a₀)]) (by linarith [le_abs_self (-2 * a₀)])

theorem a5uW_ww {a₀ : ℝ} (ha₀ : |a₀| = triExceptional) :
    iteratedFDeriv ℝ 2 (triPhase a₀) (a5Centre a₀) ![((1 : ℝ), (-1 : ℝ)), (1, -1)] ≠ 0 := by
  rw [OscInt.API.TriDeriv.triD2]
  simp only [a5Centre, Real.cos_neg, a5uW_cos_theta ha₀]
  have := a5uW_ne_zero ha₀
  intro h; apply this; linarith

theorem a5uW_normalPoint {a₀ : ℝ} (ha₀ : |a₀| = triExceptional) :
    ∃ ε : ℝ, ∃ h : ℝ → ℝ, NormalPointM 6 (a5F a₀ a₀) ε h := by
  have hΨ := OscInt.API.TriDeriv.triPhase_smooth a₀
  obtain ⟨ε, hε, h, hR⟩ :=
    OscInt.K2.reducedCurveExists (triPhase a₀) (a5Centre a₀) (1, 1) (1, -1) hΨ (a5uW_ww ha₀)
  have h6 := (OscInt.API.triA5Witness a₀ ha₀).2.2 ε h hε hR
  have h6' : iteratedDeriv 6 (reducedFn (triPhase a₀) (a5Centre a₀) (1, 1) (1, -1) h) 0 ≠ 0 := by
    rw [show iteratedDeriv 6 (reducedFn (triPhase a₀) (a5Centre a₀) (1, 1) (1, -1) h) 0 = _ from h6]
    have hs : (SignType.sign a₀ : ℝ) ≠ 0 := by
      rcases lt_or_gt_of_ne (a5uW_ne_zero ha₀) with hl | hl
      · rw [sign_neg hl]; norm_num
      · rw [sign_pos hl]; norm_num
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity)) hs
  obtain ⟨L, hL, hNP⟩ := OscInt.K2.chart (triPhase a₀) (a5Centre a₀) (1, 1) (1, -1) ε h 6 hΨ (by norm_num)
    (by norm_num) (a5uW_ww ha₀) hε hR h6'
  refine ⟨ε, h, ?_⟩
  have e : (fun k => triPhase a₀ (a5Centre a₀ + L k) - triPhase a₀ (a5Centre a₀) -
      fderiv ℝ (triPhase a₀) (a5Centre a₀) (L k)) = a5F a₀ a₀ := by
    funext k; rw [hL]; rfl
  rwa [e] at hNP

/-- `F_{a₀}` is even in `u` (A8). -/
theorem a5uW_F_even (h8 : A5FixedChartFacts) (a₀ α u s : ℝ) : a5F a₀ α (-u, s) = a5F a₀ α (u, s) := by
  rw [h8, h8]
  simp only [mul_neg, Real.cos_neg]

/-! ## Generic data of a normal point of order 6, even in `u` -/

/-- The sum of the norms of the first five derivatives (as in the proof of K2's P2). -/
noncomputable def a5uW_S (F : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, (‖iteratedFDeriv ℝ i F k‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) k‖)

theorem a5uW_G0 {F : ℝ × ℝ → ℝ} {ε : ℝ} {h : ℝ → ℝ} (hN : NormalPointM 6 F ε h) : Gop F 5 0 ≠ 0 := by
  obtain ⟨hF, -, hc0, hε, hh, h00, hcurve, hred⟩ := hN
  set U : Set ℝ := {t | |t| < ε} ∩ {t | dd F (t, h t) (0, 1) (0, 1) ≠ 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_abs continuous_const).inter
      (isOpen_ne_fun ((contDiff_dd_top hF _ _).continuous.comp (continuous_id.prodMk hh.continuous))
        continuous_const)
  have h0U : (0 : ℝ) ∈ U := ⟨by simpa using hε, by show dd F (0, h 0) (0, 1) (0, 1) ≠ 0; rw [h00]; exact hc0⟩
  have : iteratedDeriv 6 (fun s => F (s, h s)) 0 = Gop F 5 (0, h 0) :=
    iteratedDeriv_reduced_eq hF hUo (fun t _ => (hh.differentiable (by simp)) t)
      (fun t ht => hcurve t ht.1) (fun t ht => ht.2) 5 0 h0U
  rw [this, h00] at hred
  exact hred

/-- Continuity at `0` of finitely many functions of `k` alone. -/
theorem a5uW_nbhd {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hc0 : dd F 0 (0, 1) (0, 1) ≠ 0)
    (hG0 : Gop F 5 0 ≠ 0) :
    ∃ r > 0, ∀ k : ℝ × ℝ, dist k 0 < r →
      |dd F k (0, 1) (0, 1) - dd F 0 (0, 1) (0, 1)| ≤ |dd F 0 (0, 1) (0, 1)| / 2 ∧
      |Gop F 5 0| / 2 < |Gop F 5 k| ∧ a5uW_S F k < a5uW_S F 0 + 1 ∧
      |Gop F 5 k| < |Gop F 5 0| + 1 ∧ |Gop F 7 k| < |Gop F 7 0| + 1 := by
  have hW0 : (0 : ℝ × ℝ) ∈ Wset F := hc0
  have hSc : Continuous (a5uW_S F) := continuous_finsetSum _ fun i _ =>
    ((hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).add
      ((contDiff_snd.continuous_iteratedFDeriv (m := i) (n := ∞) (by exact_mod_cast le_top)).norm)
  have hG5 : ContinuousAt (Gop F 5) 0 :=
    (contDiffOn_Gop hF 5).continuousOn.continuousAt ((isOpen_Wset hF).mem_nhds hW0)
  have hG7 : ContinuousAt (Gop F 7) 0 :=
    (contDiffOn_Gop hF 7).continuousOn.continuousAt ((isOpen_Wset hF).mem_nhds hW0)
  have hcc : Continuous fun k => dd F k (0, 1) (0, 1) := (contDiff_dd_top hF _ _).continuous
  have ev : ∀ᶠ k in 𝓝 (0 : ℝ × ℝ),
      |dd F k (0, 1) (0, 1) - dd F 0 (0, 1) (0, 1)| ≤ |dd F 0 (0, 1) (0, 1)| / 2 ∧
      |Gop F 5 0| / 2 < |Gop F 5 k| ∧ a5uW_S F k < a5uW_S F 0 + 1 ∧
      |Gop F 5 k| < |Gop F 5 0| + 1 ∧ |Gop F 7 k| < |Gop F 7 0| + 1 := by
    filter_upwards [eventually_abs_sub_lt hcc.continuousAt (half_pos (abs_pos.mpr hc0)),
      eventually_abs_sub_lt hG5 (half_pos (abs_pos.mpr hG0)), eventually_abs_sub_lt hSc.continuousAt one_pos,
      eventually_abs_sub_lt hG5 one_pos, eventually_abs_sub_lt hG7 one_pos] with k h1 h2 h3 h4 h5
    exact ⟨h1.le, half_lt_abs_of h2, by have := (abs_lt.mp h3).2; linarith, abs_lt_add_one_of h4,
      abs_lt_add_one_of h5⟩
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.mp ev
  exact ⟨r, hr, fun k hk => H hk⟩

theorem a5uW_nbhd2 {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hP0 : fderiv ℝ F 0 (0, 1) = 0) {e : ℝ}
    (he : 0 < e) : ∃ r' > 0, ∀ x : ℝ, dist x 0 < r' → |fderiv ℝ F (x, 0) (0, 1)| < e := by
  have hyc : Continuous fun x : ℝ => fderiv ℝ F (x, 0) (0, 1) :=
    (contDiff_fderiv_apply_top hF _).continuous.comp (continuous_id.prodMk continuous_const)
  have ev' : ∀ᶠ x in 𝓝 (0 : ℝ), |fderiv ℝ F (x, 0) (0, 1)| < e := by
    filter_upwards [eventually_abs_sub_lt hyc.continuousAt he] with x hx
    have e0 : fderiv ℝ F ((0 : ℝ), (0 : ℝ)) (0, 1) = 0 := hP0
    simpa [e0] using hx
  exact Metric.eventually_nhds_iff.mp ev'

theorem a5uW_slice {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hc0 : dd F 0 (0, 1) (0, 1) ≠ 0) {r r' a b q : ℝ}
    (H : ∀ k : ℝ × ℝ, dist k 0 < r →
      |dd F k (0, 1) (0, 1) - dd F 0 (0, 1) (0, 1)| ≤ |dd F 0 (0, 1) (0, 1)| / 2)
    (H' : ∀ x : ℝ, dist x 0 < r' → |fderiv ℝ F (x, 0) (0, 1)| < |dd F 0 (0, 1) (0, 1)| * b / 4)
    (hb : b = r / 4) (hr : 0 < r) (har : 2 * a < r) (har' : 2 * a < r')
    (hq : |q| ≤ |dd F 0 (0, 1) (0, 1)| * b / 8) :
    SliceHyps (fun k => F k + q * k.2) a b (dd F 0 (0, 1) (0, 1)) :=
  { smooth := contDiff_infty.1 (hF.add (contDiff_const.mul contDiff_snd)) 4
    hb := by rw [hb]; positivity
    hc := hc0
    yy := fun x hx y hy => by
      rw [dd_addq hF]
      exact H _ (dist_zero_lt (abs_lt_of_mem_Icc hx (by linarith) har)
        (abs_lt_of_mem_Icc hy (by linarith) (by linarith)))
    y0 := fun x hx => by
      rw [fderiv_addq hF]
      have h1 := H' x (show dist x 0 < r' by
        rw [Real.dist_eq, sub_zero]; exact abs_lt_of_mem_Icc hx (by linarith) har')
      have h2 := abs_add_le (fderiv ℝ F (x, 0) (0, 1)) (q * (1 : ℝ))
      rw [mul_one] at h2 ⊢
      have : |dd F 0 (0, 1) (0, 1)| / 2 * b = |dd F 0 (0, 1) (0, 1)| * b / 2 := by ring
      rw [this]
      have hcb : 0 < |dd F 0 (0, 1) (0, 1)| * b := by rw [hb]; have := abs_pos.mpr hc0; positivity
      linarith }

/-- `∂_sQ(−x, y) = ∂_sQ(x, y)` for `Q` even in `u`. -/
theorem a5uW_fderiv_even {Q : ℝ × ℝ → ℝ} (hQ : Differentiable ℝ Q) (hev : ∀ u s, Q (-u, s) = Q (u, s))
    (x y : ℝ) : fderiv ℝ Q (-x, y) (0, 1) = fderiv ℝ Q (x, y) (0, 1) := by
  have h1 := hasDerivAt_slice (hQ (-x, y))
  have h2 := hasDerivAt_slice (hQ (x, y))
  have e : (fun t => Q (-x, t)) = fun t => Q (x, t) := funext fun t => hev x t
  rw [e] at h1
  exact h1.unique h2

/-- Evenness of the slice root, by uniqueness of the transverse critical point. -/
theorem a5uW_curve_even {Q : ℝ × ℝ → ℝ} {a b c : ℝ} (hS : SliceHyps Q a b c) (hQ : Differentiable ℝ Q)
    (hev : ∀ u s, Q (-u, s) = Q (u, s)) :
    ∀ x ∈ Icc (-a) a, implicitCurve Q b (-x) = implicitCurve Q b x := by
  intro x hx
  have hx1 : x ∈ Icc (-2 * a) (2 * a) := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hx2 : -x ∈ Icc (-2 * a) (2 * a) := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  obtain ⟨hy1, hy1'⟩ := hS.spec hx2
  obtain ⟨hy2, hy2'⟩ := hS.spec hx1
  refine hS.unique hx1 (mem_Icc_two_of_mem_Ioo hy1) (mem_Icc_two_of_mem_Ioo hy2) ?_ hy2'
  rw [← a5uW_fderiv_even hQ hev x (implicitCurve Q b (-x))]
  exact hy1'

/-- `|c|/2 · |ys q 0| ≤ |q|`: the mean value theorem in `s` at `u = 0`. -/
theorem a5uW_tilt {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hP0 : fderiv ℝ F 0 (0, 1) = 0) {q a b c : ℝ}
    (hS : SliceHyps (fun k => F k + q * k.2) a b c) (ha : 0 ≤ a) :
    |c| / 2 * |implicitCurve (fun k => F k + q * k.2) b 0| ≤ |q| := by
  set y := implicitCurve (fun k => F k + q * k.2) b 0
  have h0 : (0 : ℝ) ∈ Icc (-2 * a) (2 * a) := ⟨by linarith, by linarith⟩
  obtain ⟨hy, hy0⟩ := hS.spec h0
  have hb := hS.hb
  have hz : (0 : ℝ) ∈ Icc (-2 * b) (2 * b) := ⟨by linarith, by linarith⟩
  have hq : fderiv ℝ (fun k => F k + q * k.2) ((0 : ℝ), (0 : ℝ)) (0, 1) = q := by
    rw [fderiv_addq hF]
    have : fderiv ℝ F ((0 : ℝ), (0 : ℝ)) (0, 1) = 0 := hP0
    rw [this]; simp
  have hc := abs_pos.mpr hS.hc
  have hcc : |c| * |c| = c ^ 2 := by rw [abs_mul_abs_self, sq]
  have hcq := neg_abs_le (c * q)
  have hcq' := le_abs_self (c * q)
  rw [abs_mul] at hcq hcq'
  have key : |c| * (|c| / 2 * |y|) ≤ |c| * |q| := by
    rcases le_total 0 y with h | h
    · have := hS.growth h0 hz (mem_Icc_two_of_mem_Ioo hy) h
      rw [hy0, hq, abs_of_nonneg h] at *
      nlinarith
    · have := hS.growth h0 (mem_Icc_two_of_mem_Ioo hy) hz h
      rw [hy0, hq, abs_of_nonpos h] at *
      nlinarith
  exact le_of_mul_le_mul_left key hc

/-- The reduced derivatives along the slice root are the operator formulas of `F` (independent of `q`). -/
theorem a5uW_iter {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {a b c q : ℝ}
    (hS : SliceHyps (fun k => F k + q * k.2) a b c) (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (-2 * a) (2 * a)) :
    iteratedDeriv (j + 1) (fun x => F (x, implicitCurve (fun k => F k + q * k.2) b x) +
        q * implicitCurve (fun k => F k + q * k.2) b x) x =
      Gop F j (x, implicitCurve (fun k => F k + q * k.2) b x) := by
  have hQ : ContDiff ℝ ∞ (fun k : ℝ × ℝ => F k + q * k.2) := hF.add (contDiff_const.mul contDiff_snd)
  have hid := iteratedDeriv_reduced_eq hQ isOpen_Ioo
    (fun t ht => ((contDiffAt_implicitCurve_top hS hQ ht).differentiableAt (by simp)))
    (fun t ht => (hS.spec (Ioo_subset_Icc_self ht)).2)
    (fun t ht => hS.dd_ne_zero (Ioo_subset_Icc_self ht)
      (mem_Icc_two_of_mem_Ioo (hS.spec (Ioo_subset_Icc_self ht)).1)) j x hx
  rw [Gop_addq hF q] at hid
  exact hid

/-- The ball property of `a5uW_nbhd`, as used for every tilt. -/
def a5uW_Ball (F : ℝ × ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ k : ℝ × ℝ, dist k 0 < r →
    |dd F k (0, 1) (0, 1) - dd F 0 (0, 1) (0, 1)| ≤ |dd F 0 (0, 1) (0, 1)| / 2 ∧
    |Gop F 5 0| / 2 < |Gop F 5 k| ∧ a5uW_S F k < a5uW_S F 0 + 1 ∧
    |Gop F 5 k| < |Gop F 5 0| + 1 ∧ |Gop F 7 k| < |Gop F 7 0| + 1

theorem a5uW_pt {F : ℝ × ℝ → ℝ} {r a b c q : ℝ} (hb : b = r / 4) (ha : 0 < a) (har : 2 * a < r)
    (hS : SliceHyps (fun k => F k + q * k.2) a b c) {x : ℝ} (hx : x ∈ Icc (-a) a) :
    x ∈ Ioo (-2 * a) (2 * a) ∧ dist (x, implicitCurve (fun k => F k + q * k.2) b x) 0 < r := by
  have hx' : x ∈ Ioo (-2 * a) (2 * a) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨hx', dist_zero_lt (abs_lt_of_mem_Icc hx (by linarith) (by linarith)) ?_⟩
  have := (hS.spec (Ioo_subset_Icc_self hx')).1
  have hb' := hS.hb
  exact abs_lt.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

theorem a5uW_core {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {r a b q : ℝ} (H : a5uW_Ball F r)
    (hb : b = r / 4) (ha : 0 < a) (har : 2 * a < r) (hq1 : |q| ≤ 1)
    (hS : SliceHyps (fun k => F k + q * k.2) a b (dd F 0 (0, 1) (0, 1))) :
    CoreHypsM 6 a b (|dd F 0 (0, 1) (0, 1)| / 2) (|Gop F 5 0| / 2) (a5uW_S F 0 + 1)
      (fun k => F k + q * k.2) (implicitCurve (fun k => F k + q * k.2) b) := by
  have hQ : ContDiff ℝ ∞ (fun k : ℝ × ℝ => F k + q * k.2) := hF.add (contDiff_const.mul contDiff_snd)
  have hpt := fun x (hx : x ∈ Icc (-a) a) => a5uW_pt hb ha har hS hx
  refine ⟨hQ, contDiffOn_implicitCurve_top hS hQ, fun x hx => hS.spec (Ioo_subset_Icc_self (hpt x hx).1),
    fun x hx y hy => half_abs_le_abs_of_abs_sub_le (hS.yy x (Ioo_subset_Icc_self (hpt x hx).1) y hy),
    fun i hi x hx y hy => ?_, fun x hx => ?_⟩
  · have hk := (H (x, y) (dist_zero_lt (abs_lt_of_mem_Icc hx (by linarith) (by linarith))
      (abs_lt_of_mem_Icc hy (by linarith) (by linarith)))).2.2.1
    have h1 := norm_iteratedFDeriv_addq_le hF q i (x, y)
    have h2 : |q| * ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hq1
    have h3 : ‖iteratedFDeriv ℝ i F (x, y)‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤
        a5uW_S F (x, y) :=
      Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i F (x, y)‖ +
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖) (fun i _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    linarith
  · have e : |iteratedDeriv 6 (fun x => F (x, implicitCurve (fun k => F k + q * k.2) b x) +
        q * implicitCurve (fun k => F k + q * k.2) b x) x| =
        |Gop F 5 (x, implicitCurve (fun k => F k + q * k.2) b x)| :=
      congrArg abs (a5uW_iter hF hS 5 (hpt x hx).1)
    show _ ≤ |iteratedDeriv 6 (fun x => F (x, implicitCurve (fun k => F k + q * k.2) b x) +
        q * implicitCurve (fun k => F k + q * k.2) b x) x|
    rw [e]
    exact (H _ (hpt x hx).2).2.1.le

theorem a5uW_jets {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {r a b q c : ℝ} (H : a5uW_Ball F r)
    (hb : b = r / 4) (ha : 0 < a) (har : 2 * a < r) (hS : SliceHyps (fun k => F k + q * k.2) a b c) :
    ∀ x ∈ Icc (-a) a,
      |iteratedDeriv 6 (fun x => F (x, implicitCurve (fun k => F k + q * k.2) b x) +
          q * implicitCurve (fun k => F k + q * k.2) b x) x| ≤ |Gop F 5 0| + |Gop F 7 0| + 1 ∧
      |iteratedDeriv 8 (fun x => F (x, implicitCurve (fun k => F k + q * k.2) b x) +
          q * implicitCurve (fun k => F k + q * k.2) b x) x| ≤ |Gop F 5 0| + |Gop F 7 0| + 1 := by
  intro x hx
  have hpt := a5uW_pt hb ha har hS hx
  have e6 := a5uW_iter hF hS 5 hpt.1
  have e8 := a5uW_iter hF hS 7 hpt.1
  have hB := H _ hpt.2
  refine ⟨?_, ?_⟩
  · rw [show (6 : ℕ) = 5 + 1 from rfl, e6]
    have := abs_nonneg (Gop F 7 0)
    linarith [hB.2.2.2.1]
  · rw [show (8 : ℕ) = 7 + 1 from rfl, e8]
    have := abs_nonneg (Gop F 5 0)
    linarith [hB.2.2.2.2]

/-- The data of a normal point of order 6 that is even in `u`, uniformly in the tilt. -/
theorem a5uW_generic {F : ℝ × ℝ → ℝ} {ε : ℝ} {h : ℝ → ℝ} (hN : NormalPointM 6 F ε h)
    (hev : ∀ u s, F (-u, s) = F (u, s)) :
    ∃ q₀ > 0, ∃ a b μ ν D L : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : ℝ → ℝ → ℝ, ∀ q : ℝ, |q| ≤ q₀ →
        CoreHypsM 6 a b μ ν D (fun k => F k + q * k.2) (ys q) ∧ (∀ x ∈ Icc (-a) a, ys q (-x) = ys q x) ∧
          μ * |ys q 0| ≤ |q| ∧
          ∀ x ∈ Icc (-a) a, |iteratedDeriv 6 (fun x => F (x, ys q x) + q * ys q x) x| ≤ L ∧
            |iteratedDeriv 8 (fun x => F (x, ys q x) + q * ys q x) x| ≤ L := by
  have hG0 := a5uW_G0 hN
  obtain ⟨hF, hP0, hc0, -, -, -, -, -⟩ := hN
  obtain ⟨r, hr, H⟩ := a5uW_nbhd hF hc0 hG0
  set c := dd F 0 (0, 1) (0, 1) with hcdef
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  have hb : 0 < r / 4 := by positivity
  obtain ⟨r', hr', H'⟩ := a5uW_nbhd2 hF hP0 (e := |c| * (r / 4) / 4) (by positivity)
  set a := min r r' / 4 with hadef
  have ha : 0 < a := by positivity
  have har : 2 * a < r := by have := min_le_left r r'; linarith
  have har' : 2 * a < r' := by have := min_le_right r r'; linarith
  refine ⟨min 1 (|c| * (r / 4) / 8), by positivity, a, r / 4, |c| / 2, |Gop F 5 0| / 2, a5uW_S F 0 + 1,
    |Gop F 5 0| + |Gop F 7 0| + 1, ha, hb, half_pos hcpos, half_pos (abs_pos.mpr hG0),
    fun q => implicitCurve (fun k => F k + q * k.2) (r / 4), fun q hq => ?_⟩
  have hq1 : |q| ≤ 1 := hq.trans (min_le_left _ _)
  have hq2 : |q| ≤ |c| * (r / 4) / 8 := hq.trans (min_le_right _ _)
  have hS := a5uW_slice hF hc0 (fun k hk => (H k hk).1) H' rfl hr har har' hq2
  have hQd : Differentiable ℝ (fun k : ℝ × ℝ => F k + q * k.2) :=
    (hF.add (contDiff_const.mul contDiff_snd)).differentiable (by simp)
  exact ⟨a5uW_core hF H rfl ha har hq1 hS,
    a5uW_curve_even hS hQd (fun u s => by simp only [hev]),
    a5uW_tilt hF hP0 hS ha.le, a5uW_jets hF H rfl ha har hS⟩

/-! ## A9 -/

/-- **A9** Base data at `a₀`, uniformly in the tilt. -/
theorem a5BaseData : OscInt.Blueprint.A5U.A5BaseDataFacts := by
  intro h8 a₀ ha₀
  obtain ⟨ε, h, hN⟩ := a5uW_normalPoint ha₀
  exact a5uW_generic hN (a5uW_F_even h8 a₀ a₀)

end OscInt.A5UAux
