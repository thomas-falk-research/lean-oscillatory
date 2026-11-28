/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayNormalized
import OscInt.Front.FamilyC10

/-!
# Batch A5U, part B1 (first half): K2's normalised data (P2) uniformly in a parameter

Route `docs/proof-A5U.md`, section 5 (B1), with the fallback "`Gop` joint continuity via parametric
`ContDiff.fderiv`" of the lead's planning notes (outside the repository). For a family `Φ α` that is `C^∞` jointly
in `(α, k)` and a normal point of order `m` of `Φ α₀` at `0`, the core hypotheses `CoreHypsM m` of `Φ α + q s` hold
with one set of constants for all `|α − α₀| ≤ ρ`, `|q| ≤ q₀` (`a5uB_paramData`).

The proof is the one of `OscInt.K2.normalizedDataM` with continuity at `(α₀, 0)` of functions of `(α, k)` in
place of continuity at `0` of functions of `k`:
* `(α, k) ↦ ∂_v Φ α k` and `∂²` are jointly `C^∞` (`ContDiff.fderiv_apply`);
* `(α, k) ↦ Gop (Φ α) j k` is `C^∞` at every point with `∂²_s Φ α k ≠ 0` (`a5uB_contDiffAt_Gop`, induction
  on `j` with `ContDiffAt.fderiv`);
* `(α, k) ↦ ‖Dⁱ Φ α k‖` is continuous (`OscInt.API.familyCk_of_uncurry`).
-/

namespace OscInt.A5UAux

open Set Filter Topology OscInt.Statements OscInt.Blueprint.K2 OscInt.StationaryPhase.ImplicitAux
  OscInt.K2.NormalizedDataMAux
open scoped ContDiff

/-! ## Joint smoothness of the operator formulas -/

/-- Directional derivatives of a jointly smooth family are jointly smooth. -/
theorem a5uB_contDiff_fderiv {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (Φ p.1) p.2 v) := by
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (x : ℝ × (ℝ × ℝ)) (z : ℝ × ℝ) => Φ x.1 z) :=
    hΦ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h1.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- Second directional derivatives of a jointly smooth family are jointly smooth. -/
theorem a5uB_contDiff_dd {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (v w : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => dd (Φ p.1) p.2 v w) :=
  a5uB_contDiff_fderiv (Φ := fun α k => fderiv ℝ (Φ α) k v) (a5uB_contDiff_fderiv hΦ v) w

/-- The step of the operator: `Gop Q (j + 1) = D_x Gop Q j + Y1 Q · D_y Gop Q j`. -/
theorem a5uB_Gop_succ (Q : ℝ × ℝ → ℝ) (j : ℕ) (k : ℝ × ℝ) :
    Gop Q (j + 1) k = fderiv ℝ (Gop Q j) k (1, 0) + Y1 Q k * fderiv ℝ (Gop Q j) k (0, 1) := rfl

/-- `(α, k) ↦ Gop (Φ α) j k` is `C^∞` at every point where `∂²_s Φ α k ≠ 0`. -/
theorem a5uB_contDiffAt_Gop {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ∀ (j : ℕ) (p : ℝ × (ℝ × ℝ)), dd (Φ p.1) p.2 (0, 1) (0, 1) ≠ 0 →
      ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Gop (Φ p.1) j p.2) p
  | 0, _, _ => (a5uB_contDiff_fderiv hΦ (1, 0)).contDiffAt
  | j + 1, p, hp => by
    have IH : ContDiffAt ℝ ∞ (Function.uncurry fun (x : ℝ × (ℝ × ℝ)) (z : ℝ × ℝ) => Gop (Φ x.1) j z)
        (p, p.2) :=
      (a5uB_contDiffAt_Gop hΦ j p hp).comp (p, p.2)
        ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
    have hD : ∀ v : ℝ × ℝ, ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (Gop (Φ x.1) j) x.2 v) p :=
      fun v => (IH.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const
    have hY : ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => Y1 (Φ x.1) x.2) p :=
      ((a5uB_contDiff_dd hΦ (0, 1) (1, 0)).contDiffAt.div (a5uB_contDiff_dd hΦ (0, 1) (0, 1)).contDiffAt
        hp).neg
    have e : (fun x : ℝ × (ℝ × ℝ) => Gop (Φ x.1) (j + 1) x.2) = fun x =>
        fderiv ℝ (Gop (Φ x.1) j) x.2 (1, 0) + Y1 (Φ x.1) x.2 * fderiv ℝ (Gop (Φ x.1) j) x.2 (0, 1) :=
      funext fun x => a5uB_Gop_succ _ j x.2
    rw [e]
    exact (hD (1, 0)).add (hY.mul (hD (0, 1)))

/-- The sum of the norms of the derivatives of order `≤ 4` of `F` and of `k ↦ k.2`. -/
noncomputable def a5uB_S (F : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, (‖iteratedFDeriv ℝ i F k‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) k‖)

/-- `(α, k) ↦ a5uB_S (Φ α) k` is continuous. -/
theorem a5uB_continuous_S {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => a5uB_S (Φ p.1) p.2) := by
  have hFam := OscInt.API.familyCk_of_uncurry ℝ 4 Φ (contDiff_infty.1 hΦ 4) Set.univ
  have hmap : Continuous (fun p : ℝ × (ℝ × ℝ) => ((⟨p.1, trivial⟩ : (Set.univ : Set ℝ)), p.2)) :=
    (continuous_fst.subtype_mk _).prodMk continuous_snd
  refine continuous_finsetSum _ fun i hi => ?_
  have hi4 : i ≤ 4 := by simp at hi; omega
  exact ((hFam.2 i (by exact_mod_cast hi4)).comp hmap).norm.add
    ((contDiff_snd.continuous_iteratedFDeriv (m := i) (n := ∞) (by exact_mod_cast le_top)).norm.comp
      continuous_snd)

/-! ## One phase: the core hypotheses from bounds on a box -/

/-- Along the reduced curve, `Gop F (m − 1) 0 ≠ 0` at a normal point of order `m` (as in P2). -/
theorem a5uB_Gop_ne {F : ℝ × ℝ → ℝ} {m : ℕ} {ε : ℝ} {h : ℝ → ℝ} (hm : 1 ≤ m) (hN : NormalPointM m F ε h) :
    Gop F (m - 1) 0 ≠ 0 := by
  obtain ⟨hF, -, hc0, hε, hh, h00, hcurve, hred⟩ := hN
  set U : Set ℝ := {t | |t| < ε} ∩ {t | dd F (t, h t) (0, 1) (0, 1) ≠ 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_abs continuous_const).inter
      (isOpen_ne_fun ((contDiff_dd_top hF _ _).continuous.comp (continuous_id.prodMk hh.continuous))
        continuous_const)
  have h0U : (0 : ℝ) ∈ U := ⟨by simpa using hε, by show dd F (0, h 0) (0, 1) (0, 1) ≠ 0; rw [h00]; exact hc0⟩
  have := iteratedDeriv_reduced_eq hF hUo (fun t _ => (hh.differentiable (by simp)) t)
    (fun t ht => hcurve t ht.1) (fun t ht => ht.2) (m - 1) 0 h0U
  rw [Nat.sub_add_cancel hm] at this
  rw [this, h00] at hred
  exact hred

theorem a5uB_abs_le_two {x a : ℝ} (hx : x ∈ Icc (-a) a) : |x| ≤ 2 * a :=
  abs_le.mpr ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩

/-- The slice hypotheses for `F + q s` from bounds on the box `|x| ≤ 2a`, `|y| ≤ 2b`. -/
theorem a5uB_sliceHyps {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {a b c q : ℝ} (hb : 0 < b) (hc : c ≠ 0)
    (hq2 : |q| ≤ |c| * b / 8)
    (H : ∀ x y : ℝ, |x| ≤ 2 * a → |y| ≤ 2 * b → |dd F (x, y) (0, 1) (0, 1) - c| ≤ |c| / 2)
    (H' : ∀ x : ℝ, |x| ≤ 2 * a → |fderiv ℝ F (x, 0) (0, 1)| < |c| * b / 4) :
    SliceHyps (fun k => F k + q * k.2) a b c :=
  { smooth := contDiff_infty.1 (hF.add (contDiff_const.mul contDiff_snd)) 4
    hb := hb
    hc := hc
    yy := fun x hx y hy => by
      rw [dd_addq hF]
      exact H x y (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)
    y0 := fun x hx => by
      rw [fderiv_addq hF]
      have h1 := H' x (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
      have h2 := abs_add_le (fderiv ℝ F (x, 0) (0, 1)) (q * (1 : ℝ))
      rw [mul_one] at h2 ⊢
      have : |c| / 2 * b = |c| * b / 2 := by ring
      rw [this]
      have : 0 < |c| * b := mul_pos (abs_pos.mpr hc) hb
      linarith }

/-- `CoreHypsM` for `F + q s` from bounds on the box `|x| ≤ 2a`, `|y| ≤ 2b` (the second half of P2). -/
theorem a5uB_coreHyps {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {m : ℕ} (hm : 1 ≤ m) {a b c G0 S0 q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) (hq1 : |q| ≤ 1) (hq2 : |q| ≤ |c| * b / 8)
    (H : ∀ x y : ℝ, |x| ≤ 2 * a → |y| ≤ 2 * b → |dd F (x, y) (0, 1) (0, 1) - c| ≤ |c| / 2 ∧
      |G0| / 2 < |Gop F (m - 1) (x, y)| ∧ a5uB_S F (x, y) < S0 + 1)
    (H' : ∀ x : ℝ, |x| ≤ 2 * a → |fderiv ℝ F (x, 0) (0, 1)| < |c| * b / 4) :
    CoreHypsM m a b (|c| / 2) (|G0| / 2) (S0 + 1) (fun k => F k + q * k.2)
      (implicitCurve (fun k => F k + q * k.2) b) := by
  set Q : ℝ × ℝ → ℝ := fun k => F k + q * k.2 with hQdef
  have hQ : ContDiff ℝ ∞ Q := hF.add (contDiff_const.mul contDiff_snd)
  have hS : SliceHyps Q a b c := a5uB_sliceHyps hF hb hc hq2 (fun x y hx hy => (H x y hx hy).1) H'
  have hIoo : ∀ x ∈ Icc (-a) a, x ∈ Ioo (-2 * a) (2 * a) := fun x hx =>
    ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hyr : ∀ x ∈ Icc (-a) a, |implicitCurve Q b x| ≤ 2 * b := fun x hx =>
    a5uB_abs_le_two (Ioo_subset_Icc_self (hS.spec (Ioo_subset_Icc_self (hIoo x hx))).1)
  refine ⟨hQ, contDiffOn_implicitCurve_top hS hQ, fun x hx => hS.spec (Ioo_subset_Icc_self (hIoo x hx)),
    fun x hx y hy => half_abs_le_abs_of_abs_sub_le (hS.yy x (Ioo_subset_Icc_self (hIoo x hx)) y hy),
    fun i hi x hx y hy => ?_, fun x hx => ?_⟩
  · have hk := (H x y (a5uB_abs_le_two hx) (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)).2.2
    have h1 := norm_iteratedFDeriv_addq_le hF q i (x, y)
    have h2 : |q| * ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hq1
    have h3 : ‖iteratedFDeriv ℝ i F (x, y)‖ + ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖ ≤
        a5uB_S F (x, y) :=
      Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i F (x, y)‖ +
        ‖iteratedFDeriv ℝ i (fun k : ℝ × ℝ => k.2) (x, y)‖) (fun i _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    linarith
  · have hid := iteratedDeriv_reduced_eq hQ isOpen_Ioo
      (fun t ht => ((contDiffAt_implicitCurve_top hS hQ ht).differentiableAt (by simp)))
      (fun t ht => (hS.spec (Ioo_subset_Icc_self ht)).2)
      (fun t ht => hS.dd_ne_zero (Ioo_subset_Icc_self ht)
        (mem_Icc_two_of_mem_Ioo (hS.spec (Ioo_subset_Icc_self ht)).1)) (m - 1) x (hIoo x hx)
    rw [Nat.sub_add_cancel hm, hQdef, Gop_addq hF q] at hid
    rw [hid]
    exact (H x _ (a5uB_abs_le_two hx) (hyr x hx)).2.1.le

/-! ## The family: uniform data near `(α₀, 0)` -/

/-- A property eventually true at `(α₀, 0)` holds for `|α − α₀|, |x|, |y| ≤ r`. -/
theorem a5uB_box {α₀ : ℝ} {P : ℝ × (ℝ × ℝ) → Prop} (h : ∀ᶠ p in 𝓝 ((α₀, 0) : ℝ × (ℝ × ℝ)), P p) :
    ∃ r > 0, ∀ α x y : ℝ, |α - α₀| ≤ r → |x| ≤ r → |y| ≤ r → P (α, (x, y)) := by
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, by positivity, fun α x y hα hx hy => H ?_⟩
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

/-- **B1, normalised data uniformly in the parameter.** -/
theorem a5uB_paramData {Φ : ℝ → ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) {α₀ ε : ℝ}
    {h : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m) (hN : NormalPointM m (Φ α₀) ε h) :
    ∃ ρ > 0, ∃ q₀ > 0, ∃ a b μ ν D : ℝ, 0 < a ∧ 0 < b ∧ 0 < μ ∧ 0 < ν ∧
      ∃ ys : ℝ → ℝ → ℝ → ℝ, ∀ α : ℝ, |α - α₀| ≤ ρ → ∀ q : ℝ, |q| ≤ q₀ →
        CoreHypsM m a b μ ν D (fun k => Φ α k + q * k.2) (ys α q) := by
  have hP0 : fderiv ℝ (Φ α₀) 0 (0, 1) = 0 := hN.2.1
  have hc0 : dd (Φ α₀) 0 (0, 1) (0, 1) ≠ 0 := hN.2.2.1
  have hG0 : Gop (Φ α₀) (m - 1) 0 ≠ 0 := a5uB_Gop_ne (by omega) hN
  set c := dd (Φ α₀) 0 (0, 1) (0, 1) with hcdef
  set G0 := Gop (Φ α₀) (m - 1) 0 with hG0def
  set S0 := a5uB_S (Φ α₀) 0 with hS0def
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  have hGpos : 0 < |G0| := abs_pos.mpr hG0
  have hGc := (a5uB_contDiffAt_Gop hΦ (m - 1) ((α₀, 0) : ℝ × (ℝ × ℝ)) hc0).continuousAt
  have ev : ∀ᶠ p in 𝓝 ((α₀, 0) : ℝ × (ℝ × ℝ)), |dd (Φ p.1) p.2 (0, 1) (0, 1) - c| ≤ |c| / 2 ∧
      |G0| / 2 < |Gop (Φ p.1) (m - 1) p.2| ∧ a5uB_S (Φ p.1) p.2 < S0 + 1 := by
    filter_upwards [eventually_abs_sub_lt (a5uB_contDiff_dd hΦ (0, 1) (0, 1)).continuous.continuousAt
        (half_pos hcpos), eventually_abs_sub_lt hGc (half_pos hGpos),
      eventually_abs_sub_lt (a5uB_continuous_S hΦ).continuousAt one_pos] with p h1 h2 h3
    exact ⟨h1.le, half_lt_abs_of h2, by have := (abs_lt.mp h3).2; linarith⟩
  obtain ⟨r, hr, H⟩ := a5uB_box ev
  set b := r / 4 with hbdef
  have hb : 0 < b := by positivity
  have hcb : 0 < |c| * b / 4 := by positivity
  have ev' : ∀ᶠ p in 𝓝 ((α₀, 0) : ℝ × (ℝ × ℝ)), |fderiv ℝ (Φ p.1) p.2 (0, 1)| < |c| * b / 4 := by
    filter_upwards [eventually_abs_sub_lt (a5uB_contDiff_fderiv hΦ (0, 1)).continuous.continuousAt hcb]
      with p hp
    simpa [hP0] using hp
  obtain ⟨r', hr', H'⟩ := a5uB_box ev'
  set a := min r r' / 4 with hadef
  have ha : 0 < a := by positivity
  have har : 2 * a ≤ r := by have := min_le_left r r'; linarith
  have har' : 2 * a ≤ r' := by have := min_le_right r r'; linarith
  refine ⟨min r r', lt_min hr hr', min 1 (|c| * b / 8), by positivity, a, b, |c| / 2, |G0| / 2, S0 + 1, ha,
    hb, half_pos hcpos, half_pos hGpos, fun α q => implicitCurve (fun k => Φ α k + q * k.2) b,
    fun α hα q hq => ?_⟩
  have hα1 : |α - α₀| ≤ r := hα.trans (min_le_left _ _)
  have hα2 : |α - α₀| ≤ r' := hα.trans (min_le_right _ _)
  have hΦα : ContDiff ℝ ∞ (Φ α) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  exact a5uB_coreHyps hΦα (by omega) ha hb hc0 (hq.trans (min_le_left _ _)) (hq.trans (min_le_right _ _))
    (fun x y hx hy => H α x y hα1 (hx.trans har) (hy.trans (by linarith)))
    (fun x hx => H' α x 0 hα2 (hx.trans har') (by simpa using hr'.le))

end OscInt.A5UAux
