/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4
import OscInt.StationaryPhase.Implicit
import OscInt.StationaryPhase.Local
import OscInt.StationaryPhase.Family

/-!
# S4.1, part D2: the rescaled family is of class `C⁴`

`OscInt.D4.rescaleFamily : OscInt.Blueprint.RescaleFamilyFacts`. Route: `docs/proof-S4.md`, Step 2, in the form
adopted after the route referee (`review/2026-11-06-S4-proof-route.md`, MINOR 1).

* Write `φ = C + R` with `C = cubicPoly (cubicCoeffs φ)`. Since `C(εz) = ε³C(z)`,
  `rescale φ ε = C + ε⁻³R(ε ·)` for `ε ≠ 0`, and `= C + 0` at `ε = 0` (`remFam`).
* `DⁱC(0) = Dⁱφ(0)` for `i ≤ 3` (`iteratedFDeriv_cubic_zero`): explicit derivatives of the cubic, and the
  coordinate formula of the symmetric trilinear form `ddd φ 0` (`ddd_eq_coord`, symmetry from `dd_comm` applied
  to `φ` and to `fderiv φ · u`). Hence `DⁱR(0) = 0` for `i ≤ 3`.
* Iterating the mean value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`, `norm_fderiv_iteratedFDeriv`)
  gives `‖DʲR(x)‖ ≤ S‖x‖⁴⁻ʲ` on the unit ball (`exists_remainder_bound`).
* `Dʲ(ε⁻³R(ε·))(z) = ε^{j-3} DʲR(εz)` (`iteratedFDeriv_remFam`), jointly continuous for `ε ≠ 0`, and of norm
  `≤ S|ε|‖z‖⁴⁻ʲ`, so it tends to `0` as `ε → 0` locally uniformly in `z`.
-/

open Filter Topology OscInt.Statements OscInt.Blueprint
open scoped ContDiff

namespace OscInt.D4.RescaleAux
open OscInt.StationaryPhase.ImplicitAux

theorem fd_cubic (q : ℝ × ℝ × ℝ × ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (cubicPoly q) y v = (3 * q.1 * v.1 + q.2.1 * v.2) * y.1 ^ 2 +
      (2 * q.2.1 * v.1 + 2 * q.2.2.1 * v.2) * (y.1 * y.2) + (q.2.2.1 * v.1 + 3 * q.2.2.2 * v.2) * y.2 ^ 2 := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h := ((((h1.pow 3).const_mul q.1).fun_add (((h1.pow 2).fun_mul h2).const_mul q.2.1)).fun_add
      ((h1.fun_mul (h2.pow 2)).const_mul q.2.2.1)).fun_add ((h2.pow 3).const_mul q.2.2.2)
  have e : cubicPoly q = fun y : ℝ × ℝ => q.1 * y.1 ^ 3 + q.2.1 * (y.1 ^ 2 * y.2) +
      q.2.2.1 * (y.1 * y.2 ^ 2) + q.2.2.2 * y.2 ^ 3 := by
    funext y; simp only [cubicPoly]; ring
  rw [e]
  rw [h.fderiv]
  simp
  ring

theorem fd_quad (α β γ : ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => α * y.1 ^ 2 + β * (y.1 * y.2) + γ * y.2 ^ 2) y w =
      (2 * α * w.1 + β * w.2) * y.1 + (β * w.1 + 2 * γ * w.2) * y.2 := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h := (((h1.pow 2).const_mul α).fun_add ((h1.fun_mul h2).const_mul β)).fun_add ((h2.pow 2).const_mul γ)
  rw [h.fderiv]
  simp
  ring

theorem dd_cubic (q : ℝ × ℝ × ℝ × ℝ) (y u v : ℝ × ℝ) :
    dd (cubicPoly q) y u v =
      (2 * (3 * q.1 * u.1 + q.2.1 * u.2) * v.1 + (2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.2) * y.1 +
      ((2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.1 + 2 * (q.2.2.1 * u.1 + 3 * q.2.2.2 * u.2) * v.2) * y.2 := by
  have : (fun y => fderiv ℝ (cubicPoly q) y u) = fun y : ℝ × ℝ =>
      (3 * q.1 * u.1 + q.2.1 * u.2) * y.1 ^ 2 + (2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * (y.1 * y.2) +
        (q.2.2.1 * u.1 + 3 * q.2.2.2 * u.2) * y.2 ^ 2 := funext fun y => fd_cubic q y u
  rw [dd, this, fd_quad]

theorem ddd_cubic (q : ℝ × ℝ × ℝ × ℝ) (y u v w : ℝ × ℝ) :
    ddd (cubicPoly q) y u v w =
      (2 * (3 * q.1 * u.1 + q.2.1 * u.2) * v.1 + (2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.2) * w.1 +
      ((2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.1 + 2 * (q.2.2.1 * u.1 + 3 * q.2.2.2 * u.2) * v.2) * w.2 := by
  have : (fun y => dd (cubicPoly q) y u v) = fun y : ℝ × ℝ =>
      (2 * (3 * q.1 * u.1 + q.2.1 * u.2) * v.1 + (2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.2) * y.1 +
      ((2 * q.2.1 * u.1 + 2 * q.2.2.1 * u.2) * v.1 + 2 * (q.2.2.1 * u.1 + 3 * q.2.2.2 * u.2) * v.2) * y.2 :=
    funext fun y => dd_cubic q y u v
  rw [ddd, this, sanity_fd_lin]

/-- Symmetry of `ddd` in the first two directions. -/
theorem ddd_swap12 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 3 f) (k u v w : ℝ × ℝ) :
    ddd f k u v w = ddd f k v u w := by
  have : (fun y => dd f y u v) = fun y => dd f y v u :=
    funext fun y => dd_comm (hf.of_le (by norm_num)) y u v
  rw [ddd, this, ddd]

/-- Symmetry of `ddd` in the last two directions. -/
theorem ddd_swap23 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 3 f) (k u v w : ℝ × ℝ) :
    ddd f k u v w = ddd f k u w v := by
  have hg : ContDiff ℝ 2 (fun y => fderiv ℝ f y u) := contDiff_fderiv_apply (n := 2) hf u
  exact dd_comm hg k v w

/-- Coordinate formula for the symmetric trilinear form `ddd f k` of a `C³` function. -/
theorem ddd_eq_coord {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 3 f) (k u v w : ℝ × ℝ) :
    ddd f k u v w = u.1 * v.1 * w.1 * ddd f k (1, 0) (1, 0) (1, 0) +
      (u.1 * v.1 * w.2 + u.1 * v.2 * w.1 + u.2 * v.1 * w.1) * ddd f k (1, 0) (1, 0) (0, 1) +
      (u.1 * v.2 * w.2 + u.2 * v.1 * w.2 + u.2 * v.2 * w.1) * ddd f k (1, 0) (0, 1) (0, 1) +
      u.2 * v.2 * w.2 * ddd f k (0, 1) (0, 1) (0, 1) := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd : ∀ a b : ℝ × ℝ, DifferentiableAt ℝ (fun y => dd f y a b) k := fun a b =>
    ((contDiff_dd (n := 1) hf a b).differentiable (by norm_num)) k
  have e : (fun y => dd f y u v) = fun y => u.1 * v.1 * dd f y (1, 0) (1, 0) +
      (u.1 * v.2 + u.2 * v.1) * dd f y (1, 0) (0, 1) + u.2 * v.2 * dd f y (0, 1) (0, 1) :=
    funext fun y => OscInt.StationaryPhase.LocalAux.dd_eq_coord h2 y u v
  have hw : ∀ a b : ℝ × ℝ, ddd f k a b w = w.1 * ddd f k a b (1, 0) + w.2 * ddd f k a b (0, 1) := by
    intro a b
    have : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    simp only [ddd]
    conv_lhs => rw [this]
    simp only [map_add, map_smul, smul_eq_mul]
  have hsum : ddd f k u v w = u.1 * v.1 * ddd f k (1, 0) (1, 0) w +
      (u.1 * v.2 + u.2 * v.1) * ddd f k (1, 0) (0, 1) w + u.2 * v.2 * ddd f k (0, 1) (0, 1) w := by
    rw [ddd, e]
    rw [fderiv_fun_add (by fun_prop) (by fun_prop), fderiv_fun_add (by fun_prop) (by fun_prop),
      fderiv_const_mul (hd _ _), fderiv_const_mul (hd _ _), fderiv_const_mul (hd _ _)]
    simp [ddd]
  rw [hsum, hw, hw, hw, ddd_swap23 hf k (1, 0) (0, 1) (1, 0), ddd_swap23 hf k (0, 1) (0, 1) (1, 0),
    ddd_swap12 hf k (0, 1) (1, 0) (0, 1)]
  ring

theorem cubicPoly_smul (q : ℝ × ℝ × ℝ × ℝ) (ε : ℝ) (z : ℝ × ℝ) :
    cubicPoly q (ε • z) = ε ^ 3 * cubicPoly q z := by
  simp only [cubicPoly, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem contDiff_cubicPoly (q : ℝ × ℝ × ℝ × ℝ) : ContDiff ℝ ∞ (cubicPoly q) := by
  unfold cubicPoly; fun_prop

theorem iteratedFDeriv_two_eq_dd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ × ℝ) (m : Fin 2 → ℝ × ℝ) :
    iteratedFDeriv ℝ 2 f k m = dd f k (m 1) (m 0) := by
  rw [dd_eq_iteratedFDeriv hf le_rfl]
  congr 1; funext i; fin_cases i <;> rfl

theorem iteratedFDeriv_three_eq_ddd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 3 f) (k : ℝ × ℝ)
    (m : Fin 3 → ℝ × ℝ) : iteratedFDeriv ℝ 3 f k m = ddd f k (m 2) (m 1) (m 0) := by
  rw [ddd_eq_iteratedFDeriv hf le_rfl]
  congr 1; funext i; fin_cases i <;> rfl

/-- The cubic part has the same derivatives of order `≤ 3` at `0` as `φ`. -/
theorem iteratedFDeriv_cubic_zero {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (h0 : φ 0 = 0)
    (h1 : fderiv ℝ φ 0 = 0) (h2 : ∀ v w, dd φ 0 v w = 0) {i : ℕ} (hi : i ≤ 3) :
    iteratedFDeriv ℝ i (cubicPoly (cubicCoeffs φ)) 0 = iteratedFDeriv ℝ i φ 0 := by
  have hC := contDiff_cubicPoly (cubicCoeffs φ)
  interval_cases i
  · ext m; simp [cubicPoly, h0]
  · ext m; simp [iteratedFDeriv_one_apply, fd_cubic, h1]
  · ext m
    rw [iteratedFDeriv_two_eq_dd (hC.of_le (by simp)),
      iteratedFDeriv_two_eq_dd (hφ.of_le (by norm_num)), dd_cubic, h2]
    simp
  · ext m
    rw [iteratedFDeriv_three_eq_ddd (hC.of_le (by simp)),
      iteratedFDeriv_three_eq_ddd (hφ.of_le (by norm_num)), ddd_cubic, ddd_eq_coord (hφ.of_le (by norm_num))]
    simp only [cubicCoeffs]
    ring

section Bounds
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Mean value step: `f(0) = 0` and `‖Df(y)‖ ≤ S‖y‖ⁿ` on the unit ball give `‖f(x)‖ ≤ S‖x‖ⁿ⁺¹` there. -/
theorem norm_le_of_norm_fderiv_le {f : E → F} (hf : Differentiable ℝ f) (h0 : f 0 = 0) {S : ℝ}
    (hS : 0 ≤ S) {n : ℕ} (h : ∀ y : E, ‖y‖ ≤ 1 → ‖fderiv ℝ f y‖ ≤ S * ‖y‖ ^ n) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖f x‖ ≤ S * ‖x‖ ^ (n + 1) := by
  have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖, ‖fderiv ℝ f y‖ ≤ S * ‖x‖ ^ n := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    exact (h y (hy.trans hx)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy n) hS)
  have := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le (fun y _ => hf y) hb
    (Metric.mem_closedBall_self (norm_nonneg x)) (mem_closedBall_zero_iff.mpr le_rfl)
  simpa [h0, pow_succ, mul_assoc] using this

/-- A `C⁴` function whose derivatives of order `≤ 3` vanish at `0` has `‖DʲR(x)‖ ≤ S‖x‖⁴⁻ʲ` on the
unit ball. -/
theorem exists_remainder_bound [ProperSpace E] {R : E → F} (hR : ContDiff ℝ 4 R)
    (h : ∀ i ≤ 3, iteratedFDeriv ℝ i R 0 = 0) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ j ≤ 4, ∀ x : E, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ j R x‖ ≤ S * ‖x‖ ^ (4 - j) := by
  obtain ⟨S₀, hS₀⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    (hR.continuous_iteratedFDeriv (m := 4) le_rfl).continuousOn
  set S := max S₀ 0
  have hS : 0 ≤ S := le_max_right _ _
  have h4 : ∀ x : E, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ 4 R x‖ ≤ S * ‖x‖ ^ 0 := fun x hx => by
    rw [pow_zero, mul_one]
    exact (hS₀ x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)
  have step : ∀ i < 4, ∀ n : ℕ, (∀ y : E, ‖y‖ ≤ 1 → ‖iteratedFDeriv ℝ (i + 1) R y‖ ≤ S * ‖y‖ ^ n) →
      ∀ x : E, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ i R x‖ ≤ S * ‖x‖ ^ (n + 1) := by
    intro i hi n hn x hx
    exact norm_le_of_norm_fderiv_le (hR.differentiable_iteratedFDeriv (by exact_mod_cast hi))
      (h i (by omega)) hS (fun y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hn y hy) hx
  have h3 := step 3 (by norm_num) 0 h4
  have h2 := step 2 (by norm_num) 1 h3
  have h1 := step 1 (by norm_num) 2 h2
  have h0 := step 0 (by norm_num) 3 h1
  refine ⟨S, hS, fun j hj => ?_⟩
  interval_cases j
  exacts [h0, h1, h2, h3, h4]

end Bounds

/-- The non-polynomial part of the rescaled family: `ε⁻³ R(ε ·)`, and `0` at `ε = 0`. -/
noncomputable def remFam (R : ℝ × ℝ → ℝ) (ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  if ε = 0 then 0 else (ε ^ 3)⁻¹ * R (ε • z)

theorem remFam_of_ne {R : ℝ × ℝ → ℝ} {ε : ℝ} (hε : ε ≠ 0) :
    remFam R ε = fun z => (ε ^ 3)⁻¹ • R (ε • z) := by
  funext z; simp [remFam, hε]

theorem contDiff_remFam {R : ℝ × ℝ → ℝ} (hR : ContDiff ℝ 4 R) (ε : ℝ) : ContDiff ℝ 4 (remFam R ε) := by
  by_cases hε : ε = 0
  · have : remFam R ε = fun _ => 0 := by funext z; simp [remFam, hε]
    rw [this]; exact contDiff_const
  · rw [remFam_of_ne hε]
    exact (contDiff_const (c := (ε ^ 3)⁻¹)).smul (hR.comp (contDiff_const_smul ε))

/-- `Dʲ(ε⁻³ R(ε ·))(z) = ε^{j-3} DʲR(εz)`. -/
theorem iteratedFDeriv_remFam {R : ℝ × ℝ → ℝ} (hR : ContDiff ℝ 4 R) {ε : ℝ} (hε : ε ≠ 0) {j : ℕ}
    (hj : j ≤ 4) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ j (remFam R ε) z = ((ε ^ 3)⁻¹ * ε ^ j) • iteratedFDeriv ℝ j R (ε • z) := by
  have hj' : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
  set L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := ε • ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have e : (fun z => R (ε • z)) = fun z => R (0 + L z) := by funext z; simp [L]
  have hc : ContDiff ℝ j (fun z => R (ε • z)) :=
    (hR.of_le hj').comp (contDiff_const_smul ε)
  rw [remFam_of_ne hε, iteratedFDeriv_const_smul_apply' hc.contDiffAt, e,
    OscInt.StationaryPhase.FamilyAux.iteratedFDeriv_comp_affine hR 0 L z hj']
  ext m
  simp [L, ContinuousMultilinearMap.map_smul_univ, mul_smul]

theorem iteratedFDeriv_zero_fun' (j : ℕ) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ j (fun _ : ℝ × ℝ => (0 : ℝ)) z = 0 := by
  cases j with
  | zero => ext m; simp
  | succ n => rw [iteratedFDeriv_succ_const]; rfl

theorem scale_arith {e a S : ℝ} (he : 0 < e) {j : ℕ} (hj : j ≤ 4) :
    (e ^ 3)⁻¹ * e ^ j * (S * (e * a) ^ (4 - j)) = S * e * a ^ (4 - j) := by
  have h : e ^ j * e ^ (4 - j) = e ^ 3 * e := by rw [← pow_add, Nat.add_sub_cancel' hj]; ring
  have h3 : e ^ 3 ≠ 0 := by positivity
  rw [mul_pow]
  calc (e ^ 3)⁻¹ * e ^ j * (S * (e ^ (4 - j) * a ^ (4 - j)))
      = (e ^ 3)⁻¹ * (e ^ j * e ^ (4 - j)) * S * a ^ (4 - j) := by ring
    _ = S * e * a ^ (4 - j) := by rw [h]; field_simp

/-- Bound for the rescaled remainder: `‖Dʲ(ε⁻³R(ε·))(z)‖ ≤ S |ε| ‖z‖⁴⁻ʲ` when `|ε| ‖z‖ ≤ 1`. -/
theorem norm_iteratedFDeriv_remFam_le {R : ℝ × ℝ → ℝ} (hR : ContDiff ℝ 4 R) {S : ℝ}
    (hb : ∀ j ≤ 4, ∀ x : ℝ × ℝ, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ j R x‖ ≤ S * ‖x‖ ^ (4 - j))
    {j : ℕ} (hj : j ≤ 4) {ε : ℝ} {z : ℝ × ℝ} (hz : |ε| * ‖z‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (remFam R ε) z‖ ≤ S * |ε| * ‖z‖ ^ (4 - j) := by
  by_cases hε : ε = 0
  · have : remFam R ε = fun _ => 0 := by funext z; simp [remFam, hε]
    rw [this, iteratedFDeriv_zero_fun']; simp [hε]
  · have he : 0 < |ε| := abs_pos.mpr hε
    rw [iteratedFDeriv_remFam hR hε hj, norm_smul, norm_mul, norm_inv, norm_pow, norm_pow,
      Real.norm_eq_abs, ← scale_arith he hj]
    have hn : ‖ε • z‖ = |ε| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
    gcongr
    rw [← hn]
    exact hb j hj _ (hn ▸ hz)

/-- Joint continuity of `(ε, z) ↦ Dʲ(ε⁻³R(ε·))(z)`, with value `0` at `ε = 0`. -/
theorem continuous_iteratedFDeriv_remFam {R : ℝ × ℝ → ℝ} (hR : ContDiff ℝ 4 R)
    (h : ∀ i ≤ 3, iteratedFDeriv ℝ i R 0 = 0) {j : ℕ} (hj : j ≤ 4) :
    Continuous fun q : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ j (remFam R q.1) q.2 := by
  obtain ⟨S, -, hb⟩ := exists_remainder_bound hR h
  have hj' : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
  have hcR := hR.continuous_iteratedFDeriv hj'
  rw [continuous_iff_continuousAt]
  rintro ⟨ε₀, z₀⟩
  by_cases h0 : ε₀ = 0
  · subst h0
    have hval : iteratedFDeriv ℝ j (remFam R 0) z₀ = 0 := by
      have : remFam R 0 = fun _ => 0 := by funext z; simp [remFam]
      rw [this, iteratedFDeriv_zero_fun']
    have hg : Continuous fun q : ℝ × (ℝ × ℝ) => S * |q.1| * ‖q.2‖ ^ (4 - j) := by fun_prop
    have hg0 : Tendsto (fun q : ℝ × (ℝ × ℝ) => S * |q.1| * ‖q.2‖ ^ (4 - j)) (𝓝 (0, z₀)) (𝓝 0) := by
      simpa using hg.tendsto (0, z₀)
    have hev : ∀ᶠ q : ℝ × (ℝ × ℝ) in 𝓝 (0, z₀), |q.1| * ‖q.2‖ < 1 :=
      ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simp)
    show Tendsto _ _ (𝓝 (iteratedFDeriv ℝ j (remFam R 0) z₀))
    rw [hval]
    exact squeeze_zero_norm' (hev.mono fun q hq => norm_iteratedFDeriv_remFam_le hR hb hj hq.le) hg0
  · have hev : (fun q : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ j (remFam R q.1) q.2) =ᶠ[𝓝 (ε₀, z₀)]
        fun q => ((q.1 ^ 3)⁻¹ * q.1 ^ j) • iteratedFDeriv ℝ j R (q.1 • q.2) := by
      filter_upwards [continuous_fst.continuousAt.eventually_ne h0] with q hq
      exact iteratedFDeriv_remFam hR hq hj q.2
    refine ContinuousAt.congr ?_ hev.symm
    have h1 : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => (q.1 ^ 3)⁻¹ * q.1 ^ j) (ε₀, z₀) :=
      ((continuous_fst.pow 3).continuousAt.inv₀ (pow_ne_zero 3 h0)).mul (continuous_fst.pow j).continuousAt
    exact h1.smul (hcR.comp (continuous_fst.smul continuous_snd)).continuousAt

end OscInt.D4.RescaleAux

namespace OscInt.D4

open RescaleAux

/-- **D2** The rescaled phases `ε⁻³ φ(ε ·)`, with the cubic part at `ε = 0`, form a family of class `C⁴`. -/
theorem rescaleFamily : OscInt.Blueprint.RescaleFamilyFacts := by
  intro φ hφ h0 h1 h2
  set C := cubicPoly (cubicCoeffs φ) with hCdef
  have hC : ContDiff ℝ 4 C := (contDiff_cubicPoly _).of_le (by simp)
  have hR : ContDiff ℝ 4 (φ - C) := hφ.sub hC
  have hR0 : ∀ i ≤ 3, iteratedFDeriv ℝ i (φ - C) 0 = 0 := fun i hi => by
    rw [iteratedFDeriv_sub_apply (hφ.of_le (by exact_mod_cast (by omega : i ≤ 4))).contDiffAt
      (hC.of_le (by exact_mod_cast (by omega : i ≤ 4))).contDiffAt,
      iteratedFDeriv_cubic_zero hφ h0 h1 h2 hi, sub_self]
  have hres : ∀ ε, rescale φ ε = fun z => C z + remFam (φ - C) ε z := by
    intro ε; funext z
    by_cases hε : ε = 0
    · simp [rescale, remFam, hε, hCdef]
    · simp only [rescale, remFam, hε, ite_false, Pi.sub_apply, hCdef, cubicPoly_smul]
      field_simp
      ring
  refine ⟨fun ε => by rw [hres]; exact hC.add (contDiff_remFam hR ε), fun j hj => ?_⟩
  simp_rw [hres]
  have hj' : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
  exact OscInt.StationaryPhase.FamilyAux.continuous_iteratedFDeriv_add (f := fun _ : ℝ => C)
    (g := remFam (φ - C)) (fun _ => hC.of_le hj') (fun ε => (contDiff_remFam hR ε).of_le hj')
    ((hC.continuous_iteratedFDeriv hj').comp continuous_snd)
    (continuous_iteratedFDeriv_remFam hR hR0 hj)

end OscInt.D4
