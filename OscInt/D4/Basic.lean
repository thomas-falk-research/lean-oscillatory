/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.D4
import OscInt.StationaryPhase.Assembly

/-!
# S4.1: the elementary parts D1, D7, D8, D9

Proves the blueprint propositions of `Blueprint/D4.lean` that need no geometry (route: `docs/proof-S4.md`,
Steps 1, 4, 5).

* `normalizeFacts` (D1): `normalize φ = (φ − φ(0)) + lin (−∇φ(0))`, so `dd`/`ddd` are unchanged
  (`dd_add_lin`, `fderiv_sub_const`); pointwise `tφ + y·κ = tφ(0) + (t normalize φ + (y + t∇φ(0))·κ)`, and the
  factor `exp(i t φ(0))` has norm one.
* `cutoff` (D7): `χ(z) = b(z₁) b(z₂)` for a one-dimensional `ContDiffBump` with radii `1, 2`; `χ(2z) ≤ χ(z)`
  because `χ(z) = 1` for `‖z‖ ≤ 1` and `χ(2z) = 0` otherwise.
* `trivialBound` (D8): the integral is a set integral over `B̄(0, r)`, of max-norm area `(2r)²`.
* `dyadicSum` (D9): `J` is the least `j` with `t ε_j³ < 1`; each term equals `t^{-2/3} (t ε_j³)^{-1/6}
  ≤ t^{-2/3} (8^{-1/6})^{J-1-j}`, and `∑ (8^{-1/6})^i ≤ 4` since `8^{-1/6} ≤ 3/4`.
-/

namespace OscInt.D4

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase
open scoped ContDiff

namespace BasicAux

theorem clm_apply_eq_lin (L : (ℝ × ℝ) →L[ℝ] ℝ) (κ : ℝ × ℝ) :
    L κ = lin (L (1, 0), L (0, 1)) κ := by
  have : κ = κ.1 • ((1 : ℝ), (0 : ℝ)) + κ.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, lin]; simp [smul_eq_mul]; ring

theorem normalize_eq (φ : ℝ × ℝ → ℝ) :
    normalize φ = fun κ => (φ κ - φ 0) + lin (-grad0 φ) κ := by
  funext κ
  rw [OscInt.Blueprint.normalize, clm_apply_eq_lin (fderiv ℝ φ 0) κ]
  simp only [lin, grad0, Prod.fst_neg, Prod.snd_neg]; ring

theorem dd_sub_const (φ : ℝ × ℝ → ℝ) (c : ℝ) : dd (fun κ => φ κ - c) = dd φ := by
  funext y v w
  simp only [dd, fderiv_sub_const]

/-- `ε² (t ε³)^{-5/6} = t^{-2/3} (t ε³)^{-1/6}`. -/
theorem term_eq {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ε ^ 2 * (t * ε ^ 3) ^ (-(5 : ℝ) / 6) = t ^ (-(2 : ℝ) / 3) * (t * ε ^ 3) ^ (-(1 : ℝ) / 6) := by
  have h3 : ∀ z : ℝ, (ε ^ 3) ^ z = ε ^ (3 * z) := fun z => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  rw [Real.mul_rpow ht.le (by positivity), Real.mul_rpow ht.le (by positivity), h3, h3,
    ← Real.rpow_natCast ε 2, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ht, mul_comm (ε ^ _),
    mul_assoc, ← Real.rpow_add hε]
  norm_num

/-- `8^{-1/6} ≤ 3/4`. -/
theorem s_le : (8 : ℝ) ^ (-(1 : ℝ) / 6) ≤ 3 / 4 := by
  have hpos : 0 < (8 : ℝ) ^ (-(1 : ℝ) / 6) := by positivity
  have h6 : ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ (6 : ℕ) = 1 / 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra h
  rw [not_le] at h
  have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (6 : ℕ) ≠ 0)
  rw [h6] at this; norm_num at this

theorem geom_le (J : ℕ) : ∑ i ∈ Finset.range J, ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ i ≤ 4 := by
  set s := (8 : ℝ) ^ (-(1 : ℝ) / 6)
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 3 / 4 := s_le
  have hsJ : 0 ≤ s ^ J := pow_nonneg hs0 J
  have hne : s - 1 ≠ 0 := by linarith
  rw [geom_sum_eq (by linarith : s ≠ 1), div_le_iff_of_neg (by linarith)]
  nlinarith

theorem exists_small {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 1 ≤ t) :
    ∃ j : ℕ, t * (δ / 2 ^ j) ^ 3 < 1 := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hx0 : 0 < δ / 2 ^ j := by positivity
  have hx1 : δ / 2 ^ j ≤ 1 := by rw [div_le_one h2]; exact hδ1.trans (one_le_pow₀ (by norm_num))
  have hx3 : (δ / 2 ^ j) ^ 3 ≤ δ / 2 ^ j := by
    calc (δ / 2 ^ j) ^ 3 ≤ (δ / 2 ^ j) ^ 1 := pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
      _ = _ := pow_one _
  calc t * (δ / 2 ^ j) ^ 3 ≤ t * (δ / 2 ^ j) := by gcongr
    _ ≤ t * (1 / 2 ^ j) := by gcongr
    _ < 1 := by rw [mul_one_div, div_lt_one h2]; exact hj

theorem sq_le_of_lt {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (h : t * x ^ 3 < 1) :
    x ^ 2 ≤ t ^ (-(2 : ℝ) / 3) := by
  have h1 : x ^ 3 ≤ t⁻¹ := by
    rw [← one_div, le_div_iff₀ ht]; linarith
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h2
  convert h2 using 2 <;> norm_num

/-- With `n = J - 1 - j`: the `j`-th term is at most `t^{-2/3} (8^{-1/6})^n`. -/
theorem term_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (j n : ℕ) (h : 1 ≤ t * (δ / 2 ^ (j + n)) ^ 3) :
    (δ / 2 ^ j) ^ 2 * (t * (δ / 2 ^ j) ^ 3) ^ (-(5 : ℝ) / 6) ≤
      t ^ (-(2 : ℝ) / 3) * ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := by
  rw [term_eq ht (by positivity)]
  gcongr
  have hm : t * (δ / 2 ^ j) ^ 3 = t * (δ / 2 ^ (j + n)) ^ 3 * (8 : ℝ) ^ n := by
    rw [pow_add, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    field_simp
    ring
  have h8 : (1 : ℝ) * (8 : ℝ) ^ n ≤ t * (δ / 2 ^ j) ^ 3 := by rw [hm]; gcongr
  rw [one_mul] at h8
  rw [Real.rpow_pow_comm (by norm_num)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h8 (by norm_num)

end BasicAux

/-- **D1** Normalisation. -/
theorem normalizeFacts : NormalizeFacts := by
  intro φ hφ
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hc2 : ContDiff ℝ 2 (fun κ => φ κ - φ 0) := (hφ.of_le (by norm_num)).sub contDiff_const
  have hdd : dd (normalize φ) = dd φ := by
    rw [BasicAux.normalize_eq, dd_add_lin hc2, BasicAux.dd_sub_const]
  refine ⟨?_, by simp [OscInt.Blueprint.normalize], ?_, hdd, ?_, ?_⟩
  · exact (hφ.sub contDiff_const).sub (fderiv ℝ φ 0).contDiff
  · have h := ((hd 0).hasFDerivAt.sub_const (φ 0)).sub (fderiv ℝ φ 0).hasFDerivAt
    rw [show OscInt.Blueprint.normalize φ = (fun x => φ x - φ 0) - ⇑(fderiv ℝ φ 0) from rfl, h.fderiv,
      sub_self]
  · funext y u v w; simp only [ddd, hdd]
  · intro A t y
    have hpt : ∀ κ, t * φ κ + lin y κ = t * φ 0 + (t * normalize φ κ + lin (y + t • grad0 φ) κ) := by
      intro κ
      rw [BasicAux.normalize_eq]
      simp only [lin, grad0, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have : oscInt2 (fun κ => t * φ κ + lin y κ) A =
        Complex.exp (↑(t * φ 0) * Complex.I) *
          oscInt2 (fun κ => t * normalize φ κ + lin (y + t • grad0 φ) κ) A := by
      rw [oscInt2, oscInt2, ← integral_const_mul]
      congr 1; funext κ
      rw [hpt κ, Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **D7** A smooth product cut-off. -/
theorem cutoff : CutoffFacts := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : ℝ × ℝ → ℝ := fun z => b z.1 * b z.2
  have hsupp : tsupport χ ⊆ Metric.closedBall 0 2 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have h1 : b z.1 ≠ 0 := left_ne_zero_of_mul hz
    have h2 : b z.2 ≠ 0 := right_ne_zero_of_mul hz
    have m1 : z.1 ∈ Metric.closedBall (0 : ℝ) 2 := by
      rw [← b.tsupport_eq]; exact subset_tsupport _ h1
    have m2 : z.2 ∈ Metric.closedBall (0 : ℝ) 2 := by
      rw [← b.tsupport_eq]; exact subset_tsupport _ h2
    rw [mem_closedBall_zero_iff] at *
    rw [Prod.norm_def]; exact max_le m1 m2
  have hone : ∀ z : ℝ × ℝ, ‖z‖ ≤ 1 → χ z = 1 := by
    intro z hz
    rw [Prod.norm_def] at hz
    have m1 : z.1 ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [mem_closedBall_zero_iff]; exact (le_max_left _ _).trans hz
    have m2 : z.2 ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [mem_closedBall_zero_iff]; exact (le_max_right _ _).trans hz
    simp only [χ, b.one_of_mem_closedBall m1, b.one_of_mem_closedBall m2, mul_one]
  have hIcc : ∀ z, χ z ∈ Icc (0 : ℝ) 1 := fun z =>
    ⟨mul_nonneg b.nonneg b.nonneg, by
      nlinarith [b.nonneg (x := z.1), b.nonneg (x := z.2), b.le_one (x := z.1), b.le_one (x := z.2)]⟩
  refine ⟨χ, ?_, hIcc, hone, hsupp, fun z => ?_⟩
  · exact (b.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd)
  · by_cases hz : ‖z‖ ≤ 1
    · rw [hone z hz]; exact (hIcc _).2
    · have : (2 : ℝ) • z ∉ tsupport χ := by
        intro h
        have := hsupp h
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_two] at this
        exact hz (by linarith)
      rw [image_eq_zero_of_notMem_tsupport this]; exact (hIcc _).1

/-- **D8** Trivial bound by the area of the support ball. -/
theorem trivialBound : TrivialBoundFacts := by
  intro Q A M r _ hM hA
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hzero : ∀ k, k ∉ Metric.closedBall (0 : ℝ × ℝ) r →
      Complex.exp (↑(Q k) * Complex.I) * A k = 0 := by
    intro k hk
    rw [image_eq_zero_of_notMem_tsupport (fun h => hk (hA h)), mul_zero]
  rw [oscInt2, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hfin : volume (Metric.closedBall (0 : ℝ × ℝ) r) < ⊤ := measure_closedBall_lt_top
  refine (norm_setIntegral_le_of_norm_le_const (C := M) hfin fun k _ => ?_).trans ?_
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hM k
  · rcases lt_or_ge r 0 with hr | hr
    · rw [Metric.closedBall_eq_empty.mpr hr, measureReal_empty, mul_zero]; positivity
    · have : volume.real (Metric.closedBall (0 : ℝ × ℝ) r) = 4 * r ^ 2 := by
        rw [show (0 : ℝ × ℝ) = ((0 : ℝ), (0 : ℝ)) from rfl, ← closedBall_prod_same,
          measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_closedBall,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
        ring
      rw [this, mul_comm]

/-- **D9** Dyadic summation. -/
theorem dyadicSum : DyadicSumFacts := by
  intro δ t hδ hδ1 ht
  have ht0 : 0 < t := by linarith
  classical
  have hex := BasicAux.exists_small hδ hδ1 ht
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex hj)
  · exact BasicAux.sq_le_of_lt ht0 (by positivity) (Nat.find_spec hex)
  · set J := Nat.find hex
    have hmin : ∀ j < J, 1 ≤ t * (δ / 2 ^ j) ^ 3 := fun j hj => le_of_not_gt (Nat.find_min hex hj)
    calc ∑ j ∈ Finset.range J, (δ / 2 ^ j) ^ 2 * (t * (δ / 2 ^ j) ^ 3) ^ (-(5 : ℝ) / 6)
        ≤ ∑ j ∈ Finset.range J, t ^ (-(2 : ℝ) / 3) * ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ (J - 1 - j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          apply BasicAux.term_le hδ ht0
          have : j + (J - 1 - j) = J - 1 := by omega
          rw [this]; exact hmin _ (by omega)
      _ = t ^ (-(2 : ℝ) / 3) * ∑ i ∈ Finset.range J, ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ i := by
          rw [← Finset.mul_sum, Finset.sum_range_reflect (fun i => ((8 : ℝ) ^ (-(1 : ℝ) / 6)) ^ i) J]
      _ ≤ t ^ (-(2 : ℝ) / 3) * 4 := by gcongr; exact BasicAux.geom_le J
      _ = 4 * t ^ (-(2 : ℝ) / 3) := mul_comm _ _

end OscInt.D4
