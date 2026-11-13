/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeCubeRoot

/-!
# Batch LE2: P-band and P-cap from P-ibp and P-var (route `docs/proof-LE2.md`)

`BandLowFacts`, `BandHighFacts`, `CapLowFacts`, `CapHighFacts` and `WholeFacts`, each proved from `IbpFacts` and
`VarFacts`. With `ξ = t v`, `g k = t v − t sin k`, `p = arcsin (v − δ)` and `q = arcsin (v + δ)`, the kernel integral is
split (`intervalIntegral.integral_add_adjacent_intervals`) into pieces where `|g| ≥ t δ`, bounded by one integration by
parts (P-ibp) with the variation integral split at the turning point `±π/2` and evaluated by P-var, and band or cap
pieces, bounded by their length. The shared pieces (route referee, "shared pieces") are proved once:
`posLow` (`[−π − p, p]`), `posHighL` (`[−π, p]`), `posHighR` (`[π − p, π]`), `negPiece` (`[q, π − q]`) and `J_len`.
-/

namespace OscInt.LatticeCubeRootAux.Pieces

open Set OscInt.Statements OscInt.Blueprint.LatticeCubeRoot Real

/-- The kernel integral over `[a, b]` with `ξ = t v`. -/
noncomputable def J (t v a b : ℝ) : ℂ := ∫ k in a..b, Complex.exp (↑(t * cos k + t * v * k) * Complex.I)

/-- The variation integral `∫_a^b |g′|/g²` of P-ibp for the lattice phase with `ξ = t v`. -/
noncomputable def V (t v a b : ℝ) : ℝ := ∫ k in a..b, |-(t * cos k)| / (t * v - t * sin k) ^ 2

theorem kernel_eq (t v : ℝ) : latticeKernel1 t (t * v) = J t v (-π) π := rfl

theorem J_add (t v a b c : ℝ) : J t v a b + J t v b c = J t v a c := by
  have h : Continuous fun k : ℝ => Complex.exp (↑(t * cos k + t * v * k) * Complex.I) := by fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable _ _) (h.intervalIntegrable _ _)

/-- A band or cap piece, bounded by its length. -/
theorem J_len (t v a b : ℝ) (h : a ≤ b) : ‖J t v a b‖ ≤ b - a := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := a) (b := b)
    (f := fun k : ℝ => Complex.exp (↑(t * cos k + t * v * k) * Complex.I))
    (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr h)] at this

/-- The variation integral splits at an interior point (its integrand is continuous where `g ≠ 0`). -/
theorem V_add {t v a b c : ℝ} (hne : ∀ k ∈ Icc a b, t * v - t * sin k ≠ 0) (hac : a ≤ c) (hcb : c ≤ b) :
    V t v a b = V t v a c + V t v c b := by
  have hc : ContinuousOn (fun k : ℝ => |-(t * cos k)| / (t * v - t * sin k) ^ 2) (Icc a b) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun k hk => pow_ne_zero 2 (hne k hk))
  have h1 : IntervalIntegrable (fun k : ℝ => |-(t * cos k)| / (t * v - t * sin k) ^ 2) MeasureTheory.volume a c :=
    (hc.mono (by rw [uIcc_of_le hac]; exact Icc_subset_Icc_right hcb)).intervalIntegrable
  have h2 : IntervalIntegrable (fun k : ℝ => |-(t * cos k)| / (t * v - t * sin k) ^ 2) MeasureTheory.volume c b :=
    (hc.mono (by rw [uIcc_of_le hcb]; exact Icc_subset_Icc_left hac)).intervalIntegrable
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

/-- P-ibp for the lattice phase `t cos k + t v k`. -/
theorem ibp (hI : IbpFacts) {t v a b : ℝ} (hab : a ≤ b) (hne : ∀ k ∈ Icc a b, t * v - t * sin k ≠ 0) :
    ‖J t v a b‖ ≤ 1 / |t * v - t * sin a| + 1 / |t * v - t * sin b| + V t v a b :=
  hI (fun x => t * cos x + t * v * x) (fun x => t * v - t * sin x) (fun x => -(t * cos x)) a b hab
    (fun x _ => (((hasDerivAt_cos x).const_mul t).add ((hasDerivAt_id' x).const_mul (t * v))).congr_deriv
      (by ring))
    (fun x _ => ((hasDerivAt_sin x).const_mul t).const_sub (t * v))
    (by fun_prop : Continuous fun x => -(t * cos x)).continuousOn hne

theorem sin_neg_pi_sub (x : ℝ) : sin (-π - x) = sin x := by
  rw [show -π - x = -(x + π) by ring, sin_neg, sin_add_pi, neg_neg]

theorem g_neg_half (t v : ℝ) : t * v - t * sin (-(π / 2)) = t * (1 + v) := by
  rw [sin_neg, sin_pi_div_two]; ring

theorem g_half (t v : ℝ) : t * v - t * sin (π / 2) = -(t * (1 - v)) := by
  rw [sin_pi_div_two]; ring

theorem g_neg_pi (t v : ℝ) : t * v - t * sin (-π) = t * v := by
  rw [sin_neg, sin_pi]; ring

theorem g_pi (t v : ℝ) : t * v - t * sin π = t * v := by
  rw [sin_pi]; ring

/-- A piece with `g > 0` and turning point `−π/2`: P-ibp, then P-var on `[a, −π/2]` (branch 2) and `[−π/2, b]`
(branch 1). -/
theorem posTurn (hI : IbpFacts) (hV : VarFacts) {t v a b : ℝ} (ht : 0 < t) (ha : -(π + π / 2) ≤ a)
    (ham : a ≤ -(π / 2)) (hmb : -(π / 2) ≤ b) (hb : b ≤ π / 2) (hpos : ∀ k ∈ Icc a b, 0 < t * v - t * sin k) :
    ‖J t v a b‖ ≤ 2 / (t * v - t * sin a) + 2 / (t * v - t * sin b) - 2 / (t * (1 + v)) := by
  have hne : ∀ k ∈ Icc a b, t * v - t * sin k ≠ 0 := fun k hk => (hpos k hk).ne'
  have h1 := ibp hI (ham.trans hmb) hne
  rw [V_add hne ham hmb] at h1
  have e1 := (hV t (t * v) a (-(π / 2)) ht ham (fun k hk => hne k ⟨hk.1, hk.2.trans hmb⟩)).2
    (Or.inr (Icc_subset_Icc ha le_rfl))
  have e2 := (hV t (t * v) (-(π / 2)) b ht hmb (fun k hk => hne k ⟨ham.trans hk.1, hk.2⟩)).1
    (Icc_subset_Icc le_rfl hb)
  unfold V at h1
  rw [e1, e2, g_neg_half, abs_of_pos (hpos a ⟨le_rfl, ham.trans hmb⟩),
    abs_of_pos (hpos b ⟨ham.trans hmb, le_rfl⟩)] at h1
  refine h1.trans (le_of_eq ?_); ring

/-- A piece with `g < 0` and turning point `π/2`: P-ibp, then P-var on `[a, π/2]` (branch 1) and `[π/2, b]`
(branch 2). -/
theorem negTurn (hI : IbpFacts) (hV : VarFacts) {t v a b : ℝ} (ht : 0 < t) (ha : -(π / 2) ≤ a)
    (ham : a ≤ π / 2) (hmb : π / 2 ≤ b) (hb : b ≤ π + π / 2) (hneg : ∀ k ∈ Icc a b, t * v - t * sin k < 0) :
    ‖J t v a b‖ ≤ 2 / (t * sin a - t * v) + 2 / (t * sin b - t * v) - 2 / (t * (1 - v)) := by
  have hne : ∀ k ∈ Icc a b, t * v - t * sin k ≠ 0 := fun k hk => (hneg k hk).ne
  have h1 := ibp hI (ham.trans hmb) hne
  rw [V_add hne ham hmb] at h1
  have e1 := (hV t (t * v) a (π / 2) ht ham (fun k hk => hne k ⟨hk.1, hk.2.trans hmb⟩)).1
    (Icc_subset_Icc ha le_rfl)
  have e2 := (hV t (t * v) (π / 2) b ht hmb (fun k hk => hne k ⟨ham.trans hk.1, hk.2⟩)).2
    (Or.inl (Icc_subset_Icc le_rfl hb))
  unfold V at h1
  rw [e1, e2, g_half, abs_of_neg (hneg a ⟨le_rfl, ham.trans hmb⟩),
    abs_of_neg (hneg b ⟨ham.trans hmb, le_rfl⟩), neg_sub, neg_sub, div_neg] at h1
  rw [← neg_sub (t * sin a) (t * v), ← neg_sub (t * sin b) (t * v), div_neg, div_neg] at h1
  refine h1.trans (le_of_eq ?_); ring

/-- A piece with `g > 0` inside `[π/2, π + π/2]`: P-ibp and P-var (branch 2). -/
theorem posBr2 (hI : IbpFacts) (hV : VarFacts) {t v a b : ℝ} (ht : 0 < t) (ha : π / 2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ π + π / 2) (hpos : ∀ k ∈ Icc a b, 0 < t * v - t * sin k) :
    ‖J t v a b‖ ≤ 2 / (t * v - t * sin a) := by
  have hne : ∀ k ∈ Icc a b, t * v - t * sin k ≠ 0 := fun k hk => (hpos k hk).ne'
  have h1 := ibp hI hab hne
  have e1 := (hV t (t * v) a b ht hab hne).2 (Or.inl (Icc_subset_Icc ha hb))
  unfold V at h1
  rw [e1, abs_of_pos (hpos a ⟨le_rfl, hab⟩), abs_of_pos (hpos b ⟨hab, le_rfl⟩)] at h1
  refine h1.trans (le_of_eq ?_); ring

/-- `sin k ≤ sin p` on `[−π − p, p]` (monotonicity of `sin` on `[−π/2, π/2]` and `sin (−π − k) = sin k`). -/
theorem sin_le_left {p k : ℝ} (hp2 : p ≤ π / 2) (hk : k ∈ Icc (-π - p) p) :
    sin k ≤ sin p := by
  rcases le_total (-(π / 2)) k with h | h
  · exact sin_le_sin_of_le_of_le_pi_div_two h hp2 hk.2
  · rw [← sin_neg_pi_sub k]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) hp2 (by linarith [hk.1])

/-- `sin k ≤ sin p` on `[π − p, π]` for `p ≤ π/2` (`sin k = sin (π − k)`). -/
theorem sin_le_right {p k : ℝ} (hp2 : p ≤ π / 2) (hk : k ∈ Icc (π - p) π) : sin k ≤ sin p := by
  rw [← sin_pi_sub k]
  exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [hk.2, pi_pos]) hp2 (by linarith [hk.1])

/-- `sin q ≤ sin k` on `[q, π − q]`. -/
theorem le_sin_mid {q k : ℝ} (hq1 : -(π / 2) ≤ q) (hk : k ∈ Icc q (π - q)) : sin q ≤ sin k := by
  rcases le_total k (π / 2) with h | h
  · exact sin_le_sin_of_le_of_le_pi_div_two hq1 h hk.1
  · rw [← sin_pi_sub k]
    exact sin_le_sin_of_le_of_le_pi_div_two hq1 (by linarith) (by linarith [hk.2])

/-- `g ≥ t δ > 0` where `sin k ≤ v − δ`. -/
theorem g_pos {t v δ k : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hk : sin k ≤ v - δ) : 0 < t * v - t * sin k := by
  nlinarith [mul_pos ht hδ, mul_le_mul_of_nonneg_left hk ht.le]

/-- **Shared piece** `[−π − p, p]` for `v − δ ≤ 0` (Band low, Cap low): `4/(tδ) − 2/(t(1 + v))`. -/
theorem posLow (hI : IbpFacts) (hV : VarFacts) {t v δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (h1 : -1 ≤ v - δ)
    (h2 : v - δ ≤ 0) :
    ‖J t v (-π - arcsin (v - δ)) (arcsin (v - δ))‖ ≤ 4 / (t * δ) - 2 / (t * (1 + v)) := by
  have hs := sin_arcsin h1 (by linarith)
  have hp1 := neg_pi_div_two_le_arcsin (v - δ)
  have hp2 := arcsin_le_pi_div_two (v - δ)
  have hp0 := arcsin_nonpos.mpr h2
  have h := posTurn hI hV (v := v) (a := -π - arcsin (v - δ)) ht (by linarith) (by linarith) hp1 hp2
    (fun k hk => g_pos ht hδ ((sin_le_left hp2 hk).trans hs.le))
  rw [sin_neg_pi_sub, hs] at h
  refine h.trans (le_of_eq ?_); ring

/-- **Shared piece** `[−π, p]` for `0 ≤ v − δ ≤ 1` (Band high, Cap high): `2/(tv) + 2/(tδ) − 2/(t(1 + v))`. -/
theorem posHighL (hI : IbpFacts) (hV : VarFacts) {t v δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (h1 : 0 ≤ v - δ)
    (h2 : v - δ ≤ 1) :
    ‖J t v (-π) (arcsin (v - δ))‖ ≤ 2 / (t * v) + 2 / (t * δ) - 2 / (t * (1 + v)) := by
  have hs := sin_arcsin (by linarith) h2
  have hp1 := neg_pi_div_two_le_arcsin (v - δ)
  have hp2 := arcsin_le_pi_div_two (v - δ)
  have hp0 := arcsin_nonneg.mpr h1
  have h := posTurn hI hV (v := v) (a := -π) ht (by linarith [pi_pos]) (by linarith [pi_pos]) hp1 hp2
    (fun k hk => g_pos ht hδ ((sin_le_left hp2 ⟨by linarith [hk.1], hk.2⟩).trans hs.le))
  rw [g_neg_pi, hs] at h
  refine h.trans (le_of_eq ?_); ring

/-- **Shared piece** `[π − p, π]` for `0 ≤ v − δ ≤ 1` (Band high, Cap high): `2/(tδ)`. -/
theorem posHighR (hI : IbpFacts) (hV : VarFacts) {t v δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (h1 : 0 ≤ v - δ)
    (h2 : v - δ ≤ 1) :
    ‖J t v (π - arcsin (v - δ)) π‖ ≤ 2 / (t * δ) := by
  have hs := sin_arcsin (by linarith) h2
  have hp2 := arcsin_le_pi_div_two (v - δ)
  have hp0 := arcsin_nonneg.mpr h1
  have h := posBr2 hI hV (v := v) (a := π - arcsin (v - δ)) (b := π) ht (by linarith) (by linarith)
    (by linarith [pi_pos])
    (fun k hk => g_pos ht hδ ((sin_le_right hp2 hk).trans hs.le))
  rw [sin_pi_sub, hs] at h
  refine h.trans (le_of_eq ?_); ring

/-- **Shared piece** `[q, π − q]` for `0 ≤ v + δ ≤ 1` (Band low, Band high): `4/(tδ) − 2/(t(1 − v))`. -/
theorem negPiece (hI : IbpFacts) (hV : VarFacts) {t v δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (h1 : 0 ≤ v + δ)
    (h2 : v + δ ≤ 1) :
    ‖J t v (arcsin (v + δ)) (π - arcsin (v + δ))‖ ≤ 4 / (t * δ) - 2 / (t * (1 - v)) := by
  have hs := sin_arcsin (by linarith) h2
  have hq1 := neg_pi_div_two_le_arcsin (v + δ)
  have hq2 := arcsin_le_pi_div_two (v + δ)
  have h := negTurn hI hV (v := v) (b := π - arcsin (v + δ)) ht hq1 hq2 (by linarith) (by linarith)
    (fun k hk => by
      have := (hs.symm.le.trans (le_sin_mid hq1 hk))
      nlinarith [mul_pos ht hδ, mul_le_mul_of_nonneg_left this ht.le])
  rw [sin_pi_sub, hs] at h
  refine h.trans (le_of_eq ?_); ring

theorem split3 (t v a b c d : ℝ) : J t v a d = J t v a b + J t v b c + J t v c d := by
  rw [J_add, J_add]

theorem split5 (t v a b c d e f : ℝ) :
    J t v a f = J t v a b + J t v b c + J t v c d + J t v d e + J t v e f := by
  rw [J_add, J_add, J_add, J_add]

theorem norm5 (x₁ x₂ x₃ x₄ x₅ : ℂ) : ‖x₁ + x₂ + x₃ + x₄ + x₅‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ := by
  linarith [norm_add_le (x₁ + x₂ + x₃ + x₄) x₅, norm_add_le (x₁ + x₂ + x₃) x₄, norm_add_le (x₁ + x₂) x₃,
    norm_add_le x₁ x₂]

theorem norm3 (x₁ x₂ x₃ : ℂ) : ‖x₁ + x₂ + x₃‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ := by
  linarith [norm_add_le (x₁ + x₂) x₃, norm_add_le x₁ x₂]

theorem recip_band {t v : ℝ} (ht : 0 < t) (h0 : 0 ≤ v) (h1 : v < 1) :
    4 / (t * (1 - v ^ 2)) = 2 / (t * (1 + v)) + 2 / (t * (1 - v)) := by
  have : 0 < 1 - v := by linarith
  have : 0 < 1 + v := by linarith
  have : 0 < 1 - v ^ 2 := by nlinarith
  field_simp
  ring

theorem recip_end {t v : ℝ} (ht : 0 < t) (h0 : 0 < v) :
    2 / (t * v) - 2 / (t * (1 + v)) = 2 / (t * v * (v + 1)) := by
  have : 0 < 1 + v := by linarith
  have : 0 < v + 1 := by linarith
  field_simp
  ring

/-- **P-band**, low velocities: bands `[−π, −π − p]`, `[p, q]`, `[π − q, π]` by length, `[−π − p, p]` and
`[q, π − q]` by P-ibp and P-var. -/
theorem bandLow_of (hI : IbpFacts) (hV : VarFacts) : BandLowFacts := by
  intro t v δ ht hv hδ hvδ hvd
  have hp1 := neg_pi_div_two_le_arcsin (v - δ)
  have hp0 := arcsin_nonpos.mpr (show v - δ ≤ 0 by linarith)
  have hq2 := arcsin_le_pi_div_two (v + δ)
  have hq0 := arcsin_nonneg.mpr (show 0 ≤ v + δ by linarith)
  have hpq := arcsin_le_arcsin (show v - δ ≤ v + δ by linarith)
  rw [kernel_eq, split5 t v (-π) (-π - arcsin (v - δ)) (arcsin (v - δ)) (arcsin (v + δ)) (π - arcsin (v + δ)) π]
  refine (norm5 _ _ _ _ _).trans ?_
  have b1 := J_len t v (-π) (-π - arcsin (v - δ)) (by linarith)
  have b2 := posLow hI hV ht hδ (show -1 ≤ v - δ by linarith) (by linarith)
  have b3 := J_len t v (arcsin (v - δ)) (arcsin (v + δ)) hpq
  have b4 := negPiece hI hV ht hδ (show 0 ≤ v + δ by linarith) hvd.le
  have b5 := J_len t v (π - arcsin (v + δ)) π (by linarith)
  have e1 := recip_band ht hv (show v < 1 by linarith)
  have e2 : 8 / (t * δ) = 4 / (t * δ) + 4 / (t * δ) := by ring
  linarith

/-- **P-band**, high velocities: bands `[p, q]`, `[π − q, π − p]` by length, `[−π, p]`, `[q, π − q]` and
`[π − p, π]` by P-ibp and P-var. -/
theorem bandHigh_of (hI : IbpFacts) (hV : VarFacts) : BandHighFacts := by
  intro t v δ ht hδ hδv hvd
  have hp0 := arcsin_nonneg.mpr (show 0 ≤ v - δ by linarith)
  have hp2 := arcsin_le_pi_div_two (v - δ)
  have hq2 := arcsin_le_pi_div_two (v + δ)
  have hpq := arcsin_le_arcsin (show v - δ ≤ v + δ by linarith)
  rw [kernel_eq, split5 t v (-π) (arcsin (v - δ)) (arcsin (v + δ)) (π - arcsin (v + δ)) (π - arcsin (v - δ)) π]
  refine (norm5 _ _ _ _ _).trans ?_
  have b1 := posHighL hI hV ht hδ (show 0 ≤ v - δ by linarith) (by linarith)
  have b2 := J_len t v (arcsin (v - δ)) (arcsin (v + δ)) hpq
  have b3 := negPiece hI hV ht hδ (show 0 ≤ v + δ by linarith) hvd.le
  have b4 := J_len t v (π - arcsin (v + δ)) (π - arcsin (v - δ)) (by linarith)
  have b5 := posHighR hI hV ht hδ (show 0 ≤ v - δ by linarith) (by linarith)
  have e1 := recip_band ht (show 0 ≤ v by linarith) (show v < 1 by linarith)
  have e2 : 8 / (t * δ) = 2 / (t * δ) + 4 / (t * δ) + 2 / (t * δ) := by ring
  linarith

/-- **P-cap**, low velocities: the cap `[−π, −π − p] ∪ [p, π]` by length, `[−π − p, p]` by P-ibp and P-var. -/
theorem capLow_of (hI : IbpFacts) (hV : VarFacts) : CapLowFacts := by
  intro t v δ ht hv hδ hvδ hvd
  have hp0 := arcsin_nonpos.mpr (show v - δ ≤ 0 by linarith)
  have hp2 := arcsin_le_pi_div_two (v - δ)
  rw [kernel_eq, split3 t v (-π) (-π - arcsin (v - δ)) (arcsin (v - δ)) π]
  refine (norm3 _ _ _).trans ?_
  have b1 := J_len t v (-π) (-π - arcsin (v - δ)) (by linarith)
  have b2 := posLow hI hV ht hδ hvd.le (by linarith)
  have b3 := J_len t v (arcsin (v - δ)) π (by linarith [pi_pos])
  linarith

/-- **P-cap**, high velocities: the cap `[p, π − p]` by length, `[−π, p]` and `[π − p, π]` by P-ibp and P-var. -/
theorem capHigh_of (hI : IbpFacts) (hV : VarFacts) : CapHighFacts := by
  intro t v δ ht hδ hδv hvd
  have hp2 := arcsin_le_pi_div_two (v - δ)
  rw [kernel_eq, split3 t v (-π) (arcsin (v - δ)) (π - arcsin (v - δ)) π]
  refine (norm3 _ _ _).trans ?_
  have b1 := posHighL hI hV ht hδ (show 0 ≤ v - δ by linarith) hvd.le
  have b2 := J_len t v (arcsin (v - δ)) (π - arcsin (v - δ)) (by linarith)
  have b3 := posHighR hI hV ht hδ (show 0 ≤ v - δ by linarith) hvd.le
  have e1 := recip_end ht (show 0 < v by linarith)
  have e2 : 4 / (t * δ) = 2 / (t * δ) + 2 / (t * δ) := by ring
  linarith

/-- **P-cap**, whole interval (`v > 1`): P-ibp on `[−π, π]`, the variation split at `−π/2` and `π/2` (P-var,
branches 2, 1, 2). -/
theorem whole_of (hI : IbpFacts) (hV : VarFacts) : WholeFacts := by
  intro t v ht hv
  have hp := pi_pos
  have hpos : ∀ k, 0 < t * v - t * sin k := fun k =>
    g_pos (δ := v - 1) ht (by linarith) (by linarith [sin_le_one k])
  have hne : ∀ k ∈ Icc (-π) π, t * v - t * sin k ≠ 0 := fun k _ => (hpos k).ne'
  have h1 := ibp hI (by linarith) hne
  rw [V_add hne (show -π ≤ -(π / 2) by linarith) (by linarith),
    V_add (fun k hk => hne k ⟨by linarith [hk.1], hk.2⟩) (show -(π / 2) ≤ π / 2 by linarith) (by linarith)] at h1
  have e1 := (hV t (t * v) (-π) (-(π / 2)) ht (by linarith) (fun k _ => (hpos k).ne')).2
    (Or.inr (Icc_subset_Icc (by linarith) le_rfl))
  have e2 := (hV t (t * v) (-(π / 2)) (π / 2) ht (by linarith) (fun k _ => (hpos k).ne')).1 subset_rfl
  have e3 := (hV t (t * v) (π / 2) π ht (by linarith) (fun k _ => (hpos k).ne')).2
    (Or.inl (Icc_subset_Icc le_rfl (by linarith)))
  unfold V at h1
  rw [e1, e2, e3, g_neg_pi, g_pi, g_neg_half, g_half, div_neg, abs_of_pos (by nlinarith)] at h1
  rw [kernel_eq]
  have e4 := recip_end ht (show 0 < v by linarith)
  have e6 : 1 / (t * (1 - v)) = -(1 / (t * (v - 1))) := by
    rw [show t * (1 - v) = -(t * (v - 1)) by ring, div_neg]
  have e7 : 2 / (t * (v - 1)) = 1 / (t * (v - 1)) + 1 / (t * (v - 1)) := by ring
  have e8 : 2 / (t * v) = 1 / (t * v) + 1 / (t * v) := by ring
  have e9 : 2 / (t * (1 + v)) = 1 / (t * (1 + v)) + 1 / (t * (1 + v)) := by ring
  linarith

end OscInt.LatticeCubeRootAux.Pieces
