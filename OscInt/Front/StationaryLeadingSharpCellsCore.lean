/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/
import Blueprint.StationaryLeadingSharp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Batch SPL-N, parts N3 and N6: `√π` enclosure and generic cell soundness (helper of agent C)

Route `docs/proof-SPLN.md`, section 2, **N3** and **N6**. The Taylor centre `splnCentre s x` is split as
`A(x) + s D(x)` with `Re A = x + Σ (I_{4k+1} − I_{4k+3})`, `Im A = −Σ (I_{4k} − I_{4k+2})`,
`D = (−x² + i x²)/4`; over `ℚ` the real and imaginary parts at `s ∈ {s₀, s₁}` are computable (`splnC_re`,
`splnC_im`). A Boolean checker `splnC_cellOK` over `ℚ` (endpoint budgets `q − (b−a)²/(4a) − 2 I_32(x)`, squared
norms at `s₀, s₁`) is proved sound (`splnC_cell`), with coverage by a chain checker (`splnC_chain_sound`).
-/

namespace OscInt.SPLNAux

open OscInt.Statements OscInt.Blueprint.SPLN

/-! ### Rational data -/

/-- `I_j(x)` over `ℚ`. -/
def splnC_Iq (j : ℕ) (x : ℚ) : ℚ :=
  x ^ (2 * j + 3) / (2 ^ j * (j.factorial : ℚ) * ((2 * j + 1) * (2 * j + 2) * (2 * j + 3)))

/-- `Σ_{k<n} (I_{4k+1} − I_{4k+3})` over `ℚ`. -/
def splnC_sumR (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => splnC_sumR x k + (splnC_Iq (4 * k + 1) x - splnC_Iq (4 * k + 3) x)

/-- `Σ_{k<n} (I_{4k} − I_{4k+2})` over `ℚ`. -/
def splnC_sumJ (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => splnC_sumJ x k + (splnC_Iq (4 * k) x - splnC_Iq (4 * k + 2) x)

/-- Real part of the centre at `s`. -/
def splnC_re (s x : ℚ) : ℚ := x - s * x ^ 2 / 4 + splnC_sumR x 8

/-- Imaginary part of the centre at `s`. -/
def splnC_im (s x : ℚ) : ℚ := s * x ^ 2 / 4 - splnC_sumJ x 8

/-- `s₀ = 1772453850905516/10¹⁵`. -/
def splnC_s0 : ℚ := 1772453850905516 / 10 ^ 15

/-- `s₁ = s₀ + 10⁻¹⁵`. -/
def splnC_s1 : ℚ := splnC_s0 + 1 / 10 ^ 15

theorem splnC_Iq_cast (j : ℕ) (x : ℚ) : ((splnC_Iq j x : ℚ) : ℝ) = splnI j x := by
  simp only [splnC_Iq, splnI]
  push_cast
  ring

theorem splnC_sumR_cast (x : ℚ) (n : ℕ) :
    ((splnC_sumR x n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, (splnI (4 * k + 1) x - splnI (4 * k + 3) x) := by
  induction n with
  | zero => simp [splnC_sumR]
  | succ n ih =>
    rw [splnC_sumR, Finset.sum_range_succ, ← ih, Rat.cast_add, Rat.cast_sub, splnC_Iq_cast, splnC_Iq_cast]

theorem splnC_sumJ_cast (x : ℚ) (n : ℕ) :
    ((splnC_sumJ x n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, (splnI (4 * k) x - splnI (4 * k + 2) x) := by
  induction n with
  | zero => simp [splnC_sumJ]
  | succ n ih =>
    rw [splnC_sumJ, Finset.sum_range_succ, ← ih, Rat.cast_add, Rat.cast_sub, splnC_Iq_cast, splnC_Iq_cast]

/-! ### The centre as `A + s D` -/

/-- Sum over `range (4n)` in blocks of four. -/
theorem splnC_sum4 (f : ℕ → ℂ) (n : ℕ) : ∑ j ∈ Finset.range (4 * n), f j =
    ∑ k ∈ Finset.range n, (f (4 * k) + f (4 * k + 1) + f (4 * k + 2) + f (4 * k + 3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [add_assoc]

/-- The constant part `A(x)` of the centre. -/
noncomputable def splnC_A (x : ℝ) : ℂ :=
  ⟨x + ∑ k ∈ Finset.range 8, (splnI (4 * k + 1) x - splnI (4 * k + 3) x),
    -∑ k ∈ Finset.range 8, (splnI (4 * k) x - splnI (4 * k + 2) x)⟩

/-- The `s`-coefficient `D(x)` of the centre. -/
noncomputable def splnC_D (x : ℝ) : ℂ := ⟨-(x ^ 2 / 4), x ^ 2 / 4⟩

theorem splnC_sum32 (x : ℝ) : ∑ j ∈ Finset.range 32, Complex.I ^ j * (splnI j x : ℂ) =
    ((∑ k ∈ Finset.range 8, (splnI (4 * k) x - splnI (4 * k + 2) x) : ℝ) : ℂ) +
      Complex.I * ((∑ k ∈ Finset.range 8, (splnI (4 * k + 1) x - splnI (4 * k + 3) x) : ℝ) : ℂ) := by
  rw [show 32 = 4 * 8 from rfl, splnC_sum4, Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul, pow_one, Complex.I_sq,
    Complex.I_pow_three]
  push_cast
  ring

theorem splnC_centre_AD (s x : ℝ) : splnCentre s x = splnC_A x + (s : ℂ) * splnC_D x := by
  unfold splnCentre
  rw [splnC_sum32]
  apply Complex.ext <;> simp [splnC_A, splnC_D, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem splnC_AD_re (s x : ℚ) : (splnC_A x + (((s : ℝ)) : ℂ) * splnC_D x).re = (splnC_re s x : ℝ) := by
  simp [splnC_A, splnC_D, splnC_re, splnC_sumR_cast]
  ring

theorem splnC_AD_im (s x : ℚ) : (splnC_A x + (((s : ℝ)) : ℂ) * splnC_D x).im = (splnC_im s x : ℝ) := by
  simp [splnC_A, splnC_D, splnC_im, splnC_sumJ_cast]
  ring

/-! ### Norm lemmas -/

theorem splnC_norm_le (z : ℂ) (B : ℝ) (hB : 0 ≤ B) (h : z.re ^ 2 + z.im ^ 2 ≤ B ^ 2) : ‖z‖ ≤ B := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg z) hB two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

theorem splnC_lt_norm (z : ℂ) (T : ℝ) (h : T ^ 2 < z.re ^ 2 + z.im ^ 2) : T < ‖z‖ := by
  by_contra hn
  replace hn := not_lt.mp hn
  have h2 := pow_le_pow_left₀ (norm_nonneg z) hn 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  nlinarith

/-- Convexity of `s ↦ ‖A + sD‖`. -/
theorem splnC_affine_le (A D : ℂ) (s₀ s₁ s B : ℝ) (h0s : s₀ ≤ s) (hs1 : s ≤ s₁)
    (h0 : ‖A + (s₀ : ℂ) * D‖ ≤ B) (h1 : ‖A + (s₁ : ℂ) * D‖ ≤ B) : ‖A + (s : ℂ) * D‖ ≤ B := by
  rcases eq_or_lt_of_le (h0s.trans hs1) with heq | hlt
  · have : s = s₀ := le_antisymm (heq ▸ hs1) h0s
    rw [this]; exact h0
  obtain ⟨t, ht0, ht1, hst⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ s = (1 - t) * s₀ + t * s₁ := by
    refine ⟨(s - s₀) / (s₁ - s₀), div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith), ?_⟩
    field_simp
    ring
  have he : A + (s : ℂ) * D = ((1 - t : ℝ) : ℂ) * (A + (s₀ : ℂ) * D) + ((t : ℝ) : ℂ) * (A + (s₁ : ℂ) * D) := by
    rw [hst]; push_cast; ring
  rw [he]
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * (A + (s₀ : ℂ) * D)‖ + ‖((t : ℝ) : ℂ) * (A + (s₁ : ℂ) * D)‖ := norm_add_le _ _
    _ = (1 - t) * ‖A + (s₀ : ℂ) * D‖ + t * ‖A + (s₁ : ℂ) * D‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg ht0]
    _ ≤ (1 - t) * B + t * B := by
        have : 0 ≤ 1 - t := by linarith
        gcongr
    _ = B := by ring

/-! ### N3 -/

/-- **N3** `s₀ ≤ √π ≤ s₁`. -/
theorem splnC_sqrtPi : ((splnC_s0 : ℚ) : ℝ) ≤ Real.sqrt Real.pi ∧ Real.sqrt Real.pi ≤ ((splnC_s1 : ℚ) : ℝ) := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  constructor
  · rw [Real.le_sqrt (by norm_num [splnC_s0]) Real.pi_pos.le]
    norm_num [splnC_s0] at hp1 ⊢
    linarith
  · rw [Real.sqrt_le_left (by norm_num [splnC_s1, splnC_s0])]
    norm_num [splnC_s1, splnC_s0] at hp2 ⊢
    linarith

/-! ### N6: the checker and its soundness -/

/-- The endpoint test: `B ≥ 0` and `‖P(x, sᵢ)‖² ≤ B²` for `i = 0, 1`. -/
def splnC_endOK (B x : ℚ) : Bool :=
  decide (0 ≤ B) && decide (splnC_re splnC_s0 x ^ 2 + splnC_im splnC_s0 x ^ 2 ≤ B ^ 2) &&
    decide (splnC_re splnC_s1 x ^ 2 + splnC_im splnC_s1 x ^ 2 ≤ B ^ 2)

/-- The interpolation pad `(b − a)²/(4a)` (that is `M (b − a)²/8` with `M = 2/a`). -/
def splnC_pad (a b : ℚ) : ℚ := (b - a) ^ 2 / (4 * a)

/-- The cell test for `[a, b] ⊆ [1/2, 4]` and the target `q`. -/
def splnC_cellOK (q : ℚ) (c : ℚ × ℚ) : Bool :=
  decide (1 / 2 ≤ c.1) && decide (c.1 ≤ c.2) && decide (c.2 ≤ 4) &&
    splnC_endOK (q - splnC_pad c.1 c.2 - 2 * splnC_Iq 32 c.1) c.1 &&
    splnC_endOK (q - splnC_pad c.1 c.2 - 2 * splnC_Iq 32 c.2) c.2

/-- The coverage test: the cells, in order, cover `[c, d]`. -/
def splnC_chain : ℚ → List (ℚ × ℚ) → ℚ → Bool
  | _, [], _ => false
  | c, p :: L, d => decide (p.1 ≤ c) && (decide (d ≤ p.2) || splnC_chain p.2 L d)

theorem splnC_chain_sound (L : List (ℚ × ℚ)) : ∀ c d : ℚ, splnC_chain c L d = true →
    ∀ x : ℝ, (c : ℝ) ≤ x → x ≤ d → ∃ p ∈ L, (p.1 : ℝ) ≤ x ∧ x ≤ p.2 := by
  induction L with
  | nil => intro c d h; simp [splnC_chain] at h
  | cons p L ih =>
    intro c d h x hcx hxd
    simp only [splnC_chain, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hp, hor⟩ := h
    have hp' : (p.1 : ℝ) ≤ c := by exact_mod_cast hp
    by_cases hx : x ≤ p.2
    · exact ⟨p, by simp, hp'.trans hcx, hx⟩
    · replace hx := not_le.mp hx
      rcases hor with hd | hr
      · have : (d : ℝ) ≤ p.2 := by exact_mod_cast hd
        linarith
      · obtain ⟨p', hp'L, h1, h2⟩ := ih p.2 d hr x hx.le hxd
        exact ⟨p', by simp [hp'L], h1, h2⟩

/-- Endpoint soundness: N1 + N2 (Taylor facts) and N3 turn `splnC_endOK B x` into `‖κ₊(x)‖ ≤ B + 2 I_32(x)`. -/
theorem splnC_endOK_sound (hT : SplnTaylorFacts) (B x : ℚ) (hx0 : 0 ≤ x) (hx4 : x ≤ 4)
    (h : splnC_endOK B x = true) : ‖splKernelPos x‖ ≤ (B : ℝ) + 2 * splnI 32 x := by
  simp only [splnC_endOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hB, h0⟩, h1⟩ := h
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hn : ∀ s : ℚ, splnC_re s x ^ 2 + splnC_im s x ^ 2 ≤ B ^ 2 →
      ‖splnC_A x + (((s : ℝ)) : ℂ) * splnC_D x‖ ≤ B := by
    intro s hs
    refine splnC_norm_le _ _ hB' ?_
    rw [splnC_AD_re, splnC_AD_im]
    exact_mod_cast hs
  have hc : ‖splnCentre (Real.sqrt Real.pi) x‖ ≤ B := by
    rw [splnC_centre_AD]
    exact splnC_affine_le _ _ _ _ _ _ splnC_sqrtPi.1 splnC_sqrtPi.2 (hn _ h0) (hn _ h1)
  have hTx := hT x (by exact_mod_cast hx0) (by exact_mod_cast hx4)
  calc ‖splKernelPos x‖ = ‖splnCentre (Real.sqrt Real.pi) x + (splKernelPos x - splnCentre (Real.sqrt Real.pi) x)‖ := by
        congr 1; ring
    _ ≤ ‖splnCentre (Real.sqrt Real.pi) x‖ + ‖splKernelPos x - splnCentre (Real.sqrt Real.pi) x‖ := norm_add_le _ _
    _ ≤ B + 2 * splnI 32 x := add_le_add hc hTx

/-- **N6** Generic cell soundness: a passing cell `[a, b]` gives `‖κ₊‖ ≤ q` on `[a, b]` (interpolation with
`M = 2/a` from N4). -/
theorem splnC_cell (hT : SplnTaylorFacts) (hS : SplnSecondFacts) (hI : SplnInterpFacts) (q : ℚ)
    (c : ℚ × ℚ) (hc : splnC_cellOK q c = true) (x : ℝ) (hxa : (c.1 : ℝ) ≤ x) (hxb : x ≤ c.2) :
    ‖splKernelPos x‖ ≤ q := by
  simp only [splnC_cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ha, hab⟩, hb⟩, hea⟩, heb⟩ := hc
  obtain ⟨κ₁, κ₂, d1, d2, hb2⟩ := hS
  have ha' : (1 / 2 : ℝ) ≤ c.1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr ha
    rwa [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  have hab' : (c.1 : ℝ) ≤ c.2 := by exact_mod_cast hab
  have hapos : (0 : ℝ) < c.1 := by linarith
  have hEa := splnC_endOK_sound hT _ c.1 (by linarith) (hab.trans hb) hea
  have hEb := splnC_endOK_sound hT _ c.2 (by linarith) hb heb
  push_cast [splnC_Iq_cast] at hEa hEb
  have hpad : ((splnC_pad c.1 c.2 : ℚ) : ℝ) = 2 / (c.1 : ℝ) * ((c.2 : ℝ) - c.1) ^ 2 / 8 := by
    simp only [splnC_pad]
    push_cast
    field_simp
    ring
  have key := hI splKernelPos κ₁ κ₂ c.1 c.2 (2 / c.1) hab'
    (fun t ht => d1 t (by linarith [ht.1])) (fun t ht => d2 t (by linarith [ht.1]))
    (fun t ht => (hb2 t (by linarith [ht.1])).trans (div_le_div_of_nonneg_left (by norm_num) hapos ht.1))
    x ⟨hxa, hxb⟩
  rw [← hpad] at key
  have hm : max ‖splKernelPos c.1‖ ‖splKernelPos c.2‖ ≤ q - (splnC_pad c.1 c.2 : ℝ) :=
    max_le (by linarith) (by linarith)
  linarith

/-! ### N9: the lower point -/

/-- `x₀ = 8123/5000`. -/
def splnC_x0 : ℚ := 8123 / 5000

/-- The midpoint `s_m = (s₀ + s₁)/2`. -/
def splnC_sm : ℚ := (splnC_s0 + splnC_s1) / 2

/-- The threshold `q_low + 2 I_32(x₀) + (s₁ − s₀) x₀²/4`. -/
def splnC_T : ℚ :=
  72197399 / 100000000 + 2 * splnC_Iq 32 splnC_x0 + (splnC_s1 - splnC_s0) * splnC_x0 ^ 2 / 4

/-- The lower-point test `T² < ‖P(x₀, s_m)‖²`. -/
def splnC_lowOK : Bool :=
  decide (splnC_T ^ 2 < splnC_re splnC_sm splnC_x0 ^ 2 + splnC_im splnC_sm splnC_x0 ^ 2)

/-- `‖centre(√π, x) − centre(s_m, x)‖ ≤ (s₁ − s₀) x²/4`. -/
theorem splnC_centre_mid (x : ℚ) :
    ‖splnCentre (Real.sqrt Real.pi) x - (splnC_A x + (((splnC_sm : ℚ) : ℝ) : ℂ) * splnC_D x)‖ ≤
      ((splnC_s1 : ℚ) - (splnC_s0 : ℝ)) * (x : ℝ) ^ 2 / 4 := by
  rw [splnC_centre_AD]
  have he : splnC_A x + ((Real.sqrt Real.pi : ℝ) : ℂ) * splnC_D x -
      (splnC_A x + (((splnC_sm : ℚ) : ℝ) : ℂ) * splnC_D x) =
      ((Real.sqrt Real.pi - (splnC_sm : ℝ) : ℝ) : ℂ) * splnC_D x := by
    push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hD : ‖splnC_D x‖ ≤ (x : ℝ) ^ 2 / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [splnC_D, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    ring
  have hs : |Real.sqrt Real.pi - (splnC_sm : ℝ)| ≤ (((splnC_s1 : ℚ) : ℝ) - splnC_s0) / 2 := by
    have h := splnC_sqrtPi
    rw [abs_le]
    simp only [splnC_sm]
    push_cast
    constructor <;> linarith [h.1, h.2]
  calc |Real.sqrt Real.pi - (splnC_sm : ℝ)| * ‖splnC_D x‖
      ≤ ((((splnC_s1 : ℚ) : ℝ) - splnC_s0) / 2) * ((x : ℝ) ^ 2 / 2) :=
        mul_le_mul hs hD (norm_nonneg _) (by linarith [abs_nonneg (Real.sqrt Real.pi - (splnC_sm : ℝ))])
    _ = _ := by ring

/-- **N9** soundness: the lower-point test gives `‖κ₊(8123/5000)‖ > 72197399/10⁸`. -/
theorem splnC_lower_of (hT : SplnTaylorFacts) (h : splnC_lowOK = true) :
    (72197399 / 100000000 : ℝ) < ‖splKernelPos (8123 / 5000)‖ := by
  simp only [splnC_lowOK, decide_eq_true_eq] at h
  have hx : ((splnC_x0 : ℚ) : ℝ) = 8123 / 5000 := by norm_num [splnC_x0]
  rw [← hx]
  have hTx := hT (splnC_x0 : ℝ) (by rw [hx]; norm_num) (by rw [hx]; norm_num)
  have hlt : (splnC_T : ℝ) < ‖splnC_A splnC_x0 + (((splnC_sm : ℚ) : ℝ) : ℂ) * splnC_D splnC_x0‖ := by
    apply splnC_lt_norm
    rw [splnC_AD_re, splnC_AD_im]
    exact_mod_cast h
  have hTd : (splnC_T : ℝ) = 72197399 / 100000000 + 2 * splnI 32 (splnC_x0 : ℝ) +
      ((splnC_s1 : ℚ) - (splnC_s0 : ℝ)) * (splnC_x0 : ℝ) ^ 2 / 4 := by
    simp only [splnC_T]
    push_cast [splnC_Iq_cast]
    ring
  have hm := splnC_centre_mid splnC_x0
  have h1 := norm_sub_norm_le (splnC_A splnC_x0 + (((splnC_sm : ℚ) : ℝ) : ℂ) * splnC_D splnC_x0)
    (splnCentre (Real.sqrt Real.pi) splnC_x0)
  have h2 := norm_sub_norm_le (splnCentre (Real.sqrt Real.pi) splnC_x0) (splKernelPos splnC_x0)
  rw [norm_sub_rev] at h1 h2
  linarith

end OscInt.SPLNAux
