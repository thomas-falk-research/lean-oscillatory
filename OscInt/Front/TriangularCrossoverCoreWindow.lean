/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriangularDecayCore
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Batch A5U, part A12a: the core window estimate in the chart (`A5CoreWindowFacts`)

Route `stmts/proof-A5U-draft.md`, sections 3–4. Order of choices: the data of A9 at `a₀` (`q₀, a, b, μ, ν, D, L`,
the curves `ys q`); `η` from A6 with `c_B = 24`, `K = 10`, `d_min = ν/2`, `d_max = max(ν/2, L + 64)`; `δ` from A6
with `max L 0 + 256`; `C₇` from A7(iii); the shrunken half-width `a' = min a δ`; `P` from A4 and `C₆` from
`OscInt.K2.coreEstimateM` (order 6, `ν/2`, `D + 16`); then `q₁ = min q₀ (μ δ⁴/4)` and `r = min (min 1 (ν/128)) (δ⁴/8)`.
All of this precedes `α`, `q`, `t`, `p` and the amplitude.

For `|α − a₀| ≤ r`, `|q| ≤ q₁`: `Q_{α,q} = Q_{a₀,q} + (α − a₀)(cos 2u − 1)` (A8) and A10 keep `CoreHypsM 6` with `ν/2`
and `D + 16` (`a5uX_pert`). If `t ε³ ≤ 1` the order-6 estimate and A7(ii) give `C₆ M W`. Otherwise A11 bounds the jets
at `0` (`|g″(0)| ≤ δ⁴`, `|g⁗(0)| ≥ 24ε − 10|g″(0)|`), A5 gives the Taylor forms, A6 the pointwise three-threshold
alternative on `(−a', a')`, A4 the estimate and A7(iii) the weight.
-/

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open scoped ContDiff

/-- `CoreHypsM` is monotone: shrink `a` and `ν`, enlarge `D`. -/
theorem a5uX_coreHypsM_mono {m : ℕ} {a a' b μ ν ν' D D' : ℝ} {Q : ℝ × ℝ → ℝ} {ys : ℝ → ℝ}
    (h : CoreHypsM m a b μ ν D Q ys) (haa : a' ≤ a) (hν : ν' ≤ ν) (hD : D ≤ D') :
    CoreHypsM m a' b μ ν' D' Q ys := by
  obtain ⟨hQ, hys, hcrit, hlow, hDb, hνm⟩ := h
  have hsub : Icc (-a') a' ⊆ Icc (-a) a := Icc_subset_Icc (by linarith) haa
  exact ⟨hQ, hys.mono (Ioo_subset_Ioo (by linarith) (by linarith)), fun x hx => hcrit x (hsub hx),
    fun x hx y hy => hlow x (hsub hx) y hy, fun i hi x hx y hy => (hDb i hi x (hsub hx) y hy).trans hD,
    fun x hx => hν.trans (hνm x (hsub hx))⟩

/-- `Q_{α,q} = Q_{a₀,q} + (α − a₀)(cos 2u − 1)` (A8). -/
theorem a5uX_Q_split (h8 : A5FixedChartFacts) (a₀ α q : ℝ) :
    a5Q a₀ α q = fun k => a5Q a₀ a₀ q k + (α - a₀) * (Real.cos (2 * k.1) - 1) := by
  funext k
  simp only [a5Q]
  rw [h8, h8]
  ring

/-- The reduced function of the perturbed phase is `g_{α,q}`. -/
theorem a5uX_red_split (h8 : A5FixedChartFacts) (a₀ α q : ℝ) (ys : ℝ → ℝ) :
    (fun x => a5Q a₀ a₀ q (x, ys x) + (α - a₀) * (Real.cos (2 * x) - 1)) = a5Red a₀ α q ys := by
  funext x
  simp only [a5Red, a5Q]
  rw [h8, h8]
  ring

/-- The reduced function is even when the curve is. -/
theorem a5uX_red_even (h8 : A5FixedChartFacts) {a₀ α q a : ℝ} {ys : ℝ → ℝ}
    (hev : ∀ x ∈ Icc (-a) a, ys (-x) = ys x) : ∀ x ∈ Ioo (-a) a, a5Red a₀ α q ys (-x) = a5Red a₀ α q ys x := by
  intro x hx
  simp only [a5Red, a5Q]
  rw [hev x (Ioo_subset_Icc_self hx), h8, h8]
  simp only [Real.cos_neg, mul_neg]

/-- The perturbed data: `CoreHypsM 6` with `ν/2`, `D + 16`, and the jet bounds of `g_{α,q}` on `[−a, a]`. -/
theorem a5uX_pert (h8 : A5FixedChartFacts) (h10 : PerturbLongitudinalFacts) {a₀ α q a b μ ν D L : ℝ}
    {ys : ℝ → ℝ} (ha : 0 < a) (hC : CoreHypsM 6 a b μ ν D (a5Q a₀ a₀ q) ys)
    (hL : ∀ x ∈ Icc (-a) a,
      |iteratedDeriv 6 (a5Red a₀ a₀ q ys) x| ≤ L ∧ |iteratedDeriv 8 (a5Red a₀ a₀ q ys) x| ≤ L)
    (hε : |α - a₀| ≤ 1) (hεν : 128 * |α - a₀| ≤ ν) :
    CoreHypsM 6 a b μ (ν / 2) (D + 16) (a5Q a₀ α q) ys ∧
      ∀ x ∈ Icc (-a) a, ν / 2 ≤ |iteratedDeriv 6 (a5Red a₀ α q ys) x| ∧
        |iteratedDeriv 6 (a5Red a₀ α q ys) x| ≤ L + 64 ∧ |iteratedDeriv 8 (a5Red a₀ α q ys) x| ≤ L + 256 := by
  obtain ⟨hdiff, hcore⟩ := h10 6 a b μ ν D (α - a₀) (a5Q a₀ a₀ q) ys hC
  rw [a5uX_red_split h8] at hdiff hcore
  rw [← a5uX_Q_split h8] at hcore
  have hνb : ∀ x ∈ Icc (-a) a, ν ≤ |iteratedDeriv 6 (a5Red a₀ a₀ q ys) x| := hC.2.2.2.2.2
  have hjet : ∀ x ∈ Icc (-a) a, ν / 2 ≤ |iteratedDeriv 6 (a5Red a₀ α q ys) x| ∧
      |iteratedDeriv 6 (a5Red a₀ α q ys) x| ≤ L + 64 ∧ |iteratedDeriv 8 (a5Red a₀ α q ys) x| ≤ L + 256 := by
    intro x hx
    have hx' : x ∈ Ioo (-2 * a) (2 * a) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have d6 : |iteratedDeriv 6 (a5Red a₀ α q ys) x - iteratedDeriv 6 (a5Red a₀ a₀ q ys) x| ≤
        2 ^ 6 * |α - a₀| := hdiff 6 (by norm_num) x hx'
    have d8 : |iteratedDeriv 8 (a5Red a₀ α q ys) x - iteratedDeriv 8 (a5Red a₀ a₀ q ys) x| ≤
        2 ^ 8 * |α - a₀| := hdiff 8 (by norm_num) x hx'
    have e1 := abs_sub_abs_le_abs_sub (iteratedDeriv 6 (a5Red a₀ α q ys) x) (iteratedDeriv 6 (a5Red a₀ a₀ q ys) x)
    have e2 := abs_sub_abs_le_abs_sub (iteratedDeriv 6 (a5Red a₀ a₀ q ys) x) (iteratedDeriv 6 (a5Red a₀ α q ys) x)
    have e3 := abs_sub_abs_le_abs_sub (iteratedDeriv 8 (a5Red a₀ α q ys) x) (iteratedDeriv 8 (a5Red a₀ a₀ q ys) x)
    rw [abs_sub_comm] at e2
    have h1 := hνb x hx
    have h2 := hL x hx
    norm_num at d6 d8
    refine ⟨by linarith, by linarith, by linarith⟩
  refine ⟨?_, hjet⟩
  exact a5uX_coreHypsM_mono (hcore (ν / 2) fun x hx => (hjet x hx).1) le_rfl le_rfl
    (by linarith [abs_nonneg (α - a₀)])

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open scoped ContDiff

/-- The target weight is nonnegative. -/
theorem a5uX_cw_nonneg (a₀ α : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ crossWeight a₀ α t := by
  unfold crossWeight crossEnvelope
  split_ifs <;> positivity

/-- `|g″(0)| ≤ δ⁴` from A11's `g″(0) = 4(α* − α)` and `|α* − a₀| ≤ |y|/2`. -/
theorem a5uX_jetA {a₀ α y A2 δ : ℝ} (hA2 : A2 = 4 * (a5Moving a₀ y - α))
    (hcl : |a5Moving a₀ y - a₀| ≤ |y| / 2) (hy : |y| ≤ δ ^ 4 / 4) (hα : |α - a₀| ≤ δ ^ 4 / 8) :
    |A2| ≤ δ ^ 4 := by
  have h := abs_sub_le (a5Moving a₀ y) a₀ α
  rw [abs_sub_comm a₀ α] at h
  rw [hA2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- The pointwise three-threshold alternative on `(−a', a')`, from A5 and A6. -/
theorem a5uX_alt (h5 : EvenJetTaylorFacts) (h8 : A5FixedChartFacts) {a₀ α q a a' δ η ν L' dmax : ℝ}
    {ys : ℝ → ℝ} (ha : 0 < a) (haa : a' ≤ a) (haδ : a' ≤ δ)
    (hsep : ∀ ε A B D u g₂ g₃ g₄ : ℝ, 0 < ε → ε ≤ δ ^ 2 → |A| ≤ δ ^ 4 → |u| ≤ δ → ν / 2 ≤ |D| →
        |D| ≤ dmax → 24 * ε - 10 * |A| ≤ |B| →
        |g₂ - (A + B * u ^ 2 / 2 + D * u ^ 4 / 24)| ≤ L' * u ^ 6 →
        |g₃ - (B * u + D * u ^ 3 / 6)| ≤ L' * |u| ^ 5 →
        |g₄ - (B + D * u ^ 2 / 2)| ≤ L' * u ^ 4 →
          η * ε ^ 2 < |g₂| ∨ η * (ε * √ε) < |g₃| ∨ η * ε < |g₄|)
    (hsm : ContDiffOn ℝ ∞ (a5Red a₀ α q ys) (Ioo (-a) a)) (hev : ∀ x ∈ Icc (-a) a, ys (-x) = ys x)
    (h8b : ∀ x ∈ Icc (-a) a, |iteratedDeriv 8 (a5Red a₀ α q ys) x| ≤ L')
    (hd6 : ν / 2 ≤ |iteratedDeriv 6 (a5Red a₀ α q ys) 0|)
    (hd6' : |iteratedDeriv 6 (a5Red a₀ α q ys) 0| ≤ dmax)
    (hε0 : 0 < |α - a₀|) (hεδ : |α - a₀| ≤ δ ^ 2) (hA : |iteratedDeriv 2 (a5Red a₀ α q ys) 0| ≤ δ ^ 4)
    (hB : 24 * |α - a₀| - 10 * |iteratedDeriv 2 (a5Red a₀ α q ys) 0| ≤
      |iteratedDeriv 4 (a5Red a₀ α q ys) 0|) :
    ∀ x ∈ Ioo (-a') a', η * |α - a₀| ^ 2 < |iteratedDeriv 2 (fun x => a5Q a₀ α q (x, ys x)) x| ∨
      η * (|α - a₀| * √|α - a₀|) < |iteratedDeriv 3 (fun x => a5Q a₀ α q (x, ys x)) x| ∨
      η * |α - a₀| < |iteratedDeriv 4 (fun x => a5Q a₀ α q (x, ys x)) x| := by
  intro x hx
  have hxa : x ∈ Ioo (-a) a := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨t2, t3, t4⟩ := h5 (a5Red a₀ α q ys) a L' ha hsm (a5uX_red_even h8 hev)
    (fun y hy => h8b y (Ioo_subset_Icc_self hy)) x hxa
  have hxδ : |x| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact hsep _ _ _ _ x _ _ _ hε0 hεδ hA hxδ hd6 hd6' hB t2 t3 t4

/-- The order-6 branch (`t ε³ ≤ 1`): `OscInt.K2.coreEstimateM` and A7(ii). -/
theorem a5uX_order6 (h7 : CrossEnvelopeFacts) {a₀ α q a' b μ ν D C₆ K M t p : ℝ} {ys : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ}
    (hC₆ : ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M t p : ℝ),
      CoreHypsM 6 a' b μ ν D Q ys → AmpBound 2 (Icc (-a') a' ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (Q k + p * k.1)) A‖ ≤ C₆ * M * t ^ (-(1 / 2 + 1 / ((6 : ℕ) : ℝ))))
    (hC : CoreHypsM 6 a' b μ ν D (a5Q a₀ α q) ys) (hA : AmpBound 2 (Icc (-a') a' ×ˢ Icc (-b) b) A M)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hK : C₆ ≤ K) (hsmall : t * |α - a₀| ^ 3 ≤ 1) :
    ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) A‖ ≤ K * M * crossWeight a₀ α t := by
  have ht0 : 0 < t := by linarith
  have hE := h7.2.1 |α - a₀| t (abs_nonneg _) ht0 hsmall
  have hwt : crossWeight a₀ α t = t ^ (-(2 : ℝ) / 3) := by
    unfold crossWeight
    rw [hE, mul_one]
  have h6b := hC₆ (a5Q a₀ α q) ys A M t p hC hA ht
  have hexp : t ^ (-(1 / 2 + 1 / ((6 : ℕ) : ℝ))) = t ^ (-(2 : ℝ) / 3) := by norm_num
  rw [hexp, ← hwt] at h6b
  exact h6b.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hM) (a5uX_cw_nonneg a₀ α ht0))

end OscInt.A5UAux

namespace OscInt.A5UAux

open Set MeasureTheory OscInt.Statements OscInt.Blueprint OscInt.Blueprint.K2 OscInt.Blueprint.A5U
open scoped ContDiff

/-- The multi-order branch (`t ε³ ≥ 1`): A4 with `l_j = η ε^{(6−j)/2}` and A7(iii). -/
theorem a5uX_multi {a₀ α q a' b μ ν D P η C₇ K M t p : ℝ} {ys : ℝ → ℝ} {A : ℝ × ℝ → ℂ}
    (hP : ∀ (Q : ℝ × ℝ → ℝ) (ys : ℝ → ℝ) (A : ℝ × ℝ → ℂ) (M t p ν l₂ l₃ l₄ : ℝ),
      0 < ν → 0 < l₂ → 0 < l₃ → 0 < l₄ → CoreHypsM 6 a' b μ ν D Q ys →
      (∀ x ∈ Ioo (-a') a', l₂ < |iteratedDeriv 2 (fun x => Q (x, ys x)) x| ∨
        l₃ < |iteratedDeriv 3 (fun x => Q (x, ys x)) x| ∨ l₄ < |iteratedDeriv 4 (fun x => Q (x, ys x)) x|) →
      AmpBound 2 (Icc (-a') a' ×ˢ Icc (-b) b) A M → 1 ≤ t →
        ‖oscInt2 (fun k => t * (Q k + p * k.1)) A‖ ≤
          P * M * t ^ (-(1 : ℝ) / 2) *
            (8 * (t * l₂) ^ (-(1 : ℝ) / 2) + 18 * (t * l₃) ^ (-(1 : ℝ) / 3) + 38 * (t * l₄) ^ (-(1 : ℝ) / 4)))
    (hC₇ : ∀ ε t : ℝ, 0 < ε → 1 ≤ t → 1 ≤ t * ε ^ 3 →
      t ^ (-(1 : ℝ) / 2) * (8 * (t * (η * ε ^ 2)) ^ (-(1 : ℝ) / 2) +
          18 * (t * (η * (ε * √ε))) ^ (-(1 : ℝ) / 3) + 38 * (t * (η * ε)) ^ (-(1 : ℝ) / 4)) ≤
        C₇ * (t ^ (-(2 : ℝ) / 3) * crossEnvelope (ε * t ^ ((1 : ℝ) / 3))))
    (hη : 0 < η) (hν : 0 < ν) (hC : CoreHypsM 6 a' b μ ν D (a5Q a₀ α q) ys)
    (halt : ∀ x ∈ Ioo (-a') a', η * |α - a₀| ^ 2 < |iteratedDeriv 2 (fun x => a5Q a₀ α q (x, ys x)) x| ∨
      η * (|α - a₀| * √|α - a₀|) < |iteratedDeriv 3 (fun x => a5Q a₀ α q (x, ys x)) x| ∨
      η * |α - a₀| < |iteratedDeriv 4 (fun x => a5Q a₀ α q (x, ys x)) x|)
    (hA : AmpBound 2 (Icc (-a') a' ×ˢ Icc (-b) b) A M) (ht : 1 ≤ t) (hM : 0 ≤ M) (hε0 : 0 < |α - a₀|)
    (hbig : 1 ≤ t * |α - a₀| ^ 3) (hK : max P 0 * max C₇ 0 ≤ K) :
    ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) A‖ ≤ K * M * crossWeight a₀ α t := by
  have ht0 : 0 < t := by linarith
  have hsq : 0 < √|α - a₀| := Real.sqrt_pos.2 hε0
  have hW0 := a5uX_cw_nonneg a₀ α ht0
  have h4b := hP (a5Q a₀ α q) ys A M t p ν _ _ _ hν (by positivity) (by positivity) (by positivity) hC halt hA ht
  have h7b : _ ≤ C₇ * crossWeight a₀ α t := hC₇ |α - a₀| t hε0 ht hbig
  generalize hX : 8 * (t * (η * |α - a₀| ^ 2)) ^ (-(1 : ℝ) / 2) +
      18 * (t * (η * (|α - a₀| * √|α - a₀|))) ^ (-(1 : ℝ) / 3) +
      38 * (t * (η * |α - a₀|)) ^ (-(1 : ℝ) / 4) = X at h4b h7b
  have hX0 : 0 ≤ X := by rw [← hX]; positivity
  have hT : 0 < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
  calc ‖oscInt2 (fun k => t * (a5Q a₀ α q k + p * k.1)) A‖ ≤ P * M * t ^ (-(1 : ℝ) / 2) * X := h4b
    _ = P * M * (t ^ (-(1 : ℝ) / 2) * X) := by ring
    _ ≤ max P 0 * M * (t ^ (-(1 : ℝ) / 2) * X) := by gcongr; exact le_max_left _ _
    _ ≤ max P 0 * M * (max C₇ 0 * crossWeight a₀ α t) :=
        mul_le_mul_of_nonneg_left (h7b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0))
          (mul_nonneg (le_max_right _ _) hM)
    _ = (max P 0 * max C₇ 0) * M * crossWeight a₀ α t := by ring
    _ ≤ K * M * crossWeight a₀ α t := by gcongr

/-- **A12a** The core window estimate, from A4's bound, A5, A6, A7, A8, A9's bound, A10 and A11's bound. -/
theorem a5CoreWindow : A5CoreWindowFacts := by
  intro h4 h5 h6 h7 h8 h9 h10 h11 a₀ ha₀
  obtain ⟨q₀, hq₀, a, b, μ, ν, D, L, ha, hb, hμ, hν, ys, hys⟩ := h9 a₀ ha₀
  obtain ⟨η, hη, hηδ⟩ := h6 24 10 (ν / 2) (max (ν / 2) (L + 64)) (by norm_num) (by norm_num) (by positivity)
    (le_max_left _ _)
  obtain ⟨δ, hδ, hδ1, hsep⟩ := hηδ (max L 0 + 256) (by positivity)
  obtain ⟨C₇, hC₇⟩ := h7.2.2 η hη
  have ha' : 0 < min a δ := lt_min ha hδ
  obtain ⟨P, hP⟩ := h4 (min a δ) b μ (D + 16) ha' hb hμ
  obtain ⟨C₆, hC₆⟩ := OscInt.K2.coreEstimateM 6 (by norm_num) (min a δ) b μ (ν / 2) (D + 16) ha' hb hμ
    (by positivity)
  have hδ4 : δ ^ 4 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
  refine ⟨min q₀ (μ * δ ^ 4 / 4), lt_min hq₀ (by positivity), min a δ, ha', b, hb,
    min (min 1 (ν / 128)) (δ ^ 4 / 8), lt_min (lt_min one_pos (by positivity)) (by positivity),
    max C₆ 0 + max P 0 * max C₇ 0, ?_⟩
  intro α q hα hq A M t p hA ht
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA.2.2 0 (by norm_num) 0)
  have hα1 : |α - a₀| ≤ 1 := hα.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hαν : 128 * |α - a₀| ≤ ν := by
    have := hα.trans ((min_le_left _ _).trans (min_le_right _ _)); linarith
  have hαδ : |α - a₀| ≤ δ ^ 4 / 8 := hα.trans (min_le_right _ _)
  obtain ⟨hC, hev, hys0, hjet⟩ := hys q (hq.trans (min_le_left _ _))
  obtain ⟨hCα, hjα⟩ := a5uX_pert h8 h10 ha hC hjet hα1 hαν
  have hCα' := a5uX_coreHypsM_mono hCα (min_le_left a δ) le_rfl le_rfl
  by_cases hsmall : t * |α - a₀| ^ 3 ≤ 1
  · exact a5uX_order6 h7 hC₆ hCα' hA ht hM
      ((le_max_left _ _).trans (le_add_of_nonneg_right (by positivity))) hsmall
  push Not at hsmall
  have hε0 : 0 < |α - a₀| := by
    by_contra h0
    have h00 : |α - a₀| = 0 := le_antisymm (not_lt.mp h0) (abs_nonneg _)
    rw [h00] at hsmall
    norm_num at hsmall
  have hy0 : |ys q 0| ≤ δ ^ 4 / 4 := by
    have h1 : μ * |ys q 0| ≤ μ * (δ ^ 4 / 4) := by linarith [hys0, hq.trans (min_le_right _ _)]
    exact le_of_mul_le_mul_left h1 hμ
  have hpi : |ys q 0| < Real.pi / 4 := by
    have : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
    linarith [Real.pi_gt_three]
  obtain ⟨-, hcl, hjets⟩ := h11 a₀ ha₀ q a (ys q) ha hC.2.1 (fun x hx => (hC.2.2.1 x hx).2) hpi
  obtain ⟨hA2, -, hB⟩ := hjets α
  have hsm : ContDiffOn ℝ ∞ (a5Red a₀ α q (ys q)) (Ioo (-a) a) :=
    (hCα.1.comp_contDiffOn (contDiffOn_id.prodMk hCα.2.1)).mono
      (Ioo_subset_Ioo (by linarith) (by linarith))
  have h0 : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha.le⟩
  have halt := a5uX_alt h5 h8 ha (min_le_left a δ) (min_le_right a δ) hsep hsm hev
    (fun x hx => (hjα x hx).2.2.trans (by linarith [le_max_left L 0])) (hjα 0 h0).1
    ((hjα 0 h0).2.1.trans (le_max_right _ _)) hε0 (hαδ.trans (by linarith))
    (a5uX_jetA hA2 hcl hy0 hαδ) hB
  exact a5uX_multi hP hC₇ hη (by positivity) hCα' halt hA ht hM hε0 hsmall.le
    (le_add_of_nonneg_left (by positivity))

end OscInt.A5UAux
