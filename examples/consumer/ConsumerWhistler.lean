/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: whistler waves at the inflection of the parallel branch (S1.3)

Only `import OscInt.API` and Mathlib. Answers Track C, item C1, of the external research packet of 2026-11-12
(`review/2026-11-12-DNLS-packet-answers.md`).

Model (paper, not formalised here): the cold-plasma parallel whistler branch `ω(k) = c²k²Ω/(ω_pe² + c²k²)` above the ion
gyrofrequency (Eliasson–Shukla, GRL 31 (2004), §2, as read by the external reviewer). With `q = ck/ω_pe`, `τ = Ωt` and
`ζ = (ω_pe/c) z`, a wave packet band-limited to `q ∈ [1/2, 2/3]` is, up to a constant factor absorbed in the amplitude,
  `E(τ, ζ) = ∫_{1/2}^{2/3} e^{i(ζq − τ h(q))} A(q) dq`, `h(q) = q²/(1 + q²)`.
The group velocity `h′` has its maximum at the inflection `q = 1/√3 ∈ [1/2, 2/3]`, where `h″ = 0`, so the packet
disperses like `τ^{−1/3}` (an Airy-type front), not `τ^{−1/2}`. This file proves, from the frozen and proved S1.3
(`OscInt.vanDerCorput_three`), the explicit bound
  `‖E(τ, ζ)‖ ≤ 18 (43740 τ / 28561)^{−1/3} (|A(2/3)| + ∫ |A′|)` for every `τ > 0` and every real `ζ`,
uniformly in the observation point `ζ`. The constant `43740/28561 ≤ min |h‴|` on the band is a hand bound, proved here.
What it does not give: anything about the frozen-background approximation, other branches, damping or nonlinear
coupling; the identification of `E` with the physical field is the paper step above. For one fixed amplitude a sharper
classical analysis exists; the point is an explicit, checked inequality uniform in `ζ`.
-/

open OscInt.Statements

namespace ConsumerWhistler

/-- The whistler phase without its linear term: `−τ q²/(1 + q²)`. -/
noncomputable def phase (τ q : ℝ) : ℝ := -τ * (q ^ 2 / (1 + q ^ 2))

/-- Its derivative. -/
noncomputable def phase1 (τ q : ℝ) : ℝ := -τ * (2 * q / (1 + q ^ 2) ^ 2)

/-- Its second derivative. -/
noncomputable def phase2 (τ q : ℝ) : ℝ := -τ * ((2 - 6 * q ^ 2) / (1 + q ^ 2) ^ 3)

/-- Its third derivative. -/
noncomputable def phase3 (τ q : ℝ) : ℝ := τ * (24 * q * (1 - q ^ 2) / (1 + q ^ 2) ^ 4)

theorem one_add_sq_pos (q : ℝ) : 0 < 1 + q ^ 2 := by positivity

theorem hasDerivAt_phase (τ q : ℝ) : HasDerivAt (phase τ) (phase1 τ q) q := by
  have h0 : (1 + q ^ 2) ≠ 0 := (one_add_sq_pos q).ne'
  have hn : HasDerivAt (fun q : ℝ => q ^ 2) (2 * q) q := by simpa using hasDerivAt_pow 2 q
  have hd : HasDerivAt (fun q : ℝ => 1 + q ^ 2) (2 * q) q := by simpa using (hasDerivAt_pow 2 q).const_add 1
  have := (hn.div hd h0).const_mul (-τ)
  convert this using 1
  · funext y; simp [phase]
  · unfold phase1; field_simp; ring

theorem hasDerivAt_phase1 (τ q : ℝ) : HasDerivAt (phase1 τ) (phase2 τ q) q := by
  have h1 : (1 + q ^ 2) ≠ 0 := (one_add_sq_pos q).ne'
  have h0 : (1 + q ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  have hn : HasDerivAt (fun q : ℝ => 2 * q) 2 q := by simpa using (hasDerivAt_id q).const_mul 2
  have hd : HasDerivAt (fun q : ℝ => (1 + q ^ 2) ^ 2) (2 * (1 + q ^ 2) * (2 * q)) q := by
    have := (hasDerivAt_pow 2 (1 + q ^ 2)).comp q ((hasDerivAt_pow 2 q).const_add 1)
    simpa [Function.comp_def] using this
  have := (hn.div hd h0).const_mul (-τ)
  convert this using 1
  · funext y; simp [phase1]
  · unfold phase2; field_simp; ring

theorem hasDerivAt_phase2 (τ q : ℝ) : HasDerivAt (phase2 τ) (phase3 τ q) q := by
  have h1 : (1 + q ^ 2) ≠ 0 := (one_add_sq_pos q).ne'
  have h0 : (1 + q ^ 2) ^ 3 ≠ 0 := pow_ne_zero 3 h1
  have hn : HasDerivAt (fun q : ℝ => 2 - 6 * q ^ 2) (-(6 * (2 * q))) q := by
    have := ((hasDerivAt_pow 2 q).const_mul 6).const_sub 2
    simpa using this
  have hd : HasDerivAt (fun q : ℝ => (1 + q ^ 2) ^ 3) (3 * (1 + q ^ 2) ^ 2 * (2 * q)) q := by
    have := (hasDerivAt_pow 3 (1 + q ^ 2)).comp q ((hasDerivAt_pow 2 q).const_add 1)
    simpa [Function.comp_def] using this
  have := (hn.div hd h0).const_mul (-τ)
  convert this using 1
  · funext y; simp [phase2]
  · unfold phase3; field_simp; ring

theorem hasDerivOn_of_hasDerivAt {f f' : ℝ → ℝ} (h : ∀ q, HasDerivAt f (f' q) q) (a b : ℝ) : HasDerivOn f f' a b :=
  ⟨fun q _ => (h q).continuousAt.continuousWithinAt, fun q _ => h q⟩

/-- **The hand bound** `|h‴(q)| ≥ 43740/28561` on the band: `q ≥ 1/2`, `1 − q² ≥ 5/9` and `(1 + q²)⁴ ≤ (13/9)⁴`. -/
theorem third_lower {q : ℝ} (h1 : 1 / 2 ≤ q) (h2 : q ≤ 2 / 3) :
    43740 / 28561 ≤ 24 * q * (1 - q ^ 2) / (1 + q ^ 2) ^ 4 := by
  have hpos : 0 < (1 + q ^ 2) ^ 4 := by positivity
  rw [le_div_iff₀ hpos]
  have hq2 : q ^ 2 ≤ 4 / 9 := by nlinarith
  have hA : (1 + q ^ 2) ^ 4 ≤ (13 / 9) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hB : 12 * (5 / 9 : ℝ) ≤ 24 * q * (1 - q ^ 2) := by nlinarith
  have hC : (43740 / 28561 : ℝ) * (13 / 9) ^ 4 = 12 * (5 / 9) := by norm_num
  nlinarith

/-- **The whistler bound** (S1.3): for every `τ > 0`, every observation point `ζ` and every amplitude `A` on the band,
`‖∫_{1/2}^{2/3} e^{i(ζq − τq²/(1+q²))} A(q) dq‖ ≤ 18 (43740 τ / 28561)^{−1/3} (|A(2/3)| + ∫ |A′|)`. -/
theorem whistler_bound (τ ζ : ℝ) (hτ : 0 < τ) (A A' : ℝ → ℂ) (hA : AmplitudeOn A A' (1 / 2) (2 / 3)) :
    ‖oscInt (fun q => phase τ q + ζ * q) A (1 / 2) (2 / 3)‖ ≤
      18 * (43740 / 28561 * τ) ^ (-(1 : ℝ) / 3) * ampNorm A A' (1 / 2) (2 / 3) := by
  refine OscInt.vanDerCorput_three (phase τ) (phase1 τ) (phase2 τ) (phase3 τ) A A' (1 / 2) (2 / 3)
    (43740 / 28561 * τ) ζ (by norm_num) (by positivity) (hasDerivOn_of_hasDerivAt (hasDerivAt_phase τ) _ _)
    (hasDerivOn_of_hasDerivAt (hasDerivAt_phase1 τ) _ _) (hasDerivOn_of_hasDerivAt (hasDerivAt_phase2 τ) _ _)
    (fun q hq => ?_) hA
  rw [phase3, abs_mul, abs_of_pos hτ, mul_comm (43740 / 28561 : ℝ) τ]
  have h := third_lower hq.1.le hq.2.le
  calc τ * (43740 / 28561) ≤ τ * (24 * q * (1 - q ^ 2) / (1 + q ^ 2) ^ 4) := mul_le_mul_of_nonneg_left h hτ.le
    _ ≤ τ * |24 * q * (1 - q ^ 2) / (1 + q ^ 2) ^ 4| := mul_le_mul_of_nonneg_left (le_abs_self _) hτ.le

/-- The inflection: `h″(1/√3) = 0`, so the stationary point of the group velocity lies inside the band
(`1/2 < 1/√3 < 2/3`). -/
theorem inflection (τ : ℝ) : phase2 τ (1 / Real.sqrt 3) = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  unfold phase2
  have : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, h3]; norm_num
  rw [this]
  norm_num

theorem inflection_in_band : 1 / 2 < 1 / Real.sqrt 3 ∧ 1 / Real.sqrt 3 < 2 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := by positivity
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hpos]; nlinarith
  · rw [div_lt_div_iff₀ hpos (by norm_num)]; nlinarith

/-- With the constant amplitude `A = 1`: `‖∫_{1/2}^{2/3} e^{i(ζq − τh(q))} dq‖ ≤ 18 (43740 τ/28561)^{−1/3}`, which is
below the trivial bound `1/6` (the band length) once `τ > 28561 · 108³ / 43740 ≈ 8.23 · 10⁵` (arithmetic, not proved
here). The large threshold reflects S1.3's constant 18 and the narrow band; it is a valid bound, not a sharp one. -/
theorem whistler_bound_one (τ ζ : ℝ) (hτ : 0 < τ) :
    ‖oscInt (fun q => phase τ q + ζ * q) (fun _ => 1) (1 / 2) (2 / 3)‖ ≤ 18 * (43740 / 28561 * τ) ^ (-(1 : ℝ) / 3) := by
  have h := whistler_bound τ ζ hτ (fun _ => 1) (fun _ => 0)
    ⟨continuousOn_const, fun _ _ => hasDerivAt_const _ _, intervalIntegrable_const⟩
  simpa [ampNorm] using h

end ConsumerWhistler
