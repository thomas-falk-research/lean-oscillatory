/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: single-photon transition amplitudes on a cosine-band lattice (T0E)

Only `import OscInt.API` and Mathlib. Answers the external application study of 2026-11-10
(`review/2026-11-10-external-followup-answers.md`, "The quantum-photonics application study").

Model (paper, not formalised here): a lossless, homogeneous, one-dimensional photonic lattice with hopping `κ > 0`
(for example the synthetic orbital-angular-momentum lattice). Its one-photon transition amplitude over `n` sites after
time `t` is a unit-modulus phase times `U(s, n) = (2π)⁻¹ ∫_{−π}^{π} e^{i(s cos k + nk)} dk` with `s = 2κt`. This
file proves, from the frozen and proved T0E (`OscInt.API.latticeKernel1Explicit`):
* `‖U(s, n)‖ ≤ b(s) := (24 · 2^{1/4} s^{−1/2} + 36 · 2^{1/6} s^{−1/3}) / (2π)` for `s > 0`, every real `n`;
* `‖U(s, n)‖ ≤ 1` for every `s` (the trivial bound), so every single-site transition probability is at most
  `min(1, b(s))²`;
* `b(s) < 1` for every `s ≥ 519` (so the comment "t > 518" in batch LE is right to the integer).
What it does not give: anything about loss, input/output coupling, finite chains, control or fidelity; the identification
of `U` with the physical amplitude is the paper step above.
-/

open OscInt.Statements OscInt.API OscInt.API.LatticeExplicitSanity

namespace ConsumerPhotonLattice

/-- The normalised transition amplitude `U(s, n) = (2π)⁻¹ I(s, n)`. -/
noncomputable def amp (s n : ℝ) : ℂ := ((2 * Real.pi)⁻¹ : ℝ) * latticeKernel1 s n

/-- The normalised T0E envelope `b(s)`. -/
noncomputable def envelope (s : ℝ) : ℝ :=
  (24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * s ^ (-(1 : ℝ) / 2) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) * s ^ (-(1 : ℝ) / 3)) /
    (2 * Real.pi)

theorem norm_amp (s n : ℝ) : ‖amp s n‖ = ‖latticeKernel1 s n‖ / (2 * Real.pi) := by
  rw [amp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_eq_div]

/-- The trivial bound: `‖U(s, n)‖ ≤ 1` for every `s` and `n`. -/
theorem amp_le_one (s n : ℝ) : ‖amp s n‖ ≤ 1 := by
  rw [norm_amp, div_le_one (by positivity)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi) (C := 1)
    (f := fun k : ℝ => Complex.exp (↑(s * Real.cos k + n * k) * Complex.I))
    (fun k _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [abs_of_nonneg (by linarith [Real.pi_pos])] at h
  simpa [latticeKernel1] using h.trans (by linarith)

/-- **The explicit envelope**, from T0E: `‖U(s, n)‖ ≤ b(s)` for `s > 0`, uniformly in `n`. -/
theorem amp_le_envelope (s n : ℝ) (hs : 0 < s) : ‖amp s n‖ ≤ envelope s := by
  rw [norm_amp, envelope]
  exact div_le_div_of_nonneg_right (latticeKernel1Explicit s n hs) (by positivity)

/-- Every single-site transition probability is at most `min(1, b(s))²`. -/
theorem prob_le (s n : ℝ) (hs : 0 < s) : ‖amp s n‖ ^ 2 ≤ min 1 (envelope s) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (le_min (amp_le_one s n) (amp_le_envelope s n hs)) 2

/-- `b` is antitone on `(0, ∞)`. -/
theorem envelope_antitone {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') : envelope s' ≤ envelope s := by
  unfold envelope
  have h1 : s' ^ (-(1 : ℝ) / 2) ≤ s ^ (-(1 : ℝ) / 2) := Real.rpow_le_rpow_of_nonpos hs hss' (by norm_num)
  have h2 : s' ^ (-(1 : ℝ) / 3) ≤ s ^ (-(1 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos hs hss' (by norm_num)
  gcongr

/-- `519^{−1/2} < 1/22.78` and `519^{−1/3} < 1/8.036`. -/
theorem rpow519 : (519 : ℝ) ^ (-(1 : ℝ) / 2) < 1 / 22.78 ∧ (519 : ℝ) ^ (-(1 : ℝ) / 3) < 1 / 8.036 := by
  have hpos : (0 : ℝ) < 519 := by norm_num
  constructor
  · have hsq : ((519 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 519 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; norm_num [Real.rpow_neg_one]
    exact lt_of_pow_eq (by norm_num) hsq (by norm_num)
  · have hcb : ((519 : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = 1 / 519 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; norm_num [Real.rpow_neg_one]
    exact lt_of_pow_eq (by norm_num) hcb (by norm_num)

/-- **The usefulness threshold**: `b(s) < 1` for every `s ≥ 519`, so the T0E probability bound is non-trivial there. -/
theorem envelope_lt_one {s : ℝ} (hs : 519 ≤ s) : envelope s < 1 := by
  refine lt_of_le_of_lt (envelope_antitone (by norm_num) hs) ?_
  obtain ⟨h1, h2⟩ := rpow519
  have ha : (2 : ℝ) ^ ((1 : ℝ) / 4) < 1.18921 :=
    lt_of_pow_eq (by norm_num) two_rpow_quarter_pow (by norm_num)
  have hb : (2 : ℝ) ^ ((1 : ℝ) / 6) < 1.12247 :=
    lt_of_pow_eq (by norm_num) two_rpow_sixth_pow (by norm_num)
  have ha0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hb0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 6) := by positivity
  have hp1 : 0 ≤ (519 : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hp2 : 0 ≤ (519 : ℝ) ^ (-(1 : ℝ) / 3) := by positivity
  have hpi := Real.pi_gt_d4
  unfold envelope
  rw [div_lt_one (by positivity)]
  nlinarith [mul_le_mul ha.le h1.le hp1 (by norm_num), mul_le_mul hb.le h2.le hp2 (by norm_num)]

end ConsumerPhotonLattice
