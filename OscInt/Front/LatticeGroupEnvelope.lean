/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Batch LS, part P-envelope: the real-analysis envelope

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `EnvelopeFacts`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeEnvelopeAux

open OscInt.Blueprint.LatticeGroup

theorem min_power_envelope {a u p : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hp : 0 ≤ p) :
    min 1 ((a / u) ^ p) ≤ (1 + a) ^ p * (1 + u) ^ (-p) := by
  -- Real.rpow_neg and Real.div_rpow: goal becomes a comparison of powers of ratios.
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    ← Real.div_rpow (by positivity) (by positivity)]
  by_cases h : u ≤ a
  · -- Real.one_le_rpow: the small-time branch is bounded by one.
    refine (min_le_left _ _).trans (Real.one_le_rpow ?_ hp)
    exact (le_div_iff₀ (by positivity)).2 (by linarith)
  · -- Real.rpow_le_rpow: the large-time ratio comparison is elementary.
    refine (min_le_right _ _).trans (Real.rpow_le_rpow (by positivity) ?_ hp)
    apply (div_le_div_iff₀ hu (by positivity)).2
    nlinarith [le_of_not_ge h]

theorem cube_rescaling {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) (d : ℕ) :
    c ^ d * (2 * u) ^ (-(d : ℝ) / 3) = (c ^ 3 / 2 / u) ^ ((d : ℝ) / 3) := by
  have hp : (c ^ 3) ^ ((d : ℝ) / 3) = c ^ d := by
    -- Real.rpow_mul and Real.rpow_natCast: 3(d/3)=d, including d=0.
    rw [← Real.rpow_natCast c 3, ← Real.rpow_mul hc]
    have he : ((3 : ℕ) : ℝ) * ((d : ℝ) / 3) = d := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have he : -(d : ℝ) / 3 = -((d : ℝ) / 3) := by ring
  -- Both denominators are positive, so the inverse-power identity has no zero case.
  rw [he, Real.rpow_neg (by positivity), ← hp, ← div_eq_mul_inv,
    ← Real.div_rpow (by positivity) (by positivity), div_div]

theorem envelopeFacts : EnvelopeFacts := by
  intro d t ht
  have hu : 0 < |t| := abs_pos.mpr ht
  have hc : 0 ≤ 8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi) := by positivity
  -- cube_rescaling reduces the Blueprint coefficient exactly to (tau/|t|)^(d/3).
  rw [cube_rescaling hc hu d]
  have h := min_power_envelope
    (a := (8 * (1 + Real.sqrt 7) / 3 / (2 * Real.pi)) ^ 3 / 2)
    (u := |t|) (p := (d : ℝ) / 3) (by positivity) hu (by positivity)
  have he : -(d : ℝ) / 3 = -((d : ℝ) / 3) := by ring
  simpa only [he] using h

end OscInt.LatticeEnvelopeAux
