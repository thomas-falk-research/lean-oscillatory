/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.TriangularCrossover
import OscInt.Front.TriDeriv

/-!
# Batch A5U, part A8: `A5FixedChartFacts`

Route: `docs/proof-A5U.md`, section 1. In the chart `k* + L(u, s)` with `k* = (θ₀, −θ₀)` the two arguments
are `θ₀ + (u + s)` and `−θ₀ + (u − s)`, their sum is `2u`, and `DΨ_α(k*) L(u, s) = −2 s sin θ₀` by
`OscInt.API.TriDeriv.triD1`; the closed form follows from `cos(x + u) + cos(x − u) = 2 cos x cos u`.
-/

namespace OscInt.A5UAux

open OscInt.Statements OscInt.Blueprint.A5U

/-- The cosine sum identity in the form used by the chart. -/
theorem a5uG3_cos_pair (θ u s : ℝ) :
    Real.cos (θ + (u + s)) + Real.cos (-θ + (u - s)) = 2 * Real.cos (θ + s) * Real.cos u := by
  have h1 : θ + (u + s) = (θ + s) + u := by ring
  have h2 : -θ + (u - s) = -((θ + s) - u) := by ring
  rw [h1, h2, Real.cos_neg, Real.cos_add, Real.cos_sub]
  ring

/-- **A8** The fixed chart: the closed form of `F_α`. -/
theorem a5FixedChart : A5FixedChartFacts := by
  intro a₀ α k
  obtain ⟨u, s⟩ := k
  set θ := a5Theta a₀ with hθ
  have hk : a5Centre a₀ + a5L (u, s) = (θ + (u + s), -θ + (u - s)) := by
    simp only [a5Centre, a5L, ← hθ, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one, mul_neg]
    congr 1
  have hL : a5L (u, s) = (u + s, u - s) := by
    simp only [a5L, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one, mul_neg, sub_eq_add_neg]
  have hsum : θ + (u + s) + (-θ + (u - s)) = 2 * u := by ring
  simp only [a5F]
  rw [hk, hL, OscInt.API.TriDeriv.triD1]
  simp only [triPhase, a5Centre, ← hθ]
  rw [hsum, add_neg_cancel, Real.sin_zero, Real.cos_zero, Real.cos_neg, Real.sin_neg]
  have hc := a5uG3_cos_pair θ u s
  linear_combination hc
