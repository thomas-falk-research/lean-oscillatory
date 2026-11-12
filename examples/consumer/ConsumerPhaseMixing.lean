/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: phase mixing of free-streaming plasma (FE-S2.1)

Only `import OscInt.API` and Mathlib. Answers `review/2026-11-10-external-followup-answers.md` (the dimension discussion:
a kinetic phase space does not make a high-dimensional oscillatory integral, but each Fourier mode of the density is an
oscillatory integral over velocity).

Model (paper, not formalised here): collisionless free streaming `∂ₜ f + v · ∇ₓ f = 0` with a two-dimensional velocity
`v ∈ ℝ²` has solution `f(t, x, v) = f₀(x − tv, v)`, so the density mode with wave vector `k` is
`ρ̂(t, k) = ∫ e^{−it k·v} f̂₀(k, v) dv`. This decay of `ρ̂` by velocity oscillation is **phase mixing**, the linear core
of Landau damping. Here the velocity profile `A = f̂₀(k, ·)` is `C^N` with compact support; the wave vector enters as the
linear functional `L = −k·(·)` (any `L` with `‖L‖ ≥ c`, Lean's operator norm with the max norm on `ℝ × ℝ`).

From the proved FE-S2.1 (`OscInt.API.nonStationaryFE`) with the zero phase: for every `N`, compact `K` and `c > 0`
there is one constant `C` with `|ρ̂(t, k)| ≤ C M t^{−N}` for every profile in the `C^N` budget `M`, every `t ≥ 1` and
every wave vector with `‖L‖ ≥ c`: free streaming mixes every mode faster than any power of `t`, uniformly away from
`k = 0`. What it does not give: self-consistent fields (Vlasov–Poisson), Landau damping rates, three-dimensional
velocities (ROADMAP I3), collisions, or an explicit constant.
-/

open OscInt.Statements OscInt.API

namespace ConsumerPhaseMixing

/-- **Phase mixing of free streaming** (2D velocity): every density Fourier mode decays faster than any power of `t`,
uniformly over smooth compactly supported velocity profiles and over wave vectors bounded away from 0. -/
theorem phaseMixing (N : ℕ) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ N A → tsupport A ⊆ K → (∀ j ≤ N, ∀ v, ‖iteratedFDeriv ℝ j A v‖ ≤ M) → c ≤ ‖L‖ → 1 ≤ t →
      ‖∫ v : ℝ × ℝ, Complex.exp (↑(t * L v) * Complex.I) * A v‖ ≤ C * M / t ^ N := by
  obtain ⟨C, hC⟩ := nonStationaryFE N (fun _ => 0) K c contDiff_const hK hc
  refine ⟨C, fun A M L t hA hsupp hM hL ht => ?_⟩
  have h := hC A M L t hA hsupp hM (fun k _ => by simpa using hL) ht
  simpa using h

end ConsumerPhaseMixing
