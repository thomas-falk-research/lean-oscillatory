/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeGroupAssembly
import OscInt.Front.LatticeGroupOp
import OscInt.Front.LatticeGroupExp
import OscInt.Front.LatticeGroupUnique
import OscInt.Front.LatticeGroupConv
import OscInt.Front.LatticeGroupBound
import OscInt.Front.LatticeGroupEnvelope

/-!
# Batch LS: the final theorems

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. LS-E, LS-K, LS-D and LS-D′ at their frozen statement types, from the nine parts and the compiled assembly
`OscInt/Front/LatticeGroupAssembly.lean`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.API

open OscInt.Statements OscInt.LatticeGroupAux OscInt.LatticeConvAux
open OscInt.LatticeKernelBoundAux OscInt.LatticeEnvelopeAux

/-- **LS-E** (`LatticeSchrodingerExistsStatement`): every `f ∈ ℓ²(ℤ^d)` is the datum of a strong solution of
`i u′ + Δu = 0` (`u′ = iΔu`, derivative in the `ℓ²` norm at every real time), every `d`. The classical construction
`u(t) = e^{itΔ} f`: `Δ` is bounded on `ℓ²(ℤ^d)` with norm at most `4d`, so the operator exponential exists. -/
theorem latticeSchrodingerExists : LatticeSchrodingerExistsStatement :=
  lsE_of lapOpFacts expSolutionFacts

/-- **LS-K** (`LatticeSchrodingerKernelStatement`): every solution with datum `f ∈ ℓ²(ℤ^d)` is
`u(t)(x) = Σ_y G_d(t, x − y) f(y)`, the series converging absolutely, with
`G_d(t, z) = (2π)^{−d} e^{−2idt} K_d(2t, z)`; in particular the solution is unique. The kernel formula of the free
discrete Schrödinger equation; for `d = 1` it is Stefanov–Kevrekidis, arXiv nlin/0409009, eq. (6), as cited in
`docs/statements.md`. -/
theorem latticeSchrodingerKernel : LatticeSchrodingerKernelStatement :=
  lsK_of lapOpFacts expSolutionFacts uniqueFacts kernelConvFacts

/-- **LS-D** (`LatticeSchrodingerDispersiveStatement`): the dispersive estimate
`|u(t)(x)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}} ‖f‖₁` for `ℓ¹` data and `t ≠ 0`, every `d`, with the explicit constant
`C* = 8(1 + √7)/3`. The `t^{−d/3}` rate is the classical one for the discrete Schrödinger group on `ℤ^d`
(Stefanov–Kevrekidis for `d = 1`); the explicit constant comes from TdE′ (`OscInt.API.hypercubicCubeRoot`). -/
theorem latticeSchrodingerDispersive : LatticeSchrodingerDispersiveStatement :=
  lsD_of latticeSchrodingerKernel kernelBoundFacts

/-- **LS-D′** (`LatticeSchrodingerDecayStatement`): decay at every real time,
`|u(t)(x)| ≤ (1 + τ)^{d/3} (1 + |t|)^{−d/3} ‖f‖₁` with `τ = (C*/(2π))³/2 ≈ 1.852`, every `d`; LS-D for `t ≠ 0`, and
`u(0) = f` at `t = 0`. -/
theorem latticeSchrodingerDecay : LatticeSchrodingerDecayStatement :=
  lsDp_of latticeSchrodingerDispersive envelopeFacts

end OscInt.API
