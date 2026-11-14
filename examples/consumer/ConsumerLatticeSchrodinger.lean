/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: the time dependence of the lattice Schrödinger kernel (batch LS)

Only `import OscInt.API` and Mathlib. The sanity layer `OscInt/Front/LatticeGroupSanity.lean` proves, from LS-E and
LS-K taken as hypotheses, that `t ↦ G_1(t, x)` has derivative `iΔδ₀(x)` at `t = 0`. With LS-E and LS-K now proved,
those become unconditional facts about the kernel as defined (`schrodingerKernel`, with the gauge `e^{−2idt}` and the
time `2t` in `K_d`):
* `∂ₜG_1(0, 0) = −2i` (`kernel_deriv_origin`);
* `∂ₜG_1(0, e₁) = i` (`kernel_deriv_e1`), hence not `i/2` (`kernel_deriv_e1_ne_half`).

What these pin, by hand computation (not compiled): with `K_1(t, ·)` in place of `K_1(2t, ·)` the derivative at `e₁`
would be `i/2`, since `∫_{−π}^{π} cos k e^{ik} dk = π`; without the gauge the derivative at the origin would be `0`,
since `∫_{−π}^{π} cos k dk = 0`. The pre-proof answers deferred these unconditional pins to the proof of LS-K
(`review/2026-11-12-LS-pre-proof-answers.md`, referee A's finding 2); the post-proof adversarial review asked for them
(`review/2026-11-14-LS-post-proof-answers.md`, item 5).
-/

open OscInt.Statements OscInt.API OscInt.API.LatticeGroupSanity

/-- **Unconditional**: `∂ₜG_1(0, 0) = −2i`. -/
theorem kernel_deriv_origin : HasDerivAt (fun t => schrodingerKernel 1 t 0) (-2 * Complex.I) 0 :=
  kernel_deriv_zero_origin latticeSchrodingerExists latticeSchrodingerKernel

/-- **Unconditional**: `∂ₜG_1(0, e₁) = i`. -/
theorem kernel_deriv_e1 : HasDerivAt (fun t => schrodingerKernel 1 t (latticeUnit 1 0)) Complex.I 0 :=
  kernel_deriv_zero_e1 latticeSchrodingerExists latticeSchrodingerKernel

/-- **Unconditional**: the derivative at `e₁` is not `i/2`. -/
theorem kernel_deriv_e1_ne_half :
    ¬ HasDerivAt (fun t => schrodingerKernel 1 t (latticeUnit 1 0)) (Complex.I / 2) 0 := by
  intro h
  have h' : Complex.I / 2 = Complex.I := h.unique kernel_deriv_e1
  have : Complex.I = 0 := by linear_combination (-2 : ℂ) * h'
  exact Complex.I_ne_zero this
