/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.PeriodicAnalyticAssembly
import OscInt.Front.PeriodicAnalyticShift
import OscInt.Front.PeriodicAnalyticSeries
import OscInt.Front.PeriodicAnalyticAlias

/-!
# Batch PA: the final theorems

Route `docs/proof-PA.md` (refereed; revision section); assembly `OscInt/Front/PeriodicAnalyticAssembly.lean`; parts
`OscInt/Front/PeriodicAnalyticShift.lean` (contour shift), `OscInt/Front/PeriodicAnalyticSeries.lean` (pointwise
Fourier series) and `OscInt/Front/PeriodicAnalyticAlias.lean` (alias bound; the kernel integrand). The mathematics is
classical: PA-T is Theorem 3.2 of Trefethen and Weideman (SIAM Review 56, 2014), in essence Davis (1959); LC-1 is a
Kapteyn/Siegel-type bound for Bessel functions of integer order (`docs/prior_art.md`).
-/

namespace OscInt.API

open OscInt.Statements OscInt.PeriodicAnalyticAux

/-- **PA-C** (`FourierCoeffStripStatement`): for `v` holomorphic, `2π`-periodic and bounded by `M` on the strip
`|Im z| < a`, `|∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}` for every integer `k`. Contour shift, then `b ↑ a`. -/
theorem fourierCoeffStrip : FourierCoeffStripStatement := fourierCoeffStrip_of contourShiftFacts

/-- **PA-T** (`TrapezoidalRuleStatement`): the `N`-point trapezoidal rule for such a `v` has error at most
`4πM / (e^{aN} − 1)` (Trefethen–Weideman 2014, Theorem 3.2). PA-C, the pointwise Fourier series and aliasing. -/
theorem trapezoidalRule : TrapezoidalRuleStatement :=
  trapezoidalRule_of fourierCoeffStrip fourierSeriesFacts aliasBoundFacts

/-- **LC-1** (`LatticeKernel1LightConeStatement`): `|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}` for the 1D lattice kernel,
every real `t`, integer `n` and `η ≥ 0`: outside the light cone `|n| > |t|` the kernel is exponentially small.
PA-C applied to `z ↦ e^{it cos z}`. -/
theorem latticeKernel1LightCone : LatticeKernel1LightConeStatement :=
  latticeKernel1LightCone_of fourierCoeffStrip kernelIntegrandFacts

end OscInt.API
