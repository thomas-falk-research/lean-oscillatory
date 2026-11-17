/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.HadamardWalkAssembly
import OscInt.Front.HadamardWalkKernelRec
import OscInt.Front.HadamardWalkPhase
import OscInt.Front.HadamardWalkKernelBound
import OscInt.Front.HadamardWalkLinear

/-!
# Batch HW: the final theorems

Route `docs/proof-HW.md` (read by one route referee, an AI agent of the lead's model family; "Parts as integrated"); assembly `OscInt/Front/HadamardWalkAssembly.lean`; parts
`OscInt/Front/HadamardWalkKernelRec.lean` (the kernel at times `0`, `1` and its recursion),
`OscInt/Front/HadamardWalkPhase.lean` (the derivative chain of the dispersion relation with its two lower bounds;
the amplitude and its variation on four arcs), `OscInt/Front/HadamardWalkKernelBound.lean` (HW-K, from the proved
second- and third-derivative van der Corput bounds S1.2 and S1.3 on four arcs) and
`OscInt/Front/HadamardWalkLinear.lean` (the arithmetic of HW-D; linearity and translation invariance of the walk).
The rate `t^{−1/3}` and the argument are known, with implicit constants in print (`docs/prior_art.md`, batch HW);
the constants here are explicit and far from sharp (`docs/statements.md`, batch HW, choice 3 and clarification b).
Nothing here is claimed as new mathematics.
-/

namespace OscInt.API

open OscInt.Statements OscInt.HadamardWalkAux

/-- **HW-R** (`HadamardKernelStatement`): the Hadamard walk on `ℤ` from the point state `(a, b)`, after `t + 1` steps,
is `((a + b)/√2 · K(t+1, x+1) + a K(t, x), (a − b)/√2 · K(t+1, x−1) + b K(t, x))` with the scalar kernel `K`. -/
theorem hadamardKernelFormula : HadamardKernelStatement := hadamardKernelFormula_of hadamardKernelRecFacts

/-- **HW-K** (`HadamardKernelBoundStatement`): `|K(t, x)| ≤ 7 t^{−1/2} + 12 t^{−1/3}` for `t ≥ 1` and every site `x`. -/
theorem hadamardKernelBound : HadamardKernelBoundStatement :=
  hadamardKernelBound_of hadamardPhaseFacts hadamardAmplitudeFacts

/-- **HW-D** (`HadamardDecayStatement`): for `t ≥ 1`, each component of the walk from the point state `(a, b)` has
modulus at most `39 (|a| + |b|) t^{−1/3}` at every site. -/
theorem hadamardDecay : HadamardDecayStatement :=
  hadamardDecay_of hadamardKernelRecFacts hadamardKernelFormula hadamardKernelBound hadamardDecayArithFacts

/-- **HW-L** (`HadamardDispersiveStatement`): for an initial state of finite support and `t ≥ 1`, each component of
the walk has modulus at most `39 t^{−1/3} ∑ (|ψ₀,₁(y)| + |ψ₀,₂(y)|)` at every site. -/
theorem hadamardDispersive : HadamardDispersiveStatement := hadamardDispersive_of hadamardDecay hadamardLinearFacts

end OscInt.API
