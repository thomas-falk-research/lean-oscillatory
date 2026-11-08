/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.Core
import OscInt.Front.Convert
import OscInt.Front.ConvertSanity
import OscInt.Front.Poly
import OscInt.Front.Sanity
import OscInt.Front.Examples
import OscInt.Front.FamilySanity
import OscInt.Front.FamilySanity2
import OscInt.Front.FamilyC10
import OscInt.Front.Local
import OscInt.Front.GlobalSanity
import OscInt.Front.LatticeExplicitSanity
import OscInt.Front.GlobalNondegLocalSanity
import OscInt.Front.GlobalFinal
import OscInt.Front.LatticeFinal
import OscInt.Front.LatticeExplicitFinal

/-!
# OscInt public API

Import this file: it imports every final theorem of OscInt and declares nothing itself (implementation files live
under `OscInt/Front/`, so that no module except the root has submodules: `leanchecker M` replays every module whose
name starts with `M`, in parallel, lessons 30). `tools/check_entry_point.sh` checks that this import exposes every
statement and proving theorem of `stamps/statements.json`. Every theorem in the table below has, as its type, a
statement constant that was frozen, stamped and blind-reviewed (`stamps/statements.json`, `docs/statements.md`); the
S1–S4 theorems keep their names in `OscInt`, and the front-end theorems F1 and F2 are proved here from them by short
bridge lemmas (`d4Constant_eq_closed` is such a helper; its type is not a frozen statement). For S1–S4 the statement
was reviewed before any proof existed; for F1 and F2 the bridge proofs were drafted before the statements were
stamped and reviewed, so that claim is not made for them (process note in `docs/statements.md`, "Front end, batch 1");
for batch 2 see the clarification of 2026-11-07 there.

| Name | Statement | Textbook form |
|---|---|---|
| `OscInt.vanDerCorput_one/two/three` | S1.1–S1.3 | van der Corput's lemma with amplitude, constants c₁ = 3, c₂ = 8, c₃ = 18, i.e. Stein's c_k = 5·2^{k−1} − 2 (E. M. Stein, *Harmonic Analysis*, 1993, Ch. VIII §1) |
| `OscInt.nonStationary` | S2.1 | non-stationary phase, O(m^{−N}) (Stein, Ch. VIII §2), uniform over compact families and linear terms |
| `OscInt.stationaryPhase` | S2.2 | the stationary-phase bound O(m^{−n/2}) for n = 2 (Hörmander, *ALPDO I*, §7.7; Stein, Ch. VIII §2), uniform in the linear term |
| `OscInt.fold` | S3 | the uniform fold (A₂) estimate O(m^{−5/6}) (Arnold–Gusein-Zade–Varchenko, *Singularities of Differentiable Maps II*; Duistermaat 1974) |
| `OscInt.d4Bound`, `OscInt.d4BoundNe` | S4.1, S4.1′ | the uniform D4 (umbilic) estimate O(t^{−2/3}) (oscillation index −2/3 of D4, AGV II) |
| `OscInt.d4Limit`, `OscInt.d4ConstantPos`, `OscInt.d4ConstantClosedForm` | S4.2–S4.4 | the D4 leading term t^{2/3}∫e^{itφ}A → c_C A(0), c_C > 0, and c_C = Γ(1/3)²/(√3 \|Disc\|^{1/6}) for Disc < 0, Γ(1/3)²/Disc^{1/6} for Disc > 0 |
| `OscInt.API.ampBoundOfContDiff` | F1 | a Cⁿ function with compact support has bounded derivatives |
| `OscInt.API.d4LimitClosedForm` | F2 | the D4 leading term with the closed-form constant, for one C² amplitude (S4.2 ∧ S4.4 ∧ F1) |
| `OscInt.API.dd_iteratedFDeriv`, `ddd_iteratedFDeriv`, `hessDet_eq_det`, `cubicCoeffs_eq` | C1–C4 | the nested directional derivatives, the Hessian determinant and the cubic part in Mathlib's `iteratedFDeriv` and `Matrix.det` (symmetry of iterated derivatives of C^k functions) |
| `OscInt.API.disc_eq_cubic_discr`, `disc_ne_zero_iff_isolated` | C5, C6 | `disc` is Mathlib's `Cubic.discr`; a binary cubic has an isolated critical point at 0 iff its discriminant is nonzero |
| `OscInt.API.foldOrNondeg_iff`, `foldOrNondeg_of_hasFDeriv` | C7, C7′ | the fold-or-nondegenerate condition as "det ≠ 0, or rank one with third derivative nonzero along the kernel" (matrix kernel/rank form; from `HasFDerivAt` data) |
| `OscInt.API.gradLower_iff`, `ampBound_conv` | C8, C9 | gradient lower bounds in the Euclidean and max norms; amplitude bounds ↔ `ContDiff` with compact support |
| `OscInt.API.nonStationaryFE`, `stationaryPhaseFE`, `foldFE`, `d4BoundFE` | FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′ | S2.1, S2.2, S3, S4.1′ for one phase in Mathlib's idiom (`ContDiff`, `tsupport`, `iteratedFDeriv` bounds, linear terms as functionals) |
| `OscInt.API.Poly.*` (helpers, not statements) | P2 | derivative data of explicit polynomial phases from `ring` identities (`examples/consumer/ConsumerFormula.lean`) |

The textbook references say which classical statement each formalises; they are given at chapter level from the
author's knowledge of the literature and were not re-checked against the books when this file was written (a human
expert review of the statements is an open owner item, ROADMAP §6); the precise Lean hypotheses (derivatives
continuous up to the endpoints, amplitude bounds `AmpBound`, the fold condition on all of K, …) are in
`docs/statements.md`, and what they add or omit relative to the textbooks is recorded there and in `docs/STATUS.md`.
-/
