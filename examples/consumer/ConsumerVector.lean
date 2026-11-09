/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer example: vector-valued amplitudes (batch VT)

Only `import OscInt.API` and Mathlib. The proved theorems GD-C-V, GD-V, GD-F-V, GD-N-V applied on closed data through the
sanity theorems: matrix-valued, `ℂ²`-valued, bounded-sequence-valued amplitudes, and one constant for every `ℂⁿ`.
-/

open OscInt.API OscInt.API.VectorSanity

example := globalNondeg_of_vec globalNondegVec
example := globalNondeg_matrix globalNondegVec
example := globalNondeg_bounded globalNondegVec
example := globalNondeg_uniform_dim globalNondegVec
example := globalFold_pair globalFoldVec
example := globalDecay_pair globalDecayVec
example := globalDecayCrit_pair globalDecayCritVec
