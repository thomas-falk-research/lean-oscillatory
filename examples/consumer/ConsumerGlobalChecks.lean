/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.API

/-!
# Consumer checks: every batch-GD theorem applied to concrete data

Answers the post-proof referees (A and B, MINOR: GD-C, GD-F, GD-N and T1 were applied to concrete data only through
the conditional sanity theorems). Each line below feeds the *proved* theorem into a sanity theorem of
`OscInt/Front/GlobalSanity.lean`, whose data (the elliptic and hyperbolic umbilics, a translate with its D4 point at
`(1, 1)`, a D4 point outside `K`, a critical-points-only datum, a fold, a mixed quadratic, `m^{-1/2}`, the torus
moments, the lattice kernel) discharge every hypothesis, so each conclusion is a statement about that data.
Compiled by `make quick`.
-/

open OscInt.API OscInt.API.GlobalSanity

namespace ConsumerGlobalChecks

example := globalDecay_ell globalDecay
example := globalDecay_hyp globalDecay
example := globalDecay_hyp_offK globalDecay
example := globalDecay_hypShift globalDecay
example := globalDecayCrit_ell globalDecayCrit
example := globalDecayCrit_hyp globalDecayCrit
example := globalDecayCrit_hyp_crit globalDecayCrit
example := globalFold_fold globalFold
example := globalNondeg_quad globalNondeg
example := sharpness_sqrt sharpness
example := torusUnfold_moments torusUnfold
example := latticeLaplacianDecay_diag latticeLaplacianDecay
example := latticeLaplacian_sharp_all sharpness latticeLaplacianLimit

end ConsumerGlobalChecks
