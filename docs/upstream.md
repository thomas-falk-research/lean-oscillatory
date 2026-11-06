# Upstream candidates

Lemmas that would join Mathlib, with the target file. None exist yet (M2 produces them). Each needs conversion to
Mathlib's module syntax (`module`, `public import`) before a pull request; OscInt files are plain files (see
`docs/toolchain.md`). No pull request is opened without the owner's go.

| Lemma | Target Mathlib file | Branch | Status |
|---|---|---|---|
| `OscInt.StationaryPhase.ChangeAux.integral_comp_continuousLinearEquiv` (∫ f(Lx) dμ = abs(det L)⁻¹ ∫ f dμ, add-Haar μ, no integrability) | `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean` | — | proved (G2), not yet upstream-polished |
| `OscInt.StationaryPhase.ChangeAux.norm_iteratedFDeriv_mul_le_of_forall_le` (uniform Leibniz bound 2ⁿ·B·M) | `Mathlib/Analysis/Calculus/ContDiff/Bounds.lean` | — | proved (G2) |
| `OscInt.StationaryPhase.ChangeAux.exists_forall_norm_iteratedFDeriv_le` (Cⁿ with compact support ⇒ one bound for all derivatives ≤ n) | `Mathlib/Analysis/Calculus/ContDiff/Bounds.lean` | — | proved (G2) |
| `OscInt.StationaryPhase.FamilyAux.norm_iteratedFDeriv_comp_affine_le` (‖Dⁱ(f ∘ (a + L·))‖ ≤ ‖Dⁱf‖‖L‖ⁱ; Mathlib has only the isometry version) | `Mathlib/Analysis/Calculus/ContDiff/Bounds.lean` | — | proved (G1) |
| `OscInt.StationaryPhase.FamilyAux.continuous_iteratedFDeriv_comp_affine`, `continuous_iteratedFDeriv_add` (jointly continuous derivatives of parametrised families) | new file `Mathlib/Analysis/Calculus/ContDiff/Parametric.lean` | — | proved (G1) |
| `OscInt.StationaryPhase.PartitionAux.exists_smooth_partition_compact` (finite C^∞ partition of unity with compact supports on a finite-dimensional space) | `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` (normed-space corollary) | — | proved (G3) |
| `OscInt.StationaryPhase.PartitionAux.contDiff_omega_hasCompactSupport_eq_zero` (compactly supported analytic ⇒ 0) | `Mathlib/Analysis/Analytic/Uniqueness.lean` | — | proved (G3) |
