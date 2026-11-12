/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Cusp
import OscInt.Cusp.Implicit4
import OscInt.D4.Basic
import OscInt.StationaryPhase.Local
import OscInt.StationaryPhase.Family

/-! Batch A3, P5: normalization by the A3 witness directions and subtraction of the affine part.
The cubic vanishing hypothesis is retained in the frozen input but is not used by this part.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`. -/

namespace OscInt.Cusp.NormalizeAux

open OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase
open OscInt.StationaryPhase.ImplicitAux
open scoped ContDiff

/-- A nonzero A3 numerator forces its kernel witness to be nonzero. -/
theorem witness_ne_zero {φ : ℝ × ℝ → ℝ} {v w : ℝ × ℝ}
    (hred : iteratedFDeriv ℝ 2 φ 0 ![w, w] * iteratedFDeriv ℝ 4 φ 0 ![v, v, v, v] -
      3 * iteratedFDeriv ℝ 3 φ 0 ![v, v, w] ^ 2 ≠ 0) : v ≠ 0 := by
  intro hv
  have h4 : iteratedFDeriv ℝ 4 φ 0 ![v, v, v, v] = 0 :=
    (iteratedFDeriv ℝ 4 φ 0).map_coord_zero (0 : Fin 4) (by simpa using hv)
  have h3 : iteratedFDeriv ℝ 3 φ 0 ![v, v, w] = 0 :=
    (iteratedFDeriv ℝ 3 φ 0).map_coord_zero (0 : Fin 3) (by simpa using hv)
  apply hred
  rw [h4, h3]
  ring

/-- Zero determinant with a nonzero column makes the other column a scalar multiple. -/
theorem exists_smul_of_det_eq_zero {v w : ℝ × ℝ} (hv : v ≠ 0)
    (hdet : v.1 * w.2 - v.2 * w.1 = 0) : ∃ r : ℝ, w = r • v := by
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hv2
      apply hv
      exact Prod.ext hv1 hv2
    have hw1 : w.1 = 0 := by
      have hm : v.2 * w.1 = 0 := by rw [hv1] at hdet; nlinarith
      exact (mul_eq_zero.mp hm).resolve_left hv2
    refine ⟨w.2 / v.2, ?_⟩
    apply Prod.ext
    · simp [hw1, hv1]
    · change w.2 = (w.2 / v.2) * v.2
      field_simp [hv2]
  · refine ⟨w.1 / v.1, ?_⟩
    apply Prod.ext
    · change w.1 = (w.1 / v.1) * v.1
      field_simp [hv1]
    · change w.2 = (w.1 / v.1) * v.2
      field_simp [hv1]
      nlinarith [hdet]

/-- The Hessian kernel and the nonzero transverse entry force the witness determinant to be nonzero. -/
theorem witness_det_ne_zero {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) {v w : ℝ × ℝ}
    (hv : v ≠ 0) (hker : ∀ z, iteratedFDeriv ℝ 2 φ 0 ![v, z] = 0)
    (hww : iteratedFDeriv ℝ 2 φ 0 ![w, w] ≠ 0) : v.1 * w.2 - v.2 * w.1 ≠ 0 := by
  intro hdet
  obtain ⟨r, hr⟩ := exists_smul_of_det_eq_zero hv hdet
  have hzero : dd φ 0 w w = 0 := by
    calc
      dd φ 0 w w = dd φ 0 w (r • v) := congrArg (dd φ 0 w) hr
      _ = r * dd φ 0 w v := by simp [dd]
      _ = 0 := by rw [dd_eq_iteratedFDeriv hφ (by norm_num), hker w, mul_zero]
  apply hww
  simpa only [dd_eq_iteratedFDeriv hφ (by norm_num)] using hzero

/-- The affine subtraction preserves the diagonal fourth derivative, by differentiating its `ddd` identity. -/
theorem normalize_four {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (k v : ℝ × ℝ) :
    iteratedFDeriv ℝ 4 (normalize φ) k ![v, v, v, v] =
      iteratedFDeriv ℝ 4 φ k ![v, v, v, v] := by
  obtain ⟨hN, -, -, -, h3, -⟩ := OscInt.D4.normalizeFacts φ hφ
  rw [← dddd_eq_iteratedFDeriv hN k v v v v, ← dddd_eq_iteratedFDeriv hφ k v v v v]
  simp only [dddd, h3]

/-- Transport the diagonal fourth derivative through the linear coordinate change. -/
theorem normalize_comp_four {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (v : ℝ × ℝ) :
    iteratedFDeriv ℝ 4 (fun k => normalize φ (L k)) 0 ![v, v, v, v] =
      iteratedFDeriv ℝ 4 φ 0 ![L v, L v, L v, L v] := by
  have hN := (OscInt.D4.normalizeFacts φ hφ).1
  have h := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => ℝ × ℝ) ℝ => A ![v, v, v, v])
    (FamilyAux.iteratedFDeriv_comp_affine hN (0 : ℝ × ℝ)
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (0 : ℝ × ℝ) (i := 4) (by norm_num))
  have hvec : (fun i : Fin 4 => L (![v, v, v, v] i)) = ![L v, L v, L v, L v] := by
    funext i
    fin_cases i <;> rfl
  have h' : iteratedFDeriv ℝ 4 (fun k => normalize φ (L k)) 0 ![v, v, v, v] =
      iteratedFDeriv ℝ 4 (normalize φ) 0 ![L v, L v, L v, L v] := by
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, map_zero, zero_add, hvec] using h
  exact h'.trans (normalize_four hφ 0 (L v))

/-- The ordered third directional derivative equals the mixed entry in the A3 invariant. -/
theorem ddd_eq_a3_entry {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (v w : ℝ × ℝ) :
    ddd φ 0 v v w = iteratedFDeriv ℝ 3 φ 0 ![v, v, w] := by
  have h3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_num)
  calc
    ddd φ 0 v v w = ddd φ 0 v w v := ddd_swap23 h3 0 v v w
    _ = ddd φ 0 w v v := ddd_swap12 h3 0 v w v
    _ = iteratedFDeriv ℝ 3 φ 0 ![v, v, w] := ddd_eq_iteratedFDeriv hφ (by norm_num) 0 w v v

/-- Normal-point identities in coordinates with the two prescribed A3 columns. -/
theorem normalPoint4_of_columns {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) {v w : ℝ × ℝ}
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (hLv : L (1, 0) = v) (hLw : L (0, 1) = w)
    (hker : ∀ z, iteratedFDeriv ℝ 2 φ 0 ![v, z] = 0)
    (hww : iteratedFDeriv ℝ 2 φ 0 ![w, w] ≠ 0)
    (hred : iteratedFDeriv ℝ 2 φ 0 ![w, w] * iteratedFDeriv ℝ 4 φ 0 ![v, v, v, v] -
      3 * iteratedFDeriv ℝ 3 φ 0 ![v, v, w] ^ 2 ≠ 0) :
    NormalPoint4 (fun k => normalize φ (L k)) := by
  obtain ⟨hN, -, hdf, hdd, hddd, -⟩ := OscInt.D4.normalizeFacts φ hφ
  have hd : ∀ u z, dd (fun k => normalize φ (L k)) 0 u z = dd φ 0 (L u) (L z) := by
    intro u z
    have h := LocalAux.dd_comp_affine (hN.of_le (by norm_num)) (0 : ℝ × ℝ)
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (0 : ℝ × ℝ) u z
    simpa [hdd] using h
  have ht : ∀ u z r, ddd (fun k => normalize φ (L k)) 0 u z r = ddd φ 0 (L u) (L z) (L r) := by
    intro u z r
    have h := LocalAux.ddd_comp_affine (hN.of_le (by norm_num)) (0 : ℝ × ℝ)
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (0 : ℝ × ℝ) u z r
    simpa [hddd] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := LocalAux.fderiv_comp_affine_apply (f := normalize φ) (0 : ℝ × ℝ)
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (0 : ℝ × ℝ) (0, 1)
      (hN.differentiable (by norm_num) _)
    simpa [hdf] using h
  · rw [hd, hLw, dd_eq_iteratedFDeriv hφ (by norm_num)]
    exact hww
  · rw [hd, hLw, hLv, dd_eq_iteratedFDeriv hφ (by norm_num)]
    exact hker w
  · rw [normalize_comp_four hφ L, ht, hd, hLv, hLw,
      dd_eq_iteratedFDeriv hφ (by norm_num), ddd_eq_a3_entry hφ]
    intro hz
    apply hred
    field_simp [hww] at hz
    nlinarith [hz]

end OscInt.Cusp.NormalizeAux

namespace OscInt.Cusp

open OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase NormalizeAux
open scoped ContDiff

/-- A3-P5: choose the A3 witness columns and subtract the affine part of the phase at the origin. -/
theorem a3Normalize : A3NormalizeFacts := by
  intro φ hφ hA
  obtain ⟨v, w, hker, hww, _hcubic, hred⟩ := hA
  have h4 : ContDiff ℝ 4 φ := hφ.of_le (by simp)
  obtain ⟨L, hLv, hLw⟩ := LocalAux.exists_equiv_cols v w
    (witness_det_ne_zero h4 (witness_ne_zero hred) hker hww)
  refine ⟨L, ?_⟩
  change NormalPoint4 (fun k => normalize φ (L k))
  exact normalPoint4_of_columns h4 L hLv hLw hker hww hred

end OscInt.Cusp
