/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.LatticeGroup
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Batch LS, part P-stencil: the stencil powers of the lattice Laplacian

Route `docs/proof-LS.md`; interfaces `Blueprint/LatticeGroup.lean`. Proves `StencilFacts`.

Provenance: drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in `docs/prior_art.md`, batch LS)
and made to elaborate by the lead's proof agents with mechanical fixes only (no change of route, statement or
lemma), recorded in `review/2026-11-14-external-R4-answers.md`.
-/

namespace OscInt.LatticeStencilAux

open OscInt.Statements OscInt.Blueprint.LatticeGroup

noncomputable def lapMajorant (d : ℕ) (g : (Fin d → ℤ) → ℂ) (z : Fin d → ℤ) : ℝ :=
  ∑ j, (‖g (z + latticeUnit d j)‖ + ‖g (z - latticeUnit d j)‖ + 2 * ‖g z‖)

theorem shift_summable {d : ℕ} {g : (Fin d → ℤ) → ℝ} (hg : Summable g)
    (e : Fin d → ℤ) : Summable (fun z => g (z + e)) ∧ Summable (fun z => g (z - e)) := by
  -- Equiv.summable_iff reindexes both translations bijectively.
  exact ⟨(Equiv.addRight e).summable_iff.mpr hg,
    (Equiv.subRight e).summable_iff.mpr hg⟩

theorem lapMajorant_summable {d : ℕ} {g : (Fin d → ℤ) → ℂ}
    (hg : Summable (fun z => ‖g z‖)) : Summable (lapMajorant d g) := by
  -- summable_sum combines finitely many absolutely summable shifts.
  exact summable_sum fun j _ =>
    ((shift_summable hg (latticeUnit d j)).1.add
      (shift_summable hg (latticeUnit d j)).2).add (hg.mul_left 2)

theorem lapMajorant_tsum {d : ℕ} {g : (Fin d → ℤ) → ℂ}
    (hg : Summable (fun z => ‖g z‖)) :
    ∑' z, lapMajorant d g z = 4 * d * ∑' z, ‖g z‖ := by
  -- The finite coordinate sum commutes with the absolutely convergent site sum.
  simp only [lapMajorant]
  rw [Summable.tsum_finsetSum (fun j _ =>
    ((shift_summable hg (latticeUnit d j)).1.add
      (shift_summable hg (latticeUnit d j)).2).add (hg.mul_left 2))]
  have heach : ∀ j : Fin d,
      (∑' z, (‖g (z + latticeUnit d j)‖ + ‖g (z - latticeUnit d j)‖ + 2 * ‖g z‖)) =
        4 * ∑' z, ‖g z‖ := by
    intro j
    obtain ⟨hp, hm⟩ := shift_summable hg (latticeUnit d j)
    rw [(hp.add hm).tsum_add (hg.mul_left 2), hp.tsum_add hm, tsum_mul_left]
    have hplus := (Equiv.addRight (latticeUnit d j)).tsum_eq (fun z => ‖g z‖)
    have hminus := (Equiv.addRight (-latticeUnit d j)).tsum_eq (fun z => ‖g z‖)
    change (∑' z, ‖g (z + latticeUnit d j)‖) = _ at hplus
    change (∑' z, ‖g (z + -latticeUnit d j)‖) = _ at hminus
    rw [hplus]
    simp only [sub_eq_add_neg] at hminus ⊢
    rw [hminus]
    ring
  simp_rw [heach]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem lap_norm_le_majorant {d : ℕ} (g : (Fin d → ℤ) → ℂ) (z : Fin d → ℤ) :
    ‖latticeLaplacian d g z‖ ≤ lapMajorant d g z := by
  -- norm_sum_le, norm_sub_le, norm_add_le give the pointwise majorant.
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h := (norm_sub_le (g (z + latticeUnit d j) + g (z - latticeUnit d j)) (2 * g z)).trans
    (add_le_add_left (norm_add_le _ _) _)
  norm_num [norm_mul] at h
  exact h

theorem lap_l1 {d : ℕ} {g : (Fin d → ℤ) → ℂ}
    (hg : Summable (fun z => ‖g z‖)) :
    Summable (fun z => ‖latticeLaplacian d g z‖) ∧
      ∑' z, ‖latticeLaplacian d g z‖ ≤ 4 * d * ∑' z, ‖g z‖ := by
  have hm := lapMajorant_summable hg
  have hs := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (lap_norm_le_majorant g) hm
  refine ⟨hs, ?_⟩
  -- Summable.tsum_le_tsum turns the pointwise majorant into the l1 operator bound.
  exact (hs.tsum_le_tsum (lap_norm_le_majorant g) hm).trans_eq (lapMajorant_tsum hg)

theorem stencil_l1 (d n : ℕ) :
    Summable (fun z => ‖stencil d n z‖) ∧ ∑' z, ‖stencil d n z‖ ≤ (4 * d) ^ n := by
  classical
  induction n with
  | zero =>
      -- The zero stencil is one actual Kronecker mass, not a hypothesis.
      simp only [stencil, apply_ite norm, norm_one, norm_zero]
      exact ⟨(hasSum_ite_eq 0 1).summable, by rw [tsum_ite_eq]; simp⟩
  | succ n ih =>
      obtain ⟨hs, hb⟩ := lap_l1 ih.1
      refine ⟨hs, hb.trans ?_⟩
      calc 4 * d * (∑' z, ‖stencil d n z‖) ≤ 4 * d * (4 * d) ^ n :=
          mul_le_mul_of_nonneg_left ih.2 (by positivity)
        _ = (4 * d) ^ (n + 1) := by ring

theorem convolution_norm_summable {d : ℕ} {g : (Fin d → ℤ) → ℂ}
    (hg : Summable (fun z => ‖g z‖)) (f : LatticeL2 d) (x : Fin d → ℤ) :
    Summable (fun y => ‖g (x - y) * f y‖) := by
  have hs : Summable (fun y => ‖g (x - y)‖) := (Equiv.subLeft x).summable_iff.mpr hg
  -- lp.norm_apply_le_norm is used with p=2 explicitly.
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_) (hs.mul_right ‖f‖)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) f y) (norm_nonneg _)

theorem convolution_norm_bound {d : ℕ} {g : (Fin d → ℤ) → ℂ}
    (hg : Summable (fun z => ‖g z‖)) (f : LatticeL2 d) (x : Fin d → ℤ) :
    ∑' y, ‖g (x - y) * f y‖ ≤ (∑' z, ‖g z‖) * ‖f‖ := by
  have hs : Summable (fun y => ‖g (x - y)‖) := (Equiv.subLeft x).summable_iff.mpr hg
  have hb : ∀ y, ‖g (x - y) * f y‖ ≤ ‖g (x - y)‖ * ‖f‖ := by
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) f y) (norm_nonneg _)
  have h := (convolution_norm_summable hg f x).tsum_le_tsum hb (hs.mul_right ‖f‖)
  have hsub := (Equiv.subLeft x).tsum_eq (fun z => ‖g z‖)
  simp only [Equiv.subLeft_apply] at hsub
  rw [tsum_mul_right, hsub] at h
  exact h

theorem stencil_succ_mul (d n : ℕ) (f : LatticeL2 d) (x y : Fin d → ℤ) :
    stencil d (n + 1) (x - y) * f y =
      ∑ j, (stencil d n ((x + latticeUnit d j) - y) * f y +
        stencil d n ((x - latticeUnit d j) - y) * f y -
          2 * (stencil d n (x - y) * f y)) := by
  -- Translation identities are proved in the additive lattice, before multiplication.
  have hp : ∀ e : Fin d → ℤ, x - y + e = x + e - y := fun e => by abel
  have hm : ∀ e : Fin d → ℤ, x - y - e = x - e - y := fun e => by abel
  simp only [stencil, latticeLaplacian, Finset.sum_mul, add_mul, sub_mul, hp, hm, mul_assoc]

theorem stencil_convolution (d : ℕ) (A : LatticeL2 d →L[ℂ] LatticeL2 d)
    (hA : ∀ (g : LatticeL2 d) (x : Fin d → ℤ),
      A g x = latticeLaplacian d (fun y => g y) x) (n : ℕ) :
    ∀ (f : LatticeL2 d) (x : Fin d → ℤ),
      (A ^ n) f x = ∑' y, stencil d n (x - y) * f y := by
  classical
  induction n with
  | zero =>
      intro f x
      -- tsum_ite_eq singles out y=x; sub_eq_zero fixes the subtraction orientation.
      simp [stencil, sub_eq_zero]
  | succ n ih =>
      intro f x
      have hs (x' : Fin d → ℤ) := (convolution_norm_summable (stencil_l1 d n).1 f x').of_norm
      rw [pow_succ', mul_apply_eq_comp, hA, latticeLaplacian]
      simp_rw [ih, stencil_succ_mul]
      rw [Summable.tsum_finsetSum (fun j _ =>
        ((hs (x + latticeUnit d j)).add (hs (x - latticeUnit d j))).sub ((hs x).mul_left 2))]
      apply Finset.sum_congr rfl
      intro j _
      rw [((hs (x + latticeUnit d j)).add (hs (x - latticeUnit d j))).tsum_sub
        ((hs x).mul_left 2), (hs (x + latticeUnit d j)).tsum_add (hs (x - latticeUnit d j)),
        tsum_mul_left]

theorem stencilFacts : StencilFacts := by
  intro d A hA n
  refine ⟨stencil_l1 d n, ?_⟩
  intro f x
  exact ⟨convolution_norm_summable (stencil_l1 d n).1 f x,
    stencil_convolution d A hA n f x⟩

end OscInt.LatticeStencilAux
