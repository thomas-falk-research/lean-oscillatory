/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Front.LatticeExplicitAssembly
import OscInt.VanDerCorput.Final

/-!
# Batch LE: the parts (route `docs/proof-LE.md`)

P-angle, P-vdc2 (from the frozen and proved S1.2, `OscInt.vanDerCorput_two`), P-vdc3 (from S1.3,
`OscInt.vanDerCorput_three`), and T6F (Fubini on the box).
-/

namespace OscInt.LatticeExplicitAux

open Set OscInt.Statements OscInt.Blueprint

/-- `2^{−1/2} = √2/2`. -/
theorem two_rpow_neg_half : (2 : ℝ) ^ (-(1 : ℝ) / 2) = √2 / 2 := by
  rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : √2 ≠ 0 := by positivity
  field_simp
  linarith

/-- **P-angle** -/
theorem leAngle : LEAngleFacts := by
  intro x hx
  have h1 : Real.cos (Real.pi / 4) ≤ Real.cos |x| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) hx
  rw [Real.cos_abs, Real.cos_pi_div_four] at h1
  rw [two_rpow_neg_half]
  exact h1

theorem hasDerivOn_tcos (t a b : ℝ) :
    HasDerivOn (fun k => t * Real.cos k) (fun k => t * -Real.sin k) a b :=
  ⟨(by fun_prop : Continuous fun k => t * Real.cos k).continuousOn,
    fun x _ => (Real.hasDerivAt_cos x).const_mul t⟩

theorem hasDerivOn_tnsin (t a b : ℝ) :
    HasDerivOn (fun k => t * -Real.sin k) (fun k => t * -Real.cos k) a b :=
  ⟨(by fun_prop : Continuous fun k => t * -Real.sin k).continuousOn,
    fun x _ => (Real.hasDerivAt_sin x).neg.const_mul t⟩

theorem hasDerivOn_tncos (t a b : ℝ) :
    HasDerivOn (fun k => t * -Real.cos k) (fun k => t * - -Real.sin k) a b :=
  ⟨(by fun_prop : Continuous fun k => t * -Real.cos k).continuousOn,
    fun x _ => (Real.hasDerivAt_cos x).neg.const_mul t⟩

/-- The oscillatory integral of S1 with `φ = t cos`, `ψ = 1` and linear term `ξ` is the piece of `latticeKernel1`. -/
theorem oscInt_tcos (t ξ a b : ℝ) :
    oscInt (fun x => (fun k => t * Real.cos k) x + ξ * x) (fun _ => (1 : ℂ)) a b =
      ∫ k in a..b, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I) := by
  simp [oscInt]

/-- **P-vdc2** -/
theorem lePiece2 : LEPiece2Facts := by
  intro t ξ a b ht hab hcos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hμ : 0 < t * (2 : ℝ) ^ (-(1 : ℝ) / 2) := mul_pos ht h2
  have hv := OscInt.vanDerCorput_two _ _ _ _ _ a b _ ξ hab hμ (hasDerivOn_tcos t a b) (hasDerivOn_tnsin t a b)
    (fun x hx => by
      rw [abs_mul, abs_neg, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hcos x hx) ht.le)
    (sanity_amplitude_one a b).1
  rw [(sanity_amplitude_one a b).2, mul_one, oscInt_tcos] at hv
  refine hv.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, Real.mul_rpow ht.le h2.le, ← Real.rpow_mul (by norm_num)]
  have e1 : t ^ (-(1 : ℝ) / 2) = (t ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg ht.le]; ring_nf
  have e2 : (2 : ℝ) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ (-(1 : ℝ) / 2 * (1 / 2)))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; ring_nf
  have p1 : 0 < t ^ ((1 : ℝ) / 2) := by positivity
  have p2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 2 * (1 / 2)) := by positivity
  rw [e1, e2]
  field_simp

/-- **P-vdc3** -/
theorem lePiece3 : LEPiece3Facts := by
  intro t ξ a b ht hab hsin
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hμ : 0 < t * (2 : ℝ) ^ (-(1 : ℝ) / 2) := mul_pos ht h2
  have hv := OscInt.vanDerCorput_three _ _ _ _ _ _ a b _ ξ hab hμ (hasDerivOn_tcos t a b)
    (hasDerivOn_tnsin t a b) (hasDerivOn_tncos t a b)
    (fun x hx => by
      rw [neg_neg, abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hsin x hx) ht.le)
    (sanity_amplitude_one a b).1
  rw [(sanity_amplitude_one a b).2, mul_one, oscInt_tcos] at hv
  refine hv.trans (le_of_eq ?_)
  rw [Real.mul_rpow ht.le h2.le, ← Real.rpow_mul (by norm_num)]
  norm_num
  ring

/-- **T6F** The 2D kernel factorises (Fubini on the box). -/
theorem t6f : LatticeKernelFactorStatement := by
  intro t x
  have e : ∀ k : ℝ × ℝ,
      Complex.exp (↑(t * (Real.cos k.1 + Real.cos k.2) + ((x.1 : ℝ) * k.1 + (x.2 : ℝ) * k.2)) * Complex.I) =
        Complex.exp (↑(t * Real.cos k.1 + (x.1 : ℝ) * k.1) * Complex.I) *
          Complex.exp (↑(t * Real.cos k.2 + (x.2 : ℝ) * k.2) * Complex.I) := by
    intro k; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold latticeKernel latticeKernel1 torusBox
  simp_rw [e]
  rw [MeasureTheory.Measure.volume_eq_prod]
  refine (MeasureTheory.setIntegral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    (fun k : ℝ => Complex.exp (↑(t * Real.cos k + (x.1 : ℝ) * k) * Complex.I))
    (fun k : ℝ => Complex.exp (↑(t * Real.cos k + (x.2 : ℝ) * k) * Complex.I)) _ _).trans ?_
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hp, ← intervalIntegral.integral_of_le hp]

end OscInt.LatticeExplicitAux
