/-
Copyright (c) 2025 Joris Roos. All rights reserved.
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Manasa Praveen, Thomas Falk III
Modified 2026 by Thomas Falk III: extends OscInt.VanDerCorput, which is derived from roos-j/lean-oscillatory; the proof
text was drafted with an external AI tool and integrated with fixes (provenance in the module docstring).
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.Cusp
import OscInt.VanDerCorput.Final

/-!
# Order-four van der Corput with amplitude

The proof extends the split-and-transfer argument in `OscInt.VanDerCorput.Higher` and
`OscInt.VanDerCorput.Assembly`; those files attribute the route to J. Roos and M. Praveen.
The order-four bound here is obtained directly from the existing order-three plain bound.

Provenance: the proof text was drafted with an external reviewer's AI tool (OpenAI; AI-use disclosure in
`docs/prior_art.md`, batch A3) and integrated by the lead with elaboration fixes, recorded in
`review/2026-11-12-A3-packet-answers.md`.
-/

namespace OscInt.Cusp.VdC4Aux

open Set MeasureTheory Complex OscInt.Statements OscInt.Blueprint
open OscInt.VanDerCorput.HigherAux

/-- The two outer cubic bounds and the middle interval give coefficient 38. -/
lemma constant_four {μ : ℝ} (hμ : 0 < μ) :
    2 * μ ^ (-(1 : ℝ) / 4) +
      2 * (18 * (μ * μ ^ (-(1 : ℝ) / 4)) ^ (-(1 : ℝ) / 3)) =
      38 * μ ^ (-(1 : ℝ) / 4) := by
  have hpower : (μ * μ ^ (-(1 : ℝ) / 4)) ^ (-(1 : ℝ) / 3) =
      μ ^ (-(1 : ℝ) / 4) := by
    rw [Real.mul_rpow (le_of_lt hμ) (Real.rpow_nonneg (le_of_lt hμ) _),
      ← Real.rpow_mul (le_of_lt hμ), ← Real.rpow_add hμ]
    norm_num
  rw [hpower]
  ring

/-- Split the third derivative, then apply the existing cubic estimate on each far interval. -/
lemma plain_four (hS : SplitFacts) (h3 : VdC3PlainFacts)
    (φ φ₁ φ₂ φ₃ φ₄ : ℝ → ℝ) (a b μ : ℝ) (hab : a ≤ b) (hμ : 0 < μ)
    (hφ : HasDerivOn φ φ₁ a b) (hφ₁ : HasDerivOn φ₁ φ₂ a b)
    (hφ₂ : HasDerivOn φ₂ φ₃ a b) (hφ₃ : HasDerivOn φ₃ φ₄ a b)
    (hlow : ∀ x ∈ Ioo a b, μ ≤ |φ₄ x|) :
    ‖∫ x in a..b, Complex.exp (↑(φ x) * Complex.I)‖ ≤
      38 * μ ^ (-(1 : ℝ) / 4) := by
  obtain ⟨-, d, hd, hdist⟩ := hS φ₃ φ₄ a b μ hab hμ hφ₃ hlow
  have hr : 0 < μ ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hμ _
  rw [← constant_four hμ]
  refine split_bound φ a b d _ _ hab hd (le_of_lt hr) hφ.1 ?_
  intro s t has hst htb hfar
  refine h3 φ φ₁ φ₂ φ₃ s t _ hst (mul_pos hμ hr)
    (hasDerivOn_mono hφ has htb) (hasDerivOn_mono hφ₁ has htb)
    (hasDerivOn_mono hφ₂ has htb) ?_
  intro x hx
  have hxI : x ∈ Icc a b := ⟨le_trans has (le_of_lt hx.1), le_trans (le_of_lt hx.2) htb⟩
  exact le_trans (mul_le_mul_of_nonneg_left (hfar x hx) (le_of_lt hμ)) (hdist x hxI)

/-- Shift the order-one derivative by the linear coefficient and transfer the plain bound to the amplitude. -/
lemma with_amplitude (hS : SplitFacts) (h3 : VdC3PlainFacts)
    (hA : AmplitudeTransferFacts) : VdC4Facts := by
  intro D ψ ψ' a b μ p hab hμ hD hlow hψ
  have hD₀ : HasDerivOn (D 0) (D 1) a b := hD 0 (by norm_num)
  have hD₁ : HasDerivOn (D 1) (D 2) a b := hD 1 (by norm_num)
  have hD₂ : HasDerivOn (D 2) (D 3) a b := hD 2 (by norm_num)
  have hD₃ : HasDerivOn (D 3) (D 4) a b := hD 3 (by norm_num)
  have hφp := OscInt.VanDerCorput.HasDerivOn.add_linear hD₀ p
  refine hA _ ψ ψ' a b (38 * μ ^ (-(1 : ℝ) / 4)) hab (by positivity)
    hφp.1 hψ fun y hy => ?_
  exact plain_four hS h3 _ _ (D 2) (D 3) (D 4) a y μ hy.1 hμ
    (OscInt.VanDerCorput.HasDerivOn.mono hφp le_rfl hy.2)
    (OscInt.VanDerCorput.HasDerivOn.mono
      (OscInt.VanDerCorput.HasDerivOn.add_const hD₁ p) le_rfl hy.2)
    (OscInt.VanDerCorput.HasDerivOn.mono hD₂ le_rfl hy.2)
    (OscInt.VanDerCorput.HasDerivOn.mono hD₃ le_rfl hy.2)
    (fun x hx => hlow x (Ioo_subset_Ioo le_rfl hy.2 hx))

end OscInt.Cusp.VdC4Aux

namespace OscInt.Cusp

open OscInt.Blueprint OscInt.VanDerCorput

/-- **A3-P1** Order-four van der Corput with amplitude, constant 38, uniform in the linear term. -/
theorem vdc4 : VdC4Facts :=
  VdC4Aux.with_amplitude splitFacts
    (vdc3Plain splitFacts (vdc2Plain splitFacts vdc1Plain)) amplitudeTransfer

end OscInt.Cusp
