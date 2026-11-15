/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import OscInt.Statements.D4Uniform
import OscInt.Front.Sanity

/-! # Sanity theorems through the batch-D4U statement constants

As for batches LE, LE2, HC and LS (lessons 17, 33, 38, 44): every theorem about a frozen statement of
`OscInt/Statements/D4Uniform.lean` takes that statement constant as its hypothesis and discharges its hypotheses on
generic data. Planted copies: `docs/replay/plants/2026-11-15-D4U/`.

Data.
* Phase: the generic cubic `x³ + 2x²y + 3xy² + 5y³` (all coefficients nonzero and distinct, `disc = −367`); bite: `x³`
  (`disc = 0`) fails `D4LimitPhase`.
* Amplitude: a C^∞ bump `bumpC δ`, equal to `1` on `B̄(0, δ/2)` and supported in `B̄(0, δ)`, for the `δ` the statement
  provides.
* Family: the scalings `{c · bumpC δ : c ∈ [1, 2]}`, an infinite family that is C²-totally bounded
  (`scaleFamily_totallyBounded`); bite: the unbounded scalings `{n · B : n ∈ ℕ}` are not (`natFamily_not_totallyBounded`).
* S4.2U through its constant: the limit `c_C · c` uniformly in `c ∈ [1, 2]` (`uniform_sanity`).
* S4.2O through its constant: the limit `c_C` along every bounded path of offsets `t ↦ y(t)` (`offset_sanity`).
-/

namespace OscInt.API.D4UniformSanity

open Filter Topology OscInt.Statements OscInt.D4

theorem coeffs_generic : cubicCoeffs (genCubic 1 2 3 5) = (1, 2, 3, 5) :=
  (OscInt.API.Sanity.Aux.hyps_genCubic 1 2 3 5).2.2.2.2

/-- The generic cubic satisfies the phase hypotheses. -/
theorem phase_generic : D4LimitPhase (genCubic 1 2 3 5) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := OscInt.API.Sanity.Aux.hyps_genCubic 1 2 3 5
  exact ⟨h1, h2, h3, h4, by rw [h5]; norm_num [disc]⟩

/-- Bite: `x³` (`disc = 0`) fails the phase hypotheses. -/
theorem phase_bite : ¬ D4LimitPhase (genCubic 1 0 0 0) := by
  rintro ⟨-, -, -, -, h⟩
  rw [(OscInt.API.Sanity.Aux.hyps_genCubic 1 0 0 0).2.2.2.2] at h
  exact h (by norm_num [disc])

/-- A C^∞ bump, `1` on `B̄(0, δ/2)`, supported in `B̄(0, δ)`, as a complex amplitude. -/
noncomputable def bumpC (δ : ℝ) (hδ : 0 < δ) : ℝ × ℝ → ℂ :=
  fun k => ((⟨δ / 2, δ, by positivity, by linarith⟩ : ContDiffBump (0 : ℝ × ℝ)) k : ℂ)

theorem bumpC_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ 2 (bumpC δ hδ) :=
  Complex.ofRealCLM.contDiff.comp (ContDiffBump.contDiff _)

theorem bumpC_tsupport (δ : ℝ) (hδ : 0 < δ) : tsupport (bumpC δ hδ) ⊆ Metric.closedBall 0 δ := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have : Function.support (bumpC δ hδ) = Function.support b := by
    ext k; simp [bumpC, b, Function.mem_support]
  rw [tsupport, this, ← tsupport, b.tsupport_eq]

theorem bumpC_zero (δ : ℝ) (hδ : 0 < δ) : bumpC δ hδ 0 = 1 := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have h := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  simp only [bumpC]
  exact_mod_cast h

theorem bumpC_ampBound (δ : ℝ) (hδ : 0 < δ) : ∃ M : ℝ, AmpBound 2 (Metric.closedBall 0 δ) (bumpC δ hδ) M :=
  OscInt.API.ampBoundOfContDiff 2 _ _ (isCompact_closedBall 0 δ) (bumpC_contDiff δ hδ) (bumpC_tsupport δ hδ)

theorem ampBound_nonneg {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (h : AmpBound 2 K A M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0 (by norm_num) 0)

theorem ampBound_mono {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M M' : ℝ} (h : AmpBound 2 K A M) (hM : M ≤ M') :
    AmpBound 2 K A M' :=
  ⟨h.1, h.2.1, fun j hj k => (h.2.2 j hj k).trans hM⟩

theorem ampBound_smul {K : Set (ℝ × ℝ)} {A : ℝ × ℝ → ℂ} {M : ℝ} (c : ℂ) (h : AmpBound 2 K A M) :
    AmpBound 2 K (c • A) (‖c‖ * M) := by
  obtain ⟨hA, hs, hb⟩ := h
  refine ⟨hA.const_smul c, (tsupport_smul_subset_right (fun _ => c) A).trans hs, fun j hj k => ?_⟩
  rw [iteratedFDeriv_const_smul_apply ((hA.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul]
  exact mul_le_mul_of_nonneg_left (hb j hj k) (norm_nonneg c)

/-- The scalings `{c · B : c ∈ [1, 2]}` of an amplitude. -/
def scaleFamily (B : ℝ × ℝ → ℂ) : Set (ℝ × ℝ → ℂ) := {A | ∃ c ∈ Set.Icc (1 : ℝ) 2, A = (c : ℂ) • B}

/-- The scalings by `c ∈ [1, 2]` of a C² amplitude form a C²-totally bounded family. -/
theorem scaleFamily_totallyBounded {K : Set (ℝ × ℝ)} {B : ℝ × ℝ → ℂ} {M : ℝ} (hB : AmpBound 2 K B M) :
    AmpTotallyBounded K (scaleFamily B) := by
  have hM := ampBound_nonneg hB
  refine ⟨?_, fun η hη => ?_⟩
  · rintro A ⟨c, -, rfl⟩
    exact ⟨_, ampBound_smul _ hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (M / η)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hM hη.le) hN
  refine ⟨(fun j : ℕ => ((1 + j / N : ℝ) : ℂ) • B) '' Set.Iic N, (Set.finite_Iic N).image _, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast (Set.mem_Iic.mp hj)
    have h0 : (0 : ℝ) ≤ j / N := by positivity
    have h1 : (j : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact hj'
    exact ⟨1 + j / N, ⟨by linarith, by linarith⟩, rfl⟩
  rintro A ⟨c, ⟨hc1, hc2⟩, rfl⟩
  have hx0 : 0 ≤ (c - 1) * N := mul_nonneg (by linarith) hN0.le
  have hjN : ⌊(c - 1) * N⌋₊ ≤ N := by
    apply Nat.floor_le_of_le
    nlinarith
  refine ⟨_, ⟨⌊(c - 1) * N⌋₊, Set.mem_Iic.mpr hjN, rfl⟩, ?_⟩
  set j := ⌊(c - 1) * N⌋₊
  have hfl : (j : ℝ) ≤ (c - 1) * N := Nat.floor_le hx0
  have hlt : (c - 1) * N < j + 1 := Nat.lt_floor_add_one _
  have hd0 : 0 ≤ c - (1 + j / N) := by
    have : (j : ℝ) / N ≤ c - 1 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  have hd1 : c - (1 + j / N) ≤ 1 / N := by
    have : c - 1 ≤ (j + 1) / N := by rw [le_div_iff₀ hN0]; linarith
    rw [add_div] at this
    linarith
  have heq : (c : ℂ) • B - ((1 + j / N : ℝ) : ℂ) • B = ((c - (1 + j / N) : ℝ) : ℂ) • B := by
    rw [← sub_smul]
    push_cast
    ring_nf
  rw [heq]
  refine ampBound_mono (ampBound_smul _ hB) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
  have hMN : M ≤ η * N := by
    have := (div_lt_iff₀ hη).mp hN
    linarith
  calc (c - (1 + j / N)) * M ≤ 1 / N * M := mul_le_mul_of_nonneg_right hd1 hM
    _ = M / N := by ring
    _ ≤ η := by rw [div_le_iff₀ hN0]; exact hMN

/-- The scalings `{n · B : n ∈ ℕ}` of an amplitude. -/
def natFamily (B : ℝ × ℝ → ℂ) : Set (ℝ × ℝ → ℂ) := {A | ∃ n : ℕ, A = (n : ℂ) • B}

/-- Bite: the unbounded scalings of an amplitude with `B(0) = 1` are not C²-totally bounded on any `K`. -/
theorem natFamily_not_totallyBounded (K : Set (ℝ × ℝ)) {B : ℝ × ℝ → ℂ} (hB0 : B 0 = 1) :
    ¬ AmpTotallyBounded K (natFamily B) := by
  rintro ⟨-, h⟩
  obtain ⟨F, hF, -, hcov⟩ := h 1 one_pos
  obtain ⟨R, hR⟩ := (hF.image (fun b => ‖b 0‖)).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt (R + 1)
  obtain ⟨b, hbF, hb⟩ := hcov ((n : ℂ) • B) ⟨n, rfl⟩
  have h0 := hb.2.2 0 (by norm_num) 0
  rw [norm_iteratedFDeriv_zero] at h0
  have hbR : ‖b 0‖ ≤ R := hR ⟨b, hbF, rfl⟩
  have hval : ((n : ℂ) • B - b) 0 = (n : ℂ) - b 0 := by simp [hB0]
  rw [hval] at h0
  have htri := norm_sub_norm_le (n : ℂ) (b 0)
  rw [Complex.norm_natCast] at htri
  linarith

/-- S4.2U through its constant: on the generic cubic, the limit `c_C · c` holds uniformly in `c ∈ [1, 2]`. -/
theorem uniform_sanity (h : D4LimitUniformStatement) :
    ∃ δ, ∃ hδ : 0 < δ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ c ∈ Set.Icc (1 : ℝ) 2,
      ‖((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) * oscInt2 (fun κ => t * genCubic 1 2 3 5 κ) ((c : ℂ) • bumpC δ hδ) -
        (d4Constant (1, 2, 3, 5) : ℂ) * c‖ < ε := by
  obtain ⟨δ, hδ, hU⟩ := h _ phase_generic
  obtain ⟨M, hM⟩ := bumpC_ampBound δ hδ
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := hU _ (scaleFamily_totallyBounded hM) ε hε
  refine ⟨T, fun t ht c hc => ?_⟩
  have := hT t ht _ ⟨c, hc, rfl⟩
  rwa [coeffs_generic, Pi.smul_apply, bumpC_zero, smul_eq_mul, mul_one] at this

/-- S4.2O through its constant: on the generic cubic and the bump, the limit `c_C` holds along every bounded path of
offsets. -/
theorem offset_sanity (h : D4LimitOffsetStatement) :
    ∃ δ, ∃ hδ : 0 < δ, ∀ (R : ℝ) (y : ℝ → ℝ × ℝ), (∀ t, ‖y t‖ ≤ R) →
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
        oscInt2 (fun κ => t * genCubic 1 2 3 5 κ + lin (y t) κ) (bumpC δ hδ)) atTop
        (𝓝 (d4Constant (1, 2, 3, 5) : ℂ)) := by
  obtain ⟨δ, hδ, hO⟩ := h _ phase_generic
  obtain ⟨M, hM⟩ := bumpC_ampBound δ hδ
  refine ⟨δ, hδ, fun R y hy => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := hO _ M hM R ε hε
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht (y t) (hy t)
  rw [coeffs_generic, bumpC_zero, mul_one] at this
  rwa [dist_eq_norm]

end OscInt.API.D4UniformSanity
