/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Blueprint.PeriodicAnalytic

/-!
# Batch PA, part PA3: the alias bound and the integrand of the 1D lattice kernel

Route `docs/proof-PA.md`, parts P-alias and P-lc, with the corrections of the route referee.

* `aliasBoundFacts`: sum the `N` pointwise series, kill the indices that are not multiples of `N` by a finite
  geometric sum (`mul_geom_sum`), reindex the multiples by `m ↦ m * N`, subtract the term at `0` and dominate the rest
  by the two-sided geometric majorant `M r ^ |m|`, `r = e^{−aN}`.
* `kernelIntegrandFacts`: `z ↦ e^{it cos z}` is entire, `2π`-periodic and of modulus `e^{t sin x sinh y}`; the
  integrand of `latticeKernel1` at an integer is `2π`-periodic, so `[−π, π]` may be replaced by `[0, 2π]`.
-/

namespace OscInt.PeriodicAnalyticAux

open OscInt.Statements OscInt.Blueprint.PeriodicAnalytic

/-! ## P-alias -/

/-- At an index that is a multiple of `N`, every node phase `e^{i k 2πj/N}` is `1`. -/
theorem alias_exp_mul_eq_one {N : ℕ} (hN : 0 < N) (m : ℤ) (j : ℕ) :
    Complex.exp (↑(((m * (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I) = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := Complex.exp_int_mul_two_pi_mul_I (m * (j : ℤ))
  rw [← h]
  congr 1
  push_cast
  field_simp

/-- At an index that is not a multiple of `N`, the node phases `e^{i k 2πj/N}`, `j < N`, sum to `0`. -/
theorem alias_sum_exp_eq_zero {N : ℕ} (hN : 0 < N) (k : ℤ) (hk : ¬ (N : ℤ) ∣ k) :
    ∑ j ∈ Finset.range N,
      Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I) = 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set ζ : ℂ := Complex.exp (↑((k : ℝ) * (2 * Real.pi / (N : ℝ))) * Complex.I) with hζ
  have hterm : ∀ j : ℕ,
      Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I) = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow : ζ ^ N = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
  have hne : ζ - 1 ≠ 0 := by
    intro h0
    have h1 : ζ = 1 := sub_eq_zero.mp h0
    rw [hζ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    apply hk
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (k : ℂ) = (N : ℂ) * (n : ℂ) := by
      push_cast at hn
      have h4 : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
          (N : ℂ) * (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        calc (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
            = (k : ℂ) * (2 * (Real.pi : ℂ) / (N : ℂ)) * Complex.I * (N : ℂ) := by field_simp
          _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ) := by rw [hn]
          _ = (N : ℂ) * (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
      have h5 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
      exact mul_right_cancel₀ h5 h4
    exact_mod_cast h2
  have hgeom := mul_geom_sum ζ N
  rw [hpow, sub_self] at hgeom
  have hsum : ∑ j ∈ Finset.range N, ζ ^ j = 0 := (mul_eq_zero.mp hgeom).resolve_left hne
  rw [← hsum]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-- The sum of the `N` node series, reindexed over the multiples of `N`: `Σ_m N c_{mN} = Σ_{j<N} f j`. -/
theorem alias_hasSum_multiples (c : ℤ → ℂ) (f : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hf : ∀ j < N, HasSum (fun k : ℤ =>
      c k * Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I)) (f j)) :
    HasSum (fun m : ℤ => (N : ℂ) * c (m * (N : ℤ))) (∑ j ∈ Finset.range N, f j) := by
  have hall : HasSum (fun k : ℤ => ∑ j ∈ Finset.range N,
      c k * Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I))
      (∑ j ∈ Finset.range N, f j) :=
    hasSum_sum fun j hj => hf j (Finset.mem_range.mp hj)
  have hNz : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hN.ne'
  have hinj : Function.Injective fun m : ℤ => m * (N : ℤ) := mul_left_injective₀ hNz
  have hoff : ∀ k : ℤ, k ∉ Set.range (fun m : ℤ => m * (N : ℤ)) →
      ∑ j ∈ Finset.range N,
        c k * Complex.exp (↑((k : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I) = 0 := by
    intro k hk
    have hdvd : ¬ (N : ℤ) ∣ k := by
      rintro ⟨m, rfl⟩
      exact hk ⟨m, mul_comm _ _⟩
    rw [← Finset.mul_sum, alias_sum_exp_eq_zero hN k hdvd, mul_zero]
  have hre := (hinj.hasSum_iff hoff).mpr hall
  refine hre.congr_fun ?_
  intro m
  simp only [Function.comp_apply]
  rw [Finset.sum_congr rfl fun j _ => by rw [alias_exp_mul_eq_one hN m j, mul_one],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The two-sided geometric majorant: `m ↦ M r^{|m|}` off `0` and `0` at `0` has sum `2 M r / (1 − r)`. -/
theorem alias_hasSum_majorant (M : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℤ => if m = 0 then (0 : ℝ) else M * r ^ m.natAbs) (2 * (M * r * (1 - r)⁻¹)) := by
  have hgeo : HasSum (fun n : ℕ => M * r * r ^ n) (M * r * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * r)
  have hpos : HasSum (fun n : ℕ => if ((n : ℤ) + 1) = 0 then (0 : ℝ) else M * r ^ ((n : ℤ) + 1).natAbs)
      (M * r * (1 - r)⁻¹) := by
    refine hgeo.congr_fun fun n => ?_
    have h0 : ((n : ℤ) + 1) ≠ 0 := by omega
    have h1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [h0, ↓reduceIte, h1, pow_succ]
    ring
  have hneg : HasSum (fun n : ℕ => if (-((n : ℤ) + 1)) = 0 then (0 : ℝ) else M * r ^ (-((n : ℤ) + 1)).natAbs)
      (M * r * (1 - r)⁻¹) := by
    refine hgeo.congr_fun fun n => ?_
    have h0 : (-((n : ℤ) + 1)) ≠ 0 := by omega
    have h1 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [h0, ↓reduceIte, h1, pow_succ]
    ring
  have h := HasSum.of_add_one_of_neg_add_one
    (f := fun m : ℤ => if m = 0 then (0 : ℝ) else M * r ^ m.natAbs) hpos hneg
  simp only [↓reduceIte, add_zero] at h
  rw [← two_mul] at h
  exact h

/-- `2 M r / (1 − r)` with `r = e^{−x}` is `2M / (e^x − 1)`. -/
theorem alias_majorant_value (M : ℝ) {x : ℝ} (hx : 0 < x) :
    2 * (M * Real.exp (-x) * (1 - Real.exp (-x))⁻¹) = 2 * M / (Real.exp x - 1) := by
  have hE : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hE1 : Real.exp x - 1 ≠ 0 := (sub_pos.mpr hE).ne'
  rw [Real.exp_neg]
  have h1 : 1 - (Real.exp x)⁻¹ ≠ 0 := by
    have : 1 - (Real.exp x)⁻¹ = (Real.exp x - 1) / Real.exp x := by field_simp
    rw [this]
    exact div_ne_zero hE1 hE0
  field_simp

/-- **P-alias** The alias bound for sequences: `|N⁻¹ Σ_{j<N} f j − c_0| ≤ 2M / (e^{aN} − 1)`. -/
theorem aliasBoundFacts : AliasBoundFacts := by
  intro c f a M N ha hN hc hf
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNC : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNpos.ne'
  have hx : 0 < a * (N : ℝ) := mul_pos ha hNpos
  -- the mean of the `f j` is the sum of `c (m N)` over all integers `m`
  have hmult := (alias_hasSum_multiples c f hN hf).mul_left (((N : ℝ) : ℂ)⁻¹)
  have hmean : HasSum (fun m : ℤ => c (m * (N : ℤ))) (((N : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range N, f j) := by
    refine hmult.congr_fun ?_
    intro m
    rw [Complex.ofReal_natCast, ← mul_assoc, inv_mul_cancel₀ (by simpa using hNC), one_mul]
  -- subtract the term at `0`
  have hzero : HasSum (fun m : ℤ => if m = 0 then c 0 else 0) (c 0) := hasSum_ite_eq 0 (c 0)
  have hdiff := hmean.sub hzero
  -- dominate by the geometric majorant
  have hr0 : 0 ≤ Real.exp (-(a * (N : ℝ))) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(a * (N : ℝ))) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hmaj := alias_hasSum_majorant M hr0 hr1
  rw [alias_majorant_value M hx] at hmaj
  refine hdiff.norm_le_of_bounded hmaj ?_
  intro m
  by_cases hm : m = 0
  · subst hm
    simp
  · simp only [hm, ↓reduceIte, sub_zero]
    refine (hc (m * (N : ℤ))).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 2
    have habs : |((m * (N : ℤ) : ℤ) : ℝ)| = (m.natAbs : ℝ) * (N : ℝ) := by
      push_cast
      rw [abs_mul, abs_of_nonneg hNpos.le, Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    ring

/-! ## P-lc -/

/-- The real part of `t cos z · i` is `t sin x sinh y` for `z = x + iy`. -/
theorem kernelIntegrand_re (t : ℝ) (z : ℂ) :
    ((t : ℂ) * Complex.cos z * Complex.I).re = t * (Real.sin z.re * Real.sinh z.im) := by
  rw [Complex.cos_eq z]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  ring

/-- On the strip `|Im z| < η` the modulus of `e^{it cos z}` is at most `e^{|t| sinh η}`. -/
theorem kernelIntegrand_norm_le (t η : ℝ) (z : ℂ) (hz : |z.im| < η) :
    ‖Complex.exp ((t : ℂ) * Complex.cos z * Complex.I)‖ ≤ Real.exp (|t| * Real.sinh η) := by
  rw [Complex.norm_exp, kernelIntegrand_re, Real.exp_le_exp]
  have h1 : |Real.sin z.re * Real.sinh z.im| ≤ Real.sinh η := by
    rw [abs_mul, Real.abs_sinh]
    have hs : Real.sinh |z.im| ≤ Real.sinh η := Real.sinh_le_sinh.mpr hz.le
    have hs0 : 0 ≤ Real.sinh |z.im| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
    calc |Real.sin z.re| * Real.sinh |z.im| ≤ 1 * Real.sinh |z.im| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) hs0
      _ = Real.sinh |z.im| := one_mul _
      _ ≤ Real.sinh η := hs
  calc t * (Real.sin z.re * Real.sinh z.im) ≤ |t * (Real.sin z.re * Real.sinh z.im)| := le_abs_self _
    _ = |t| * |Real.sin z.re * Real.sinh z.im| := abs_mul _ _
    _ ≤ |t| * Real.sinh η := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- `z ↦ e^{it cos z}` is periodic-analytic on every strip of half-width `η`, with bound `e^{|t| sinh η}`. -/
theorem kernelIntegrand_periodicAnalyticOn (t η : ℝ) :
    PeriodicAnalyticOn (fun z : ℂ => Complex.exp ((t : ℂ) * Complex.cos z * Complex.I)) η
      (Real.exp (|t| * Real.sinh η)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun z : ℂ => Complex.exp ((t : ℂ) * Complex.cos z * Complex.I) :=
      Complex.differentiable_exp.comp
        (((differentiable_const (t : ℂ)).mul Complex.differentiable_cos).mul (differentiable_const Complex.I))
    exact hd.differentiableOn
  · intro z _
    have h2 : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; rfl
    simp only [h2, Complex.cos_add_two_pi]
  · intro z hz
    exact kernelIntegrand_norm_le t η z hz

/-- The integrand of the 1D lattice kernel at an integer `n` is `2π`-periodic. -/
theorem kernelIntegrand_periodic (t : ℝ) (n : ℤ) :
    Function.Periodic (fun k : ℝ => Complex.exp (↑(t * Real.cos k + (n : ℝ) * k) * Complex.I))
      (2 * Real.pi) := by
  intro k
  change Complex.exp (↑(t * Real.cos (k + 2 * Real.pi) + (n : ℝ) * (k + 2 * Real.pi)) * Complex.I) =
    Complex.exp (↑(t * Real.cos k + (n : ℝ) * k) * Complex.I)
  rw [Real.cos_add_two_pi]
  have h : (↑(t * Real.cos k + (n : ℝ) * (k + 2 * Real.pi)) : ℂ) * Complex.I =
      ↑(t * Real.cos k + (n : ℝ) * k) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The 1D lattice kernel at an integer `n` is the Fourier integral of index `−n` of `θ ↦ e^{it cos θ}`. -/
theorem kernelIntegrand_latticeKernel1_eq (t : ℝ) (n : ℤ) :
    latticeKernel1 t (n : ℝ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((t : ℂ) * Complex.cos (θ : ℂ) * Complex.I) *
        Complex.exp (↑(-(((-n : ℤ) : ℝ) * θ)) * Complex.I) := by
  have hper := (kernelIntegrand_periodic t n).intervalIntegral_add_eq (-Real.pi) 0
  have e1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have e2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := zero_add _
  rw [e1, e2] at hper
  unfold latticeKernel1
  rw [hper]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **P-lc** The integrand of the 1D lattice kernel is periodic-analytic, and the kernel is its Fourier integral. -/
theorem kernelIntegrandFacts : KernelIntegrandFacts :=
  ⟨fun t η _ => kernelIntegrand_periodicAnalyticOn t η, kernelIntegrand_latticeKernel1_eq⟩

end OscInt.PeriodicAnalyticAux
