import OscInt.API

/-!
# Consumer example: the 2D lattice Schrödinger dispersive estimate (acceptance of ROADMAP P3, T6)

Only `import OscInt.API` and Mathlib. The propagator of `i ∂ₜu = H u` with `Ĥ(k) = −(cos k₁ + cos k₂)` (the discrete
Laplacian up to a constant and a time scale, `docs/statements.md`, batch GD) acts on a finitely supported
`f : ℤ² →₀ ℂ` by convolution with the kernel `(2π)^{-2} K(t, ·)`,
  (e^{-itH} f)(x) = (2π)^{-2} Σ_y K(t, x − y) f(y).
T6 (`OscInt.API.latticeLaplacianDecay`) gives the dispersive estimate
  ‖e^{-itH} f‖_{ℓ^∞} ≤ C t^{-2/3} ‖f‖_{ℓ¹}   for t ≥ 1,
and T6L with SH (`OscInt.API.latticeLaplacianLimit`, `OscInt.API.sharpness`) shows that no better power holds.
-/

open OscInt.Statements

namespace ConsumerLattice

/-- The propagator on finitely supported data, defined by its kernel. -/
noncomputable def propagator (t : ℝ) (f : ℤ × ℤ →₀ ℂ) (x : ℤ × ℤ) : ℂ :=
  ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * f.sum fun y a => latticeKernel t (x - y) * a

/-- **The ℓ¹ → ℓ^∞ dispersive estimate** with rate `t^{-2/3}`. -/
theorem dispersive : ∃ C : ℝ, ∀ (t : ℝ) (f : ℤ × ℤ →₀ ℂ) (x : ℤ × ℤ), 1 ≤ t →
    ‖propagator t f x‖ ≤ C * t ^ (-(2 : ℝ) / 3) * f.sum fun _ a => ‖a‖ := by
  obtain ⟨C, hC⟩ := OscInt.API.latticeLaplacianDecay
  refine ⟨((2 * Real.pi) ^ 2)⁻¹ * C, fun t f x ht => ?_⟩
  have hpi : 0 < ((2 * Real.pi) ^ 2)⁻¹ := by positivity
  have key : ‖f.sum fun y a => latticeKernel t (x - y) * a‖ ≤ C * t ^ (-(2 : ℝ) / 3) * f.sum fun _ a => ‖a‖ := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC t (x - y) ht) (norm_nonneg _)
  unfold propagator
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  calc ((2 * Real.pi) ^ 2)⁻¹ * ‖f.sum fun y a => latticeKernel t (x - y) * a‖
      ≤ ((2 * Real.pi) ^ 2)⁻¹ * (C * t ^ (-(2 : ℝ) / 3) * f.sum fun _ a => ‖a‖) :=
        mul_le_mul_of_nonneg_left key hpi.le
    _ = ((2 * Real.pi) ^ 2)⁻¹ * C * t ^ (-(2 : ℝ) / 3) * f.sum fun _ a => ‖a‖ := by ring

/-- **Sharpness**: no bound `C t^{-3/4}` on the kernel holds uniformly in `x` (T6L + SH). -/
theorem not_faster : ¬ ∃ C : ℝ, ∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t → ‖latticeKernel t x‖ ≤ C * t ^ (-(3 : ℝ) / 4) :=
  OscInt.API.GlobalSanity.latticeLaplacian_sharp OscInt.API.sharpness OscInt.API.latticeLaplacianLimit

/-- **GD on a phase given by a formula with all three point types** in the amplitude's support: `x³ + y³` on
`B̄(0, 1)` is nondegenerate off the axes, a fold on the axes and a D4 point (hyperbolic umbilic, `discr = −27`) at
`0`; the classification is discharged in `OscInt/Front/GlobalSanity.lean` (`hyp_classified`, from `hessian_hyp`,
`third_hyp`, `ker_diag_left/right`), and the proved theorem GD gives `m^{-2/3}` uniformly over all linear terms. -/
example : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
    ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 1 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
    1 ≤ m → ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (OscInt.API.GlobalSanity.hypPhase k + L k)) * Complex.I) * A k‖ ≤
      C * M * m ^ (-(2 : ℝ) / 3) :=
  OscInt.API.GlobalSanity.globalDecay_hyp OscInt.API.globalDecay

end ConsumerLattice
