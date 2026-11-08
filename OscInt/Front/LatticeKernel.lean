import OscInt.Front.Torus
import OscInt.Front.LatticeSymbol
import OscInt.Front.GlobalAssembly
import OscInt.Front.GlobalLocal

/-!
# T6: dispersive decay of the 2D lattice Laplacian (lead)

Route `docs/proof-GD.md` R8: unfold the torus integral with the explicit weight of T1 (`OscInt.API.Torus`), write the
phase as `t (ω(k) + L(k))` with `L = x/t`, and apply GD with the classification of `ω = cos k₁ + cos k₂` (GD-P3).
-/

namespace OscInt.API.LatticeKernelAux

open OscInt.Statements OscInt.Blueprint.GD OscInt.API.Torus Filter Topology MeasureTheory
open scoped ContDiff

/-- The lattice integrand `e^{i(t(cos k₁ + cos k₂) + x·k)}`. -/
noncomputable def latticeIntegrand (t : ℝ) (x : ℤ × ℤ) (k : ℝ × ℝ) : ℂ :=
  Complex.exp (↑(t * (Real.cos k.1 + Real.cos k.2) + ((x.1 : ℝ) * k.1 + (x.2 : ℝ) * k.2)) * Complex.I)

theorem latticeIntegrand_continuous (t : ℝ) (x : ℤ × ℤ) : Continuous (latticeIntegrand t x) := by
  unfold latticeIntegrand; fun_prop

theorem exp_add_two_pi_int (θ : ℝ) (n : ℤ) :
    Complex.exp (↑(θ + (n : ℝ) * (2 * Real.pi)) * Complex.I) = Complex.exp (↑θ * Complex.I) := by
  rw [show (↑(θ + (n : ℝ) * (2 * Real.pi)) * Complex.I : ℂ) = ↑θ * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem latticeIntegrand_periodic₁ (t : ℝ) (x : ℤ × ℤ) (k : ℝ × ℝ) :
    latticeIntegrand t x (k.1 + 2 * Real.pi, k.2) = latticeIntegrand t x k := by
  unfold latticeIntegrand
  conv_rhs => rw [← exp_add_two_pi_int _ x.1]
  congr 3
  rw [Real.cos_add_two_pi]; ring

theorem latticeIntegrand_periodic₂ (t : ℝ) (x : ℤ × ℤ) (k : ℝ × ℝ) :
    latticeIntegrand t x (k.1, k.2 + 2 * Real.pi) = latticeIntegrand t x k := by
  unfold latticeIntegrand
  conv_rhs => rw [← exp_add_two_pi_int _ x.2]
  congr 3
  rw [Real.cos_add_two_pi]; ring

/-- The kernel as an integral over `ℝ²` with the unfolding weight. -/
theorem latticeKernel_eq (t : ℝ) (x : ℤ × ℤ) :
    latticeKernel t x = ∫ k : ℝ × ℝ, (unfoldWeight k : ℂ) * latticeIntegrand t x k :=
  unfoldFacts.2.2.2 _ (latticeIntegrand_continuous t x) (latticeIntegrand_periodic₁ t x)
    (latticeIntegrand_periodic₂ t x)

/-- The linear term `x / t` as a functional. -/
noncomputable def linOf (t : ℝ) (x : ℤ × ℤ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ((x.1 : ℝ) / t) • ContinuousLinearMap.fst ℝ ℝ ℝ + ((x.2 : ℝ) / t) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem latticeIntegrand_eq (t : ℝ) (ht : t ≠ 0) (x : ℤ × ℤ) (k : ℝ × ℝ) :
    latticeIntegrand t x k =
      Complex.exp (↑(t * ((fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2) k + linOf t x k)) * Complex.I) := by
  unfold latticeIntegrand linOf
  congr 3
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp

/-- The weight as a complex amplitude: `C²`, supported in `B̄(0, 4)`, with derivative bounds. -/
theorem weight_amp : ∃ M : ℝ, ContDiff ℝ 2 (fun k => (unfoldWeight k : ℂ)) ∧
    tsupport (fun k => (unfoldWeight k : ℂ)) ⊆ Metric.closedBall 0 4 ∧
    ∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j (fun k => (unfoldWeight k : ℂ)) k‖ ≤ M := by
  have hc : ContDiff ℝ 2 (fun k => (unfoldWeight k : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (unfoldWeight_contDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  have hs : tsupport (fun k => (unfoldWeight k : ℂ)) ⊆ Metric.closedBall 0 4 := by
    refine (tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero unfoldWeight).trans ?_
    exact tsupport_unfoldWeight
  obtain ⟨M, -, -, hM⟩ := OscInt.API.ampBoundOfContDiff 2 _ _ (isCompact_closedBall 0 4) hc hs
  exact ⟨M, hc, hs, hM⟩

end OscInt.API.LatticeKernelAux

namespace OscInt.API

open OscInt.Statements OscInt.API.LatticeKernelAux OscInt.API.Torus

/-- **T6** (`LatticeLaplacianDecayStatement`). -/
theorem latticeLaplacianDecay : LatticeLaplacianDecayStatement := by
  have hGD := OscInt.API.GlobalAux.globalDecay_of OscInt.API.GlobalLocal.d4PieceFacts
    OscInt.API.GlobalLocal.bumpFacts OscInt.API.GlobalLocal.mulBoundFacts OscInt.API.GlobalLocal.largeLFacts
  obtain ⟨M, hc, hs, hM⟩ := weight_amp
  obtain ⟨C, hC⟩ := hGD (fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2) (Metric.closedBall 0 4) Set.univ
    OscInt.Blueprint.GD.latticeD4 (isCompact_closedBall _ _) isOpen_univ (Set.subset_univ _) (Set.subset_univ _)
    (by fun_prop : ContDiff ℝ 4 fun k : ℝ × ℝ => Real.cos k.1 + Real.cos k.2).contDiffOn
    OscInt.API.LatticeSymbol.latticeSymbolFacts
  refine ⟨C * M, fun t x ht => ?_⟩
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  rw [latticeKernel_eq]
  have := hC (fun k => (unfoldWeight k : ℂ)) M (linOf t x) t hc hs hM ht
  simp_rw [latticeIntegrand_eq t ht0 x, mul_comm (unfoldWeight _ : ℂ)]
  exact this

end OscInt.API
