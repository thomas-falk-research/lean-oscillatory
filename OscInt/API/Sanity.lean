import OscInt.API
import OscInt.D4.Sanity

/-!
# Front-end batch 1: non-vacuity and bite (post-proof)

Answers the statement referees' MINORs (`review/2026-11-07-API1-pre-proof-{A,B}.md`):
* `apiSanity_elliptic_hyps`, `apiSanity_generic_hyps`: F2's phase hypotheses hold for the elliptic umbilic
  x³ − 3xy² (`disc = 108 > 0`) and for x³ + 2x²y + 3xy² + 5y³ (all coefficients nonzero, `disc = −367 < 0`).
* `apiSanity_elliptic_constant`: an independent value for the elliptic branch, `d4ClosedConstant 108 = √π Γ(1/6)/3`.
  The right-hand side is derived off-line for x³ − 3xy²: C(cos θ, sin θ) = cos 3θ, so J = ∫₀^{2π} |cos 3θ|^{−2/3} dθ
  = 2 B(1/2, 1/6) and c = (Γ(2/3)/2) · J/3 = √π Γ(1/6)/3; the Lean proof reaches it from the definition through
  Legendre duplication and Euler reflection (`OscInt.D4.gammaSixth`, which the S4.4 proof also uses).
* `apiSanity_elliptic_bite`: F2 applied to x³ − 3xy² and a bump amplitude gives a nonzero limit, so
  `t^{2/3} |∫ e^{itφ} A|` does not tend to `0`.
-/

namespace OscInt.API.Sanity

open Filter Topology OscInt.Statements OscInt.D4

theorem Aux.hyps_genCubic (a b c d : ℝ) :
    ContDiff ℝ 4 (genCubic a b c d) ∧ genCubic a b c d 0 = 0 ∧ fderiv ℝ (genCubic a b c d) 0 = 0 ∧
      (∀ v w, dd (genCubic a b c d) 0 v w = 0) ∧ cubicCoeffs (genCubic a b c d) = (a, b, c, d) := by
  refine ⟨genCubic_contDiff a b c d, by simp [genCubic], ?_, dd_genCubic_zero a b c d, cubicCoeffs_genCubic a b c d⟩
  ext
  · simp [fd_genCubic]
  · simp [fd_genCubic]

/-- F2's phase hypotheses for the elliptic umbilic `x³ − 3xy²` (`disc = 108`). -/
theorem apiSanity_elliptic_hyps :
    ContDiff ℝ 4 (genCubic 1 0 (-3) 0) ∧ genCubic 1 0 (-3) 0 0 = 0 ∧ fderiv ℝ (genCubic 1 0 (-3) 0) 0 = 0 ∧
      (∀ v w, dd (genCubic 1 0 (-3) 0) 0 v w = 0) ∧ disc (cubicCoeffs (genCubic 1 0 (-3) 0)) = 108 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Aux.hyps_genCubic 1 0 (-3) 0
  exact ⟨h1, h2, h3, h4, by rw [h5]; norm_num [disc]⟩

/-- F2's phase hypotheses for `x³ + 2x²y + 3xy² + 5y³` (all coefficients nonzero, `disc = −367`). -/
theorem apiSanity_generic_hyps :
    ContDiff ℝ 4 (genCubic 1 2 3 5) ∧ genCubic 1 2 3 5 0 = 0 ∧ fderiv ℝ (genCubic 1 2 3 5) 0 = 0 ∧
      (∀ v w, dd (genCubic 1 2 3 5) 0 v w = 0) ∧ disc (cubicCoeffs (genCubic 1 2 3 5)) = -367 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Aux.hyps_genCubic 1 2 3 5
  exact ⟨h1, h2, h3, h4, by rw [h5]; norm_num [disc]⟩

theorem Aux.rpow_108 : (108 : ℝ) ^ ((1 : ℝ) / 6) = 2 ^ ((1 : ℝ) / 3) * Real.sqrt 3 := by
  have hx : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt 3 := by positivity
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h3 : Real.sqrt 3 ^ 6 = 27 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  have h6 : ((2 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt 3) ^ 6 = 108 := by rw [mul_pow, h2, h3]; norm_num
  rw [← h6, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]

/-- The elliptic branch at `disc = 108` equals `√π Γ(1/6)/3`, an independent value (duplication and reflection). -/
theorem apiSanity_elliptic_constant :
    d4ClosedConstant 108 = Real.sqrt Real.pi * Real.Gamma (1 / 6) / 3 := by
  have h7 := gammaSixth
  unfold OscInt.Blueprint.GammaSixthFacts at h7
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hs3p : 0 < Real.sqrt 3 := by positivity
  simp only [d4ClosedConstant, show ¬ (108 : ℝ) < 0 by norm_num, ↓reduceIte, Aux.rpow_108]
  rw [h7]
  field_simp
  rw [sq, hs3]

/-- Bite: F2 on `x³ − 3xy²` with a bump amplitude (`A(0) = 1`) gives a limit `c ≠ 0`. -/
theorem apiSanity_elliptic_bite :
    ∃ (A : ℝ × ℝ → ℂ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
        ∫ k : ℝ × ℝ, Complex.exp (↑(t * genCubic 1 0 (-3) 0 k) * Complex.I) * A k) atTop (𝓝 c) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := apiSanity_elliptic_hyps
  obtain ⟨δ, hδ, hlim⟩ := d4LimitClosedForm _ h1 h2 h3 h4 (by rw [h5]; norm_num)
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hA : ContDiff ℝ 2 (fun k => (b k : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hs : tsupport (fun k => (b k : ℂ)) ⊆ Metric.closedBall 0 δ := by
    have : Function.support (fun k => (b k : ℂ)) = Function.support b := by
      ext k; simp [Function.mem_support]
    rw [tsupport, this, ← tsupport, b.tsupport_eq]
  refine ⟨_, _, ?_, hlim _ hA hs⟩
  have hpos := sanity_d4ClosedConstant_pos (disc (cubicCoeffs (genCubic 1 0 (-3) 0))) (by rw [h5]; norm_num)
  have h0 : (b 0 : ℂ) = 1 := by simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  simp only [h0, mul_one, ne_eq, Complex.ofReal_eq_zero]
  exact hpos.ne'

end OscInt.API.Sanity
