# S4.3 proof route (the D4 constant is positive, Gamma-free)

Statement: `OscInt.Statements.D4ConstantPosStatement`. Blueprint parts C1–C5: `Blueprint/D4Limit.lean`. Assembly:
`OscInt.D4.d4ConstantPos_of` (`OscInt/D4/ConstantPos.lean`), checked by Lean against the parts and already passing
`GammaFree.lean`. Every part's proof must pass it too.

## The cosine moment (C1, C2)
C1. For R > 0: ∫₀^R cos u · u^{−1/3} du = R^{−1/3} sin R + (1/3)∫₀^R sin u · u^{−4/3} du. Integration by parts on
[ε, R] with (sin u · u^{−1/3})′ = cos u · u^{−1/3} − (1/3) sin u · u^{−4/3}, then ε → 0⁺: |sin ε · ε^{−1/3}| ≤ ε^{2/3}
→ 0, and both integrands are integrable on (0, R) (|cos u · u^{−1/3}| ≤ u^{−1/3}, |sin u · u^{−4/3}| ≤ u^{−1/3} since
|sin u| ≤ u), so the interval integrals over [ε, R] converge to those over [0, R].

C2. S(R) = ∫₀^R sin u · u^{−4/3} du converges as R → ∞ to some S > 0.
- Convergence: on [1, ∞), |sin u · u^{−4/3}| ≤ u^{−4/3}, integrable (exponent < −1); so S(R) → S.
- Positivity (the alternating series of the brief): write the integral over [0, 2Nπ] as Σ_{k<N} b_k with
  b_k = ∫_{2kπ}^{2kπ+π} sin u · (u^{−4/3} − (u+π)^{−4/3}) du (substitute u ↦ u + π on the negative hump, where
  sin(u + π) = −sin u). On (2kπ, 2kπ + π), sin u > 0 and u^{−4/3} > (u + π)^{−4/3}, so every b_k > 0. Hence
  S(2Nπ) ≥ b₀ > 0 for N ≥ 1, and S = lim S(2Nπ) ≥ b₀ > 0. (The humps of sin alternate in sign and, weighted by the
  decreasing u^{−4/3}, decrease in modulus.)
Then R^{−1/3} sin R → 0 gives cosMomentPartial R → S/3, so `cosMoment = S/3 > 0` (`Tendsto.limUnder_eq`).
This replaces the a₀ + a₁ > 0 grouping (6% margin) noted by referee B: after one integration by parts every pair
of humps contributes positively, so no numerical bound is needed.

## The angular integral (C3, C4, C5)
C3. Let g(θ) = C(cos θ, sin θ), ω = (cos θ, sin θ), ω⊥ = (−sin θ, cos θ). Then g′(θ) = ∇C(ω)·ω⊥ and, by Euler,
∇C(ω)·ω = 3C(ω). If g(θ) = g′(θ) = 0 then ∇C(ω) = 0 at ω ≠ 0; by Euler for the quadratic ∇C, H(ω)ω = 2∇C(ω) = 0
and C(ω) = 0, which forces Disc = 0 (the algebraic lemma `OscInt.D4.GaugeAux.disc_eq_zero` with z = v = ω).
C4. If g is C¹ and on [a, b] every zero is simple, the zeros in [a, b] are finitely many; near a zero x₀,
|g(x)| ≥ (|g′(x₀)|/2)|x − x₀|, so |g|^{−α} ≤ C|x − x₀|^{−α}, integrable for α < 1; away from the zeros |g| is
bounded below. (In Lean: cover [a, b] by finitely many intervals on which either |g| ≥ c or |g′| ≥ c (compactness);
on the latter g is strictly monotone and the change of variables `integrableOn_image_iff_integrableOn_abs_deriv_smul`
reduces to |u|^{−α} on a bounded interval.)
C5. The integrand is ≥ 0, integrable, and > 0 on an open interval (q ≠ 0 since disc q ≠ 0, so g ≢ 0, and g is
continuous); `intervalIntegral.integral_pos_iff_support_of_nonneg_ae` gives `angularMoment q > 0`.
