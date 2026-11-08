# Design: stationary-phase leading terms (ROADMAP P2) — draft, not frozen

Status: design document with draft statements. Nothing here is a frozen statement; a statement derived from it goes
through the full procedure (`CONTRIBUTING.md`). Numeric pre-registration already done for the nondegenerate case:
`docs/prereg/2026-11-08-P3b-leading-term.md`, RESULT PASS (`numerics/results-spleading-2026-11-08.txt`).

## 1. Nondegenerate leading term in 2D (LT-N)
Classical statement (Hörmander, ALPDO I, Thm 7.7.5; Stein, Harmonic Analysis, Ch. VIII §2, Prop. 3), n = 2: for Ψ
smooth, A smooth with compact support, k₀ the only critical point of Ψ in supp A, H = D²Ψ(k₀) invertible,

  I(m) = ∫ e^{imΨ} A = (2π/m) |det H|^{−1/2} e^{iπ sgn(H)/4} e^{imΨ(k₀)} A(k₀) + R(m),  |R(m)| ≤ C m^{−2}.

Draft Lean statement (same idiom as batch GD):
```lean
/-- The signature of a symmetric 2×2 matrix with nonzero determinant: 2, 0 or −2. -/
noncomputable def sig2 (H : Matrix (Fin 2) (Fin 2) ℝ) : ℤ :=
  if H.det < 0 then 0 else if 0 < H 0 0 then 2 else -2

def StationaryPhaseLeadingStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (k₀ : ℝ × ℝ),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 6 Ψ U → fderiv ℝ Ψ k₀ = 0 →
    (hessianMatrix Ψ k₀).det ≠ 0 → (∀ k ∈ K, k ≠ k₀ → fderiv ℝ Ψ k ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
      ContDiff ℝ 4 A → tsupport A ⊆ K → (∀ j ≤ 4, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖(∫ k : ℝ × ℝ, Complex.exp (↑(m * Ψ k) * Complex.I) * A k) -
          (2 * Real.pi / m) * |(hessianMatrix Ψ k₀).det| ^ (-(1 : ℝ) / 2) *
            Complex.exp (↑(Real.pi * sig2 (hessianMatrix Ψ k₀) / 4 + m * Ψ k₀) * Complex.I) * A k₀‖ ≤ C * M / m ^ 2
```
Open choices to settle before freezing (each a reviewer question): (a) the smoothness orders (C⁶ phase, C⁴ amplitude
suffice for the O(m⁻²) remainder by the standard proof; check against the route); (b) uniformity over a compact set of
linear terms, where the critical point k₀(L) moves: state it with k₀ given as a function of L (`k₀ : K′ → ℝ × ℝ`,
continuous, `DΨ(k₀ L) + L = 0`), or with the uniqueness hypothesis per L and the conclusion "for each L in K′" with C
uniform; (c) `k₀` inside `K` or allowed on its boundary (it must be in `interior K` for the leading term to be
`A(k₀)`, or else the statement is false unless `A` vanishes there: it does, as `tsupport A ⊆ K` — then the term is
correct but trivial; a reviewer should check the edge case).
Proof route (not started): Morse lemma with C^k control (not in Mathlib), or the direct route: reduce to a quadratic
phase by a C^k change of variables, then the Gaussian Fourier transform (`fourierIntegral_gaussian_pi` and relatives,
lessons 1: check names at the pin) with an amplitude-Taylor remainder. Estimated effort: large (the Morse lemma with
parameters alone is a multi-day formalisation). This is why it is not in batch GD.

## 2. Fold (Airy-type) leading term (LT-F)
Classical (AGV II; Duistermaat 1974): at a fold critical point k₀ of Ψ (Hessian of rank one with nonzero eigenvalue
λ, third derivative τ = D³Ψ(k₀)[e, e, e] ≠ 0 along the unit kernel vector e) with no linear term, the integral is
asymptotic to m^{−5/6} times a constant times A(k₀). Candidate constant (CONJECTURED, from the product of the 1D
Gaussian integral across the fold and ∫_ℝ e^{i a s³} ds = Γ(1/3)/(√3 a^{1/3}) for a = |τ|/6 > 0 along it):
c_F = (2π/|λ|)^{1/2} e^{iπ sgn(λ)/4} (6/|τ|)^{1/3} Γ(1/3)/√3. The remainder order is not settled here; the
pre-registered check below measures it before any statement is written.
Draft statement shape (exact constant deliberately left open until the numeric check):
```lean
def FoldLeadingStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (k₀ : ℝ × ℝ), IsOpen U → k₀ ∈ U → ContDiffOn ℝ 6 Ψ U →
    fderiv ℝ Ψ k₀ = 0 → (hessianMatrix Ψ k₀).rank = 1 → (fold condition at k₀, FoldOrNondegMatrix's second branch) →
    ∃ δ > 0, ∀ A, ContDiff ℝ 4 A → tsupport A ⊆ Metric.closedBall k₀ δ →
      Tendsto (fun m : ℝ => ((m ^ ((5 : ℝ) / 6) : ℝ) : ℂ) * Complex.exp (-(↑(m * Ψ k₀)) * Complex.I) *
        ∫ k, Complex.exp (↑(m * Ψ k) * Complex.I) * A k) atTop (𝓝 (foldConstant Ψ k₀ * A k₀))
```
with `foldConstant Ψ k₀` = the candidate c_F above. Pre-registered numeric check
(to be registered before any statement is written): the same trapezoid method as P3b on Ψ = x³/3 + y² and two
perturbations, criteria |error| < 2 % at m = 640 and a measured remainder slope reported (not a pass criterion until the order
is derived), with a control that replaces e^{iπ sgn(λ)/4} by 1 (must fail).

## 3. Sharpness from leading terms
SH (batch GD) turns any of these limits into a matching lower bound and excludes faster rates; applied in batch GD to
D4 via T6L. For LT-N it shows that m^{−1} is sharp whenever A(k₀) ≠ 0.
