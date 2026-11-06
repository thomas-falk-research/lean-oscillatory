<!-- Blind pre-proof review of S4.1, referee B (fresh-context agent). Prompt: review/prompts/S4-pre-proof.md. Read commit 8a54564. Verbatim final report. -->

8a545647e8c8e50a382198cb5d252848c3ef1c7e

# Referee B: blind pre-proof statement review of S4.1 (`D4BoundStatement`)

**Bottom line:** the statement is FAITHFUL to the docs and TRUE. It is FAITHFUL-WEAKER than the classical D4 result, because `Disc < 0` leaves out the elliptic umbilic. There are no BLOCKER or MAJOR findings.

I read only what the prompt allows: `docs/statements.md` (S2/S3 and S4), `OscInt/Statements/D4.lean` and `OscInt/Statements/StationaryPhase.lean`. My scratch file is `/tmp/refS4B/t.lean`, compiled with `nice -n 10 lake env lean`. In it, `disc (1,0,-3,0) = 108`, `disc (0,1,0,1) = -4`, `disc 0 = 0` and `-(2:ℝ)/3 = -2/3` all check, and `sanity_D4_hyps` uses only the standard axioms. I wrote nothing in the repository.

## 1. Verdict
- **Against `docs/statements.md` S4.1: FAITHFUL.** The pieces match the text one for one:
  - C⁴ phase;
  - `∀ v w, dd φ 0 v w = 0` is D²φ(0) = 0;
  - `disc (cubicCoeffs φ) < 0`;
  - `∃ δ > 0, ∃ C` comes before `A M y t`;
  - `AmpBound 2 (closedBall 0 δ) A M`, `1 ≤ t`, and the phase is `t * φ κ + lin y κ`;
  - the bound is `C * M * t ^ (-(2:ℝ)/3)`.
- **Against the classical result: FAITHFUL-WEAKER.** The classical uniform t^{-2/3} bound holds at any D4 point, i.e. Disc ≠ 0. `Disc < 0` covers only the hyperbolic umbilic D4⁺ (for example x³+y³). The elliptic umbilic D4⁻ (for example x³ − 3xy², which has Disc = 108 > 0) is excluded. Within its scope the statement is the classical one.
- **TRUE.** A sketch, consistent with the route in the docs:
  - Subtract φ(0) (a phase factor) and ∇φ(0)·κ (absorbed into y). Then rescale annuli at dyadic scales ε ≥ t^{-1/3}, with m = tε³ ≥ 1. The rescaled phase ε⁻³φ(εz) minus its constant and linear Taylor terms is a C⁴ family down to ε = 0, where it equals the cubic C.
  - For Disc < 0, C is fold-or-nondegenerate on the annulus. For x³+y³, Hess C = 36xy degenerates on the axes, the kernel there is the other axis, and the third derivative along it is 6 ≠ 0.
  - Bounded rescaled linear terms: S3 gives ε²(tε³)^{-5/6}, which sums to about t^{-2/3}.
  - Large rescaled linear terms: S2.1 with N = 2 (only C² amplitude is needed) gives ε²(tε³)^{-2}, which also sums to about t^{-2/3}.
  - The inner ball of radius t^{-1/3} contributes at most M·t^{-2/3}.
  - The rescaled amplitude A(εz)·χ(z) has C² bounds of order M for ε ≤ 1.
  - This matches the D4 oscillation index 2/3. The deformations under linear perturbation are A1, A2, A3 and D4, whose decay rates 1, 5/6, 3/4 and 2/3 are all at least 2/3.
- I have no counterexample.

## 2. `cubicCoeffs`, `disc` and the isolated-critical-point claim
- **`ddd` order.** `ddd Ψ k u v w = ∂_w∂_v∂_u Ψ`. So `ddd φ 0 e₁ e₁ e₂ = ∂₂∂₁∂₁φ(0)` and `ddd φ 0 e₁ e₂ e₂ = ∂₂∂₂∂₁φ(0)`. For C⁴ (hence C³) φ these are symmetric, so the argument order does not matter.
- **Coefficients.** In (1/6)Σ ∂ᵢⱼₖ κᵢκⱼκₖ, the x²y coefficient is 3·∂₁₁₂/6 = ∂₁₁₂/2 and the xy² coefficient is ∂₁₂₂/2. So a = ∂₁₁₁/6, b = ∂₁₁₂/2, c = ∂₁₂₂/2, d = ∂₂₂₂/6 are correct.
- **`disc`.** b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd is the standard discriminant of the homogeneous binary cubic, and it stays valid when a = 0.
  - x³+y³ = (x+y)(x²−xy+y²) gives −27 (proved in `sanity_D4_hyps`), so Disc < 0 means one real linear factor.
  - y(x²+y²) gives −4 (one real factor).
  - x³ − 3xy² gives 108 (three real factors).
- **Disc < 0 implies an isolated critical point at 0.** This is correct:
  - Disc < 0 forces C ≢ 0, since C ≡ 0 gives Disc = 0.
  - If ∇C(z) = 0 with z ≠ 0, Euler's identity gives 3C(z) = z·∇C(z) = 0, so C = ℓQ with ℓ(z) = 0.
  - Then ∇C(z) = Q(z)∇ℓ with ∇ℓ ≠ 0, so Q(z) = 0. By homogeneity ℓ divides Q, so C has a repeated factor and Disc = 0.
  - The same argument works for Disc > 0.

## 3. Vacuity and conventions
- **The hypotheses can be met non-trivially.** `sanity_D4_hyps` (x³+y³) does this. Non-zero amplitudes with `AmpBound 2 (closedBall 0 δ)` exist for every δ > 0 (a bump function; `sanity_ampBound_exists` covers radius 1, and rescaling gives any δ).
  - M < 0 makes `AmpBound` unsatisfiable, since the j = 0 case gives ‖A k‖ ≤ M. That case is harmless.
  - The conclusion is not trivial: the trivial bound M·(2δ)² does not decay in t.
- **Quantifier order.** `∃ δ > 0, ∃ C` comes after `φ` and before `A, M, y, t`. δ must depend on φ, so this order is right.
- **Omitting ∇φ(0) = 0 is correct.** Writing φ = φ̃ + g·κ with ∇φ̃(0) = 0 turns `t·g·κ + y·κ` into `(tg + y)·κ`, and `y` ranges over all of ℝ². Uniformity in y ∈ ℝ² is therefore equivalent to uniformity in p = y/t ∈ ℝ² for the form t(φ + p·κ), and the bound stays true and uniform.
- **`Real.rpow`.** It is applied to t ≥ 1 > 0, and `-(2:ℝ)/3` parses as −2/3 (checked).
- **Max-norm ball.** `Metric.closedBall 0 δ` on `ℝ × ℝ` is the square [−δ, δ]². Since δ is existential, this changes nothing.
- The C⁴ phase class and the nested `fderiv`s (`dd`, `ddd`) agree with the true derivatives.
- `oscInt2` is integrable here: the integrand is continuous with compact support.

## 4. Ill-conditioned regimes
- **Disc → 0.** φ is fixed and Disc < 0 is strict, so δ and C may depend on |Disc|; the statement allows that. No uniformity in φ is claimed, which is correct, since C must blow up as Disc → 0.
- **Large |y|.** Covered (S2.1 regime, see section 1).
- **t near 1.** Covered by the trivial bound M·4δ² absorbed into C.
- **Support touching ∂B̄(0, δ).** Harmless: the support condition is closure ⊆ closed ball, all amplitude bounds are global, and δ is chosen small enough that the fold-or-nondegenerate property holds on the whole closed ball minus 0.

## 5. Findings
No BLOCKER. No MAJOR.

- **MINOR 1 (scope narrower than classical D4).** The Lean hypothesis is `disc (cubicCoeffs φ) < 0`. This restricts the result to the hyperbolic umbilic D4⁺. Classical uniform t^{-2/3} decay also holds for the elliptic umbilic D4⁻ (Disc > 0, e.g. x³ − 3xy²), and Disc ≠ 0 is exactly the "isolated critical point" condition. The statement is faithful to `docs/statements.md` and the brief; if the brief intends all D4 points, `≠ 0` would be the faithful hypothesis. Either way the docs should say explicitly that D4⁻ is out of scope.
  - The route is no harder for Disc > 0: Hess C is then definite, so the annulus is nondegenerate for S2.2/S3, which is the easier case.
- **NIT 2 (comment wording).** The header comment "a gradient at `0` is absorbed by the uniformity in `y`" could add that the absorption is `y ↦ y + t∇φ(0)`, which is why the statement needs `y` unrestricted rather than in a compact set.
- **NIT 3 (sanity coverage).** No sanity theorem shows amplitudes exist for arbitrary δ; `sanity_ampBound_exists` is fixed at radius 1. This is mathematically obvious and does not affect the statement.