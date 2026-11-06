<!-- Blind pre-proof review of S4.1, referee A (fresh-context agent). Prompt: review/prompts/S4-pre-proof.md. Read commit 8a54564. Verbatim final report. -->

8a545647e8c8e50a382198cb5d252848c3ef1c7e

# Referee A: blind pre-proof statement review of S4.1 (`D4BoundStatement`)

I read only `docs/statements.md` (S2, S3, S4), `OscInt/Statements/D4.lean` and `OscInt/Statements/StationaryPhase.lean`. My scratch file was `/tmp/refS4A/check.lean`. It compiled with one harmless error: in my own third `example`, `simp` closed the goal before `ring` ran, which is a bookkeeping slip, not a finding. The useful outputs:
- `sanity_D4_hyps` uses only `[propext, Classical.choice, Quot.sound]`.
- `disc (1,0,-3,0) = 108`.
- `disc (1,0,p,q)` reduces to `-4p³ - 27q²`.

I wrote nothing in the repository.

## 1. Verdict
- **Against `docs/statements.md` S4.1: FAITHFUL.** Each part of the mathematics matches the Lean text:
  - C⁴ phase: `ContDiff ℝ 4 φ`.
  - D²φ(0) = 0: `∀ v w, dd φ 0 v w = 0`.
  - Disc C < 0: `disc (cubicCoeffs φ) < 0`.
  - Amplitude bound (2, B̄(0, δ), M): `AmpBound 2 (Metric.closedBall 0 δ) A M`.
  - The quantifiers over y ∈ ℝ² and t ≥ 1, and the bound C·M·t^{-2/3}, all match.
- **Against the classical result: FAITHFUL-WEAKER.** The classical uniform t^{-2/3} bound holds at every D4 point, i.e. whenever Disc ≠ 0. That covers both D4⁺ (the hyperbolic umbilic x³+y³, Disc = −27 < 0) and D4⁻ (the elliptic umbilic x³−3xy², Disc = 108 > 0). `Disc < 0` keeps only D4⁺. Within that class the statement is the classical one. Whether this matches the brief's intent is MINOR-1 below.
- **TRUE (expected; no counterexample found).**
  - *Model case.* For the cubic x³+y³ itself, van der Corput (k = 3) in x, uniform in the linear term, gives F(y) = O(t^{-1/3}). The same applied to ∂_yA bounds F′, which needs ∂ₓ∂_yA, so C² is enough. A second van der Corput in y then gives t^{-2/3}.
  - *General φ, via the documented route.* Remove φ(0) (a unimodular factor) and ∇φ(0) (absorbed into y). The disc |κ| ≤ t^{-1/3} contributes at most M·t^{-2/3}. On a dyadic annulus at scale ε, the rescaled phase Φ(ε,·) is a C⁴ family on [0, ε₀]. S3 applies on the annulus with m = tε³, and S2.1 handles large rescaled linear terms. Each piece is ≲ ε²·M·(tε³)^{-5/6}, and summing over ε ≥ t^{-1/3} is geometric, giving t^{-5/6}·t^{1/6} = t^{-2/3}.
  - *S3's hypothesis on the annulus.* A D4⁺ cubic is real-linearly equivalent to x³+y³. Its Hessian degenerates only on the two axes, and there the third derivative along the kernel is 6C(v) ≠ 0, so the fold condition holds everywhere.
  - *Sharpness and necessity.* With y = 0 and A(0) ≠ 0 the integral is ~ c·t^{-2/3}, so the exponent is sharp. The Disc condition is needed: φ = x³ + y⁴ has Disc = 0 and decays only like t^{-7/12}.

## 2. `cubicCoeffs` and `disc`
- **`cubicCoeffs` is correct.** `ddd Ψ k u v w` is ∂_w∂_v∂_uΨ(k). For C³ (here C⁴) phases mixed partials commute, so argument order does not matter. The coefficients of (1/6)Σ∂_{ijk}φ(0)κᵢκⱼκₖ are:
  - x³: ∂₁₁₁/6.
  - x²y: 3·∂₁₁₂/6 = ∂₁₁₂/2, matching `ddd φ 0 (1,0) (1,0) (0,1) / 2`.
  - xy²: ∂₁₂₂/2.
  - y³: ∂₂₂₂/6.
  - `sanity_D4_hyps` confirms (1,0,0,1) for x³+y³. The mixed coefficients b and c are not exercised by any sanity theorem (NIT-1).
- **`disc` is the standard discriminant of the binary cubic** with the convention Disc < 0 ⇔ one real linear factor and a pair of complex-conjugate factors:
  - x³+y³ gives −27.
  - The specialisation (1, 0, p, q) gives −4p³ − 27q², the familiar depressed-cubic discriminant.
  - x³−3xy² gives +108 (three real lines).
- **Disc < 0 ⇒ 0 is an isolated critical point of C: correct.**
  - By Euler, x·Cₓ + y·C_y = 3C. If ∇C(p) = 0 with p ≠ 0, then C(p) = 0, so the linear form ℓ through p divides C: C = ℓ·Q.
  - Then ∇C(p) = Q(p)·∇ℓ, and ∇ℓ ≠ 0, so Q(p) = 0 and ℓ² divides C.
  - A repeated factor forces Disc = 0. The homogeneous form covers a = 0 (a root at infinity), and C ≡ 0 also has Disc = 0.
  - Conversely, an isolated critical point holds if and only if Disc ≠ 0, which is what MINOR-1 relies on.

## 3. Vacuity and conventions
- **Not vacuous.**
  - The hypotheses are met non-trivially: `sanity_D4_hyps` (x³+y³) compiles.
  - Nonzero amplitudes satisfying `AmpBound 2 (closedBall 0 δ) A M` exist for every δ > 0 (`sanity_ampBound_exists` gives radius 1; rescaling gives any δ).
  - `AmpBound` forces M ≥ 0, so negative M cannot be used to make the bound trivial.
  - The amplitude is continuous with compact support, so the Bochner integral is genuine; Lean's value 0 for non-integrable integrands is never reached.
- **Quantifier order is correct:** `∃ δ > 0, ∃ C : ℝ, ∀ (A) (M) (y) (t)`. δ and C depend only on φ. Choosing δ existentially is the standard localisation, not a loophole.
- **Omitting ∇φ(0) = 0 is correct.**
  - Write φ = φ(0) + g·κ + C + R. Then e^{itφ(0)} is unimodular, and t·g·κ + y·κ = (y + t·g)·κ with y + t·g ∈ ℝ² arbitrary.
  - So the general statement reduces exactly to the gradient-free case, and the bound stays uniform in all y ∈ ℝ².
  - Note that ∇φ(0) is not rescaling-stable (ε^{-3}φ(εz) contains ε^{-2}g·z), so this reduction is necessary, and it is available.
- **`Real.rpow`:** `t ^ (-(2 : ℝ) / 3)` parses as (−2)/3 (checked), with t ≥ 1 > 0, so there are no edge cases.
- **Max-norm ball:** `closedBall 0 δ` in `ℝ × ℝ` is the square [−δ, δ]², as the docs state. Like the max-norm operator norms inside `AmpBound`, this changes only the constants.

## 4. Ill-conditioned regimes
- **Disc → 0:** not a uniformity issue. φ is fixed and C may depend on φ, so blow-up as Disc → 0 is allowed and correctly not excluded.
- **Large |y|:** after removing g, |∇φ| ≲ δ² on the ball. For |y| ≫ tδ² the phase is non-stationary and two integrations by parts (using C² of A) give ≪ M·t^{-2/3}. The intermediate range is the D4 regime handled by the route. The statement does not restrict y, and none is needed.
- **t near 1:** trivial, since |I| ≤ 4δ²·M. The condition t ≥ 1 only removes the meaningless t → 0 regime.
- **Support touching ∂B̄(0, δ):** harmless. A is C² on all of ℝ², so its derivatives vanish continuously at the edge of the support, and no boundary terms arise.

## 5. Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR-1 (scope, owner decision).** The hypothesis `disc (cubicCoeffs φ) < 0` covers only the hyperbolic umbilic D4⁺. The classical D4 estimate, and the brief's wording "the cubic part has an isolated critical point" (if that wording is the brief's only condition), correspond to `disc (cubicCoeffs φ) ≠ 0`, which also includes the elliptic umbilic D4⁻ (e.g. x³−3xy², Disc = 108).
  - The documented route covers D4⁻ at no extra cost: its cubic has a definite Hessian covariant (−36(x²+y²) for x³−3xy²), so it is nondegenerate on every annulus and the `hessDet ≠ 0` branch of `FoldOrNondeg` applies.
  - If the brief explicitly says Disc < 0, the statement is faithful as written. Otherwise either replace `< 0` with `≠ 0`, or state in the header that D4⁻ is deliberately excluded.
  - The docs sentence "implied by Disc C < 0" is true but is only one direction; the converse (isolated critical point ⇒ Disc ≠ 0) is what makes ≠ 0 the natural hypothesis.
- **NIT-1.** No sanity theorem exercises the mixed coefficients b and c of `cubicCoeffs`; x³+y³ has b = c = 0. A check such as `cubicCoeffs (fun k => k.1^2 * k.2) = (0, 1, 0, 0)` would pin the `/2` normalisation and the `ddd` argument pattern. Mathematically they are correct as written.
- **NIT-2.** The docstring and header say "uniformly in `y ∈ ℝ²`" but not that C may depend on φ in an ill-conditioned way (for example as Disc → 0). That dependence is implicit in `∃ δ C` after `φ`; one clause in the header would pre-empt the question.

**Bottom line:** the statement is FAITHFUL to `docs/statements.md`, a correct special case (D4⁺) of the classical result, TRUE as far as I can determine, and non-vacuous. Its conventions (cubic coefficients, discriminant sign, quantifier order, the dropped gradient hypothesis, rpow, max-norm ball) are all correct. The only substantive point is the owner decision in MINOR-1: Disc < 0 versus Disc ≠ 0.