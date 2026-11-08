# Statements

The mathematics of every frozen statement, in plain notation, with hypotheses, constants and quantifier order.
A statement appears here before its Lean file exists; the blind reviewer compares the two.

## S1. One-dimensional van der Corput lemma with amplitude

Source of the forms and constants: J. Roos and M. Praveen, `roos-j/lean-oscillatory` (commit `cf564e0`), Mathlib
PR #39406, following E. M. Stein, *Harmonic Analysis* (1993), Ch. VIII §1.2, Proposition 2 and Corollary.
Constant c_k = 5·2^{k−1} − 2: c₁ = 3, c₂ = 8, c₃ = 18.

Common notation. Real numbers a ≤ b. A real phase φ and a complex amplitude ψ on [a, b]. "f has derivative f′ on
[a, b]" means: f is continuous on the closed interval [a, b] and differentiable at every point of the open interval
(a, b) with derivative f′(x) there (the values of f′ at a and b play no role). The amplitude hypothesis: ψ has
derivative ψ′ on [a, b] in this sense (ψ complex-valued) and ψ′ is Lebesgue integrable on [a, b]. Write

  I(φ, ψ; a, b) = ∫_a^b e^{iφ(x)} ψ(x) dx,    A(ψ; a, b) = |ψ(b)| + ∫_a^b |ψ′(x)| dx.

The plain (amplitude-free) forms are the case ψ ≡ 1, ψ′ ≡ 0, where A = 1. Because the hypotheses on [a, b] are
inherited by every subinterval [c, d] ⊆ [a, b], each statement below holds on every subinterval; this is how the
amplitude forms are proved and is not stated separately.

**S1.1 (first derivative).** For all φ, φ′, φ″, ψ, ψ′, all a ≤ b and all ν > 0: if φ has derivative φ′ on [a, b],
φ′ has derivative φ″ on [a, b], φ′ is monotone (nondecreasing or nonincreasing) on (a, b), |φ′(x)| ≥ ν for all
x ∈ (a, b), and ψ satisfies the amplitude hypothesis, then

  |I(φ, ψ; a, b)| ≤ (3/ν) · A(ψ; a, b).

**S1.2 (second derivative, uniform in a linear term).** For all φ, φ′, φ″, ψ, ψ′, all a ≤ b, all μ > 0 and all
p ∈ ℝ: if φ has derivative φ′ on [a, b], φ′ has derivative φ″ on [a, b], |φ″(x)| ≥ μ for all x ∈ (a, b), and ψ
satisfies the amplitude hypothesis, then, with φ_p(x) = φ(x) + p x,

  |I(φ_p, ψ; a, b)| ≤ (8/√μ) · A(ψ; a, b).

**S1.3 (third derivative, uniform in a linear term).** As S1.2 with additionally φ″ having derivative φ‴ on [a, b]
and |φ‴(x)| ≥ μ on (a, b) in place of the bound on φ″:

  |I(φ_p, ψ; a, b)| ≤ 18 μ^{−1/3} · A(ψ; a, b).

Modelling choices (all explicit in the Lean header):
- S1.1 assumes φ′ differentiable on (a, b) (no continuity or integrability of φ″ is assumed), as the source
  development assumes φ ∈ C²; Stein's statement needs only φ′ monotone. This is weaker than Stein, matching the source.
- Every derivative used is continuous up to the endpoints (the "continuous on [a, b]" part of "has derivative on
  [a, b]" for φ′ and, in S1.3, φ″). The source assumes C^k on [a, b], which implies this.
- The amplitude needs ψ′ integrable rather than ψ ∈ C¹ (more general). Without integrability, Lean's integral of
  |ψ′| would be 0 by convention and the bound would be false, so the hypothesis is necessary.
- The linear term p x in S1.2, S1.3 is the brief's "invariant under adding a linear term": the hypotheses are on φ
  alone and p is arbitrary. S1.1 has no linear term (it would change the hypothesis on φ′).
- Constants are explicit numbers; no existential constant appears.

Clarification added after the S1 stamp (2026-11-05, from the adversarial review; the stamped text above is
unchanged): "weaker than Stein" means the *theorem* is weaker, because its hypotheses are stronger. Relative to Stein,
S1.1 excludes phases whose φ′ is monotone but not differentiable on (a, b) (e.g. piecewise linear φ′) or unbounded at
an endpoint; S1.2 and S1.3 exclude phases whose φ′ (and, for S1.3, φ″) is not continuous up to the endpoints. The
endpoint cases are recovered by applying the statement on [a, d] with d < b and letting d → b; the non-differentiable
case is not.

## S2, S3. Two-dimensional oscillatory integrals: non-stationary phase, nondegenerate stationary phase, fold

Common notation. Points k = (k₁, k₂) ∈ ℝ² (Lean: `ℝ × ℝ` with Lebesgue measure; its norm is the max norm, which
changes existential constants only). For p ∈ ℝ², p·k = p₁k₁ + p₂k₂. For a real phase Q and a complex amplitude A,
I(Q, A) = ∫_{ℝ²} e^{iQ(k)} A(k) dk. Directional derivatives: ∂_vΨ(k) = DΨ(k)v, ∂_w∂_vΨ(k), ∂_w∂_v∂_uΨ(k).
Hessian determinant H(Ψ, k) = ∂₁∂₁Ψ(k)·∂₂∂₂Ψ(k) − (∂₂∂₁Ψ(k))². k is a critical point of Ψ + p·(·) if
∂₁Ψ(k) + p₁ = ∂₂Ψ(k) + p₂ = 0. "Amplitude bound (n, K, M)": A is Cⁿ on ℝ², its support closure lies in K, and
‖DʲA(k)‖ ≤ M for all k and all j ≤ n (this replaces a sup-norm ‖A‖_{Cⁿ}: the bound holds with M = ‖A‖_{Cⁿ}).
A family of phases over a compact topological space Λ is "of class Cⁿ" if each Ψ_σ is Cⁿ on ℝ² and
(σ, k) ↦ DʲΨ_σ(k) is jointly continuous for j ≤ n. All constants below are existential and depend only on the
data quantified before them (family, K, K′, c, N), never on A, M, σ, p or m.

**S2.1 (non-stationary phase).** For every compact space Λ, every N ∈ ℕ, every family Ψ of class C^{N+1}, every
compact K ⊂ ℝ² and every c > 0 there is C such that for all A, M with amplitude bound (N, K, M), all σ ∈ Λ, all
p ∈ ℝ² with |∇Ψ_σ(k) + p| ≥ c for every k ∈ K, and all m ≥ 1:
  |I(m(Ψ_σ + p·), A)| ≤ C M m^{−N}.

**S2.2 (nondegenerate stationary phase, uniform in a linear term).** For every C⁴ phase Ψ on ℝ² and compact
K, K′ ⊂ ℝ² such that H(Ψ, k) ≠ 0 whenever k ∈ K is a critical point of Ψ + p·(·) for some p ∈ K′, there is C such
that for all A, M with amplitude bound (2, K, M), all p ∈ K′ and all m ≥ 1:
  |I(m(Ψ + p·), A)| ≤ C M m^{−1}.

**S3 (uniform fold estimate).** For every compact space Λ, every family Ψ of class C⁴ and compact K, K′ ⊂ ℝ² such
that for every σ and every k ∈ K either H(Ψ_σ, k) ≠ 0, or the Hessian of Ψ_σ at k is nonzero with
∂_v∂_v∂_vΨ_σ(k) ≠ 0 for every nonzero v in its kernel (rank one, third derivative along the kernel nonzero), there
is C such that for all A, M with amplitude bound (2, K, M), all σ, all p ∈ K′ and all m ≥ 1:
  |I(m(Ψ_σ + p·), A)| ≤ C M m^{−5/6}.

Modelling choices and deviations from the brief (explicit in the Lean header):
- Amplitude regularity C² in S2.2 and S3, where the brief writes ‖A‖_{C^N} and ‖A‖_{C⁴}. This is stronger than
  the brief; the lead's proof route (implicit function y*(x), one integration by parts in y, 1D van der Corput in x)
  uses two derivatives of A (PLAUSIBLE, not yet checked by a referee), and C² in S3 is what the brief's S4 bound
  with ‖A‖_{C²} needs.
- Phase regularity C⁴ in S2.2 and S3 (the route needs the Hadamard factor Q − Q(x, y*) = (y − y*)²H with H ∈ C²);
  C^{N+1} in S2.1 (N integrations by parts).
- Phases are defined on all of ℝ². A phase Cⁿ on a neighbourhood of K can be cut off to a global Cⁿ phase without
  changing any integral with supp A ⊆ K, so nothing is lost.
- S2.1 and S3 hold uniformly over a compact family Λ of phases (S4 applies them to the rescaled phases
  ε⁻³φ(ε·), ε ∈ [0, ε₀]); S2.1 is uniform over all p with the gradient bound, not only p in a compact set (S4's
  linear term is unbounded after rescaling). Taking Λ a point recovers the single-phase statements.
- Conditions are imposed at every point of K (not only on supp A), because C is uniform over all A supported in K.
- In S3, the third-derivative condition is required for every kernel vector; at a rank-one point the kernel is a
  line, so this is the same as for one spanning vector.

Clarification added after the S2/S3 stamp (2026-11-05, from the route referee; the stamped text above is
unchanged): the phase regularity C⁴ in S2.2 and S3 is used by second y-derivatives of the Hadamard factors h and K
(fourth derivatives of the phase), not by the factor H mentioned above, which the refereed route does not use.

Clarification added after the S2/S3 proofs (2026-11-06, adversarial review MINOR 9 and NIT 11; stamped text
unchanged): S3 requires the fold-or-nondegenerate condition at every point of K, independently of p, including
non-critical points; it therefore excludes, e.g., Ψ = k₁³ + k₂³ + k₁ with 0 ∈ K although that phase has no critical
point. This is a deliberate restriction (it makes the condition independent of K′ and is satisfied by the S4 use, the
rescaled D4 cubics on an annulus); a version imposing it only at critical points of Ψ_σ + p· for p ∈ K′ would need a
new statement. In the rank-one branch, "Hessian nonzero" is written `∃ v w, dd ≠ 0`; together with `hessDet = 0`
(the other disjunct failing) this is exactly rank one.

## S4. Uniform D4 (umbilic) estimate

Notation as in S2/S3. For a C⁴ phase φ on ℝ² write its cubic part at 0 as C(x, y) = (1/6) D³φ(0)[(x, y)³] =
a x³ + b x²y + c xy² + d y³, so a = ∂³₁₁₁φ(0)/6, b = ∂³₁₁₂φ(0)/2, c = ∂³₁₂₂φ(0)/2, d = ∂³₂₂₂φ(0)/6, and its
discriminant Disc C = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd.

**S4.1 (uniform D4 bound).** For every C⁴ phase φ on ℝ² with D²φ(0) = 0 and Disc C < 0 there are δ > 0 and C such that
for all A, M with amplitude bound (2, B̄(0, δ), M), all y ∈ ℝ² and all t ≥ 1:
  |∫ e^{i(tφ(κ) + y·κ)} A(κ) dκ| ≤ C M t^{−2/3}.

Modelling choices: no hypothesis ∇φ(0) = 0 (a gradient at 0 is absorbed by the uniformity in y); the brief's
"C has an isolated critical point" is implied by Disc C < 0 and not stated (a nonzero critical point of a binary
cubic is, by Euler's identity, a root at which the gradient vanishes, i.e. a repeated root, so Disc C = 0);
amplitude regularity C², as in the brief; phase regularity C⁴, which is what the route (dyadic rescaling,
Φ(ε, z) = ε⁻³φ(εz) is a C⁴ family on [0, ε₀] by Taylor's formula, S3 on annuli for bounded linear terms and S2.1
for large ones) needs. B̄(0, δ) is the max-norm ball. S4.2 (the limit t^{2/3}∫e^{itφ}A → c_C A(0)) is not yet
stated: the definition of c_C awaits the owner's decision (`docs/HANDOFF.md`).

Clarification added after the S4.1 stamp (2026-11-06, from the two pre-proof referees; the stamped text above is
unchanged): `disc < 0` is the hyperbolic umbilic D4⁺ only, as the brief ("negative discriminant") and its constant
Γ(1/3)²/(√3|Disc|^{1/6}) require. The classical uniform t^{-2/3} bound also holds for the elliptic umbilic D4⁻
(Disc > 0); for a binary cubic, Disc ≠ 0 is equivalent to an isolated critical point at 0. Widening to `disc ≠ 0`
would be a new statement (owner option, `docs/HANDOFF.md`).

**S4.1′ (uniform D4 bound, both umbilics).** As S4.1 with Disc C ≠ 0 in place of Disc C < 0: for every C⁴ phase φ
on ℝ² with D²φ(0) = 0 and Disc C ≠ 0 there are δ > 0 and C such that for all A, M with amplitude bound
(2, B̄(0, δ), M), all y ∈ ℝ² and all t ≥ 1: |∫ e^{i(tφ(κ) + y·κ)} A(κ) dκ| ≤ C M t^{−2/3}. (Disc ≠ 0 is
equivalent to "C has an isolated critical point at 0", the brief's first condition; it covers the hyperbolic
umbilic D4⁺, Disc < 0, and the elliptic umbilic D4⁻, Disc > 0. S4.1 is the case Disc < 0.)

**The constant.** For a binary cubic C with Disc C ≠ 0 put
  I = ∫₀^∞ cos u · u^{−1/3} du (improper),  J(C) = ∫₀^{2π} |C(cos θ, sin θ)|^{−2/3} dθ,  c_C = I · J(C) / 3.
(Polar coordinates: ∫₀^∞ e^{isr³} r dr = (1/3)|s|^{−2/3} ∫₀^∞ e^{±iu} u^{−1/3} du for s ≠ 0, and C(−z) = −C(z)
cancels the sine part; J(C) < ∞ exactly when the real linear factors of C are simple, i.e. Disc C ≠ 0.)

**S4.2 (D4 limit).** For every C⁴ phase φ with φ(0) = 0, ∇φ(0) = 0, D²φ(0) = 0 and Disc C ≠ 0 there is δ > 0 such
that for every amplitude A with amplitude bound (2, B̄(0, δ), M): t^{2/3} ∫ e^{itφ(κ)} A(κ) dκ → c_C A(0) as t → ∞.

**S4.3 (the constant is positive).** The improper integral I converges and I > 0 (by the alternating-series
argument of the brief: on [π/2 + (k−1)π, π/2 + kπ] the integrals alternate in sign with decreasing modulus and
∫₀^{π/2} + ∫_{π/2}^{3π/2} > 0); for Disc C ≠ 0 the integrand of J(C) is integrable and c_C > 0. No Gamma function
or Mellin identity enters the statement, and the proof must not use them (checked mechanically once proved).

**S4.4 (closed form).** I = Γ(2/3)/2, and c_C = Γ(1/3)² / (√3 |Disc C|^{1/6}) if Disc C < 0 (the brief's formula),
c_C = Γ(1/3)² / (Disc C)^{1/6} if Disc C > 0.

Modelling choices for S4.1′–S4.4: c_C is *defined* by the Gamma-free formula above, so that S4.2 (analysis), S4.3
(positivity, the brief's argument) and S4.4 (special-function identity) are independent statements; together S4.2
and S4.4 give the brief's limit with its closed-form constant, and S4.3 gives c_C ≠ 0 without Gamma identities.
Improper integrals are limits of interval integrals; powers are `Real.rpow`. Decision record:
`docs/decisions/2026-11-06-S4.md`. Numerical validation: `numerics/results-d4const-2026-11-06.txt`.

Clarification added after the S4.1′–S4.4 stamp (2026-11-06, from the two pre-proof referees; the stamped text and
`OscInt/Statements/D4Limit.lean` are unchanged): (1) the brief's S4 limit "t^{2/3}∫e^{itφ}A → c_C A(0) with
c_C = Γ(1/3)²/(√3|Disc C|^{1/6})" is S4.2 together with the Disc < 0 clause of S4.4, and "c_C ≠ 0" is S4.3;
(2) in Lean `angularMoment q` is always a real number: its integrand is integrable iff `disc q ≠ 0`, and otherwise
the Bochner value is the junk 0, so `d4Constant q = 0` when `disc q = 0`; every statement assumes `disc ≠ 0` or a
sign; (3) S4.4's first conjunct is about the `limUnder` value; that the improper integral converges is S4.3's first
conjunct; (4) the S4.3 proof-method rule is checked by `GammaFree.lean` (pre-registered before any proof).

Clarification on the S4.3 method (2026-11-06, from the S4.3 route referee; the stamped statement is unchanged): the
proof integrates by parts once, ∫₀^R cos u · u^{−1/3} du = R^{−1/3} sin R + (1/3)∫₀^R sin u · u^{−4/3} du, and then
applies the alternating-series argument to the humps of sin weighted by the decreasing u^{−4/3}, each pair
[2kπ, 2kπ + 2π] contributing ∫_{2kπ}^{2kπ+π} sin u (u^{−4/3} − (u + π)^{−4/3}) du > 0. This replaces the grouping
"∫₀^{π/2} + ∫_{π/2}^{3π/2} > 0" named above, which needs a numerical bound (6% margin). No Gamma or Mellin identity
is used (`GammaFree.lean`).

Correction to clarification (2) above (2026-11-06, S4b post-proof referee B, NIT 2): for q ≠ 0 the integrand of
`angularMoment q` is integrable iff `disc q ≠ 0`; for q = 0 it is identically `0 ^ (-2/3) = 0` (integrable, J = 0).

## Front end, batch 1 (F1, F2; 2026-11-06)

User-facing forms of frozen statements, in Mathlib's idiom, proved from them by bridge lemmas in `OscInt/API.lean`
(ROADMAP §2). Lean: `OscInt/Statements/FrontEnd.lean`.

**F1 (amplitude bounds from smoothness).** For every n ∈ ℕ, every compact K ⊆ ℝ² and every A : ℝ² → ℂ of class Cⁿ
whose support closure lies in K there is M with AmpBound(n, K, A, M), i.e. A ∈ Cⁿ, tsupport A ⊆ K and
‖D^j A(k)‖ ≤ M for all j ≤ n and all k. (A continuous function with compact support is bounded; D^j A has support in
tsupport A.) It turns the amplitude hypothesis of S2–S4 into Mathlib's `ContDiff ℝ n A ∧ tsupport A ⊆ K`; what is
lost is the uniformity in M, which the frozen statements keep.

**F2 (the D4 limit with its closed-form constant).** For every C⁴ phase φ on ℝ² with φ(0) = 0, ∇φ(0) = 0,
D²φ(0) = 0 and Disc C ≠ 0 (C the cubic part of φ at 0) there is δ > 0 such that for every A ∈ C² with
tsupport A ⊆ B̄(0, δ):
  t^{2/3} ∫_{ℝ²} e^{itφ(k)} A(k) dk → c(Disc C) · A(0) as t → ∞,
where c(D) = Γ(1/3)²/(√3 |D|^{1/6}) for D < 0 (the brief's constant, hyperbolic umbilic) and c(D) = Γ(1/3)²/D^{1/6}
for D > 0 (elliptic umbilic); `d4ClosedConstant`. This is S4.2 ∧ S4.4 with F1 for the amplitude. Modelling choices:
the integral is written out (the same term as `oscInt2`); the phase hypotheses and `cubicCoeffs` are those of S4.2
(nested `fderiv`s); B̄(0, δ) is the max-norm ball; c(D) for D = 0 is never used.

Process note: the bridge proofs of F1 and F2 (about 30 lines, from S4.2, S4.4 and Mathlib) were drafted in the lead's
scratch directory before this statement was stamped and reviewed; the statements were not changed afterwards, and
the claim "statement fixed before the proof" is therefore not made for F1 and F2.

## Front end, batch 2: conversions and Mathlib-idiom front ends (API2; session 4, 2026-11-07)

Order restored. Unlike batch 1 (process note above), this batch follows the statement-first order: the statements
below, their Lean file `OscInt/Statements/Convert.lean`, sanity theorems, challenge and comparator configuration are
committed, stamped, pinned and blind-reviewed before any proof of them is written or drafted, in the repository or
in scratch (lessons 23). Bridges go in `OscInt/API/Convert.lean` (since moved to `OscInt/Front/Convert.lean`, names unchanged).

Notation as in S2/S3 and S4. Points of ℝ² are `ℝ × ℝ` (max norm). e₁ = (1, 0), e₂ = (0, 1) (`coordVec 0`,
`coordVec 1`); for e : Fin 2 → ℝ, ofFin2 e = (e 0, e 1). DⁿΨ(k) is Mathlib's `iteratedFDeriv ℝ n Ψ k`, a continuous
n-linear map; DⁿΨ(k)[v₁, …, vₙ] its value. The Hessian matrix is H(Ψ, k)ᵢⱼ = D²Ψ(k)[eᵢ, eⱼ] (`hessianMatrix`), a
`Matrix (Fin 2) (Fin 2) ℝ`; its kernel is that of `Matrix.toLin' H` (vectors e : Fin 2 → ℝ with H e = 0). A linear
term is a continuous linear functional L : ℝ² → ℝ (Mathlib's `(ℝ × ℝ) →L[ℝ] ℝ`); L(k) = p·k with p = (L e₁, L e₂).
‖L‖ is its operator norm with respect to the max norm of ℝ × ℝ, which is |L e₁| + |L e₂|. The amplitude hypothesis
"(n, K, M) in Mathlib's idiom" is: A ∈ Cⁿ (`ContDiff ℝ n A`), `tsupport A ⊆ K`, and ‖DʲA(k)‖ ≤ M for all j ≤ n and
all k; this is `AmpBound n K A M` written out, so S2–S4 apply with the same M.

Two matrix forms of the fold condition, for a 2×2 real matrix H and a function T on Fin 2 → ℝ:
- span form (`FoldCondSpan H T`): det H ≠ 0, or there is e ≠ 0 with ker H = span{e} and T(e) ≠ 0;
- rank form (`FoldCondRank H T`): det H ≠ 0, or rank H = 1 and T(e) ≠ 0 for every nonzero e ∈ ker H.
`FoldOrNondegMatrix Ψ k` is the span form with H = H(Ψ, k) and T(e) = D³Ψ(k)[ofFin2 e, ofFin2 e, ofFin2 e].

**C1 (second derivatives).** If Ψ is C² on a neighbourhood of k (`ContDiffAt ℝ 2 Ψ k`), then for all v, w:
dd Ψ k v w = D²Ψ(k)[v, w].

**C2 (third derivatives).** If Ψ is C³ on a neighbourhood of k, then for all u, v, w: ddd Ψ k u v w = D³Ψ(k)[u, v, w].
(`ddd Ψ k u v w` is ∂_w∂_v∂_uΨ(k); equality in the stated argument order uses the symmetry of D³ for C³ functions.)

**C3 (Hessian determinant).** If Ψ is C² near k: hessDet Ψ k = det H(Ψ, k).

**C4 (cubic part).** If φ is C³ near 0, then for every κ ∈ ℝ²: with (a, b, c, d) = cubicCoeffs φ,
a κ₁³ + b κ₁²κ₂ + c κ₁κ₂² + d κ₂³ = (1/6) D³φ(0)[κ, κ, κ] (`cubicForm (cubicCoeffs φ) κ`). A binary cubic is
determined by its values, so this identifies cubicCoeffs φ as the coefficients of (1/6) D³φ(0)[κ, κ, κ].

**C5 (discriminant).** For all real a, b, c, d: disc (a, b, c, d) equals Mathlib's discriminant
`(Cubic.mk a b c d).discr` of the cubic polynomial a X³ + b X² + c X + d (the dehomogenisation of the binary cubic at
κ₂ = 1). Mathlib relates `Cubic.discr` to the roots (`Cubic.discr_eq_prod_three_roots`,
`Cubic.discr_ne_zero_iff_roots_nodup`).

**C6 (isolated critical point).** For every binary cubic q: disc q ≠ 0 if and only if 0 is an isolated critical
point of κ ↦ cubicForm q κ, i.e. the derivative of the cubic is nonzero at every point of a punctured neighbourhood of
0 (`∀ᶠ z in 𝓝[≠] 0, fderiv ℝ (cubicForm q) z ≠ 0`). (For a homogeneous cubic the critical set is a cone, so
"isolated" is the same as "the only critical point"; q = 0 has disc 0 and every point critical.)

**C7 (fold condition, matrix forms).** If Ψ is C³ near k, then FoldOrNondeg Ψ k holds if and only if the span form
holds for H(Ψ, k) and T(e) = D³Ψ(k)[ofFin2 e, ofFin2 e, ofFin2 e], and if and only if the rank form holds for them.

**C7′ (fold condition from derivative data).** If Ψ has derivative D₁(y) at every y (`HasFDerivAt Ψ (D₁ y) y`), D₁ has
derivative D₂(y) at every y (D₂(y) a continuous bilinear map), and D₂ has derivative D₃ at k, then FoldOrNondeg Ψ k
holds if and only if the span form holds for H'ᵢⱼ = D₂(k)[eᵢ][eⱼ] and T(e) = D₃[ofFin2 e][ofFin2 e][ofFin2 e]. This is
the form in which a user who has computed the derivatives of an explicit phase can discharge the fold condition.

**C8 (gradient lower bound).** If Ψ is differentiable at k and c ≥ 0, then: (i) GradLower Ψ p k c holds if and only if
c ≤ ‖Dψ(k̃)‖ where ψ(x) = Ψ(x₀, x₁) + p·(x₀, x₁) on Euclidean ℝ² (`EuclideanSpace ℝ (Fin 2)`) and k̃ is k there, i.e.
the Euclidean length of ∇Ψ(k) + p is at least c; (ii) GradLower Ψ p k c implies c ≤ ‖D(Ψ + p·)(k)‖ (operator norm on
ℝ × ℝ, the max norm, so ‖·‖ = |∂₁| + |∂₂|); (iii) c ≤ ‖D(Ψ + p·)(k)‖ implies GradLower Ψ p k (c/√2).

**C9 (amplitude bounds).** (i) If K is compact and AmpBound n K A M, then A is Cⁿ and has compact support
(`HasCompactSupport A`). (ii) If A is Cⁿ with compact support, then AmpBound n (tsupport A) A M for some M. With F1
this makes AmpBound(n, K, ·, some M) equivalent to "Cⁿ and tsupport ⊆ K" for compact K.

**FE-S2.1 (non-stationary phase, Mathlib idiom).** For every N ∈ ℕ, every C^{N+1} phase Ψ, compact K and c > 0 there is
C such that for every amplitude (N, K, M) in Mathlib's idiom, every linear term L with c ≤ ‖DΨ(k) + L‖ for all k ∈ K,
and every m ≥ 1: |∫ e^{im(Ψ(k) + L(k))} A(k) dk| ≤ C M m^{−N}. (S2.1 for one phase; the gradient bound in the max
norm's operator norm, which by C8 (iii) gives S2.1's hypothesis with c/√2.)

**FE-S2.2 (nondegenerate stationary phase, Mathlib idiom).** For every C⁴ phase Ψ, compact K ⊆ ℝ² and compact set K′ of
linear terms such that det H(Ψ, k) ≠ 0 whenever k ∈ K, L ∈ K′ and DΨ(k) + L = 0, there is C such that for every
amplitude (2, K, M) in Mathlib's idiom, every L ∈ K′ and every m ≥ 1: |∫ e^{im(Ψ(k) + L(k))} A(k) dk| ≤ C M m^{−1}.

**FE-S3 (uniform fold estimate, Mathlib idiom, one phase).** As FE-S2.2, with the hypothesis FoldOrNondegMatrix Ψ k
for every k ∈ K in place of the Hessian condition, and the bound C M m^{−5/6}.

**FE-S4.1′ (uniform D4 bound, Mathlib idiom).** For every C⁴ phase φ and reals a, b, c, d such that D²φ(0) = 0,
D³φ(0)[(x, y), (x, y), (x, y)] = 6(a x³ + b x²y + c xy² + d y³) for all x, y, and `(Cubic.mk a b c d).discr ≠ 0`, there
are δ > 0 and C such that for every amplitude (2, B̄(0, δ), M) in Mathlib's idiom, every linear term L and every
t ≥ 1: |∫ e^{i(tφ(κ) + L(κ))} A(κ) dκ| ≤ C M t^{−2/3}.

Modelling choices and what is omitted.
- Front ends are for one phase. Uniformity over compact families (S2.1, S3) stays in the frozen S2.1 and S3 and a
  family front end is a later statement (ROADMAP §2, parametric uniformity).
- The linear term is a functional L, not a vector p; S2.2 and S3 ask for a compact set of functionals (the image of a
  compact set of vectors under p ↦ p·(·) is one, and conversely). FE-S2.1 is uniform over every L with the gradient
  bound, as S2.1.
- B̄(0, δ) and ‖DΨ(k) + L‖ use the max norm of ℝ × ℝ, Mathlib's norm on a product; C8 converts to the Euclidean norm.
- The cubic part in FE-S4.1′ is given by its coefficients through the identity for D³φ(0); C4 shows that these are
  `cubicCoeffs φ`. The user names the coefficients, which is what makes the hypothesis checkable for an explicit
  formula.
- C1–C4, C7 assume smoothness only near the point (`ContDiffAt`), as their content is local.
- Pre-proof sanity theorems are on data (matrices, cubics, Euclidean coordinates); non-vacuity of the derivative
  hypotheses of the front ends for explicit phases (fold x³ + y², elliptic and generic D4 cubics) is shown after the
  proofs, through the bridges, in `OscInt/API/ConvertSanity.lean` (now `OscInt/Front/ConvertSanity.lean`) and the consumer example, as for batch 1.

Clarification added after the API2 stamp (2026-11-07, from the two blind pre-proof referees, FAITHFUL ×2 on all
fourteen statements; the stamped text above and `OscInt/Statements/Convert.lean` are unchanged): (1) C7′ assumes
`HasFDerivAt` at every point; a neighbourhood of k would suffice and give a stronger statement, which would be a new
statement (candidate for the next batch); (2) C7′ is an equivalence despite its name `…OfHasFDeriv…`; (3) `disc` and
`Cubic.discr` are invariant under (a, b, c, d) ↦ (d, c, b, a), so sanity theorems on discriminant values cannot pin
the coefficient order; it is pinned by the derivative-level checks in `OscInt/Front/ConvertSanity.lean`; (4) order of
work: no Lean proof of a batch-2 statement existed in the repository or in the lead's scratch before the stamp and both
reviews; referee A wrote a one-line proof of C5 in its own scratch during its review (disclosed in
`review/2026-11-07-API2-pre-proof-answers.md`).

Correction to (4) and to the opening paragraph of this section (2026-11-07, adversarial review M3; stamped files
unchanged): what the evidence shows is narrower. The statements are timestamped (stamp
`stamps/20261107T101640Z-4acb308f54f4`, RFC 3161 ×3 at 10:16:43Z, manifest of commit 4acb308). That the two blind
reviews came before any Lean proof rests on git order and on the lead's account; the reviews were not timestamped.
The proof route, including the C6 algebraic certificates, was drafted in the lead's scratch during the review window
(the process allows a route draft; it is not Lean proof code), so "no proof drafted" in the opening paragraph is too
strong and should read "no Lean proof written". `OscInt/Front/ConvertSanity.lean` was written while the proof agents
ran. Rule for later batches: stamp the reviews before launching proof agents (lessons 29).

Note on file locations (2026-11-07, after the adversarial review M5 and lessons 30): the bridge and helper files of
batches 1 and 2 moved from `OscInt/API/` to `OscInt/Front/`; declaration names are unchanged (namespace
`OscInt.API`), and `OscInt/API.lean` is now an imports-only entry point. The stamped
`OscInt/Statements/Convert.lean` still names the old path `OscInt/API/Convert.lean` in its docstring; it cannot change.

## Front end, batch 3: compact families, the classical fold hypothesis, local smoothness (API3; session 5, 2026-11-08)

Order. The statements below, their Lean file `OscInt/Statements/Family.lean` (with sanity theorems), the challenge
`Challenge/Family.lean` and `comparator-API3.json` are committed and stamped before the blind pre-proof reviews; the
review reports are committed and stamped (a second stamp) before any Lean proof of these statements is written, in
the repository or in scratch (lessons 23, 24, 29). The proof route may be drafted during the review window; it is not
Lean proof code, and it is disclosed if drafted.

Notation as in S2/S3, S4 and batch 2. A *parameter space* is either a compact topological space Λ (internal encoding,
`FamilyCk`) or a compact set S of a real normed space E (Mathlib idiom). For a family Ψ : E → ℝ² → ℝ, Ψ_σ = Ψ(σ, ·)
and `Function.uncurry Ψ` is (σ, k) ↦ Ψ_σ(k) on E × ℝ². "C^n on V × U" is `ContDiffOn ℝ n (Function.uncurry Ψ)
(V ×ˢ U)`. For a function smooth only on an open set U, DΨ(k), H(Ψ, k), D³Ψ(k) are Mathlib's `fderiv`,
`hessianMatrix` and `iteratedFDeriv` of the function on ℝ², used only at points k of U, where they depend only on the
values of Ψ near k; values of Ψ outside U are arbitrary (Ψ need not be continuous there).

**S2.2F (nondegenerate stationary phase, compact family).** For every compact topological space Λ, family Ψ with
`FamilyCk 4 Ψ`, compact K, K′ ⊆ ℝ² such that hessDet Ψ_σ k ≠ 0 whenever σ ∈ Λ, p ∈ K′, k ∈ K and k is a critical point
of Ψ_σ + p·(·), there is C such that for every amplitude with AmpBound 2 K A M, every σ ∈ Λ, p ∈ K′ and m ≥ 1:
|I(m(Ψ_σ + p·), A)| ≤ C M m^{−1}. (S2.2 with the family uniformity that S2.1 and S3 already have.)

**S3c (uniform fold estimate, classical hypothesis).** As S3 (compact Λ, `FamilyCk 4`, compact K, K′, rate m^{−5/6}),
with the hypothesis FoldOrNondeg Ψ_σ k required only when σ ∈ Λ, p ∈ K′, k ∈ K and k is a critical point of
Ψ_σ + p·(·). S3 requires it at every k ∈ K; at a non-critical point the integrand is non-stationary and nothing is
needed. This is the classical form (the S3 post-proof referee's note, `docs/STATUS.md`).

**C10 (families in Mathlib's idiom).** For every real normed space E, n ∈ ℕ and Ψ : E → ℝ² → ℝ with
`ContDiff ℝ n (Function.uncurry Ψ)`: for every S ⊆ E, the family (σ ∈ S) ↦ Ψ_σ satisfies `FamilyCk n` (S with the
subspace topology).

**FE-S2.1L (non-stationary phase, Mathlib idiom, compact family, local smoothness).** For every real normed space E,
N ∈ ℕ, Ψ : E → ℝ² → ℝ, compact S ⊆ E, open V ⊇ S, compact K ⊆ ℝ², open U ⊇ K, with Ψ of class C^{N+1} on V × U, and
c > 0, there is C such that for every amplitude (N, K, M) in Mathlib's idiom, every σ ∈ S, every linear term L with
c ≤ ‖DΨ_σ(k) + L‖ for all k ∈ K, and every m ≥ 1: |∫ e^{im(Ψ_σ(k) + L(k))} A(k) dk| ≤ C M m^{−N}.

**FE-S2.2L (nondegenerate stationary phase, Mathlib idiom, compact family, local smoothness).** For E, Ψ, S, V, K, U as
in FE-S2.1L with Ψ of class C⁴ on V × U, and a compact set K′ of linear terms such that det H(Ψ_σ, k) ≠ 0 whenever
σ ∈ S, L ∈ K′, k ∈ K and DΨ_σ(k) + L = 0, there is C such that for every amplitude (2, K, M) in Mathlib's idiom, every
σ ∈ S, L ∈ K′ and m ≥ 1: |∫ e^{im(Ψ_σ(k) + L(k))} A(k) dk| ≤ C M m^{−1}.

**FE-S3L (uniform fold estimate, Mathlib idiom, compact family, local smoothness, classical hypothesis).** As
FE-S2.2L, with FoldOrNondegMatrix Ψ_σ k (batch 2) required whenever σ ∈ S, L ∈ K′, k ∈ K and DΨ_σ(k) + L = 0, and the
bound C M m^{−5/6}.

**FE-S4.1′L (uniform D4 bound, Mathlib idiom, local smoothness).** For every φ : ℝ² → ℝ, open U ∋ 0 with φ of class
C⁴ on U, and reals a, b, c, d such that D²φ(0) = 0, D³φ(0)[(x, y), (x, y), (x, y)] = 6(a x³ + b x²y + c xy² + d y³) for
all x, y, and `(Cubic.mk a b c d).discr ≠ 0`, there are δ > 0 and C such that for every amplitude (2, B̄(0, δ), M) in
Mathlib's idiom, every linear term L and every t ≥ 1: |∫ e^{i(tφ(κ) + L(κ))} A(κ) dκ| ≤ C M t^{−2/3}.

**FE-S2.1l, FE-S2.2l, FE-S3l (one phase, local smoothness).** FE-S2.1L, FE-S2.2L, FE-S3L for a single phase
Ψ : ℝ² → ℝ of class C^{N+1} (resp. C⁴) on an open U ⊇ K (`ContDiffOn ℝ n Ψ U`), without a parameter; FE-S3l with the
classical (critical-points-only) fold hypothesis.

Modelling choices and what is omitted.
- Families in Mathlib's idiom are indexed by a compact subset of a real normed space and smooth jointly in
  (σ, k), which is how parameter-dependent phases arise in practice (dispersion relations depending on a velocity, a
  mass, a direction). A general compact Λ is available through S2.2F and S3c with C10. Joint smoothness is more than
  `FamilyCk` asks (continuity in σ of the k-derivatives); C10 is the conversion.
- Local smoothness is in k and in σ (V × U). The amplitude's support lies in K ⊆ U; outside U the phase is arbitrary.
- FE-S4.1′L is for one phase (no family): a family D4 statement needs the D4 normal form uniformly in the parameter,
  which is new analysis, not a re-assembly; it is deferred (ROADMAP §2).
- S2.2F and S3c keep the internal encoding (`FamilyCk`, `hessDet`, `FoldOrNondeg`, `p ∈ K′` vectors) so they can be
  compared with S2.2 and S3 line by line.
- Sanity theorems in `OscInt/Statements/Family.lean`: a two-member family of distinct nondegenerate quadratics with a
  critical point present, and a bite (a degenerate member) for S2.2F; for S3c the bite x³ + y³ on K = B̄(0, 2),
  K′ = {(−3, −3)}, where the classical hypothesis holds non-vacuously but FoldOrNondeg fails at 0 ∈ K (so S3 does not
  apply); for C10 a genuinely parameter-dependent family; for local smoothness |k₁|, C⁴ on {k₁ > 0} but not C¹ on ℝ²,
  and the family σ|k₁| + k₂², C⁴ on ℝ × {k₁ > 0}. Derivative hypotheses of the Mathlib-idiom forms for explicit phases
  (an arccos-type dispersion relation, a phase singular outside the support) are shown after the proofs, through the
  bridges and the consumer example, as for batch 2.

Clarification added after the API3 stamp (2026-11-08, from the two blind pre-proof referees, FAITHFUL and TRUE ×2 on
all ten statements; the stamped text above and `OscInt/Statements/Family.lean` are unchanged; answers in
`review/2026-11-08-API3-pre-proof-answers.md`): (1) S2.2F does not follow from the frozen S2.2 and S3; it is a
re-assembly of the proved internal parts (`docs/proof-API3.md`, R1). (2) C10 serves families smooth on all of E × ℝ²;
the FE-L forms do not use it (they use a cut-off); a `ContDiffOn` form of C10 and a local form for families only
continuous in σ are candidates for a later batch. (3) The gain of the local forms is in what the user has to prove
(no hand-made cut-off), not in mathematical reach: batch 2 plus a cut-off covers the same phases. (4) "Matrix
fold-or-nondegenerate condition" in FE-S3L/FE-S3l is `FoldOrNondegMatrix`, the span form (C7 relates it to the rank
form). (5) The S3c bite in the stamped file (K′ = {(−3, −3)}) has nondegenerate critical points, so S2.2 already gives
that bound; the bite that neither S2.2 nor S3 covers is `OscInt.API.FamilySanity.foldCrit_fold_bite` (K′ = {(0, −3)}).
(6) Lessons 11: the stamped sanity theorems restate the hypotheses; the sanity theorems that exercise the statement
constants are in `OscInt/Front/FamilySanity.lean` (negative controls `docs/replay/2026-11-08-API3-sanity-plants.txt`).
(7) Metric balls on ℝ × ℝ are max-norm squares; for a phase smooth on a Euclidean disc use the set
`{k | k.1 ^ 2 + k.2 ^ 2 < 1}` for U.

Correction to the "Order" paragraph of batch 3 (2026-11-08, adversarial review m3; `review/2026-11-08-API3-answers.md`):
what the stamps show is that no proof file was committed before the review stamp
`stamps/20261108T010546Z-7bb457958327` (01:05:48Z; neither stamp's manifest contains a proof file of the batch). That
no Lean proof existed in scratch before it rests on the lead's statement; the scratch birth times the adversarial
referee observed (first proof file 01:06:25Z) are consistent with it but are not durable evidence. Also (adversarial
M1–M3): every statement of the batch now has a sanity theorem through its constant (`OscInt/Front/FamilySanity.lean`,
`FamilySanity2.lean`); such theorems cannot detect a plant that weakens a hypothesis; answering the pre-proof MAJOR this
way instead of re-freezing awaits the owner's decision on CONTRIBUTING step 5.

## Batch GD: global decay from a local classification; sharpness; the 2D lattice Laplacian (session 6, 2026-11-08)

Order. As batch 3: the statements below, `OscInt/Statements/Global.lean` (with sanity theorems), sanity theorems through
the constants with planted controls (`OscInt/Front/GlobalSanity.lean`, outputs under `docs/replay/plants/`), the
challenge `Challenge/Global.lean` and `comparator-GD.json` are committed and stamped before the blind pre-proof
reviews; the reports are committed and stamped before any Lean proof of these statements is written.
Numeric pre-registration that informed the statements (tooling, not evidence): `docs/prereg/2026-11-08-P1-classify.md`,
result `numerics/results-classify-2026-11-08.txt` (PASS: the lattice Laplacian and six arccos dispersion relations are
"nondegenerate, fold, or one of four D4 points (±π/2, ±π/2)" on the torus, the cusp control is detected; the diagonal
limit of the lattice kernel agrees with the constant below to 7.5·10⁻⁷ at n = 2560).

Notation as in batch 3. I(Ψ, L, A, m) = ∫_{ℝ²} e^{im(Ψ(k) + L(k))} A(k) dk. An *amplitude (2, K, M)* is a C² function
A : ℝ² → ℂ with tsupport A ⊆ K and ‖D^j A(k)‖ ≤ M for j ≤ 2 and all k (Mathlib's `iteratedFDeriv`). A *D4 point* of Ψ
is a point k₀ with D²Ψ(k₀) = 0 and D³Ψ(k₀)[(x, y)³] = 6(a x³ + b x²y + c xy² + d y³) for some reals a, b, c, d with
`(Cubic.mk a b c d).discr ≠ 0` (the discriminant of the binary cubic, C5); this is FE-S4.1′L's hypothesis moved from 0
to k₀. *Nondegenerate or a fold* at k is `FoldOrNondegMatrix Ψ k` (batch 2: det H ≠ 0, or the kernel of H is a line
spanned by e with D³Ψ(k)[e, e, e] ≠ 0).

**GD-C (global decay, classification at critical points).** For every Ψ : ℝ² → ℝ, compact K, open U ⊇ K, compact set
K′ of linear terms and finite set D ⊆ U such that Ψ is C⁴ on U, every point of D is a D4 point, and for every L ∈ K′
every critical point k ∈ K \ D of Ψ + L is nondegenerate or a fold: there is C with |I(Ψ, L, A, m)| ≤ C M m^{−2/3}
for every amplitude (2, K, M), every L ∈ K′ and every m ≥ 1.

**GD (global decay, all linear terms).** For Ψ, K, U, D as in GD-C such that every point of K \ D is nondegenerate or a
fold (at every point, not only at critical points): the same bound C M m^{−2/3} for every linear term L. This is the
form a dispersive estimate needs: sup over x of |∫ e^{i(tω(k) + x·k)} A(k) dk| is the sup over L = x/t.

**GD-F, GD-N.** If every point of K is nondegenerate or a fold: C M m^{−5/6} for every L. If every point of K is
nondegenerate (det H ≠ 0): C M m^{−1} for every L.

**SH (sharpness lemma).** For I : ℝ → ℂ, σ ∈ ℝ, c ∈ ℂ \ {0} with m^σ I(m) → c as m → ∞: eventually
|I(m)| ≥ (|c|/2) m^{−σ}, and for no σ′ > σ and no C does |I(m)| ≤ C m^{−σ′} hold eventually. The same for sequences
I : ℕ → ℂ.

**T1 (unfolding the torus).** There is a C^∞ function η : ℝ² → ℝ with tsupport η ⊆ B̄(0, 4) (max norm) such that
∫_{[−π, π]²} g = ∫_{ℝ²} η g for every continuous g : ℝ² → ℂ that is 2π-periodic in each variable.

**T6 (dispersive decay of the 2D lattice Laplacian).** With K(t, x) = ∫_{[−π, π]²} e^{i(t(cos k₁ + cos k₂) + x·k)} dk:
there is C with |K(t, x)| ≤ C t^{−2/3} for all t ≥ 1 and all x ∈ ℤ².

**T6L (its leading term on the diagonal).** (−1)ⁿ n^{2/3} K(n, (n, n)) → Γ(1/3)² 48^{1/6}/√3 as n → ∞, n ∈ ℕ
(`d4ClosedConstant (−1/48)`, batch 1). With SH this shows that the rate t^{−2/3} in T6 is sharp.

Modelling choices and what is omitted.
- The rate in GD-C and GD is 2/3 whether or not D is empty; GD-F and GD-N give the better rates when no D4 point
  (resp. no degenerate point) is present. "The worst type present decides the rate" is the choice of statement.
- The fold condition is required at every non-D4 point (GD) or at every non-D4 critical point for L ∈ K′ (GD-C). Near
  a D4 point, the critical points of Ψ + L for L near −DΨ(k₀) are close to k₀; the hypothesis requires them to be
  folds or nondegenerate (checked by hand for the cubic x³ + y³, CONJECTURED for every homogeneous cubic with
  nonzero discriminant; for the phases above the numeric check found no exception). Cusps (A₃) and worse are not covered (no local A₃ statement exists yet).
- D is a `Finset` contained in U; its points need not lie in K.
- K(t, x) is the kernel of e^{itH} for H = 2cos k₁ + 2cos k₂ in Fourier variables up to the factor (2π)^{−2}, the time
  scale 2 and the phase e^{−4it} of −Δ = 4 − 2cos k₁ − 2cos k₂; none changes |K| up to constants. The ℓ¹ → ℓ^∞ norm of
  the propagator is sup_x |K(t, x)|/(2π)² (a consumer example, not a statement).
- T1 is an existence statement: the weight is not named in the statement (the proof constructs it). Lattice users
  apply GD to the amplitude η · a for a smooth periodic a.
- T6L is stated along x = (n, n) at integer times n, where the only critical point is the D4 point (π/2, π/2) with
  phase value π (hence (−1)ⁿ) and cubic part (κ₁³ + κ₂³)/6, disc = −1/48. An independent route (FOLKLORE, not
  formalised): K(n, (n, n)) = (2π)²(−1)ⁿ Jₙ(n)² and Jₙ(n) ~ Γ(1/3)/(2^{2/3} 3^{1/6} π n^{1/3}) give the same constant.
- Not in this batch, with reasons: the D4 statement uniform over a compact family of phases (needs the D4 normal form
  uniformly in the parameter; new analysis); the 2D stationary-phase leading term (P2; the proof needs a Morse lemma
  with parameters, not available; draft statement in `docs/design/leading-term.md`); the 1D lattice kernel (T0) and the
  cone statements (T4/T5′/T6′).

Clarification added after the GD stamp (2026-11-08, from the two blind pre-proof referees, FAITHFUL and TRUE ×2 on all
eight statements; `OscInt/Statements/Global.lean` unchanged; answers `review/2026-11-08-GD-pre-proof-answers.md`):
(1) Near a D4 point every other degenerate point is a fold: for a binary cubic with nonzero discriminant every nonzero
degenerate point has rank one and is a fold, and by continuity of D²Ψ, D³Ψ the same holds in a punctured
neighbourhood of a D4 point of a C⁴ phase (argued on paper by both referees, not formalised; it replaces the
"CONJECTURED" above). The GD route does not need it. (2) GD's pointwise hypothesis is not stronger than the classical
one: over all L every point is a critical point of Ψ + L for L = −DΨ(k). (3) GD-C and GD keep the rate 2/3 for D = ∅;
use GD-F or GD-N for the better rates. (4) T6 is for t ≥ 1; for a dispersive estimate on all of ℝ use
K(−t, x) = conj K(t, −x) and |K(t, x)| ≤ (2π)² for |t| < 1 (consumer notes, not statements). (5) T6L's cubic
coefficients are the Taylor coefficients D³φ(0)/6 (the convention of `cubicCoeffs` and F2). (6) For the arccos
relations the fold condition along the degenerate curve is numerical only; using GD for them needs a Lean proof of
the classification, which is open.

Clarification after the GD post-proof and adversarial reviews (2026-11-08; statements unchanged; answers
`review/2026-11-08-GD-post-proof-answers.md`): (8) The ℓ¹ → ℓ^∞ norm of a convolution operator on ℤ² is the supremum
of its kernel, so T6 bounds that norm; what is machine-checked in `examples/consumer/ConsumerLattice.lean` is the
upper bound for finitely supported data and for the propagator defined by its kernel (that this is the solution
operator of `i∂ₜu = Hu` is the standard Fourier representation, not proved there). (9) T6 and T6L concern the free
discrete Laplacian; potentials are not covered.

## Batch LE: explicit constants for the 1D and 2D lattice kernels (session 7, 2026-11-08)

Order. As batch GD: the statements below, `OscInt/Statements/LatticeExplicit.lean`, sanity theorems with planted
controls (`OscInt/Front/LatticeExplicitSanity.lean`), the challenge `Challenge/LatticeExplicit.lean` and
`comparator-LE.json` are committed and stamped before the blind pre-proof reviews; the reports are committed and
stamped before any Lean proof of these statements is written. Numeric pre-registration that informed the statements
(tooling, not evidence): `docs/prereg/2026-11-08-LE-lattice-constants.md` (registered d814381, amendment 1 d26b9a4),
result `numerics/results-lattice1-2026-11-08.txt` (PASS: the bound holds on the grid with ratio ≤ 0.088; exponent
−0.334; the largest t^{1/3}|I|/(2π) found is 0.78561 ≤ Landau's 0.7858; the factorisation agrees to 5·10⁻¹³ with a
non-product quadrature; all three controls fail as required).

Why. T6 has an existential constant. Because the 2D kernel factorises (`docs/prior_art.md`, "Lattice kernels"), an
explicit constant for the 1D kernel gives one for T6. Downstream asked for explicit constants first (ROADMAP).

Notation. I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk for real t, ξ (Lean: the interval integral over [−π, π]).
K(t, x) is T6's kernel (`latticeKernel`, batch GD, unchanged). A = 24 · 2^{1/4} ≈ 28.541, B = 36 · 2^{1/6} ≈ 40.409.

**T0E (explicit bound for the 1D lattice kernel).** For every t > 0 and every real ξ:
|I(t, ξ)| ≤ A t^{−1/2} + B t^{−1/3}.

**T6F (the 2D kernel factorises).** For every real t and x ∈ ℤ²: K(t, x) = I(t, x₁) I(t, x₂).

**T6E (explicit constant for T6).** For every t ≥ 1 and x ∈ ℤ²: |K(t, x)| ≤ (A + B)² t^{−2/3}. ((A + B)² ≈ 4754.)

Route (for the reviewers' orientation only; the proofs come after the reviews). T0E: split [−π, π] at ±π/4, ±3π/4. On
the three pieces where |cos k| ≥ 1/√2 apply S1.2 (`VdC2Statement`, constant 8/√μ) to φ = t cos with μ = t/√2; on
the two where |sin k| ≥ 1/√2 apply S1.3 (`VdC3Statement`, 18 μ^{−1/3}); amplitude 1, linear term ξ. This gives
3 · 8 · 2^{1/4} t^{−1/2} + 2 · 18 · 2^{1/6} t^{−1/3}. T6F: Fubini on [−π, π]² and e^{a+b} = e^a e^b. T6E: T6F, T0E
twice, and t^{−1/2} ≤ t^{−1/3} for t ≥ 1.

Modelling choices and what is omitted.
1. ξ is real in T0E (stronger than integer ξ, which is all T6F needs); the S1 bounds are uniform in the linear term.
2. T0E is stated for t > 0: at t = 0 Lean's `Real.rpow` gives 0^{−1/2} = 0 and the bound would be false; t < 0
   reduces to t > 0 by I(−t, ξ) = conj I(t, −ξ).
3. The constants are far from sharp: at large t the truth is about 2π · 0.675 t^{−1/3} (Landau's constant 0.7858 is the
   sup over all t > 0), so B is about 9.5 times too large, and on the registered grid (A + B)² t^{−2/3} exceeds
   sup_x |K(t, x)| by a factor of at least 200 for t ≥ 1 (criterion (e): ratio 0.0048). Sharper
   constants are future work; these are the ones the frozen S1 constants give by the route above.
4. The normalisation (2π)^{−2}, the time scale and the phase e^{−4it} are omitted as in T6.
5. The Bessel identification I(t, n) = 2π iⁿ Jₙ(t) is not stated (Mathlib has no Bessel functions at the pin).
