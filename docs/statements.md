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
in scratch (lessons 23). Bridges go in `OscInt/API/Convert.lean`.

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
  proofs, through the bridges, in `OscInt/API/ConvertSanity.lean` and the consumer example, as for batch 1.

Clarification added after the API2 stamp (2026-11-07, from the two blind pre-proof referees, FAITHFUL ×2 on all
fourteen statements; the stamped text above and `OscInt/Statements/Convert.lean` are unchanged): (1) C7′ assumes
`HasFDerivAt` at every point; a neighbourhood of k would suffice and give a stronger statement, which would be a new
statement (candidate for the next batch); (2) C7′ is an equivalence despite its name `…OfHasFDeriv…`; (3) `disc` and
`Cubic.discr` are invariant under (a, b, c, d) ↦ (d, c, b, a), so sanity theorems on discriminant values cannot pin
the coefficient order; it is pinned by the derivative-level checks in `OscInt/API/ConvertSanity.lean`; (4) order of
work: no proof of a batch-2 statement existed in the repository or in the lead's scratch before the stamp and both
reviews; referee A wrote a one-line proof of C5 in its own scratch during its review (disclosed in
`review/2026-11-07-API2-pre-proof-answers.md`).
