<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

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

Clarifications after the pre-proof reviews (`review/2026-11-08-LE-pre-proof-{A,B}.md`; no statement text changed):
6. **Where the explicit bounds have content** (review A, MAJOR). The trivial bounds are |I| ≤ 2π and |K| ≤ 4π². T0E's
   right side falls below 2π only for t > 518.5, and T6E's below 4π² only for t > ((A + B)²/(4π²))^{3/2} ≈ 1321.5.
   On 1 ≤ t ≤ 1321 T6E says less than |K| ≤ 4π²; use min(4π², (A + B)² t^{−2/3}). The constants are what the frozen
   S1 constants 8 and 18 give by the route above; sharper ones are future work.
7. **Landau's constant applies to integer ξ only** (review B, MINOR-1). For non-integer ξ, I(t, ξ) is an Anger-type
   integral, not 2π i^ξ J_ξ(t), and sup t^{1/3}|I|/(2π) over real ξ exceeds 0.7858: at (t, ξ) = (5.7972479262309164,
   4.404) it is 0.80366 (review B, two methods; recomputed by the lead with Simpson's rule, N = 200000). The comparison
   in item 3 ("B about 9.5 times too large") is for integer ξ.
8. **Better bounds from the same statements** (review A, MINOR). Composing T6F with T0E directly gives
   |K(t, x)| ≤ (A t^{−1/2} + B t^{−1/3})², better than T6E by up to (A + B)²/B² ≈ 2.9 at large t. T6E with `0 < t` in
   place of `1 ≤ t` is also true (for t ≤ 1, |K| ≤ 4π² < (A + B)² t^{−2/3}; review B, MINOR-2); a corollary, not a
   re-freeze.
9. **User normalisation** (reviews A and B). For H = 2 cos k₁ + 2 cos k₂ on ℓ²(ℤ²), the kernel of e^{itH} is
   (2π)^{−2} K(2t, x), so ‖e^{itH}‖_{ℓ¹→ℓ^∞} ≤ (2π)^{−2}(A + B)²(2t)^{−2/3} ≈ 75.9 t^{−2/3} for t ≥ 1/2. Negative times
   reduce to positive ones by |K(−t, x)| = |K(t, −x)| (not formalised).
10. **What the numeric pre-registration could and could not catch** (adversarial review n6). Criterion (a) passed at a
   ratio of 0.088, so it would have caught a draft constant that is too small by more than a factor of about 11, and no
   smaller error; the constants are pinned by the proof via the S1 constants, not by the numerics.


## Batch VT: the global decay estimates for vector-valued amplitudes (session 7, 2026-11-08)

Order. As batch LE: statements `OscInt/Statements/Vector.lean`, sanity theorems with planted controls
(`OscInt/Front/VectorSanity.lean`, `docs/replay/2026-11-08-VT-sanity-plants.txt`), challenge `Challenge/Vector.lean` and
`comparator-VT.json` are committed and stamped before the blind pre-proof reviews; the reports are committed and
stamped before any Lean proof. No numeric pre-registration: the batch transfers proved bounds and makes no new
quantitative claim. Design and route: `docs/design/vector-amplitudes.md` §1 (duality).

Why. Two-band lattice models, spectral projections and matrix symbols have amplitudes with values in matrices or other
Banach spaces. The acceptance model of the owner's batch VV (a non-separable two-band model) is deferred
(`docs/design/vector-amplitudes.md` §5: the QWZ m = 3 candidate failed its decay check); this batch is the transfer
only.

Notation as in batch GD. For a complex Banach space E (a Lean `Type` with `NormedAddCommGroup E`, `NormedSpace ℂ E`,
`CompleteSpace E`), an *E-valued amplitude (2, K, M)* is A : ℝ² → E of class C² (real derivatives) with tsupport A ⊆ K
and ‖D^j A(k)‖ ≤ M for j ≤ 2. I(Ψ, L, A, m) = ∫ e^{im(Ψ(k) + L(k))} · A(k) dk (Bochner integral in E, scalar action).

**GD-C-V, GD-V, GD-F-V, GD-N-V.** Exactly GD-C, GD, GD-F, GD-N (same hypotheses on Ψ, K, U, D, K′, same rates
m^{−2/3}, m^{−2/3}, m^{−5/6}, m^{−1}) for E-valued amplitudes, with one constant C, chosen after the phase data and
before E, valid for every E: ‖I(Ψ, L, A, m)‖ ≤ C · M · rate(m).

Route (for orientation; proofs after the reviews). For ‖·‖-norming functionals: given the integral v ∈ E, Hahn–Banach
(`exists_dual_vector''`) gives ℓ ∈ E* with ‖ℓ‖ ≤ 1 and ℓ(v) = ‖v‖; ℓ commutes with the integral
(`ContinuousLinearMap.integral_comp_comm`, the integrand is continuous with compact support); ℓ ∘ A is a scalar
amplitude (2, K, M) (`iteratedFDeriv` of a composition with a continuous linear map, operator norm ≤ 1, on ℓ restricted
to ℝ-scalars); the scalar statement with its constant C gives the bound. So the constant of the scalar statement works
for every E.

Modelling choices and what is omitted.
1. E ranges over `Type` (universe 0), not over all universes (the commitment tooling hashes closed constants).
2. The scalar statements are the case E = ℂ (`•` is `*`); this is checked in the sanity file.
3. Real-valued amplitudes are covered through E = ℂ; real Banach spaces E are not (complexify).

Clarifications after the pre-proof reviews (`review/2026-11-08-VT-pre-proof-{A,B}.md`; no statement text changed):
4. **Integrability in the route** (A NIT-1, B §2). With Ψ smooth only on U, the integrand k ↦ e^{im(Ψ+L)(k)} • A(k)
   is still continuous: at k outside tsupport A it vanishes on a neighbourhood; at k ∈ tsupport A ⊆ K ⊆ U, Ψ is
   continuous (U open). It has compact support, so it is integrable, and the junk value of the Bochner integral never
   occurs.
5. **The vector statements are equivalent to the scalar ones** (A §4, B §2): E = ℂ gives the scalar statement, and the
   scalar statement gives the vector one with the same constant by duality. One constant for every E costs nothing.
6. **Matrices** (A MINOR-3, B NIT-1). `Matrix (Fin n) (Fin n) ℂ` has no global norm instance in Mathlib. Use the
   definitionally equal `Fin n → Fin n → ℂ` (entrywise sup norm), `(Fin n → ℂ) →L[ℂ] (Fin n → ℂ)` (operator norm), or
   `attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace`; all elaborate against the
   frozen statements (both referees checked). The E-uniform constant lets the user pick any of these norms.
7. **Universes and real spaces** (A MINOR-1, B NIT-2, NIT-3). `E : Type` only; a universe-polymorphic transfer theorem
   (not a frozen statement) can be added with the proofs. Real Banach spaces are not covered; Mathlib has no convenient
   complexification, so this is a real limitation for users.
8. **Order, precisely** (post-proof A NIT-1). The sanity file the pre-proof referees saw is the one in the statement stamp
   (`stamps/20261108T235416Z-961cebc296ef`); three theorems were added in answer to them and that version is in the review
   stamp (`stamps/20261109T002419Z-45505299011a`); more data were added after the post-proof reviews. The route review was
   committed before the part's proof entered the repository; the lead's draft existed in the session scratchpad meanwhile
   (lessons 42), so the claim is about commit order, which no third-party timestamp covers (post-proof A MINOR-2,
   adversarial m4). Proved: `OscInt/Front/VectorFinal.lean`; replay `docs/replay/2026-11-09-session7-VT-verify-all.txt`.

## Batch A3: the k-th derivative van der Corput bound and the uniform cusp (A3) bound (session 8, 2026-11-09)

Why (owner decision 2026-11-09, `docs/ROADMAP.md` I3): published classifications show that the discrete Klein–Gordon
equation, the lattice wave equation, the triangular lattice and the King's graph are each blocked only by A3 (cusp)
points (`docs/prior_art.md`, "Singularities of lattice dispersion relations"), and QWZ at m = 3 has exact A3 points
(`docs/design/vector-amplitudes.md` §6). OscInt's global theorems allow nondegenerate points, folds and D4 points
only. Pre-freeze checks: `numerics/a3/statement_checks.py`, output `numerics/results-a3-statements-2026-11-09.txt`.

### S1.k (k-th derivative, k ≥ 2, uniform in a linear term)

Notation as in S1. A *derivative chain of length k on [a, b]* is a sequence of functions D₀, D₁, …, D_k (only these
k + 1 are used) such that D_{j+1} is the derivative of D_j on [a, b] in the sense of S1 (D_j continuous on [a, b],
differentiable on (a, b) with derivative D_{j+1}) for every j < k. Put c_k = 5·2^{k−1} − 2.

**S1.k.** For every k ≥ 2, every derivative chain D₀, …, D_k on [a, b] (a ≤ b), all μ > 0 and p ∈ ℝ, and every ψ
satisfying the amplitude hypothesis of S1: if |D_k(x)| ≥ μ for all x ∈ (a, b), then, with φ = D₀,

  |∫_a^b e^{i(φ(x) + p x)} ψ(x) dx| ≤ c_k μ^{−1/k} · A(ψ; a, b).

Source: Stein, *Harmonic Analysis* (1993), Ch. VIII §1.2, Proposition 2 (constant c_k = 5·2^{k−1} − 2 for k ≥ 2) and
its Corollary (amplitude), as for S1. S1.2 and S1.3 are the cases k = 2, 3 with the same constants (c₂ = 8, c₃ = 18;
check E4); the sanity file derives both from S1.k. The classical proof is an induction on k with
c_{k+1} = 2c_k + 2 (split (a, b) where |D_k| ≥ δ from an interval of length ≤ 2δ around the zero of the monotone D_k,
choose δ = μ^{−1/(k+1)}), then integration by parts for the amplitude.

Modelling choices: as S1.2/S1.3 (endpoint continuity of D₀, …, D_{k−1}; ψ′ integrable; the linear term p x is
arbitrary, and adding it does not change D_k for k ≥ 2). k = 1 is excluded (S1.1 needs monotonicity of φ′). The
constant is explicit; Lean writes it as `(5 * 2 ^ (k - 1) - 2 : ℝ)` with `k - 1` a natural number (k ≥ 2) and the power
`μ ^ (-(1 : ℝ) / k)` as `Real.rpow` with μ > 0. Omitted: sharper constants (Stein's c_k is not optimal; exploratory
values for k = 4, 5 are 2.32 and 2.67 against c₄ = 38, c₅ = 78, `numerics/results-a3-statements-2026-11-09.txt`, N2).

### S5.1 and S5.1′ (uniform cusp bound, decay t^{−3/4})

Notation as in S2/S3 and S4, with derivatives written as the multilinear maps D²φ(k₀), D³φ(k₀), D⁴φ(k₀)
(`iteratedFDeriv`, as in GD's D4 points). A point k₀ is an **A3 (cusp) point** of a C⁴ phase φ on ℝ² if there are
v, w ∈ ℝ² with
  (i) D²φ(k₀)[v, z] = 0 for every z (v is in the kernel of the Hessian),
  (ii) D²φ(k₀)[w, w] ≠ 0 (the Hessian is not zero, hence of rank one, and v ≠ 0 by (iv)),
  (iii) D³φ(k₀)[v, v, v] = 0 (not a fold),
  (iv) g₄ := D²φ(k₀)[w, w] · D⁴φ(k₀)[v, v, v, v] − 3 (D³φ(k₀)[v, v, w])² ≠ 0.
It is a **stable A3 point** if moreover (v) D³φ(k₀)[v, v, w] ≠ 0.

Meaning. (iv) is h times 24 times the u⁴ coefficient of the reduced function g(u) = φ(k₀ + uv + s(u)w), where s(u)
solves ∂_s φ = 0 and h = D²φ(k₀)[w, w] (splitting lemma; `numerics/census/spec_checks.py`, check R1). By (i) and (iii),
replacing w by w + λv changes neither D²φ[w, w] nor D³φ[v, v, w] (check R3), and v is unique up to scale, so (iv) and (v)
do not depend on the choice of (v, w): the existential form is equivalent to "for every kernel vector v ≠ 0 and every
w ∉ span v". (iv) is the reduced quartic, not the straight-line quartic D⁴φ[v, v, v, v]: the phase (y + x²/2)² has
D⁴φ(0)[e₁⁴] = 6 ≠ 0 but g₄ = 0 and a whole curve of degenerate critical points (check E3-trap). (v) is the coupling of the
kernel and transverse directions; when it holds, the gradient map has a Whitney cusp at k₀ and, after the anisotropic
rescaling (u, s) ↦ (εu, ε²s), the model h s²/2 + (T/2)u²s + (Q/24)u⁴ has only nondegenerate and fold points away from
the origin (check E1, g₃ = h²u·g₄ on its degenerate curve); when (v) fails, the model h s²/2 + (Q/24)u⁴ is degenerate
with g₃ = 0 along a whole line (check E2). Every A3 point known in the corpus is stable: discrete Klein–Gordon (mass 1)
at (±π/2, ±π/2), D³ω[v, v, w] = −√5/625 with v = (−√5/25, √5/25), w = (1, 0); QWZ (m = 3) at (±a, ±a),
a = arccos(−1/3), D³ω[v, v, w] = 128√130/53551875 (computed exactly before this freeze; the census, ROADMAP I1, will
record them).

**S5.1 (uniform stable-cusp bound).** For every C^∞ phase φ on ℝ² for which 0 is a stable A3 point there are δ > 0 and
C such that for all A, M with amplitude bound (2, B̄(0, δ), M), all y ∈ ℝ² and all t ≥ 1:
  |∫ e^{i(tφ(κ) + y·κ)} A(κ) dκ| ≤ C M t^{−3/4}.

**S5.1′ (uniform cusp bound).** As S5.1 for every C^∞ phase φ for which 0 is an A3 point (condition (v) dropped).
S5.1 is the case of S5.1′ with (v); both are frozen, as S4.1 and S4.1′ were, because their proof routes differ.

Sources (records checked against Crossref in the logged sweep `review/2026-11-09-CENSUS-prior-art-sweep.md`; the
texts were not read by the lead, so the attribution is FOLKLORE until a referee or the lead reads them): uniform
estimates for simple singularities, J. J. Duistermaat, Comm. Pure Appl. Math. 27 (1974) 207–281,
DOI 10.1002/cpa.3160270205; the oscillation index of A3 (−3/4 in this normalisation), V. I. Arnol'd, Russian Math.
Surveys 28 (1973) 19–48, DOI 10.1070/rm1973v028n05abeh001609; the t^{−3/4} rate from A3 points in lattice decay
estimates, J.-C. Cuenin and I. A. Ikromov, Nonlinearity 34 (2021) 7938–7962 (read in the sweep, arXiv version).

Modelling choices.
1. At the origin, as S4.1 (a translation moves any point there); no hypothesis ∇φ(0) = 0 (absorbed by the uniformity in
   y); y is arbitrary and not scaled by t, so tp·κ is the case y = tp.
2. Phase C^∞ (`ContDiff ℝ ∞`, with `∞` the smooth index, lessons 12). The planned S5.1 route (anisotropic dyadic
   rescaling ε⁻⁴φ(εu, ε²s) in kernel/transverse coordinates, the compact-family fold bound S3 on annuli, S2.1 for large
   linear terms, mirroring the proved S4.1′ route) needs a finite order (CONJECTURED: C⁵ suffices for the rescaled family
   to be FamilyCk 4); the order is not fixed now, so as not to freeze a statement the route cannot reach. Every model in
   the census corpus is real-analytic away from its non-smooth set. A finite-smoothness or local-smoothness version is a
   later front end (as FE-S4.1′L was for S4.1′).
3. Amplitude bound (2, B̄(0, δ), M) as in S4.1 and GD, so that S5.1 and GD combine without a stronger amplitude
   hypothesis. The S5.1 route needs only C² amplitudes (the rescaled amplitudes A(εu, ε²s) have C² norms ≤ the
   original for ε ≤ 1). For S5.1′ the planned route (Morse lemma with parameters in the transverse variable, then S1.k
   with k = 4 in the kernel variable) is PLAUSIBLE with C² amplitudes; the route referee is asked to check this.
4. The exponent −3/4 cannot be improved in general: for x²y + y² and x⁴ + y² with a Gaussian amplitude,
   t^{3/4}|I(t, 0)| tends to a nonzero limit (exploratory, `numerics/results-a3-statements-2026-11-09.txt`, N0–N1);
   the uniform bound over y is consistent with the same numerics (max over nine linear terms bounded, ≈ 5.8 at t = 10⁴).

Omitted (not claimed by S5.1/S5.1′): the leading term (a Pearcey-type constant); sharpness as a theorem; uniformity over
compact families of phases; the global assembly with finitely many A3 points (the next statement, GD with cusps); any
statement about A≥4, D≥5 or E/J points.

Clarifications after the pre-proof reviews (2026-11-09; `review/2026-11-09-A3-pre-proof-{A,B}.md`, answers
`review/2026-11-09-A3-pre-proof-answers.md`; no statement text changed, the stamp `stamps/20261109T201548Z-fcb46d9a6239`
stands):
1. **S1.k proof sketch, corrected** (A NIT 7). With radius r = μ^{−1/(k+1)} around the zero of the monotone D_k, the
   threshold on the far pieces is |D_k| ≥ μr = μ^{k/(k+1)}, and the induction step gives 2c_k μ^{−1/(k+1)} + 2r =
   (2c_k + 2) μ^{−1/(k+1)}. (The sketch above wrote "where |D_k| ≥ δ … choose δ = μ^{−1/(k+1)}", mixing threshold and
   radius; the recursion c_{k+1} = 2c_k + 2 is unaffected.)
2. **Smoothness** (A NIT 8, B NIT 1). Modelling choice 2's "CONJECTURED: C⁵ suffices for the rescaled family to be
   FamilyCk 4" is superseded: both referees argue that C⁴ suffices (the weighted Taylor remainder satisfies
   ε⁻⁴ ∂^α[R(εu, ε²s)] → 0 uniformly on compact sets for |α| ≤ 4); not yet checked by the lead or a route referee. The
   frozen statements keep C^∞.
3. **The vectors behind the quoted values** (B NIT 2). QWZ (m = 3) at (a, a): the value 128√130/53551875 is for
   v = (8√65/12675)·(1, −1) (the kernel vector (q, −p) of the Hessian) and w = (1, 0); with v = (1, −1), w = (1, 0):
   D³ω[v, v, w] = 6√130/65 and g₄ = −13992/4225 (review B, exact). Discrete Klein–Gordon at (π/2, π/2) with v = (1, −1),
   w = (1, 0): D²ω[w, w] = −√5/25, D³ω[v, v, w] = −√5/5, g₄ = −3/5 (both reviews, exact); the value −√5/625 above is for
   v = (−√5/25, √5/25). Both reviews checked all four points of each model.
4. **Route note for S5.1′** (B NIT 3). One-dimensional stationary phase in the transverse variable with parameters
   (u, y₂/t) and a C² remainder, then S1.k with k = 4 in the kernel variable, suffices; no Morse lemma with parameters is
   needed, and the route does not use condition (v), so it would prove S5.1 as well. Which route is used is decided in
   the route document, before any proof.

## Batch LE2: the cube-root bound for the 1D lattice kernel, and its 2D corollary (session 10, 2026-11-10)

Order. As batch LE: the statements below, `OscInt/Statements/LatticeCubeRoot.lean`, sanity theorems with planted
controls (`OscInt/Front/LatticeCubeRootSanity.lean`), the challenge `Challenge/LatticeCubeRoot.lean` and
`comparator-LE2.json` are committed and stamped before the blind pre-proof reviews; the reviews are answered and the
route is reviewed before any Lean proof of these statements is written. Owner decision (2026-11-10, session 10): start
this batch in the session that checked the bound.

Why. T0E's constants make it beat the trivial bound |I| ≤ 2π only for t > 518.5 (batch LE, clarification 6); ROADMAP
I4 asks for a "useful from" threshold for each explicit constant. An external reviewer submitted (2026-11-10) a hand
proof of a bound with one term and a constant within a factor 2 of the best possible; the lead re-derived it line by line
(`review/2026-11-10-external-followup-answers.md`). It is useful from t ≈ 3.70. The frozen LE files are not edited.

Notation. I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk (`latticeKernel1`, batch LE, unchanged) and K(t, x) T6's kernel
(`latticeKernel`, batch GD, unchanged). C* = 8(1 + √7)/3 ≈ 9.72200.

**T0E′ (cube-root bound for the 1D lattice kernel).** For every t > 0 and every real ξ: |I(t, ξ)| ≤ C* t^{−1/3}.

**T6E′ (explicit constant for T6, cube-root form).** For every t > 0 and x ∈ ℤ²: |K(t, x)| ≤ C*² t^{−2/3}.
(C*² = (512 + 128√7)/9 ≈ 94.517.)

Route (for the reviewers' orientation only; no Lean proof exists when this is frozen; the external reviewer's hand proof does, re-derived by the lead in `review/2026-11-10-external-followup-answers.md`). T6E′ is T6F and T0E′ applied twice.
T0E′: by I(t, −ξ) = I(t, ξ) (substitute k ↦ −k) take ξ ≥ 0, and put v = ξ/t, g = t(v − sin k) (the derivative of the
phase).
1. Integration by parts on the sets where |g| ≥ tδ, with the boundary terms at ±π kept: they combine into
   2e^{−it} sin(πξ)/(tv), of size ≤ 2/(tv). The rest of [−π, π] is bounded by its length. This gives a "band" bound
   |I| ≤ 2(arcsin(v + δ) − arcsin(v − δ)) + 8/(tδ) − 4/(t(1 − v²)) [+ 2/(tv) if v > δ], valid for −1 < v − δ and
   v + δ < 1, and a "cap" bound |I| ≤ 2 arccos(v − δ) + 4/(tδ) − 2/(t(1 + v)) [+ 2/(tv) if v > δ].
2. t ≥ 8, τ = t^{−1/3}: cap with δ = 2τ² for v ≥ 1 − 2τ² (≤ 2π + 8/3); band with δ = (3/2)τ² for 1/2 ≤ v < 1 − 2τ²
   (the bound decreases in Δ = (1 − v)/τ² and equals C* at Δ = 2: the extremal case) and for 0 ≤ v ≤ 1/2 (≤ 277/30).
3. 3 ≤ t ≤ 8, δ = 1/2: cap or band; each bound is A + B/t, and t^{1/3}(A + B/t) is largest at t = 3 or t = 8, where
   rational arithmetic gives < 97/10 < C*. 4. 0 < t ≤ 3: |I| ≤ 2π and 2π·3^{1/3} < 97/10.
No Bessel function and no S1 statement is used.

Modelling choices and what is omitted.
1. ξ is real (as T0E). For non-integer ξ the integral is an Anger-type function, not a Bessel function; the end-point
   terms at ±π are the reason the proof needs the 2/(tv) terms.
2. t > 0 for both (at t = 0 Lean's `Real.rpow` gives 0^{−1/3} = 0 and both bounds are false); t < 0 reduces to t > 0
   by I(−t, ξ) = conj I(t, −ξ). T6E′ holds for every t > 0, not only t ≥ 1 (unlike T6E): each factor obeys T0E′.
3. **How good the constant is.** C* is within a factor 2 of the best constant C_opt = sup over t > 0 and real ξ of
   t^{1/3}|I(t, ξ)|: C_opt ≥ (4/5)^{1/3}|I(4/5, 0)| > 4.93 (an elementary Taylor bound, exact rational arithmetic), and
   the LE review B point (t, ξ) = (5.7972…, 4.404) gives C_opt ≥ 2π·0.80366 ≈ 5.0495 (floating point). For integer ξ
   the best constant is Landau's, 2π·0.7857… ≈ 4.937 (`docs/prior_art.md`). So C*/C_opt ≤ 1.9706 rigorously and ≈ 1.925 numerically (the overshoot over Landau's
   integer-ξ constant is ≈ 1.969).
4. **Where the bounds have content.** C* t^{−1/3} < 2π exactly when t > (C*/(2π))³ ≈ 3.7045; C*² t^{−2/3} < 4π² for the
   same t. Compared with batch LE: C* < B = 36·2^{1/6} ≈ 40.41 (T0E's t^{−1/3} coefficient alone), and
   C*² ≈ 94.517 is about 50.3 times smaller than T6E's (A + B)² ≈ 4754.
5. T0E′ is stronger than T0E for every t > 0 (C* < B, and T0E has a further positive term), so T0E becomes a corollary;
   T6E′ is stronger than T6E for t ≥ 1. Neither frozen statement is edited or withdrawn.
6. The normalisation (2π)^{−1} (per factor), the time scale and the phases are omitted as in T0E and T6.
7. AI-use disclosure (as for S5.1′, `docs/prior_art.md`): the constant and the hand proof come from the external
   reviewer's submission of 2026-11-10 (OpenAI ChatGPT 6, version as given by the owner); not authorship or credit.
   The ingredients (integration by parts with end-point terms, arcsine band lengths, convexity) are elementary and
   classical; the constant was not found in the reviewer's logged search, which is the entire novelty claim.

Clarifications after the pre-proof reviews (2026-11-10; answers `review/2026-11-10-LE2-pre-proof-answers.md`; both
referees FAITHFUL and TRUE for T0E′ and T6E′, no BLOCKER or MAJOR; no statement text changed, the stamp
`stamps/20261110T234417Z-0532b1cf8880` stands):
1. **Which step is tight** (A and B, NIT). In the route above, C* arises in the regime 1/2 ≤ v < 1 − 2τ², t ≥ 8, only
   after the relaxation (1 + s)^{−1/2} ≤ 2√2/3 on the band; the exact band expression there peaks near 8.76. The
   tightest step of the route is 3 ≤ t ≤ 8 at t = 3, v ↓ 1/2 (cap bound with the 2/(tv) term): 3^{1/3}(π + 32/9) ≈ 9.659,
   checked against 97/10 exactly (`numerics/review/followup_checks.py`, R1c-cap). The same route would give a constant
   near 9.66; C* is the frozen one.
2. **Ranges of the route's bounds** (A, NIT). The band bound needs −1 < v − δ and v + δ < 1. The cap bound needs
   −1 < v − δ < 1; when v − δ ≥ 1 (so v > 1) the whole interval has g > 0, and the bound
   |I| ≤ 2/(t(v − 1)) + 2/(tv(v + 1)) replaces it.
3. **Sanity data** (A and B, MINOR). At t = 1/8 the sanity conclusions follow from the trivial bounds; data at
   t = (31/20)³ ≈ 3.724, just above the usefulness threshold, and three T6E′ bites were added to
   `OscInt/Front/LatticeCubeRootSanity.lean` (plant record, second run). The faster rate t^{−1/2} in T0E′ is false but
   not detected by the sanity layer; it rests on the reviews and on the proof.
4. **The proof as written** (2026-11-11, post-proof reviews A and B). The Lean proof (`docs/proof-LE2.md`, "The parts as
   proved") bounds the sub-case t ≥ 8, δ ≤ v ≤ 1/2 by 9.7047·t^{−1/3}, not by 277/30: after the extremal sub-case this
   is now the smallest margin of the proof (≈ 0.017), so clarification 1's "tightest step" (t = 3, 9.659) describes the
   route sketch above, not the proof.

## Batch HC: the hypercubic lattice kernel in every dimension (session 10, 2026-11-12)

Order. As batches LE and LE2: statements, `OscInt/Statements/Hypercubic.lean`, sanity theorems with planted controls
(`OscInt/Front/HypercubicSanity.lean`), challenge `Challenge/Hypercubic.lean` and `comparator-HC.json`, frozen and
stamped before the blind pre-proof reviews; no Lean proof of these statements exists before the reviews are answered.
Owner decision (2026-11-12, session 10): "bet 1", the separable corollary that ROADMAP I3b lists as an optional early
demonstration, now with the T0E′ constant.

Why. T0E′ is a 1D estimate; by Fubini the kernel of the free lattice Schrödinger group on ℤ^d factorises into d 1D
kernels, so T0E′ gives an explicit, machine-checkable dispersive bound in every dimension d: three-dimensional crystals
and cubic optical lattices (d = 3), and every d ≥ 4 as a mathematical family. Classical and separable: no claim beyond a
machine-checked corollary with an explicit constant (`docs/prior_art.md`, "Lattice kernels").

Notation. For d ∈ ℕ, t ∈ ℝ and x ∈ ℤ^d,
K_d(t, x) = ∫_{[−π, π]^d} e^{i(t Σ_j cos k_j + Σ_j x_j k_j)} dk (Lebesgue measure on ℝ^d, Lean: `Fin d → ℝ` with its
product measure, the box `Set.univ.pi (fun _ => Icc (−π) π)`). I(t, ξ) is `latticeKernel1` (batch LE).
C* = 8(1 + √7)/3 as in batch LE2.

**TdF (the d-dimensional kernel factorises).** For every d, real t and x ∈ ℤ^d: K_d(t, x) = ∏_{j<d} I(t, x_j).

**TdE′ (explicit decay in every dimension).** For every d, every t > 0 and x ∈ ℤ^d: |K_d(t, x)| ≤ C*^d t^{−d/3}.

Route (orientation only). TdF: the integrand is ∏_j e^{i(t cos k_j + x_j k_j)} (`Complex.exp` of a sum is a product),
the restricted product measure of a box is the product of restricted measures, and the integral of a product of
one-variable functions over `Fin d → ℝ` is the product of integrals (`MeasureTheory.integral_fintype_prod_eq_prod`).
TdE′: TdF, `norm_prod`, T0E′ on each factor, and (t^{−1/3})^d = t^{−d/3}.

Modelling choices and what is omitted.
1. x ∈ ℤ^d (lattice sites), as T6; the factorisation and the bound also hold for real x, not stated.
2. d = 0 is included: K_0 = 1 (the integral over the one-point space) and both sides of TdE′ equal 1.
3. t > 0 in TdE′ (rpow at 0, as T0E′). The rate t^{−d/3} is the sharp rate for the hypercubic lattice (caustic
   directions, from the 1D rate t^{−1/3}); sharpness is not stated.
4. The constant C*^d grows exponentially in d; the bound beats the trivial |K_d| ≤ (2π)^d for t > (C*/(2π))³ ≈ 3.70 in
   every dimension. For d = 2 it is T6E′ (on `Fin 2 → ℝ` instead of ℝ × ℝ; the identification is not stated).
5. Normalisation (2π)^{−d}, time scale and phases omitted, as T6. A user's e^{itH} with H = Σ_j 2 cos k_j has kernel
   (2π)^{−d} K_d(2t, x).
6. AI-use disclosure: TdE′ inherits T0E′'s (`docs/prior_art.md`); the batch itself was proposed by the lead.

Clarifications after the pre-proof reviews (2026-11-12; answers `review/2026-11-12-HC-pre-proof-answers.md`; TdF, TdE′
FAITHFUL and TRUE ×2, no BLOCKER or MAJOR; the stamp `stamps/20261112T120616Z-c56beb57ff8c` stands):
1. "Beats the trivial bound in every dimension" means every d ≥ 1; at d = 0 both sides are 1.
2. Sanity data with 3 ∤ d (d = 2), in the non-trivial regime (d = 1, 3) and at d = 0 were added; mutations of the
   kernel definition are not seen by the sanity layer and are caught by the TdF proof (plant record).

## Batch LS: the free lattice Schrödinger group on ℤ^d (session 10, 2026-11-12)

Order. As batches LE2 and HC: statements, `OscInt/Statements/LatticeGroup.lean`, sanity theorems with planted controls
(`OscInt/Front/LatticeGroupSanity.lean`, record `docs/replay/2026-11-12-LS-sanity-plants.txt`), challenge
`Challenge/LatticeGroup.lean` and `comparator-LS.json`, frozen and stamped before the blind pre-proof reviews; no Lean proof
of these statements exists before the reviews are answered. Owner decision (2026-11-12, session 10): "B1", from the
external research packet answered in `review/2026-11-12-DNLS-packet-answers.md` (its hand proof B1; the packet's Lean
statements were not used: they do not parse, and these are written fresh).

Why. TdE′ bounds the kernel K_d; batch LS turns it into a statement about the evolution itself. It is the shared
dependency of the discrete NLS candidate (ROADMAP "Candidates"), optical-lattice hopping and numerical dispersion
(Track C items C3 and C7 of that packet). Classical mathematics; the kernel formula is in Stefanov–Kevrekidis (arXiv
nlin/0409009v1, eq. (6)). The novelty claim, if proved, is "machine-checked, with an explicit constant".

Notation. ℓ²(ℤ^d) is `lp (fun _ : Fin d → ℤ => ℂ) 2` (Lean name `LatticeL2 d`). For g : ℤ^d → ℂ,
(Δg)(x) = Σ_{j<d} (g(x + e_j) + g(x − e_j) − 2g(x)), e_j = `Pi.single j 1` (Lean `latticeLaplacian`). A **solution with
datum f** is u : ℝ → ℓ²(ℤ^d) with u(0) = f such that, at every real t, u is differentiable in the ℓ² norm with
derivative w(t) ∈ ℓ², and w(t)(x) = i (Δu(t))(x) for every site x (Lean `IsLatticeSchrodingerSolution`); that is,
i u′ + Δu = 0. G_d(t, z) = (2π)^{−d} e^{−2idt} K_d(2t, z) (Lean `schrodingerKernel`), with K_d of batch HC.
C* = 8(1 + √7)/3 and τ = (C*/(2π))³/2 ≈ 1.852.

**LS-E (existence).** For every d and f ∈ ℓ²(ℤ^d) there is a solution with datum f.

**LS-K (kernel).** For every d, every f ∈ ℓ²(ℤ^d), every solution u with datum f, every real t and x ∈ ℤ^d: the series
Σ_y G_d(t, x − y) f(y) converges absolutely and u(t)(x) = Σ_y G_d(t, x − y) f(y). (In particular the solution is unique.)

**LS-D (dispersive estimate).** For every d, every f with Σ_y |f(y)| < ∞, every solution u with datum f, every t ≠ 0 and
x: |u(t)(x)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}} Σ_y |f(y)|.

**LS-D′ (decay at every time).** Same hypotheses, every real t: |u(t)(x)| ≤ (1 + τ)^{d/3} (1 + |t|)^{−d/3} Σ_y |f(y)|.

Route (orientation only; the route document comes after the reviews). LS-K: the kernel convolution is a solution
(∂_t G_d = iΔ_z G_d by differentiating under the integral, since Δ_z e^{iz·k} = (2Σ_j cos k_j − 2d) e^{iz·k}; G_d(t, ·) is
in ℓ¹, so convolution maps ℓ² to ℓ² boundedly) and solutions of the linear equation are unique (Δ is a bounded operator
on ℓ², norm ≤ 4d; Gronwall or Mathlib's ODE uniqueness). LS-E: the kernel convolution, or `NormedSpace.exp` of iΔ.
LS-D: LS-K, TdE′ at 2|t| (negative t by conjugation, K_d(−s, x) = conj K_d(s, −x)), |K_d| ≤ (2π)^d, and the triangle
inequality. LS-D′: LS-D, since (C*/(2π))^d 2^{−d/3} = τ^{d/3} and min{1, (τ/|t|)^{d/3}} ≤ ((1 + τ)/(1 + |t|))^{d/3}, with
t = 0 from u(0) = f.

Modelling choices and what is omitted.
1. Solutions are characterised by the equation, not by an operator exponential, so "the solution of i u′ + Δu = 0 is
   the kernel convolution" is the literal claim and no operator is constructed in the frozen file. Differentiability in
   the ℓ² norm at every real time (a strong solution) is required; weaker notions are not covered.
2. The sign convention: i u′ + Δu = 0, i.e. u′ = iΔu, so u(t) = e^{itΔ} f. With the opposite sign the kernel is the
   complex conjugate; not stated.
3. d = 0 is included (one site, Δ = 0, u constant, G_0 = 1); LS-D and LS-D′ then read |f| ≤ |f|.
4. LS-D and LS-D′ take ℓ¹ data (Σ_y |f(y)| < ∞, which implies f ∈ ℓ², as `lp` already requires). The bound
   min{1, ·} is stated with its trivial part; the decaying part beats 1 exactly when |t| > τ.
5. LS-D excludes t = 0 (Lean's 0^{−d/3} = 0 would make the bound false there; bite in the sanity file).
6. Omitted: mass conservation (unitarity), the group law, ℓ^p bounds for other p, Strichartz estimates, potentials and
   nonlinear terms; these belong to the discrete NLS candidate.
7. AI-use disclosure: the hand proof that suggested the batch is from the external reviewer's packet produced with an
   OpenAI model (`review/2026-11-12-DNLS-packet-answers.md`); the statements, sanity layer and plants are the lead's.

Clarifications after the pre-proof reviews (2026-11-12; answers `review/2026-11-12-LS-pre-proof-answers.md`; LS-E, LS-K,
LS-D, LS-D′ FAITHFUL and TRUE ×2, no BLOCKER or MAJOR; the stamp `stamps/20261112T215742Z-d18e0780abdb` stands):
1. LS-D′, like LS-D, beats the trivial |u(t, x)| ≤ ‖f‖₁ only for |t| > τ ≈ 1.852, and its constant (1 + τ)^{d/3} grows
   with d. The per-dimension factor C*/(2π) = 1.547 is about 1.97 times Landau's sharp 0.786.
2. The sanity layer now also pins the derivative clause and the diagonal term of Δ (a bite), states the derivative of
   t ↦ G_1(t, x) at t = 0 implied by LS-E and LS-K, and detects x + y in place of x − y. Mutations of the gauge, the
   factor 2 and the sign of i are not refuted by the sanity layer; LS-K's proof fixes them.

## Batch D4U: the D4 limit uniformly over compact amplitude families and bounded linear offsets (session 12, 2026-11-15)

Order. As batch LS: statements, `OscInt/Statements/D4Uniform.lean`, sanity theorems with planted controls
(`OscInt/Front/D4UniformSanity.lean`, record under `docs/replay/plants/2026-11-15-D4U/`), challenge
`Challenge/D4Uniform.lean` and `comparator-D4U.json`, frozen and stamped before the blind pre-proof reviews; no Lean
proof of these statements enters the repository before the reviews are answered and stamped. Disclosed departure from
lessons 23: a hand proof and unelaborated Lean drafts of statements of this kind (with a reduction of the two
statements to the stamped S4.1′ and S4.2) existed before this freeze, in an external research packet received by the
downstream project on 2026-11-15, and the lead elaborated that packet's drafts in scratch, outside this repository, on
2026-11-15 while assessing it. The statements below are written fresh by the lead; the blind reviewers are not shown
the packet.

Why. S4.2 gives t^{2/3} ∫ e^{itφ}A → c_C A(0) for one fixed amplitude and no linear term. A downstream lower bound
(sharpness of the t^{−2/3} decay of gapped two-dimensional split-step quantum walks) evaluates the kernel at
lattice sites x_t with x_t − t v bounded but not constant, so the linear term y·k with y = x_t − t v varies with t in
a bounded set. That needs the limit uniformly over bounded linear terms, which in turn follows from uniformity over a
totally bounded family of amplitudes (the modulations e^{iy·k}A). Classical in mechanism (uniform estimate on
differences plus the fixed-amplitude limit and a finite net; compare the compact-family arguments of Ikromov–Müller);
the claim, if proved, is "machine-checked".

Notation as in S4. For K ⊆ ℝ² a family S of amplitudes is **C²-totally bounded on K** (Lean `AmpTotallyBounded K S`)
if every A ∈ S has some C² budget on K (`AmpBound 2 K A M` for some M) and for every η > 0 there is a finite subset
B ⊆ S such that every A ∈ S has some b ∈ B with `AmpBound 2 K (A − b) η` (the difference is C², supported in K, and
its derivatives of order ≤ 2 are bounded by η everywhere). The phase hypotheses of S4.2 are bundled as
`D4LimitPhase φ`: φ is C⁴, φ(0) = 0, Dφ(0) = 0, D²φ(0) = 0 and disc(C) ≠ 0 for the cubic part C at 0. ‖y‖ on ℝ² is
the max norm (Mathlib's product norm), lin y κ = y₁κ₁ + y₂κ₂.

**S4.2U (D4 limit, uniform over a totally bounded amplitude family).** For every φ with `D4LimitPhase φ` there is
δ > 0 such that for every family S that is C²-totally bounded on B̄(0, δ) and every ε > 0 there is T such that for every
t ≥ T and every A ∈ S: |t^{2/3} ∫ e^{itφ(κ)} A(κ) dκ − c_C A(0)| < ε, with c_C = `d4Constant (cubicCoeffs φ)` as in S4.2.

**S4.2O (D4 limit, uniform over bounded linear offsets).** For every φ with `D4LimitPhase φ` there is δ > 0 such that
for every amplitude A with `AmpBound 2 (B̄(0, δ)) A M` for some M, every R and every ε > 0 there is T such that for every
t ≥ T and every y ∈ ℝ² with ‖y‖ ≤ R: |t^{2/3} ∫ e^{i(tφ(κ) + y·κ)} A(κ) dκ − c_C A(0)| < ε.

Modelling choices and omissions.
1. The radius δ depends on φ only (as in S4.1′ and S4.2), not on the family, R or ε.
2. Uniformity is stated in the ε–T form, not with `TendstoUniformlyOn`; T may be any real (only large t matter;
   `t ^ (2/3)` is `Real.rpow`).
3. The offset y·κ is not multiplied by t: it is a bounded perturbation, and the limit is unchanged because the linear
   term vanishes at 0. A linear term of size t (a moving critical point) is S4.1′'s case and has no limit here.
4. S4.2U is not stated with offsets, and S4.2O not for families; the second is the first applied to the modulation
   family {e^{iy·κ}A : ‖y‖ ≤ R}, which is part of the proof, not of the statements.
5. No rate and no effective T: both statements are qualitative, like S4.2.
6. AI-use disclosure: the question and a hand proof (checked by a fresh-context referee of the lead: correct, minor
   findings only) came from an external research packet produced with an OpenAI model at the owner's request (version
   not stated for this packet); the statements, the sanity layer and the plants here are the lead's. The packet, the
   lead's scratch elaboration of its Lean drafts before the freeze and the referee check of its hand proof are recorded
   in `review/2026-11-15-D4U-packet-answers.md` (added after the post-proof reviews); the route follows the packet's
   decomposition (part names `CommonRadiusFacts`, `ModulationFacts`).

Clarifications after the pre-proof reviews (2026-11-15; answers `review/2026-11-15-D4U-pre-proof-answers.md`; S4.2U, S4.2O
FAITHFUL and TRUE ×2, no BLOCKER; the stamp `stamps/20261115T122915Z-33c56db38f65` stands):
1. "Compact amplitude families" in the heading means C²-totally bounded families (`AmpTotallyBounded`): closedness is not
   required, so the statement covers more families than compact ones.
2. Uniformity in the offset holds for each fixed R, not uniformly in R. Referee B's numerics (generic cubic, factorised
   amplitude, t up to 1e7) show an error of about 0.61 R t^{−1/3} {referee numerics, not repository data} for ‖y‖ ≤ R, and
   at y = t^{1/3}(1, 0) a different Airy-type limit (ratio about 0.59 to c_C A(0)). For linear terms of size t the
   critical point moves (modelling choice 3) and there is no c_C A(0) limit. That the uniform limit extends to
   |y| = o(t^{1/3}) is CONJECTURED (rescaling heuristic and the referee's numerics), not proved; only bounded y is stated.
   (Corrected 2026-11-15 after the post-proof reviews: the first version said that at |y| ~ t there is no stationary
   point, which is false in general, and stated the o(t^{1/3}) range as a consequence.)
3. For consumers: applied at a D4 point k₀ ≠ 0 after recentring, the integral picks up the unimodular factor
   e^{i(tφ(k₀) + y·k₀)}, which varies with t; it does not affect bounds on the modulus.
4. The sanity layer now also tests a family that is not finite-dimensional (`seqFamily`, complex amplitude values), the
   budget conjunct (bite `const_not_totallyBounded`) and the elliptic umbilic (`phase_elliptic`); planted controls,
   second run, in `docs/replay/2026-11-15-D4U-sanity-plants.txt` (one plant, C⁰ in place of C² in the net, is NOT
   DETECTED and is pinned by the proof).

## Batch PA: periodic functions analytic in a strip; the trapezoidal rule; the lattice light cone (session 13, 2026-11-16)

Order. As batches LS and D4U: statements, `OscInt/Statements/PeriodicAnalytic.lean`, sanity theorems with planted
controls (`OscInt/Front/PeriodicAnalyticSanity.lean`, record under `docs/replay/plants/2026-11-16-PA/`), challenge
`Challenge/PeriodicAnalytic.lean` and `comparator-PA.json`, frozen and stamped before the blind pre-proof reviews; no
Lean proof of these statements exists, in the repository or in scratch, before the reviews are answered and stamped.
The sanity layer and the plants were written by an agent of the lead under a brief that forbids proving the
statements.

Why. Four chains of `docs/design/unlock-map.md` (section 2.2: the light cone of the lattice kernel, the ring of N
sites, the open chain, a certified evaluator by a plain sum) are one mechanism: the Fourier coefficients of a periodic
function analytic in a strip decay exponentially, and sampling at N points folds them onto each other. The general
statements are classical. PA-T is Theorem 3.2 of L. N. Trefethen and J. A. C. Weideman, *The exponentially convergent
trapezoidal rule*, SIAM Review 56 (2014) 385–458 (theorem statement read by two sweep agents of the lead on
2026-11-16, not by the lead: "v 2π-periodic, analytic with |v| ≤ M in the strip −a < Im θ < a; then for any N ≥ 1,
|I_N − I| ≤ 4πM/(e^{aN} − 1), and the constant 4π is as small as possible"). LC-1 is Kapteyn's inequality for Bessel
functions of integer order in a parametrised form (compare DLMF 10.14.5 and 10.14.8; not re-read by the lead). No
formalisation of any of the three was found by the logged sweep (`docs/prior_art.md`, disclosure of 2026-11-16):
PLAUSIBLE-not-formalised. The claim, if proved, is "machine-checked", not new mathematics.

Notation. For a > 0 the open strip is S_a = {z ∈ ℂ : |Im z| < a} (Lean `openStrip a`). A function v : ℂ → ℂ is
**periodic-analytic on S_a with bound M** (Lean `PeriodicAnalyticOn v a M`) if it is complex-differentiable on S_a,
v(z + 2π) = v(z) for every z ∈ S_a, and |v(z)| ≤ M for every z ∈ S_a. Nothing is assumed outside S_a. The N-point
trapezoidal sum is I_N(v) = (2π/N) Σ_{j=0}^{N−1} v(2πj/N) (Lean `trapezoidalSum v N`); for a periodic function the
trapezoidal and the rectangle rule are the same sum. I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk is the 1D lattice
kernel of batch LE (`latticeKernel1`).

**PA-C (Fourier coefficients decay exponentially).** For every a > 0, every M, every v periodic-analytic on S_a with
bound M and every integer k: |∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}.

**PA-T (the trapezoidal rule converges exponentially).** For every a > 0, every M, every v periodic-analytic on S_a
with bound M and every natural number N ≥ 1: |I_N(v) − ∫_0^{2π} v(θ) dθ| ≤ 4πM / (e^{aN} − 1).

**LC-1 (light cone of the 1D lattice kernel).** For every real t, every integer n and every η ≥ 0:
|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}.

Modelling choices and omissions.
1. v is a function on all of ℂ, constrained only on the open strip. A function given only on the strip is extended
   arbitrarily; the integrals and the sum use real arguments only, which lie in the strip.
2. Periodicity is assumed on the strip, not only on the real axis. For a function analytic on the strip the two are
   equivalent (identity theorem); the statement asks for the stronger form so that no such argument is part of it.
3. The bound is on the open strip, as in Trefethen and Weideman. No continuity up to the boundary is assumed.
4. PA-C is stated for the unnormalised integral, so the Fourier coefficient c_k = (2π)^{−1}∫ satisfies
   |c_k| ≤ M e^{−a|k|}. The sign of k in the exponential is immaterial, since the bound depends on |k| only.
5. PA-T does not state that 4π is the best constant. It is, as a supremum and not as an attained value: the paper's
   example for its Theorem 2.2, transplanted to the strip, is v(z) = 2 cos(Nz), for which the ratio of the two sides
   tends to 1 as aN → ∞ (the sanity layer uses 7 cos(3z) as a datum). Nor does it state the half-plane version with
   2π (their Theorem 3.1) or the version on the real line.
5a. The paper's sum is over the nodes 2πk/N, k = 1, …, N; `trapezoidalSum` uses j = 0, …, N − 1. For a 2π-periodic
   function these are the same sum. History, from the paper's section 11 (quoted by the sweep agent): its Theorem 3.2
   "is essentially" Theorem 1 of P. J. Davis, *On the numerical integration of periodic analytic functions* (1959),
   who called the result "folklore"; the idea goes back to Poisson in the 1820s. Davis's paper was not opened.
6. LC-1 is for integer n only. For non-integer ξ the integrand is not periodic and the bound fails in general: the
   kernel then decays only like 1/|ξ| as |ξ| → ∞ (an endpoint term). η is a free parameter: for |n| > |t| the best
   choice is cosh η = |n|/|t|, which gives Kapteyn's bound; η = 0 gives the trivial bound 2π.
7. LC-1 bounds the kernel, not solutions. With LS-K and TdF it gives, on paper, for a solution u of the lattice
   Schrödinger equation with ℓ¹ datum f: |u(t, x)| ≤ e^{2d|t| sinh η} Σ_y e^{−η|x − y|₁} |f(y)|. That consequence is not
   stated in this batch.
8. Numerical truth checks by the lead before the freeze, in ball arithmetic: PA-C at 195 and PA-T at 105 parameter
   points on five functions, with ratios of the two sides up to 1.000000 and 0.999877 (the bounds are attained in the
   limit), four altered statements rejected (`numerics/results-pa-statement-checks-2026-11-16.txt`); LC-1 at 462
   points (`numerics/results-unlock-chain-checks-2026-11-16.txt`, check K3). These are tooling, not evidence.

Clarifications after the pre-proof reviews (2026-11-16; answers `review/2026-11-16-PA-pre-proof-answers.md`; PA-C, PA-T,
LC-1 FAITHFUL, no counterexample found, no BLOCKER; the stamp `stamps/20261116T130956Z-276d8d7f9605` stands):
1. The words in quotation marks after "Theorem 3.2" in "Why" are a condensed paraphrase of the theorem, not the
   paper's sentence. The paper's sum runs over the nodes 2πk/N, k = 1, …, N (modelling choice 5a).
2. In modelling choice 6, "cosh η = |n|/|t|" needs t ≠ 0. With that choice LC-1 is the right side of DLMF 10.14.5
   (Siegel's bound, which the referee compared to 1e-39); DLMF 10.14.8 is the inequality named after Kapteyn.
3. Modelling choice 8 says both bounds are "attained in the limit". PA-C is attained exactly, by `v = c·e^{ikz}` with
   `M = |c| e^{a|k|}`; LC-1 is attained exactly at t = 0, n = 0; only PA-T's constant is a supremum. No strict form and
   no smaller constant is true for PA-C or LC-1.
4. Where the statements have no content: PA-T for `aN ≤ ln 2` (the right side exceeds the trivial bound); LC-1 inside
   the light cone `|n| ≤ |t|` and at η = 0; PA-C at k = 0; all three for M < 0 (vacuous) and M = 0 (v = 0).
5. The "− 1" in PA-T's denominator is not protected by any exact datum of the sanity layer: with `e^{aN}` in its
   place the statement is false (a referee certified a counterexample in ball arithmetic, ratio 1.00779 at `e^a = 2`,
   N = 1), but functions of the form c·cos(Nz) satisfy both. It rests on the review and on the proof.
6. The sanity layer was extended after the reviews (`OscInt/Front/PeriodicAnalyticSanity2.lean`; second plant run
   `docs/replay/2026-11-16-PA-sanity-plants-second.txt`): node positions, integrality of n and k, the bound off the
   real axis, a datum at k = 0. The statement file is unchanged.
7. After the external review of batch PA (2026-11-19, `review/2026-11-19-PA-external-review-answers.md`). In
   clarification 4, "all three for M < 0 and M = 0" is wrong in scope: only PA-C and PA-T have the parameter M; LC-1
   has none. At t = 0, n ≠ 0 (clarification 2) the exponent of LC-1 is −|n|η, which has no minimiser: the bound
   holds for every η ≥ 0 and tends to 0, as it must, since the kernel is then 0. Two docstrings of the sanity layer
   say more than their theorems: `halfExp_not_periodic` ("no strip and no bound make it admissible") assumes
   0 < a, and for a ≤ 0 the strip is empty and every function is admissible; `stripExp` ("holomorphic on that strip
   only") is also holomorphic on the two open regions |Im z| > 1, where it is 0. Both docstrings were corrected
   the same day (comments only); neither theorem's statement is affected.

Proved (2026-11-16). `OscInt.API.fourierCoeffStrip`, `OscInt.API.trapezoidalRule` and
`OscInt.API.latticeKernel1LightCone` have exactly these three statements as their types (route `docs/proof-PA.md`;
post-proof reviews `review/2026-11-16-PA-KL-post-proof-answers.md`). The sentence under "Order" above, "no Lean proof
of these statements exists, in the repository or in scratch, before the reviews are answered and stamped", is, as
far as the scratch is concerned, the lead's statement and cannot be checked by a reader; what can be checked, and
the one disclosed exception (a proof plan on paper older than the freeze), is in `docs/STATUS.md`, paragraph
"Batches PA and KL (2026-11-16), what the rows rest on".

## Batch KL: the Kusmin–Landau inequality for exponential sums (session 13, 2026-11-16)

Order. As batch PA: statements, `OscInt/Statements/KusminLandau.lean`, sanity theorems with planted controls
(`OscInt/Front/KusminLandauSanity.lean`, record under `docs/replay/plants/2026-11-16-KL/`), challenge
`Challenge/KusminLandau.lean` and `comparator-KL.json`, frozen and stamped before the blind pre-proof reviews; no Lean
proof of these statements exists, in the repository or in scratch, before the reviews are answered and stamped.

Why. Explicit analytic number theory rests on exponential-sum lemmas with explicit constants. One of them, Lemma 2 of
Y. F. Cheng and S. W. Graham (Rocky Mountain J. Math. 34 (2004)), stated the bound 1/(πθ) + 1 where 2/(πθ) is
correct. G. A. Hiary, D. Patel and A. Yang (arXiv:2207.02366, read in full by a sweep agent of the lead on
2026-11-16, not by the lead) write that "the incorrect constant 1/π has impacted all published explicit subconvex
bounds on |ζ(1/2 + it)|" and that the episode "points to the need for a more automated approach in the future to
verify explicit theoretical results". The correct inequality is classical: R. Kuzmin (1927) and E. Landau,
*Über eine trigonometrische Summe*, Nachr. Ges. Wiss. Göttingen (1928) 21–24, with Landau's sharp bound cot(πθ/2)
(neither original was opened; the statements below follow J. Arias de Reyna, *On Kuzmin–Landau Lemma*,
arXiv:2002.05982, Lemma 2, and N. Elkies's lecture notes for Harvard Math 229, both read in full by the sweep agent).
The claim, if proved, is "machine-checked", not new mathematics. Formalisation prior art, found before the freeze
(`docs/prior_art.md`, section of 2026-11-16 on batches PA and KL): the inequality is already formalised in Lean 4 in
two public repositories, in difference form, with the weaker constant 1/λ in place of cot(πλ/2); no formalisation
with the constant 2/π or with Landau's sharp bound was found.

Notation. e(x) = e^{2πix}. For a real sequence c_0, …, c_N the differences are d_n = c_{n+1} − c_n, 0 ≤ n < N. They
are **monotone in [k + λ, k + 1 − λ]** (Lean `DiffsMonotoneIn c N k lam`) if d_0 ≤ d_1 ≤ … ≤ d_{N−1} or
d_0 ≥ d_1 ≥ … ≥ d_{N−1}, and k + λ ≤ d_n ≤ k + 1 − λ for every n < N, with k an integer. The sum is
S = Σ_{n=0}^{N} e(c_n) (Lean `expSum c N`, N + 1 terms).

**KL-D (Landau's form, on differences).** For every real sequence c, every N ≥ 0, every integer k and every λ with
0 < λ ≤ 1/2: if the differences of c_0, …, c_N are monotone in [k + λ, k + 1 − λ], then |S| ≤ cot(πλ/2).

**KL-C (the constant 2/π).** Under the same hypotheses, |S| ≤ 2/(πλ).

**KL-F (the textbook form).** Let f be continuous on [a, b] with derivative f′ on (a, b), f′ monotone on (a, b), and
k + λ ≤ f′(x) ≤ k + 1 − λ for every x ∈ (a, b), with k an integer and 0 < λ ≤ 1/2. Then
|Σ_{n ∈ ℤ, a ≤ n ≤ b} e(f(n))| ≤ cot(πλ/2).

Modelling choices and omissions.
1. KL-D asks nothing of a function between the integers: only the N differences matter. It is the form of Arias de
   Reyna's Lemma 2(a) (increasing differences in [θ, 1 − θ]) with Elkies's two additions: either direction of
   monotonicity, and an integer shift k (which changes no term of the sum).
2. The hypothesis is "the differences lie in one cell [k + λ, k + 1 − λ]", not "each difference is at distance at
   least λ from the integers". For a sequence the second is weaker and the inequality fails for it: the differences
   1/4, 3/4, 5/4, 7/4 are increasing and at distance 1/4 from ℤ, but lie in two cells, and the sum for
   c = (0, 1/4, 1, 9/4, 4) is 3 + 2i, of modulus √13 > cot(π/8) (the same five terms as control C3 of the numerical
   checks). For a monotone continuous derivative the two agree, which is why textbooks state the second.
3. λ ≤ 1/2 is assumed. It follows from the cell condition when N ≥ 1; for N = 0 (one term, |S| = 1) it is what makes
   cot(πλ/2) ≥ 1.
4. cot(πλ/2) is written as cos(πλ/2)/sin(πλ/2); sin(πλ/2) > 0 for 0 < λ ≤ 1/2.
5. KL-F takes the derivative as in S1 (`HasDerivOn`): f continuous on [a, b], differentiable on (a, b). Neither
   continuity of f′ nor differentiability at the end points is assumed, which is weaker than the textbook's
   "continuously differentiable". The sum is over `Finset.Icc ⌈a⌉ ⌊b⌋`; it is empty, and the bound trivial, when no
   integer lies in [a, b]. The bound holds for every sub-interval, so the choice of end points (sources use [a, b],
   [a, b) and (a, b]) does not matter.
6. Not stated: Landau's sharpness results (the bound is attained exactly for λ = 1/2 and for fractions with odd
   numerator and denominator, and is a supremum for every λ; Arias de Reyna, Lemma 2(b)–(d)). The sanity layer uses
   the attaining sequences 0, 1/3, 1 (|S| = √3 = cot(π/6)) and 0, 1/5, 2/5, 6/5, 2 (|S| = cot(π/10) ≈ 3.0777, above
   Cheng and Graham's 1/(πθ) + 1 ≈ 2.5915) as data. Also not stated: the asymmetric form (U + V)/π of Hiary, Patel
   and Yang, and the second- and third-derivative tests for sums.
7. In the derivative form the bound is not attained by the sequences of item 6 (PLAUSIBLE: a difference equal to λ
   forces f′ = λ on a whole unit interval, and a derivative cannot jump). KL-F therefore claims the bound only.
8. Numerical truth checks by the lead before the freeze: KL-D and KL-C on 4000 random rational sequences with no
   certified violation; five of Landau's sequences attain the bound to 40 digits; KL-F on 20 quadratic phases; five
   altered statements, among them Cheng and Graham's bound, rejected
   (`numerics/results-kl-statement-checks-2026-11-16.txt`). Tooling, not evidence.

Clarifications after the pre-proof reviews (2026-11-16; answers `review/2026-11-16-KL-pre-proof-answers.md`; KL-D, KL-C,
KL-F FAITHFUL, no counterexample found, no BLOCKER; the stamp `stamps/20261116T130956Z-276d8d7f9605` stands):
1. Modelling choice 6 names the sequence 0, 1/5, 2/5, 6/5, 2 as a datum of the sanity layer. That is wrong: the
   layer uses 0, 1/6, 1/3, 1/2, 4/3, 13/6, 3 (λ = 1/6, |S| = √13 ≈ 3.606, above Cheng and Graham's 6/π + 1 ≈ 2.910 and
   below cot(π/12) ≈ 3.732), whose terms are exact with √3 only. The sequence at λ = 1/5 is used in the numerical
   checks (`numerics/results-kl-statement-checks-2026-11-16.txt`), not in Lean.
2. Modelling choice 7 is wrong at λ = 1/2: there the derivative form does attain the bound (f′ constant equal to
   k + 1/2 with an odd number of integers in [a, b]; for example f(x) = x/2 on [0, 2], sum 1 = cot(π/4)). For λ < 1/2
   a referee found ratios up to 1 − 1.2·10⁻⁶⁵ and no equality; that the bound is a supremum and not attained there is
   CONJECTURED from that search.
3. In KL-F the hypothesis `lam ≤ 1/2` matters only when (a, b) is empty and a single integer lies in [a, b]
   (a = b ∈ ℤ); otherwise the cell condition implies it. KL-F does not ask for a ≤ b: for a > b the sum is empty.
4. KL-C is a corollary of KL-D (cot x ≤ 1/x on (0, π/2]). "The textbook form" for KL-F means the derivative form of
   the sources quoted in "Why"; the sources differ in end points and in whether f′ is assumed continuous.
5. The sanity layer was extended after the reviews (`OscInt/Front/KusminLandauSanity2.lean`; second plant run
   `docs/replay/2026-11-16-KL-sanity-plants-second.txt`): the last monotonicity comparison, one cell for all
   differences, a negative k, data at λ = 1/2, non-integer end points, the interval of the derivative hypothesis.
   The statement file is unchanged.

Proved (2026-11-16). `OscInt.API.kusminLandau`, `OscInt.API.kusminLandauTwoOverPi` and `OscInt.API.kusminLandauDeriv`
have exactly these three statements as their types (route `docs/proof-KL.md`; post-proof reviews
`review/2026-11-16-PA-KL-post-proof-answers.md`). The order claim under "Order" above carries the same limit as for
batch PA (`docs/STATUS.md`, paragraph "Batches PA and KL (2026-11-16), what the rows rest on"). Further
clarifications after the post-proof reviews:
1. Where the statements have no content: the bound cot(πλ/2) exceeds the trivial bound N + 1 whenever
   N + 1 ≤ cot(πλ/2) (for example every sum of up to 63 terms at λ = 1/100); KL-C is weaker than KL-D everywhere.
2. "Landau's sharp form": that cot(πλ/2) is best possible for every λ is Landau's result as reported by the
   expositions quoted in "Why"; it is not machine-checked. In Lean the bound is shown attained at λ = 1/3, and data
   exist at λ = 1/2.
3. A rational witness against Cheng and Graham's printed bound in the derivative form exists (referee C, certified
   arithmetic: f′ = 1/5 on [0, 2], linear up to 4/5 on [2, 2.01], 4/5 after, integers 0 to 4: |S| = 3.0681 against
   1/(π/5) + 1 = 2.5915, and below cot(π/10) = 3.0777). The sanity layer records that mutation of KL-F as not
   detected; the proof excludes it.
4. Corrections after the external review of batch KL (2026-11-19, `review/2026-11-19-KL-external-review-answers.md`).
   Clarification 3 of the first list is false as written. The hypothesis `lam ≤ 1/2` of KL-F is used exactly when
   (a, b) is empty (a ≥ b), where the cell condition is vacuous: if no integer lies in [a, b] (a > b, or a = b not
   an integer) the sum is empty and the conclusion reads 0 ≤ cot(πλ/2), which fails for 1 < λ < 2 (at λ = 3/2 the
   right side is −1); if a = b is an integer the sum has one term and the conclusion reads 1 ≤ cot(πλ/2), which
   fails for 1/2 < λ < 2. When (a, b) is not empty the cell condition implies λ ≤ 1/2. The referee's remark, the
   lead's answer to it and the clarification had only the one-term case. In item 1 above, "exceeds" includes
   equality (N + 1 = cot(πλ/2) is possible, for example one term at λ = 1/2). In the pre-proof answers, "the
   monotonicity clause is empty for N ≤ 2": for N = 2 the clause has the instance n = 0 and is then true for every
   sequence (two real numbers are ordered one way or the other); it restricts nothing, but it is not empty. The
   docstring of `klCore_zeta` now states its domain. The statement file is unchanged.

## Batch FR: the Schrödinger group on a ring of N sites and on an open chain of M sites (session 13, 2026-11-16)

Order. As batches PA and KL: statements, `OscInt/Statements/FiniteRing.lean`, sanity theorems with planted controls
(`OscInt/Front/FiniteRingSanity.lean`, record under `docs/replay/plants/2026-11-16-FR/`), challenge
`Challenge/FiniteRing.lean` and `comparator-FR.json`, frozen and stamped before the blind pre-proof reviews. What that
claim is worth, said at the strength the facts have (post-proof review of batches PA and KL, finding F1): no Lean
proof of these statements is in the repository history before the stamp of the review answers; the lead states
that none exists in scratch either, which a reader cannot check. A proof plan on paper does predate the freeze: one
paragraph of dependencies in `docs/design/batch-FR-draft.md`, committed in 0302925, and the derivation of the two
finite-size bounds, which the lead worked out while drafting (it is how the first form of FR-P was found not to be
sharp). The sanity layer and the plants were written by an agent of the lead under a brief that forbids proving the
statements, against the draft text; that text entered the repository unchanged (SHA-256 of the statement file
33cbb55f1348163eb0395b7509b09db13ce110aa1e27d5ff4d56293c5717d26b).

Why. Every lattice statement of OscInt so far is about the infinite lattice ℤ^d. A device is finite: a ring of N
coupled sites, or, far more often, an open chain of M sites (a waveguide array, a line of qubits). Two classical
facts connect them, and `docs/design/unlock-map.md` (nodes N2, N3; chains K8, K9) names them as the missing link
between the proved estimates and a prediction a laboratory can test: the propagator on a ring is the propagator on
the line summed over the images r + Nℤ (periodisation), and the propagator on an open chain with identical sites
is the odd part of the propagator on a ring of 2(M + 1) sites (reflection). With the light-cone bound LC-1 of batch
PA the images are small until the wave reaches a wall, with an explicit bound. The mathematics is classical (method
of images; discrete sine transform); the claim, if proved, is "machine-checked", not new mathematics. Formalisation
prior art (`docs/prior_art.md`, section of 2026-11-16 on batch FR; four web searches and a reading of Mathlib): no
formalisation of these propagators, of the method of images or of a finite-size bound was found;
PLAUSIBLE-not-formalised. The explicit bounds FR-P and FC-P were not looked for in print in this explicit form; they
follow in a few lines from classical facts, and no claim is made that they are new.

Notation. The equation is i u′ + Δu = 0 with (Δu)(x) = u(x + 1) + u(x − 1) − 2u(x), as in batch LS with d = 1.
- **Line.** G(t, n) = (2π)^{−1} e^{−2it} I(2t, n) for n ∈ ℤ (Lean `lineKernel t n`), with I the 1D lattice kernel of batch
  LE. By LS-K and TdF with d = 1 it is the kernel of the group on ℓ²(ℤ); on paper G(t, n) = e^{−2it} i^n J_n(2t).
- **Ring of N ≥ 1 sites.** A function on the ring is a function on ℤ of period N.
  R_N(t, r) = N^{−1} Σ_{j=0}^{N−1} e^{i(2t(cos k_j − 1) + r k_j)}, k_j = 2πj/N (Lean `ringKernel N t r`).
- **Open chain of M sites.** The sites are 1, …, M; the walls are 0 and M + 1, where u = 0 (every site, including the
  two end sites, has the diagonal term −2: "identical sites").
  C_M(t; x, y) = R_{2(M+1)}(t, x − y) − R_{2(M+1)}(t, x + y) (Lean `chainKernel M t x y`).

**FR-K (the ring kernel).** For every N ≥ 1, real t and integer r: s ↦ R_N(s, r) has derivative
i (R_N(t, r + 1) + R_N(t, r − 1) − 2 R_N(t, r)) at t; R_N(0, r) is 1 if N divides r and 0 otherwise;
R_N(t, r + N) = R_N(t, r).

**FR-U (it is the propagator of the ring).** For every N ≥ 1 and every u : ℝ → ℤ → ℂ with u(t, x + N) = u(t, x) and
∂_t u(t, x) = i (u(t, x + 1) + u(t, x − 1) − 2u(t, x)) for all t and x: u(t, x) = Σ_{y=0}^{N−1} R_N(t, x − y) u(0, y).

**FR-S (method of images).** For every N ≥ 1, real t and integer r, the series Σ_{m ∈ ℤ} G(t, r + mN) converges
unconditionally and its sum is R_N(t, r).

**FR-P (finite-size error of the ring).** For every N ≥ 1, real t, integer r and η > 0:
|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1).

**FC-K (the chain kernel).** For every M, real t, integers x, y with 1 ≤ y ≤ M: s ↦ C_M(s; x, y) has derivative
i (C_M(t; x + 1, y) + C_M(t; x − 1, y) − 2 C_M(t; x, y)) at t; C_M(t; 0, y) = 0 and C_M(t; M + 1, y) = 0; and for
1 ≤ x ≤ M, C_M(0; x, y) is 1 if x = y and 0 otherwise.

**FC-U (it is the propagator of the chain).** For every M and every u : ℝ → ℤ → ℂ with u(t, 0) = u(t, M + 1) = 0 for
all t and ∂_t u(t, x) = i (u(t, x + 1) + u(t, x − 1) − 2u(t, x)) for all t and 1 ≤ x ≤ M:
u(t, x) = Σ_{y=1}^{M} C_M(t; x, y) u(0, y) for all t and 1 ≤ x ≤ M.

**FC-P (finite-size error of the chain).** For every M, real t, η > 0 and sites 1 ≤ x, y ≤ M:
|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} ( e^{−(x+y)η} + 2 (cosh((x − y)η) + cosh((x + y)η)) / (e^{2(M+1)η} − 1) ).

Modelling choices and omissions.
1. One dimension only. Rings and boxes in ℤ^d factorise (TdF), but that is not stated here.
2. A function on the ring is a periodic function on ℤ, not a function on `ZMod N`; a function on the chain is a
   function on ℤ of which only the values at 0, …, M + 1 are constrained. This keeps the statements free of
   coercions between `ZMod N`, `Fin N` and ℤ; the price is that FR-U and FC-U quantify over u : ℝ → ℤ → ℂ.
3. Time derivatives are taken site by site. For finitely many sites this is the derivative of the vector.
4. N = 1 and N = 2 are included. For N = 1 the "ring" is one site with Δ = 0 and R_1 = 1. For N = 2 the two
   neighbours of a site coincide, so Δu(x) = 2(u(x + 1) − u(x)): a double bond, which is what the formula gives and
   not what a two-site device with one bond does (that device is the open chain with M = 2).
5. M = 0 is included and vacuous in FC-K and FC-P (no y with 1 ≤ y ≤ 0); in FC-U it says nothing.
6. The chain has Dirichlet walls and the same diagonal −2 at every site. A chain whose end sites have diagonal −1
   (free ends, the graph Laplacian of a path) is the EVEN reflection and is not covered; its kernel is
   R_{2M}(t, x − y) + R_{2M}(t, x + y − 1). In the physical normalisation H = −κ Σ (|x⟩⟨x+1| + h.c.) with identical
   on-site energies, the diagonal is a constant and only changes a global phase: that device is this chain.
7. FR-P and FC-P have a free parameter η > 0, as LC-1. They say nothing useful once the wave has reached a wall
   (roughly 2|t| ≥ distance to the nearest image). FR-P is sharp as a supremum: at t = 0, r = N the left side is 1 and the
   right side is (e^{Nη} + e^{−Nη})/(e^{Nη} − 1), which tends to 1 as η → ∞; no constant smaller than 2 is true (a
   control with constant 1 fails). A first draft had e^{|r|η} in place of cosh(rη); a planted control ("without the factor 2") did not fail
   on it, which showed that draft was not sharp, and the statement was sharpened before the freeze.
8. FC-P keeps three images: the wall at 0 (the term e^{−(x+y)η}), and through the ring bound the wall at M + 1 and all
   further ones. It is not sharp (largest observed ratio of the two sides 0.36).
9. Populations: the probability at site x for a unit datum at y is |C_M(t; x, y)|². The statements bound amplitudes;
   ||a|² − |b|²| ≤ |a − b| (|a| + |b|) ≤ 2|a − b| for amplitudes of modulus at most 1 turns FC-P into a bound for
   populations. That step is not stated in this batch.
10. Numerical truth checks by the lead before the freeze, in ball arithmetic, by two methods that share no formula
   (the kernels as defined against the matrix exponential of the graph Laplacian):
   `numerics/review/fr_statement_checks.py`, results `numerics/results-fr-statement-checks-2026-11-16.txt`, 12 of 12
   checks pass and five altered statements are rejected. These are tooling, not evidence.
11. Not stated, and CONJECTURED only: FR-P may hold without the "− 1" in its denominator. A certified scan by the lead
   found no violation in 159003 comparisons (N ≤ 13, 0 ≤ t ≤ 8, |r| ≤ 2N, thirteen values of η; largest ratio of the
   two sides 1.0), and the sanity layer has no datum against it (plant FR-P-e, NOT DETECTED). The route to FR-P
   (the images bounded one by one with LC-1) gives the "− 1" form and not the stronger one.
12. The sanity layer: `docs/replay/2026-11-16-FR-sanity-plants.txt`. 26 planted mutations; 23 are refuted by compiled
   witnesses, 1 is equivalent to the statement (FC-U with the sum from 0 instead of 1), 2 are not detected by any
   datum (the "− 1" of FR-P; the wall term of FC-P) and rest on the reviews and on the proof. FC-P has no exact datum
   with a nonzero left side in this layer. FR-K, FC-K and the kernels are tested at N ≤ 4 and M ≤ 2 only.

Clarifications added after the freeze of batch FR (2026-11-16, from the blind pre-proof reviews; the stamped text
above and the Lean file are unchanged; `review/2026-11-16-FR-pre-proof-answers.md`).
a. Item 7, "FR-P is sharp". The supremum 1 of the ratio of the two sides is approached at t = 0, r = ±N (η → ∞), where
   the ring site is the source and the line site is not; it is not attained. It is nearly attained along the whole
   family r = ±N with t small and N large (certified by referee B: 0.99990 at N = 10⁵, t = 1/100; 0.9858 at N = 400,
   t = 1/10), so neither the constant 2 nor the factor cosh(rη) has slack there. This is sharpness of the statement
   as quantified over all integers r, not of the finite-size error where one uses it: R_N(t, ·) has period N and the
   bound does not, so take the representative with |r| ≤ N/2. For |r| ≤ N/2 the largest ratio found is 1/e
   (0.36787943 at N = 2, r = 1, t → 0, referee A, 40 digits); with |r| < N and t ≠ 0 the largest certified ratio is
   0.5809 (N = 5000, r = 4999, t = 37/40, referee B).
b. Item 8, "largest observed ratio 0.36". That number holds for M ≤ 8 only (0.3666 certified at M = 8). The ratio
   grows with M at a site next to a wall: 0.4288 (M = 24), 0.4678 (M = 100), 0.4854 (M = 2500, x = y = 2500, t = 61/40,
   η = 197/100000; all certified by referee B), apparently towards sup |J₂| ≈ 0.4865. "Not sharp" stands.
c. Item 8 and the header of the Lean file. "FC-P keeps three images" and "up to the two nearest images" are both
   loose. The statement compares C_M with G(t, x − y) alone and bounds every image: one term for the image in the
   wall at 0, and the ring bound for the image in the wall at M + 1 and all further ones.
d. Item 9 uses |C_M(t; x, y)| ≤ 1. That is true (the group on the chain is unitary) and is not a statement of this
   batch; the definition alone gives |C_M| ≤ 2.
e. Item 6, physical normalisation: the identification with H = −κ Σ (|x⟩⟨x+1| + h.c.) also rescales time by κ.
f. FR-U and FC-U are representation formulas for a given solution. Existence of a solution for a given datum is not
   a separate statement; it follows from FR-K and FC-K by a finite linear combination.
g. Hypotheses that are present and not needed. In FC-K the derivative clause and the two wall clauses hold for every
   integer y; only the unit datum needs 1 ≤ y ≤ M (and 1 ≤ x ≤ M). In FC-P referee A found no violation with
   the four site hypotheses removed (M ≤ 6, all integers |x|, |y| ≤ 3M + 4, floating point; largest ratio 1.000). The statements are
   weaker than they could be there, as the prose is; they are not changed.
h. Variants of FC-P that no datum and no scan distinguishes from the frozen text (referee A, floating point, M ≤ 9):
   the constant 2 of the ring term replaced by 1, the "− 1" removed, cosh((x − y)η) dropped, the wall coefficient
   1 replaced by 1/2. Whether any of them is true is not known to the lead; the frozen constants are those of the
   derivation (the images bounded one by one with LC-1), not of a fit.
i. Added after the post-proof reviews (2026-11-17; `review/2026-11-17-FR-post-proof-answers.md`). FC-P holds for all
   integers x and y: the four site hypotheses are not needed (a referee compiled a proof of that in its scratch, from
   FR-P and LC-1; it is not a theorem of the library, and the frozen statement keeps the hypotheses). FR-P says
   nothing for |r| ≥ N, where its right side exceeds 1. FR-U and FC-U are about solutions defined for all real times
   (a derivative at every t); a solution given on an interval only is not covered as stated. FR-U needs the period
   at every time: with the period assumed at t = 0 only the statement is false (a null solution built from a
   function flat at 0, sites defined by the recursion), and no datum or numerical test could show it; the proof
   uses the period at every t. All seven theorems of this batch use lemmas of batch PA.
j. Added 2026-11-19 (found by the lead while answering the external review of batch PA, which reported the same
   pattern in a sibling script; `review/2026-11-19-PA-external-review-answers.md`). Item 10 overstated one of the
   twelve checks. The check "FR-S coset sum against the ring kernel, within the certified tail" compared against the
   tail plus 1e-25, which neither the script's description nor item 10 said. For N = 5 and N = 8 the tail (below
   1e-250 with |m| ≤ 60) is smaller than the enclosures at the working precision (about 1e-209), so at 46 of the 120
   points the run of 2026-11-16 showed agreement to within 1e-25 and not to within the tail. The script now sums
   |m| ≤ ⌈60/N⌉, where every tail exceeds 1e-70, and compares with the tail alone: 120 of 120 pass, and a tail smaller
   by the factor e^{−4N} fails at 6 points (the 120 of 120 is in `numerics/results-fr-statement-checks-2026-11-19.txt`;
   the control with the smaller tail was run by the lead the same day and is not kept). Its two "must differ"
   controls now need certified disjoint enclosures. The statements and their proofs are not affected.
k. Corrections after the external review of batch FR (2026-11-19, `review/2026-11-19-FR-external-review-answers.md`).
   (1) Item 8 and clarification b, "FC-P is not sharp": this is an observation and no more. The largest ratio of
   the two sides found is 0.4854; that the supremum of the ratio is below 1 is CONJECTURED, not proved. (2)
   Clarification i, "FR-P says nothing for |r| ≥ N, where its right side exceeds 1": the trivial bound on
   |R_N − G| is 2 (two kernels of modulus at most 1), so the bound still says something while it is below 2. (3)
   The docstring of the sanity theorem `chainP_half_time_false` said that at η = 3 the planted bound, 0.03041, is
   "not a violation". It is one: the left side is 0.0304426 and the planted bound 0.0304082 (ball arithmetic by
   the lead, difference 3.44e-5 certified positive); the proof in that file uses the coarse lower bound 767/25600,
   which cannot show it at η = 3. The docstring is corrected, and so is the overview of
   `OscInt/Front/FiniteRingEnergy.lean` ("constant, hence 0" needs the zero datum). (4) The control of the
   numerical script called "free ends" is the reflected image with the opposite sign on the ring of 2(M + 1)
   sites; it is not the chain of M sites with free ends. The statement file is unchanged.

## Batch VC2: the second-derivative van der Corput bound with its sharp constant (session 13, 2026-11-16)

Order. As batch FR: statements, `OscInt/Statements/SecondDerivSharp.lean`, sanity theorems with planted controls
(`OscInt/Front/SecondDerivSharpSanity.lean`, record under `docs/replay/plants/2026-11-16-VC2/`), challenge
`Challenge/SecondDerivSharp.lean` and `comparator-VC2.json`, frozen and stamped before the blind pre-proof reviews.
What differs from the earlier batches, said plainly: a complete proof on paper of VC2-S and VC2-A predates the
freeze. The lead wrote it on 2026-11-16 before drafting these statements (it is how the form of VC2-S was found), a
fresh referee read it step by step (verdict: correct after the listed repairs; two minor repairs made, not
re-refereed), and it is in `docs/prior_art.md` in outline. No Lean proof of these statements is in the repository
history before the stamp of the review answers. The sanity layer and the plants were written by an agent of the
lead under a brief that forbids proving the statements, against the draft text, which entered the repository
unchanged (SHA-256 of the statement file b0f5814eabf7541158b81697bf66cd55b01c70177252c6e35d045506b474eabb).

Why. S1.2 (and S1.k at k = 2) has Stein's constant 8. The best constant has been known since Kershner (1935, 1938;
`docs/prior_art.md`; the lead has not read Kershner's papers): it is the largest modulus of a Fresnel partial
integral, 3.3643175781…. Every explicit bound of this library that passes through the second-derivative test
carries the factor 8/3.364… = 2.38 for no reason. The theorem is classical; the claim, if proved, is "machine-checked,
sharp constant", not new mathematics. The session's map had called the constant open on the word of one paper
and was corrected the same day (session log, 2026-11-16).

Notation. A(w) = 2 ∫_0^{√(2w)} sin(w − u²/2) du for w ≥ 0 (Lean `vdc2Profile w`). With F(V) = 2 ∫_0^{√(2V)} e^{iu²/2} du
one has A(w) = Im(e^{iw} · conj F(w)) (substitute v = u²/2), so A(w) ≤ |F(w)|. "f′ increases at rate at least λ on (a, b)" means f′(y) − f′(x) ≥ λ (y − x) for all a < x ≤ y < b (Lean
`DerivIncreasesAtRate f' a b lam`); it holds if f″ ≥ λ and needs no second derivative.

**VC2-S (sharp second-derivative bound).** For all a ≤ b, λ > 0 and every f continuous on [a, b] with derivative f′ on
(a, b) that increases at rate at least λ: there is w ∈ [0, π] with |∫_a^b e^{if(x)} dx| ≤ A(w)/√λ.

**VC2-A (attained).** For every w ≥ 0: A(w) ≤ |∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx|. (The right side is |F(w)|; the phase
x²/2 on a symmetric interval satisfies the hypotheses of VC2-S with λ = 1. So sup_{[0,π]} A is the best constant.)

**VC2-N (a number).** A(w) ≤ 7/2 for 0 ≤ w ≤ π. (The supremum is 3.3643175781…, at w = 2.2974…)

**VC2-K (the test with amplitude, constant 7/2).** As S1.2 with 7/2 in place of 8: for φ with derivatives φ′, φ″ on
[a, b] in the sense of S1, |φ″| ≥ μ > 0 on (a, b), every real p and every ψ with the amplitude hypothesis of S1:
|∫_a^b e^{i(φ(x) + px)} ψ(x) dx| ≤ (7/2) μ^{−1/2} A(ψ; a, b).

Modelling choices and omissions.
1. VC2-S is stated with the profile A and an existential w, not with a supremum: the statement then contains no
   `sSup` (whose value in Lean for an unbounded or empty set would need a side condition) and is strictly stronger
   than the bound with the constant sup A. The constant itself enters through VC2-N.
2. VC2-S assumes only that f is continuous on [a, b] and differentiable inside, with the increment condition on f′;
   f′ may be unbounded at the ends. VC2-K keeps the hypotheses of S1.2 (φ′ continuous up to the ends, a second
   derivative), so that it can replace S1.2 where S1.2 is used; a derivative of constant sign follows from |φ″| ≥ μ
   by Darboux's theorem.
3. VC2-N is a bound for a number defined by an integral; 7/2 is 4 % above the supremum. A tighter rational
   (for instance 3.3644) would need a certified evaluation in Lean and is not stated.
4. The uniqueness of the extremal phase and the first-derivative test with its sharp constant 2 (which the same
   method gives) are not stated.
5. Numerical truth checks by the lead before the freeze: `numerics/review/vc2_statement_checks.py`, results
   `numerics/results-vc2-statement-checks-2026-11-16.txt`, 11 lines, all pass: the maximum of A on [0, π] is
   3.3643175781559 at w = 2.297439574; A ≤ |F| on a grid and equality at the maximiser; 60000 random phases with
   piecewise constant second derivative ≥ λ (two methods for the integral: Fresnel closed forms and adaptive
   quadrature) reach at most 3.363688 √λ^{−1}; 1500 random instances of VC2-K reach the ratio 2.41 against 7/2; three
   altered statements are rejected. The proof's referee ran a linear programme over nonincreasing densities
   (supremum 3.36039, from below). Floating point and quadrature: tooling, not evidence.
6. The sanity layer: `docs/replay/2026-11-16-VC2-sanity-plants.txt`. 62 declarations, 13 through a statement constant.
   Certified data: 33/10 ≤ A(441/200) and 33/10 ≤ |∫_{−21/10}^{21/10} e^{ix²/2} dx| (so 7/2 is within 6 % of a value of
   A, and no constant below 33/10 is true in VC2-S, VC2-N or VC2-K). 15 planted mutations: 12 are refuted by compiled
   witnesses; 2 are true weakenings (the increment condition with an absolute value, which is equivalent to the
   statement by Darboux's theorem and conjugation, so "increasing" in VC2-S is a normalisation and the decreasing
   case is the conjugate one; VC2-K with φ″ in place of |φ″|); 1 is not detected and is apparently a true
   strengthening (VC2-N on [0, 2π]: numerically A ≤ 3.3643… on all of [0, ∞); the statement keeps [0, π], which is
   what VC2-S needs). The layer proves no upper bound: the instances of VC2-S, VC2-N and VC2-K at the certified data
   are consistent with it (33/10 ≤ … ≤ 7/2) and not decided by it, and the instance of VC2-A at w = 441/200 (true gap
   0.0074) is not decided either.

Clarifications added after the freeze of batch VC2 (2026-11-17, from the blind pre-proof reviews; the stamped text
above and the Lean file are unchanged; `review/2026-11-17-VC2-pre-proof-answers.md`).
a. Modelling choice 1 is wrong where it says that the existential form of VC2-S "is strictly stronger than the bound
   with the constant sup A". The profile A is continuous on the compact interval [0, π], so "there is w ∈ [0, π] with
   X ≤ A(w)" holds exactly when X ≤ max_{[0, π]} A: the two forms are equivalent, and w is not tied to f, a or b.
   The reason given for avoiding a supremum in the Lean text stands.
b. The docstring of `vdc2Profile` in the frozen Lean file ("the largest real part, over rotations, that the quadratic
   phase can reach when its positive arc ends at phase w") does not describe the definition. The accurate
   description is the one of the Notation paragraph: A(w) = Im(e^{iw} · conj F(w)), the component of the quadratic
   integral F(w) = ∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx along one fixed rotation; A(w) ≤ |F(w)|, with equality at the
   maximiser, and A takes negative values (A(5) = −1.585). The file is frozen and is not edited.
c. "Classical" needs a caveat. The constant 3.3643175781… and its attribution to Kershner are cited from tables
   and titles; nobody in this project has read Kershner's papers or Finch's account. A referee confirmed that the
   tabulated constant is the maximum of A at the same maximiser (w = 2.2974396). Whether the classical theorem is
   stated for the class of VC2-S (an increment condition on f′, no second derivative, f′ possibly unbounded at the
   ends) is not known to the lead; for that class the evidence is the lead's proof on paper, refereed once. "The
   largest modulus of a Fresnel partial integral" should read: the largest modulus of the two-sided integral
   ∫_{−c}^{c} e^{ix²/2} dx, which is twice the largest modulus of ∫_0^c e^{iu²/2} du. That the supremum over all c is
   reached with w = c²/2 ≤ π was certified by a referee for w ≤ 400 only; the paper proof covers all w.
d. Superfluous hypotheses and notation. Continuity of f at the end points is not needed in VC2-S (the integral does
   not see f(a), f(b)); it is kept, so a convex phase that tends to +∞ at an end point is excluded. `0 ≤ w` in VC2-A
   and the lower end of the range in VC2-N are superfluous under Lean's convention √x = 0 for x < 0 (both sides are
   0); numerically the upper end is too (A ≤ 3.3643… on [0, 60]). The letter A denotes the profile here and the
   amplitude norm A(ψ; a, b) of S1 in VC2-K. VC2-K is written with μ^{−1/2} (the shape of S1.k) where S1.2 has 1/√μ;
   they are equal for μ > 0.
e. Certified by a referee in ball arithmetic (branch and bound over [0, π], 595 cells), outside Lean: the maximum
   of A on [0, π] lies in [3.364317578155899106067713, 3.364317578155899106067763], at w in
   [2.297439573597, 2.297439573620]; so VC2-N holds with a margin of at least 0.1356. Evidence, not a proof.
f. The sanity layer after the reviews: `OscInt/Front/SecondDerivSharpSanity2.lean`,
   `docs/replay/2026-11-17-VC2-sanity-plants-second.txt`. Second run, 18 planted mutations: 12 refuted by compiled
   witnesses (four mutations of the exponent of λ or μ, the constant 67/20 in VC2-N and VC2-K, five hypotheses, one
   mutation of the amplitude norm), 2 true weakenings (the statements for exact parabolas only), 4 not detected (the
   range of w in VC2-S from below; f′ in place of f in the exponential; the integrand of VC2-A; the weight of ∫|ψ′|).
g. Added 2026-11-19 after the post-proof reviews (`review/2026-11-19-VC2-post-proof-answers.md`); the text above is
   unchanged. (1) "The layer proves no upper bound" (item 6, and the pre-proof answers) is not exact: the first
   sanity layer proves A(1/2) ≤ 1 and the instance w = 1/2 of VC2-A, and eight witness files of the two plant runs
   prove A(w) ≤ 26/5 for every w ≤ π; all are older than the stamp and none is used by the proofs. (2) The
   pre-proof answers say that after a proof of VC2-N the gap of the undetected mutation "range of w in VC2-S cut
   to [0, 441/200]" closes by itself. It does not: a refutation needs A ≤ c on that range for some c below about
   3.358, and the proved bound is 7/2. What the proofs settle is that the frozen statements are theorems. (3) No
   plant mutated the definition of the profile A. Post-proof referee C found one that both sanity layers accept up
   to a script-only error (the factor 2 replaced by 41/20); it keeps VC2-S and VC2-N true and makes VC2-A false,
   and the proof of VC2-A rejects it. (4) In the second plant summary, case X1, the value 0.0173 should read
   0.0167 (2 sin(21)/100); the verdict does not change. (5) The decimal 3.3643… is not a theorem of the library
   (in Lean: 335007/100000 ≤ A(441/200) and A ≤ 7/2 on [0, π]).
h. Added 2026-11-19 after an external review (`review/2026-11-19-VC2-external-review-answers.md`); the text above is
   unchanged. (1) Item 6, "7/2 is within 6 % of a value of A": the denominator matters. Measured against the
   certified lower bound 33/10 the excess is 2/33 = 6.06 %; measured against 7/2 it is 2/35 = 5.7 %; with the
   stronger certified lower bound 335007/100000 of the second sanity layer it is below 6 % either way. (2) What the
   four statements say together, in one place: VC2-A is a one-sided projection inequality, A(w) ≤ |F(w)| for the
   symmetric Fresnel integral F(w), not an equality for each w; that the constant max A of VC2-S is attained follows
   from VC2-S, VC2-A and the compactness of [0, π] together (at a maximiser w*, max A = A(w*) ≤ |F(w*)| ≤ max A),
   and this corollary is not a Lean statement of the batch; VC2-K has the constant 7/2, which is not sharp.
   (3) Observed by the external reviewer and not statements of the batch: continuity of f at the end points is
   not needed in VC2-S (trim the interval and pass to the limit), and A(w) ≤ 7/2 holds for every real w (apply
   VC2-S and VC2-A to the quadratic phase).

## Batch HW: the Hadamard walk on the line, an explicit t^{−1/3} bound (session 13, 2026-11-16)

Order. As batch FR: statements, `OscInt/Statements/HadamardWalk.lean`, sanity theorems with planted controls
(`OscInt/Front/HadamardWalkSanity.lean`, record under `docs/replay/plants/2026-11-16-HW/`), challenge
`Challenge/HadamardWalk.lean` and `comparator-HW.json`, frozen and stamped before the blind pre-proof reviews. No Lean
proof of these statements is in the repository history before the stamp of the review answers. A proof plan on paper
does predate the freeze, and the constants of HW-K and HW-D are the constants of that plan rounded up: the plan is the
paragraph "Route" below, written by the lead while drafting. The sanity layer and the plants were written by an agent
of the lead under a brief that forbids proving the statements, against the draft text; the namespace body of that text
entered the repository unchanged (the lead removed a copyright header, which statement files do not carry, and
changed the module comment; SHA-256 of the statement file 2d18f64ff8426c7521542ae0f9d4ba2a5c0dec2dc9e5dd946ef507784c67b319,
of the draft the agent received 068de485c7c41692cbf0a25a9286c7f01ca58b91dbd72885e4126bf39458d7b9).

Why. `docs/design/unlock-map.md` (row F1 and the applications table) records a statement that algorithm papers quote
and no paper in the sweep proves with a constant: the amplitudes of the Hadamard walk on the line decay like t^{−1/3},
so the largest probability at a site decays like t^{−2/3}. Nayak and Vishwanath (arXiv:quant-ph/0010117) give the rate
with sketched proofs; Sunada and Tate (arXiv:1108.1878) prove Airy asymptotics with implicit constants; Maeda, Sasaki,
Segawa, Suzuki and Suzuki (arXiv:1808.05714, section 3) state the dispersive estimate for a constant coin as "a direct
consequence of van der Corput lemma", splitting where the second or the third derivative of the dispersion relation is
bounded below, with an implicit constant. This batch is that classical argument with every constant written out, for
the Hadamard coin, as a statement about the walk as it is defined on the lattice (no Fourier transform in the
definition of the walk). The mathematics is known; the claim, if proved, is "machine-checked, explicit constants",
not new mathematics. Prior art for the explicit constant (`docs/prior_art.md`, section on batch HW; a logged sweep of
12 queries, `numerics/results-hw-prior-art-search-2026-11-16.txt`): no explicit constant for this bound was found;
PLAUSIBLE-not-in-print, and nothing rests on it.

Notation. A state is ψ : ℤ → ℂ², ψ(x) = (ψ₁(x), ψ₂(x)). One step of the walk (Lean `hadamardStep`):

  (Uψ)(x) = ( (ψ₁(x + 1) + ψ₂(x + 1))/√2 , (ψ₁(x − 1) − ψ₂(x − 1))/√2 ),

that is: the coin H = [[1, 1], [1, −1]]/√2 at every site, then the first component moves one site to the left and the
second one site to the right. ψ_t = U^t ψ₀ (Lean `hadamardWalk ψ₀ t`); δ_{a,b} is the state (a, b) at the origin and 0
elsewhere (Lean `pointState a b`). ω(k) = arcsin(sin k/√2) (Lean `hadamardDispersion`); at quasi-momentum k the step
has the eigenvalues e^{−iω(k)} and −e^{iω(k)}. The scalar kernel (Lean `hadamardKernel t x`), for t ∈ ℕ and x ∈ ℤ:

  K(t, x) = (2π)^{−1} ∫_{−π}^{π} (e^{−itω(k)} − (−1)^t e^{itω(k)}) / √(2(1 + cos² k)) · e^{−ixk} dk.

**HW-R (the walk in terms of the kernel).** For all complex a, b, every t ≥ 0 and every site x:
U^{t+1} δ_{a,b} (x) = ( (a + b)/√2 · K(t + 1, x + 1) + a K(t, x) , (a − b)/√2 · K(t + 1, x − 1) + b K(t, x) ).

**HW-K (the kernel bound).** For every t ≥ 1 and every site x: |K(t, x)| ≤ 7 t^{−1/2} + 12 t^{−1/3}.

**HW-D (decay from a point state).** For all complex a, b, every t ≥ 1 and every site x, each component of
U^t δ_{a,b} (x) has modulus at most 39 (|a| + |b|) t^{−1/3}.

**HW-L (dispersive estimate, ℓ¹ → ℓ^∞).** For every ψ₀ with finite support, every t ≥ 1 and every site x, each
component of U^t ψ₀ (x) has modulus at most 39 t^{−1/3} Σ_y (|ψ₀,₁(y)| + |ψ₀,₂(y)|).

Route (for the reviewers' orientation only; no Lean proof exists when this is frozen).
HW-R: in Fourier variables the step is multiplication by the matrix Û(k) = [[e^{−ik}, e^{−ik}], [e^{ik}, −e^{ik}]]/√2,
of trace τ = −i√2 sin k and determinant −1, so Û² = τÛ + 1 and Û^t = α_t Û + α_{t−1} with α_0 = 0, α_1 = 1,
α_{t+1} = τ α_t + α_{t−1}; α_t = (λ₊^t − λ₋^t)/(λ₊ − λ₋) with λ₊ = e^{−iω}, λ₋ = −e^{iω}, λ₊ − λ₋ = 2 cos ω =
√(2(1 + cos² k)). K(t, ·) is the sequence of Fourier coefficients of α_t. In Lean the plan is an induction on t on
the lattice: K(0, x) = 0, K(1, x) = δ_{x,0}, K(t + 2, x) = (K(t + 1, x + 1) − K(t + 1, x − 1))/√2 + K(t, x) (the
recursion of α under the integral), and the same three facts for the walk.
HW-K: K(t, x) is 0 when t + x is even and otherwise π^{−1} ∫ g(k) e^{−i(tω(k) + xk)} dk over a period, with
g = 1/√(2(1 + cos² k)); both exponentials are bounded the same way. ω′ = cos k (1 + cos² k)^{−1/2},
ω″ = −sin k (1 + cos² k)^{−3/2}, ω‴ = −cos k (4 − 2cos² k)(1 + cos² k)^{−5/2}. Split a period into four arcs of
length π/2. Where |sin k| ≥ 1/√2: |ω″| ≥ 2/(3√3), and S1.k with k = 2 gives 8 (2t/(3√3))^{−1/2} A with
A = |g(end)| + ∫|g′| = √2 − 1/√3. Where |cos k| ≥ 1/√2: |ω‴| ≥ 2^{−3/2}, and S1.k with k = 3 gives
18 (2^{−3/2} t)^{−1/3} A with A = √3 − 1. Two arcs of each kind, two exponentials, divided by 2π:
6.8700 t^{−1/2} + 11.8634 t^{−1/3} (`numerics/results-hw-statement-checks-2026-11-16.txt`), rounded up to 7 and 12.
HW-D: from HW-R and HW-K; for t ≥ 2, (t − 1)^{−1/3} ≤ 2^{1/3} t^{−1/3} and t^{−1/2} ≤ t^{−1/3}, which gives the constant
(7 + 12)/√2 + 7√2 + 12·2^{1/3} = 38.4536 ≤ 39; t = 1 directly. HW-L: linearity and translation invariance of the step.

Modelling choices and omissions.
1. The Hadamard coin only, and one handedness (first component to the left). Other coins have the same structure
   with another dispersion relation; not stated.
2. Time is a natural number and the site an integer; t^{−1/2}, t^{−1/3} are real powers of the cast. At t = 0 Lean's
   0^{−1/3} is 0 and the bounds HW-D, HW-L would be false: the hypothesis t ≥ 1 carries content there. In HW-K it does
   not (K(0, ·) = 0); it is kept for uniformity.
3. The constants are not sharp, by a wide margin, and the statements do not say otherwise. Numerically (exact
   recursion, t ≤ 3000) sup_x |K(t, x)| t^{1/3} stays below 1.0 (0.955 at t = 3000) against 12, and the largest
   component from a point state with |a| + |b| = 1 is about 1.61 t^{−1/3} against 39 t^{−1/3}. The right side of HW-K is
   below 1 (the value of |K(1, 0)|) only from t = 2674, and the right side of HW-D is below |a| + |b| only for
   t > 39³ = 59319.
   The loss is in the constants 8 and 18 of S1.k, in counting every arc at its worst, and in the amplitude norm. A
   bound within a small factor of the truth needs the method of batch LE2 (as T0E′ improved T0E); not done here.
4. Only an upper bound. That the rate t^{−1/3} is attained (a lower bound near x = ±t/√2) is not stated.
5. HW-L is for finite support; the extension to ℓ¹ is a limit argument, not stated.
6. Unitarity of the step (conservation of Σ_x |ψ(x)|²) is not a statement of the batch; it is checked numerically
   only (item 7).
7. Numerical truth checks by the lead before the freeze, two methods that share no formula (the step recursion on
   the lattice against the kernel integral of the definition by the trapezoidal rule, itself checked against adaptive
   quadrature): `numerics/review/hw_statement_checks.py`, results
   `numerics/results-hw-statement-checks-2026-11-16.txt`, 18 lines, all pass; two altered forms of HW-R (shifts
   exchanged; the sign of b) are rejected. Floating point, not certified: tooling, not evidence.
8. The sanity layer: `docs/replay/2026-11-16-HW-sanity-plants.txt`. 76 declarations, 14 through a statement constant.
   Exact data at t ≤ 2 only: the walk after one and two steps from a point state at every site; K(0, ·) = 0,
   K(1, ·) = δ, K(2, ∓1) = ±1/√2; the identities of the dispersion relation. HW-R is tested at t = 0 and t = 1 at
   every site (this pins the handedness, the coin signs, the sign of x and the normalisation of the kernel).
   23 planted mutations: 19 are refuted by compiled witnesses (all eleven of HW-R, including the three mutations of
   the kernel and one of the dispersion relation); 1 is a true weakening (HW-K without t ≥ 1, see choice 2); 3 are
   not detected: HW-K with 19 t^{−1/2}, HW-K with 7 t^{−1/2} alone, HW-D with 39 t^{−1}. No datum lies where a bound
   beats the trivial one, so the constants 7, 12, 39 are tested only against 1, 1/√2 and 1/2, and the exponents rest
   on the reviews and on the proof. Found by the sanity agent with exact integer arithmetic, outside Lean: the
   mutation of HW-D with 39/t first fails at t = 126 (first component at x = −86 from the state (1, 0):
   2857838189219694731/2⁶³ ≈ 0.30985 against 39/126 ≈ 0.30952).

Clarifications added after the freeze of batch HW (2026-11-17, from the blind pre-proof reviews; the stamped text
above and the Lean file are unchanged; `review/2026-11-17-HW-pre-proof-answers.md`).
a. Item 8 overstated the first sanity layer: its data at t ≤ 1 pin the sign of x in the definition of the kernel and
   in the first summand of HW-R, not in the summands a K(t, x) and b K(t, x) (K(0, ·) and K(1, ·) are even). The second
   layer (`OscInt/Front/HadamardWalkSanity2.lean`, `docs/replay/2026-11-17-HW-sanity-plants-second.txt`) has the walk
   after three steps, K(3, ·) = 1/2 at ±2, K(5, ·) = 1/4, 1/2, −1/2, 1/2, 1/4 at −4, −2, 0, 2, 4, and HW-R at t = 2. Second
   run, 9 planted mutations: 6 refuted by compiled witnesses (the sign of x in each of the two summands; 39 ↦ 1 in
   HW-D and HW-L; (7, 12) ↦ (1, 0) in HW-K; the support hypothesis on one component), 2 not detected (an exponent
   mutation of HW-L; the product of the two terms of HW-K), 1 with no known violation (item f).
b. The numbers of modelling choice 3, corrected and completed by the referees: sup_x |K(t, x)| t^{1/3} equals 1 at
   t = 1 (K(1, 0) = 1) and is below 1 from t = 2 (largest value 0.9637, at t = 6; 0.9547 at t = 3000; about 0.9544
   asymptotically). The largest component from the state (1, 0) is 1.6113 t^{−1/3} at t = 3000, 1.6208 t^{−1/3} at most
   for t ≤ 3000, and about 1.6293 t^{−1/3} asymptotically. So the constants of HW-K and HW-D are about 12.6 and 23.9
   times the attained values. HW-K is implied by the trivial bound for t ≤ 1679, and HW-D and HW-L by conservation of
   the ℓ² norm for t ≤ 59319.
c. The literature locator. In arXiv:1808.05714 the sentence quoted is in Section 3 of version 1 (before Proposition
   3.12) and in Section 4 of version 3 (before Proposition 4.12). That paper states the estimate for a constant coin
   with an implicit constant, says it is also proved in two other papers, and credits Sunada and Tate
   (arXiv:1108.1878); "Airy asymptotics" above undersells that paper. Its conventions differ from this batch: the
   Euclidean norm on ℂ² and the opposite handedness.
d. Norms. HW-D and HW-L bound each component of ψ_t(x) (the maximum norm on ℂ²) by the ℓ¹ sum of |ψ₁| + |ψ₂|. With the
   Euclidean norm on ℂ² on both sides the same statements give the constant 39·2 = 78 (a factor √2 on each side).
e. The eigenvalue remark of the Notation ("at quasi-momentum k the step has the eigenvalues e^{−iω(k)} and −e^{iω(k)}")
   is for plane waves v e^{−ikx}, the convention of the kernel. In the Route, 6.8700 should read 6.8699 (6.86990…),
   and the derivation of HW-D also uses (t − 1)^{−1/2} ≤ √2 t^{−1/2} for t ≥ 2.
f. CONJECTURED, not a statement of this batch: |K(t, x)| ≤ t^{−1/3} for every t ≥ 1 and every site x. Evidence:
   floating-point evaluation of the exact recursion at every site for t ≤ 9000 (largest value of
   sup_x |K| t^{1/3} for t ≥ 2: 0.9637) and on a grid of times up to 1.6·10⁷ (two referees and a sanity agent,
   independently). What would falsify it: one pair (t, x) with |K(t, x)| t^{1/3} > 1. The route of this batch gives
   7 t^{−1/2} + 12 t^{−1/3} and cannot reach it.
g. Added 2026-11-17 after the post-proof reviews (`review/2026-11-17-HW-post-proof-answers.md`); the text above is
   unchanged. In item 8 and in the plant summary, "HW-K without t ≥ 1" is called a true weakening: dropping a
   hypothesis strengthens a statement, and here the result is equivalent to HW-K (at t = 0 both sides are 0 in Lean,
   as the plant summary says); "true and equivalent" is the accurate word. In clarification f, "independently" means: by separate AI agents of one model family, each with
   its own code, on one machine; not by independent people. HW-L is stated for finitely supported initial states.
h. Corrections after the external review of batch HW (2026-11-19, `review/2026-11-19-HW-external-review-answers.md`).
   (1) Clarification b, "1.6208 t^{−1/3} at most for t ≤ 3000", was the maximum rounded down and written as a bound.
   Exact integer arithmetic (`numerics/review/hw_exact_max_checks.py`, result
   `numerics/results-hw-exact-max-checks-2026-11-19.txt`): the largest component from the state (1, 0) exceeds
   1.6208 t^{−1/3} at t = 2990 and t = 2997 and at no other t ≤ 3000; the maximum is 1.620846… at t = 2997,
   x = −2111, above 1.62084 t^{−1/3} and below 1.62085 t^{−1/3}. (2) The header of the second sanity file said "the
   first layer tested 39 against 1/2 only"; the first layer has HW-D at t = 1 (1/√2) and t = 2 (1/2), where the
   constant 1 also holds. Corrected in the file. (3) In the pre-proof answers, "no exact datum can detect a wrong
   exponent" is too broad: 39/t fails exactly at t = 126 (recorded in the same file). What the finding supports is
   narrower: because the constants are 12 to 24 times the attained values, an exponent mutation that keeps the
   bound above the attained values at the times an exact datum reaches is not refuted by such a datum (the
   recorded cases: the exponent mutation of HW-L, and HW-K with the product of its two terms, first false near
   t = 7749). (4) The header of `numerics/review/hw_statement_checks.py` announced exact integer-pair arithmetic
   that the script never had, and its comparison of the trapezoidal rule with adaptive quadrature had one nonzero
   value among ten; the header is corrected and six points with nonzero values are added. The statement file is
   unchanged.

## Batch SPL: the leading term of a quadratic-phase integral with an explicit remainder (session 13, 2026-11-19)

Order. As batch VC2: statements, `OscInt/Statements/StationaryLeading.lean`, sanity theorems with planted controls,
challenge and comparator, frozen and stamped before the blind pre-proof reviews. What differs from "statement
first", said plainly: a complete proof on paper of SPL-I, SPL-S, SPL-K and SPL-A predates the freeze
(`docs/proof-SPL.md`, second version; its first version was read by a plan referee of the lead's model family,
`review/2026-11-19-SPL-plan-referee-answers.md`), and a registered numeric test of the draft statements was run
before the freeze (`docs/prereg/2026-11-19-SPL-quadratic-remainder.md`, PASS 12 of 12). No Lean proof of these
statements is in the repository history before the stamp of the answers to the blind reviews. Owner decision that
opened the batch: `docs/decisions/2026-11-19-next-batch-spl.md`.

Why. The library bounds oscillatory integrals from above. A consumer that needs an asymptotic formula needs the
leading term and a bound, with a stated constant and valid for every value of the large parameter, on what is left
(`docs/ROADMAP.md`, "Asymptotic expansions"; `docs/design/batch-SPL-opening.md`). This batch does that for the
normal form of a nondegenerate stationary point in one variable, the phase u²/2. The identity SPL-I is classical in
substance: it is the two-sided case, three integrations by parts, of Erdélyi's remainder representation
(`docs/prior_art.md`, gate of 2026-11-19). A leading term for the same phase is already formalised in Lean
elsewhere, for Schwartz amplitudes with a remainder in a Fourier-moment norm (`docs/prior_art.md`, second addendum);
this batch has the remainder in ‖g₃‖₁ with an explicit kernel and constant, for amplitudes that need not be
Schwartz. Nothing is claimed as new; the claim, if proved, is "machine-checked, with an explicit constant".

Notation. F(x) = ∫_0^x e^{iv²/2} dv (Lean `fresnelPrim x`); L = √π (1 + i)/2 (Lean `fresnelLimit`; it is the limit of
F at +∞, which is a fact to be proved and is not used to define anything). The kernel: for τ ≥ 0,
κ(τ) = F(τ)/2 + τ e^{iτ²/2}/2 + (iτ²/2)(L − F(τ)) (Lean `splKernelPos τ`), and κ(τ) = −κ(−τ) for τ < 0 (Lean
`splKernel`). An *amplitude* is a function g: ℝ → ℂ together with functions g₁, g₂, g₃ such that g has derivative
g₁(x) at every x, g₁ has derivative g₂(x), g₂ has derivative g₃(x), and g, g₁, g₂, g₃ are integrable on ℝ (Lean
`SplAmplitude g g₁ g₂ g₃`). ‖g₃‖₁ = ∫_ℝ |g₃|. For λ > 0,
R(g, λ) = ∫_ℝ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4} (Lean `splRemainder g lam`).

**SPL-I (the remainder as an integral).** For every amplitude and every λ > 0:
R(g, λ) = −i λ^{−3/2} ∫_ℝ g₃(t) κ(√λ t) dt.

**SPL-S (bound through the kernel).** For every amplitude and every λ > 0 there is τ ≥ 0 with
|R(g, λ)| ≤ |κ(τ)| ‖g₃‖₁ λ^{−3/2}.

**SPL-K (bound with a number).** For every amplitude and every λ > 0: |R(g, λ)| ≤ (7/8) ‖g₃‖₁ λ^{−3/2}.

**SPL-A (sharpness: attained in the limit, not by an extremiser).** For every τ ≥ 0 and ε > 0 there is an amplitude with g infinitely differentiable, of compact
support and not identically zero, such that |R(g, 1)| ≥ (|κ(τ)| − ε) ‖g₃‖₁. (With SPL-S: the best constant K in
|R| ≤ K ‖g₃‖₁ λ^{−3/2} is sup |κ|.)

What the statements say and do not say (modelling choices and omissions, for the reviewer).
1. The phase is exactly u²/2. A general phase with a nondegenerate stationary point is not treated; it is stage 2
   of the batch plan and has no statement. The sign of the phase is +. For the phase −u²/2 and a complex
   amplitude the rule is R₋(g, λ) = conj(R₊(conj g, λ)), where R₋ has e^{−iλu²/2} and e^{−iπ/4}; it is not stated in
   Lean in this freeze.
2. The amplitude is on the whole line with integrable derivatives; compactly supported functions of class C³ and
   Schwartz functions are amplitudes. End points are not treated: an integral over a bounded interval with an
   amplitude that does not vanish at the ends has contributions of order 1/λ that these statements do not describe.
3. Continuity of g₃ is not asked. Integrability of g₁ and g₂ is asked although it follows from that of g and g₃
   (proved on paper by an external session and re-derived by a checker,
   `review/2026-11-19-SPL-external-sessions-answers.md`; not proved in Lean, not used as a claim). A statement
   with two hypotheses is a possible later corollary.
4. In Lean `∫` is the Bochner integral, which is 0 for a function that is not integrable; `Integrable g` in the
   hypothesis is what makes the first term of R the integral it denotes. `√(2π/λ)` is `Real.sqrt`, and `λ^{−3/2}`
   is `Real.rpow`; both are used only for λ > 0.
5. SPL-S has the form "there is τ" used by VC2-S for a constant that is a supremum of a profile. It does not say
   where |κ| is largest or what its largest value is.
6. The number 7/8 in SPL-K is not the best constant. Numerically sup |κ| = 0.7219740, at τ = 1.6246 (registered
   test, and since then an exact-arithmetic enclosure by an external session, re-run by a checker; not a Lean
   theorem; the two decimals are rounded). A statement with a rational close to that value (SPL-N) is not in this
   batch's first freeze: its proof needs certified enclosures of the Fresnel primitive that the library does not
   have (`docs/proof-SPL.md`, sections 5 and 9).
7. SPL-A is stated at λ = 1; other λ follow by scaling, which is not stated. It gives no rate in ε.
8. The remainder is O(λ^{−3/2}) and the statements give no second term of the expansion. Consistency with the
   classical second term, of modulus (√(2π)/2) |g″(0)| λ^{−3/2}: since |g″(0)| ≤ ‖g₃‖₁/2, no constant below
   √(2π)/4 = 0.6267 can be true in SPL-K.
9. Relative to Erdélyi's theorem (one-sided integrals, stationary points and singularities of real order, any
   number of terms): one case only, two-sided, with the term in g″(0) not separated.
Sanity layer and planted controls (written by an agent of the lead against the draft text, under a brief that
forbids proving the statements; the statement file entered the repository unchanged, SHA-256
12f8d3b622949cd8a9d3d518236da7f96ae84cc26f3d72dda64bb05bfb40c715). `OscInt/Front/StationaryLeadingSanity.lean`:
96 theorems. Data: the kernel at 0 and its oddness; the two constants tied to each other
(`√(2π) e^{iπ/4} = 2 F(∞)`); the Gaussian family `e^{−(su)²/2}` as amplitudes with the closed form of its remainder
and certified bounds `√(2π) s²/(2√λ √(s⁴+λ²)) ≤ |R| ≤ √(2π) s²/(√λ √(s⁴+λ²))`; `‖g₃‖₁ = s²(2 + 8e^{−3/2})`; two bites
on the class (the constant 1; a wrong first derivative); a nonzero amplitude has `‖g₃‖₁ > 0`. Each statement is
instantiated at two Gaussians (s = 1, λ = 4 and s = 2, λ = 9); SPL-K is shown not vacuous there (the left side
is at least a third of the right side); SPL-A with SPL-K gives `|κ| ≤ 7/8`. Planted controls: 42 mutations,
`docs/replay/2026-11-19-SPL-sanity-plants.txt` (re-run by the lead, byte-identical): 22 detected, 7 detected only
under the hypothesis `|κ| ≤ 2` (no Lean proof before the freeze), 7 detected relative to the true statement, 3
equivalent, 3 true weakenings, none undetected. What the layer cannot see, said before the review: a constant
between about 0.331 and 7/8 in SPL-K (the Gaussian's ratio stops at 0.331; 7/8 ↦ 1/2 would be false and would not
be detected); the size of `|κ|` anywhere but at 0; the clauses "compact support" and "infinitely differentiable" of
SPL-A, and its existence claim for τ > 0. For those the batch rests on the fidelity reviews, on the registered
numeric test and on the external derivation, not on the sanity layer.

10. Planned for a second freeze of this batch, after a critique of this draft by an external session
    (`review/2026-11-19-SPL-external-sessions-answers.md`, section 5), and not stated here: a front end for a
    compactly supported function of class C³ with its canonical derivatives; the phase −u²/2; sharpness for every
    λ > 0; SPL-N. A user of SPL-K in this freeze supplies the three derivative functions and the four
    integrability facts.

Clarifications after the blind pre-proof reviews (2026-11-20; `review/2026-11-20-SPL-preproof-answers.md`). The
statement file is unchanged.
SPL-a. Item 3 and item 4. "Continuity of g₃ is not asked" does not mean that g₃ may jump: g₂ has the derivative
   g₃(x) at every point x, so g₃ has the intermediate-value property, and an amplitude whose second derivative has
   a corner (a cubic spline, a piecewise C³ function) is not an amplitude in the sense of these statements,
   although the identity holds for it. Admitted: third derivatives that are discontinuous by oscillation, or
   unbounded near a point, as long as they are integrable. In SPL-I both sides are Bochner integrals; the integrand
   on the right is integrable once the kernel is known to be bounded, which is part of the proof and not of the
   statement.
SPL-b. Three sentences above claim more than is there. (1) "Each statement is instantiated at two Gaussians":
   true of SPL-I, SPL-S and SPL-K; SPL-A is instantiated at τ = 0 and at τ = 1, with no Gaussian datum. (2) Item 8,
   "since |g″(0)| ≤ ‖g₃‖₁/2, no constant below √(2π)/4 can be true": the inference needs amplitudes for which that
   inequality is nearly an equality; the number is right (it is the limit of |κ| at infinity). (3) "The best
   constant is sup |κ|" is a consequence of SPL-S and SPL-A together with the fact that a nonzero amplitude has
   ‖g₃‖₁ > 0 (proved in the sanity layer); it is not a Lean statement of this freeze and concerns constants that do
   not depend on λ.
SPL-c. What the planted controls do not cover, as the two referees listed it: any change inside the kernel (a
   sign or coefficient of one of its three terms, the phase or the sign of i in the Fresnel primitive, the value
   of F(∞) except through SPL-A with SPL-K); the factor g(0) of the leading term replaced by 1, by a conjugate or by
   a modulus (all data are real even Gaussians with g(0) = 1); `0 < ε` weakened to `0 ≤ ε` in SPL-A;
   `Integrable g₃` dropped; 7/8 replaced by a number down to about 0.33. Two more would be detected by the existing
   data and were not planted: the phase `λu²/2` replaced by `λu²`, and the sign of i in the remainder. For all of
   these the batch rests, until the proofs exist, on the fidelity reviews and on numerics (the registered test and
   the referees' own), not on the sanity layer.
SPL-d (2026-11-20, after the proofs; post-proof referee C). The proofs do not turn SPL-I into a characterisation
   of the kernel: for every amplitude the integral of g₃ is zero, so SPL-I stays true when any complex constant is
   added to κ (compiled: `docs/replay/plants/2026-11-20-SPL-closed`, the file whose name starts with
   "equivalent"). What pins the kernel is its oddness, which is part of the frozen definition, together with
   SPL-I; its supremum is pinned by SPL-S with SPL-A. With the proofs, the 7 planted mutations that were refuted
   only under a bound on the kernel and the 7 refuted only relative to a true statement are refuted outright
   (`docs/replay/2026-11-20-SPL-plants-closed.txt`): 36 of 42, the others being 3 equivalent ones and 3 true
   weakenings. The mutations of SPL-c that the layer cannot see are excluded by the proofs only in the sense that
   the frozen text, and not a mutation of it, is what was proved. Two more that no datum of the layer sees
   (same referee): `λ = 1` in SPL-A replaced by another fixed λ, and `HasDerivAt` replaced by an equation with
   `deriv`.

## Batch TSD: two-saddle steepest descent with an explicit remainder (session 14, 2026-11-20)

Status of this section on 2026-11-20: prose only. No Lean statement of the batch exists, nothing is frozen, and no
Lean proof of any part exists in the repository or in the lead's scratch. Order, as for batch SPL: this prose, a
registered numeric test of it, the Lean statements with a sanity layer and planted controls, challenge and
comparator, freeze and stamp, two blind referees, and only then proofs (`CONTRIBUTING.md`). What predates the
freeze, said plainly: a proof on paper by the source's authors, re-derived three times
(`review/2026-11-20-TSD-step-referee-answers.md`: a step referee and a checker of the lead's model family, and a
session of another model family); no machine check. Owner decision that opened the batch:
`docs/decisions/2026-11-20-batch-two-saddle.md`; opening note: `docs/design/batch-TSD-opening.md`.

Source. Lemma E.1 of *The spinless modular bootstrap at large central charge* (hexagon:2611.00174v1, CC BY 4.0;
appendix "Two-saddle steepest descent with a uniform remainder"; the label in the TeX source is `lem:D.1`;
SHA-256 of the TeX file 6e167ddd9f1c8ba46680c9550fd5d84eacf3d9901d02f4c9b22433d63b2db079, downloaded again on
2026-11-20 in session 14 and equal to the value recorded in session 13). Cited, not copied.

Why. A lemma on which a current research preprint rests, with a four-page proof by a long chain of explicit
constants. The mechanism is classical (the ordinary two-saddle formula away from coalescence); this quantified
general form was not found in the literature searched (the search and its limits: section 2 of the review file
above). Nothing is claimed as new. The claim, if proved, is "machine-checked, with these constants".

Two statements are planned. **TSD-C**, the core, is about two analytic functions on a strip and has no special
function in it. **TSD-L** is the lemma in the form in which it is printed, with a function `H` in the place of
the Hankel function `H₀^{(1)}`, and follows from TSD-C by a change of variables and algebra. The first freeze of
the batch holds TSD-C only; the Lean text of TSD-L is written after the two external reports that bear on it (a
proof of the Hankel bound; an audit of how the preprint uses the lemma) have been checked.

Notation for TSD-C. For δ > 0 the closed strip is `S_δ = {z ∈ ℂ : |Im z| ≤ δ}`. A prime is the complex
derivative. `e = 2.718…` is Euler's number where it appears as a factor of a constant.

**TSD-C (two saddles on the real line, symmetric form).** Let `δ, t, s, α, β, C₂, ℓ, r` be positive real numbers
and `C₃, M, M′` nonnegative real numbers. Let `U ⊆ ℂ` be open with `S_δ ⊆ U`, and let `φ, A : U → ℂ` be
holomorphic. Assume:

1. (symmetry) for every `z ∈ S_δ`: `A(z) ≠ 0`, `φ(−z) = −φ(z)`, `φ(z̄) = conj φ(z)` and `A(−z̄) = conj A(z)`;
2. (integrability) `v ↦ A(v)` is integrable on ℝ;
3. (saddle) `φ′(s) = 0` and `φ″(s) = −α`;
4. (slopes) `Re φ′(v) ≥ β (s − v)` for `0 ≤ v ≤ s`, and `Re φ′(v) ≤ −α (v − s)` for `v ≥ s`;
5. (bounds) for every `z ∈ S_δ`: `|φ‴(z)| ≤ C₂`, `|φ⁗(z)| ≤ C₃`, `|A′(z)/A(z)| ≤ M` and `|(A′/A)′(z)| ≤ M′`;
6. (window) `ℓ ≤ √2 δ`, `C₂ ℓ ≤ α`, `C₂ ℓ ≤ (3√2/2) β`, `M ℓ ≤ 1`, `r ≤ ℓ` and `t C₂ r³ ≤ 6`;
7. (largeness) with `u = ℓ/√2`: `2M ≤ t β u` and `t α ≥ 8`.

Put `K = (e − 2)(M² + M′)` and

    ε_core = K/(tα) + (C₃/8 + M C₂/2 + K C₂)/(tα²) + (57/100 + (13/25) M) C₂²/(tα³),
    ε_tr   = 3 e^{Mℓ} e^{−tα r²/3} / (√(2π) r √(tα)),
    ε_mid  = 2 e^{Mu} √(α/(2πt)) e^{−tβ u²/4} / (βu),
    ε_far  = √(2/π) e^{Mu} e^{−tα u²/4} / (u √(tα)).

Then `v ↦ A(v) e^{itφ(v)}` is integrable on ℝ; its integral `J = ∫_ℝ A(v) e^{itφ(v)} dv` is a real number; and

    |J − 2 √(2π/(tα)) Re[e^{−iπ/4} A(s) e^{itφ(s)}]| ≤ 2 |A(s)| √(2π/(tα)) (ε_core + 2 ε_tr + ε_mid + ε_far).

Reading. By (1) the function `φ` is real on ℝ and odd, so `v ↦ tφ(v)` is a real phase with stationary points at
`s` and `−s` (and possibly at 0); the two saddle contributions are complex conjugates of each other, and the
leading term is their sum. `α` is the curvature at the saddle, `β` a lower bound for the slope of the chord of
`φ′` between 0 and `s`; both tend to 0 when the saddles coalesce (`s → 0`), and the right-hand side then
grows: the statement is the ordinary two-saddle formula with a remainder that is explicit up to coalescence, not
a uniform (Airy-type) expansion through it.

What TSD-C says and does not say (modelling choices and omissions, for the reviewer).
1. Relation to the printed lemma. With `z = b − i/2`, `t = c′`, `s = v₀`, `φ(z) = (4π/3) ∫₀^z (x − F)`, that is
   `φ(z) = −i[Φ₀(z + i/2) − Φ₀(i/2)] + (4π/3) x z`, `α = α_x`, `β = (4π/3) s_ch`, and `A` the printed amplitude at
   `z + i/2` times the unimodular constant `e^{−iπ/4} e^{c′Φ₀(i/2)}`, the four error terms are the printed ones
   term by term (`ε_mid` after substituting β), and the printed conclusion is `(2πc′/3) √(2/(πk_x)) e^{−k_x/2} J`.
2. The window `r` is a parameter with two inequalities; the printed lemma takes the largest admissible value,
   `r₁ = min{ℓ, (6/(c′C₂))^{1/3}}`. `ε_tr` decreases in `r`, so the printed choice gives the best bound, and
   TSD-C at that value is the printed form. Likewise `ℓ` is a parameter with inequalities in place of the printed
   minimum of seven quantities; no division by `C₂`, `M` or `M′` occurs.
3. Hypotheses of the printed lemma that TSD-C does not have, because its conclusion does not need them
   (step referee, finding 1; external report, checked): `c′ ≥ 39`; `δ₁ ≤ 1/4`; the lower bound on `c′F(0)`; the
   bound on the Hankel remainder; evenness of `F` and `h₀` beyond the symmetry in (1); exponential decay of the
   amplitude below the line (integrability on the line is enough, because the bounded logarithmic derivative
   carries it down); `ℓ ≤ 1`; `ℓ ≤ v₀` (it follows: `α ≤ C₂ s` because `φ″` is odd, so `ℓ ≤ α/C₂ ≤ s`); the
   printed condition (ii), `c′ α_x u₀ ≥ 2M` (it follows from (7) and `β ≤ α`, which follows from (3) and (4));
   `M′ ℓ² ≤ 1` (not needed with the coefficient `K` of item 4).
4. The amplitude coefficient. The printed lemma has `K_A = (9/2) M² + (13/8) M′`; TSD-C has the smaller
   `K = (e − 2)(M² + M′)`, from the external session's derivation (`e − 2 < 0.72`). The right-hand side increases
   with `K`, so TSD-C implies the same statement with the printed coefficient. The decimal constants of the
   printed core term are the rationals `57/100` and `13/25`.
5. Hypotheses that are implied by the others and are kept for readability: `φ′(s) = 0` (from (4) at `v = s` and
   (1)); the positivity of `C₂` (from `0 < α ≤ C₂ s`). `A ≠ 0` is needed in the mathematical reading; in Lean,
   where `x/0 = 0`, the bound on `A′/A` alone would let an amplitude vanish, and (1) excludes that explicitly.
6. Hypotheses that the three readings found necessary, each by a computed counterexample when it is dropped or
   weakened (not Lean theorems; `review/2026-11-20-TSD-step-referee-answers.md`, section 4): the largeness
   condition on `M` in (7); `φ″(s) = −α` as an equality (an inequality fails); the oddness of `φ`, the symmetry
   of `A`, and the integrability of `A`. Not decided, and therefore kept: whether `C₂ℓ ≤ α`,
   `C₂ℓ ≤ (3√2/2)β`, `Mℓ ≤ 1` and `tα ≥ 8` are needed by the statement or only by this proof.
7. Sharpness. Nothing is claimed about the constants being best. Numerically the bound is attained in the limit
   on a constructed instance (ratio of bound to measured error 1.0017, step referee), so the core term cannot be
   lowered in general; this is not a statement of the batch.
8. In Lean the integral is the Bochner integral over ℝ, which is 0 for a function that is not integrable; the
   first conclusion (integrability) is what makes `J` the integral it denotes. "`J` is real" is stated as
   `Im J = 0`. Derivatives are Mathlib's `deriv` of functions `ℂ → ℂ` that are differentiable on the open set
   `U`; the functions are total and only their values on `U` matter.
9. Not stated: the contour, the four pieces separately, any expansion beyond the leading term, any statement
   for a phase that is not odd or for saddles that are not a mirror pair, and uniformity through coalescence.

**TSD-L (the printed lemma, with the Hankel function as a parameter); planned, not in the first freeze.** In
substance: for functions `h₀, Φ₀, Φ₁, 𝓔` and `H` that satisfy the printed hypotheses (SD1) to (SD4), where `H` is
only asked to be holomorphic in the upper half-plane and to satisfy the printed bound on the remainder `ε_H`
that the factorisation `H(z) = √(2/(πz)) e^{i(z − π/4)} (1 + ε_H(z))` defines, and for `ℓ`, `u₀`, `r₁` and the
largeness conditions (i) to (iii) as printed, the number `N = (2πc′/3) ∫ 𝓘(v + i/2) dv` with
`𝓘(b) = h₀(b) H(k_x b) b` satisfies `|N − 2 Re W| ≤ 2 |W| (ε_core + 2ε_tr + ε_mid + ε_far)` with
`W = (2πc′/3) h₀(b₀) H(k_x b₀) b₀ e^{−iπ/4} √(2π/(c′α_x))` and the printed four terms with the printed
coefficient `K_A`. Here `2 Re W = Amp cos Ψ̂` and `2|W| = Amp` are the printed amplitude and phase (the lemma
states that they satisfy this identity exactly); writing the conclusion through `W` avoids a choice of argument.
Open points, to be settled before its Lean text is drafted: whether the printed closed forms of `Amp` and of
`Ψ̂` are separate conclusions; the form of the edge representation (in the abstract statement the transform
`ĥ₀(c′x²/3)` is the number `N` by hypothesis); which properties of `H` are hypotheses (holomorphy and the
remainder bound are used three times: no zero of the amplitude, integrability, and the printed remark on the
amplitude); whether `H` stays a parameter. What TSD-L would not say in any form: that the preprint's own
function satisfies (SD1) to (SD4), or anything about the preprint's theorems.

Note of 2026-11-20, after the checks of two external reports (`review/2026-11-20-external-reports-answers.md`,
sections 2 and 4). (1) The factorisation above must be read with the prefactor `√(2/π) z^{−1/2}`, principal
power; written as the principal root of the quotient `2/(πz)` it has the other sign on the negative real axis.
On the open upper half-plane, where TSD-L uses it, the two agree. (2) Hypotheses that a statement of the printed
lemma needs: bounds `M`, `M′` and the absence of zeros for the whole amplitude, the factor with `H` included;
evenness of `F`; the two slope inequalities; the symmetry of `𝓘` on the strip; integrability on the edge; `C₂`
and `C₃` as inequalities. Printed hypotheses that are idle: (SD3), (SD2)(d), (SD2)(e), `c′ ≥ 39`, the lower
bound on `c′F(0)`. Printed hypotheses that cannot be used as printed: "real on ℝ ∪ iℝ" (the preprint's own
function has poles on the imaginary axis; the condition is also redundant), "independent of `c`", and the edge
representation, which only names the integral. (3) A bound for the remainder of the Hankel function of order
zero that is stronger than the printed one, `|ε_H(z)| ≤ 1/(8|z|)` on the closed upper half-plane, with bounds
for two derivatives, has a proof on paper that was checked; the bound itself is in print (Nemes 2017). Whether
`H` stays a parameter is not decided.

## Batch TRI: the singularity types of the anisotropic triangular lattice phase (session 15, 2026-11-27)

Order. As batch SPL: the statements in `OscInt/Statements/TriangularAniso.lean`, sanity theorems with planted
controls, a challenge file and a comparator, frozen and stamped before the blind pre-proof reviews. What differs from
"statement first", said plainly:
- A complete proof on paper predates the freeze. It is an external derivation, checked by the lead with SymPy
  computations from the phase itself and by a fresh-context referee (`review/2026-11-26-A5-handoff-answers.md`).
- A registered numeric test was run before the freeze (`docs/prereg/2026-11-27-TRI.md`, OVERALL FAIL for reasons
  of resolution; second registration `docs/prereg/2026-11-27-TRI-2.md`, OVERALL FAIL, a deduplication defect at the
  A5 points; third registration `docs/prereg/2026-11-27-TRI-3.md`, OVERALL PASS). The second and third were
  registered with knowledge of the earlier runs, so they are not independent tests.

No Lean proof of these statements is in the repository history before the stamp of the answers to the blind reviews.
The batch was opened by the owner's decision of 2026-11-27, recorded in the session log
`docs/progress/2026-11-26-session15-log.md`.

Why. The band `Ψ_α(x, y) = cos x + cos y + α cos(x + y)` is the simplest nonseparable lattice dispersion relation
with a coupling parameter: the square lattice for α = 0 and the isotropic triangular lattice for α = 1. The
classification below of its singularity types, for every α, is the input to a sharp fixed-coupling decay theorem
(K2, a later batch; `review/2026-11-27-K2-proof-answers.md`). The prior-art gate found the classification for
general α, and the exceptional coupling `|α| = 1/(2√2)` where an A5 point appears, nowhere in the literature
searched (`review/2026-11-26-A5-handoff-answers.md`, section 5). The isotropic case α = 1 is in Ge–Hua–Jia–Zhou
(2025), with an incomplete proof. The claim, if proved, is "machine-checked; not found in the literature searched",
never "new".

Notation.
- `triPhase α k = cos k₁ + cos k₂ + α cos(k₁ + k₂)` on ℝ × ℝ; `a* = 1/(2√2)` (Lean `triExceptional`).
- Derivatives are `iteratedFDeriv` applied to lists of vectors, as in `IsA3Point` (batch A3); `FoldOrNondeg`
  (batch S3) is "nondegenerate, or rank one with a nonzero cubic along every kernel vector", that is A1 or A2.
- A *reduced curve* at `k₀` for vectors `v, w` and radius ε: a smooth h with h(0) = 0 and
  `DΨ(k₀ + uv + h(u)w)·w = DΨ(k₀)·w` for |u| < ε (Lean `ReducedCurve`).
- The *reduced function* `g(u) = Ψ(k₀ + uv + h(u)w) − DΨ(k₀)(uv + h(u)w)` (Lean `reducedFn`).
- *A5 point* (Lean `IsA5Point`): there are `v ≠ 0` in the Hessian kernel, w with `D²Ψ[w, w] ≠ 0`, ε > 0 and a reduced
  curve, such that `g⁽ʲ⁾(0) = 0` for j = 1, …, 5 and `g⁽⁶⁾(0) ≠ 0`.

**TRI-K (classification).** For α ≠ 0, every point of ℝ² is A1 or A2, A3, or A5 for `triPhase α`. In particular
there is no A4 point and no point with Hessian zero.

**TRI-X (the A5 locus).** If k is an A5 point of `triPhase α`, then |α| = a* and k is `(θ, −θ)` or `(−θ, θ)` modulo
2π in each coordinate, with `θ = arccos(−2α)`. For +a* that is `θ = 3π/4`; for −a* it is `θ = π/4`.

**TRI-W (the A5 witness and its sextic).** For |α| = a* the points `(θ, −θ)` and `(−θ, θ)` are A5 points. With
v = (1, 1) and w = (1, −1), every reduced curve at `(θ, −θ)` gives `g⁽⁶⁾(0) = −60√2 · sign α`. In the unit kernel
coordinate s = √2 u this is the coefficient `−sign α/(48√2)` of s⁶.

**TRI-Q (the reduced quartics).** For α ≠ 0, at `(π/2, π/2)` with v = (1, −1) and w = (1, 1): v spans the Hessian
kernel, `D³Ψ[v, v, v] = 0`, and `D²Ψ[w, w] D⁴Ψ[v⁴] − 3(D³Ψ[v, v, w])² = −12`. For 0 < |α| ≤ 1/2, at `(θ, −θ)` with
v = (1, 1) and w = (1, −1), the same hold with the value `12(8α² − 1)`. In the unit kernel coordinate the quartic
coefficients are `−1/(32α)` and `(8α² − 1)/(32α)`.

What the statements say and do not say (modelling choices and omissions, for the reviewer).
1. **The fixed phase.** Types are of the fixed phase. The linear term `n·k/t` of a lattice kernel changes only
   first derivatives, so these are the types of `Ψ_α + p·(·)` at its critical points, for every p.
2. **Points are in ℝ², not on the torus.** TRI-X gives the locus with integer shifts by 2π.
3. **The witness at one point only.** TRI-W gives the sextic at `(θ, −θ)` only. At `(−θ, θ)` it follows by the
   symmetry `(x, y) ↦ (y, x)`, which is not stated.
4. **The A5 definition.** `IsA5Point` asks for some reduced curve, while TRI-W states its value for every reduced
   curve. The implicit function theorem makes the curve unique near 0 when `D²Ψ[w, w] ≠ 0`; that is not stated.
5. **Not stated:**
   - the case α = 0 (four D4 points, from the product structure);
   - the off-axis A3 points that exist for some α (their number as a function of α);
   - the mutual exclusivity of the four types;
   - anything about decay.

Clarifications after the blind pre-proof reviews (2026-11-27; `review/2026-11-27-TRI-preproof-answers.md`). The
statement file is unchanged.
TRI-a. TRI-Q states that v lies in the Hessian kernel (`D²Ψ[v, z] = 0` for every z). It does not state that v spans
   the kernel: rank one, `D²Ψ[w, w] = 4α ≠ 0` at both points, is not part of TRI-Q, and the sanity layer computes it
   separately. In the notation paragraph, `FoldOrNondeg` asks for a nonzero cubic along every *nonzero* kernel
   vector.
TRI-b. Limits of the sanity layer, frozen with the statements (referee A, finding A2):
   - The layer does not test the transverse equation of `ReducedCurve`: replacing it by `True` is not detected.
   - It does not test the range of orders in `IsA5Point`: `Icc 1 4` in place of `Icc 1 5` is not detected.
   - With a free curve, an indefinite A3 point would count as A5.
   The frozen definitions contain neither mutation. A theorem `¬ IsA5Point (triPhase (1/4)) (π/2, π/2)`, which needs
   the uniqueness of the reduced curve, is owed with the proofs. Plant TRI-X-c is equivalent to the frozen TRI-X, not
   a true weakening (finding A5).
   Addendum (2026-11-27, route referee, finding M3; `review/2026-11-27-TRI-route-referee-answers.md`): the bite needs
   no uniqueness of the reduced curve. The bridge lemma of `docs/proof-TRI.md`, section 4, holds for every reduced
   curve, so the bite follows from TRI-X.
TRI-c. (2026-11-27, after the proofs; `review/2026-11-27-TRI-post-proof-answers.md`.)
   - **"No A4 point" is not proved.** In TRI-K's prose, and in the frozen docstrings, "in particular there is no A4
     point" is the informal reading, not a consequence of the four Lean theorems. TRI-K's disjunction is not exclusive,
     and `IsA5Point` asks for some (v, w, curve). Nothing proved excludes another choice at a locus point whose reduced
     function has `g⁽⁵⁾(0) ≠ 0`.
   - **What is proved,** through lemmas of the proof modules:
     - every reduced curve, at any point, with `g‴(0) = g⁗(0) = 0` lies on TRI-X's locus at |α| = a*;
     - at every locus point, every reduced curve for v = (1, 1), w = (1, −1) has `g⁽¹⁻⁵⁾(0) = 0`.
   - **"No point with Hessian zero"** does follow from TRI-K: each of its three conditions needs `D²Ψ[w, w] ≠ 0` for
     some w.
   - **α = 0.** "The case α = 0 is not stated" refers to its D4 points. TRI-X quantifies over all α and so implies
     that `triPhase 0` has no A5 point.
   - **The bite.** `¬ IsA5Point (triPhase (1/4)) (π/2, π/2)` is proved as a corollary of TRI-X, without uniqueness of
     the reduced curve (TRI-b, addendum).

## Batch K2: sharp fixed-coupling decay on the anisotropic triangular lattice (session 16, 2026-11-28)

Order. As batch TRI: the statements in `OscInt/Statements/TriangularDecay.lean`, sanity theorems with planted
controls, a challenge file (`Challenge/TriangularDecay.lean`) and a comparator (`comparator-K2.json`), frozen and
stamped before the blind pre-proof reviews. What differs from "statement first", said plainly:
- Proofs on paper predate the freeze. One is an external proof reviewed on 2026-11-27
  (`review/2026-11-27-K2-proof-answers.md`, with its erratum in section 5). The other is an external research packet
  with upper and lower routes, reviewed by the lead and by a fresh-context route referee on 2026-11-28
  (`review/2026-11-28-K2-packet-answers.md`). The statements were drafted by the lead after both reviews; the
  referee did not see them.
- A registered numeric test (`docs/prereg/2026-11-28-K2.md`) runs before the freeze.

No Lean proof of these statements is in the repository history before the stamp of the answers to the blind reviews.
The batch was opened by the owner's decision of 2026-11-27 (K2 as its own batch after TRI) and its integration
requested in session 16 (`docs/progress/2026-11-28-session16-log.md`).

Why. TRI classifies the singularity types of `Ψ_α(k) = cos k₁ + cos k₂ + α cos(k₁ + k₂)`. K2 turns that
classification into the decay theorem a dispersive estimate needs. The lattice Schrödinger kernel decays like
`t^{−2/3}` exactly at α ∈ {0, ±1/(2√2)}, and like `t^{−3/4}` at every other α, two-sided, for every real time. The
upper bound holds at every site; the lower bound holds at some site at each time. Three reusable statements come with
it:
- a local bound of any order m, uniform in the linear term;
- monomial asymptotics with an explicit remainder;
- Fourier localisation from a smooth bump to lattice sites.

The prior-art gate of 2026-11-27 (`review/2026-11-26-A5-handoff-answers.md`, section 5) found the two-sided bounds
away from α ∈ {0, 1}, and the exceptional set, nowhere in the literature searched. α = 0 is classical; α = 1 has an
upper bound in Ge–Hua–Jia–Zhou (2025). The claim, if proved, is "machine-checked; not found in the literature
searched", never "new".

Notation (in addition to batch TRI's).
- `triKernel α t n = ∫_{[−π, π]²} e^{i(t Ψ_α(k) + n·k)} dk` for `n ∈ ℤ²`. It is unnormalised, as `latticeKernel` of
  batch GD, so `triKernel 0 = latticeKernel`; the normalised kernel is `(2π)^{−2} triKernel`.
- `triRate α = 2/3` if `α = 0` or `|α| = a*`, and `3/4` otherwise.
- A *plateau cutoff* `(b, r)` (Lean `PlateauCutoff`): b is C¹, compactly supported and even; `b = 1` on `[−r, r]`;
  b is nonincreasing on `[0, ∞)`; and `r > 0`. Then `0 ≤ b ≤ 1` follows, and `∫_r^∞ |b′| = 1`.
- `oscInt2`, `lin`, `AmpBound`, `ReducedCurve`, `reducedFn` as in batches S2, A3 and TRI.

**K2-L (local bound of order m).** Let Ψ be smooth and `k₀, v, w ∈ ℝ²` with `v₁w₂ − v₂w₁ ≠ 0` and
`D²Ψ(k₀)[w, w] ≠ 0`. Let h be a reduced curve on `|u| < ε`, and let `m ≥ 2` with `g⁽ᵐ⁾(0) ≠ 0` for the reduced function
g. Then there are `δ > 0` and C such that, for every `C²` amplitude A with support in the closed ball of radius δ
about k₀ and derivatives of order ≤ 2 bounded by M, every `y ∈ ℝ²` and every `t ≥ 1`,
`|∫ e^{i(tΨ(κ) + y·κ)} A(κ) dκ| ≤ C M t^{−(1/2 + 1/m)}`.

**K2-MA (monomial asymptotics).** For `m ≥ 2` and `σ = ±1` there is `C ∈ ℂ` with:
- `Re C ≥ 1/(12m)`;
- `∫_{−R}^{R} e^{iσx^m} dx → C` as `R → ∞`;
- for every plateau cutoff `(b, r)` and every `t > 0`, `|∫ b(x) e^{itσx^m} dx − t^{−1/m} C| ≤ 4/(m t r^{m−1})`.

**K2-ML (monomial lower bound).** For m, σ, `(b, r)` as above and `t > 0` with `t^{1−1/m} ≥ 96 r^{1−m}`:
`|∫ b(x) e^{itσx^m} dx| ≥ t^{−1/m}/(24m)`.

**K2-F (Fourier localisation).** For a smooth `χ : ℝ² → ℂ` with support inside the open box `(−π, π)²` there is D
such that, for every continuous Ψ that is 2π-periodic in each variable, every real t, every `p ∈ ℝ²` and every B:
if `|∫_{[−π, π]²} e^{i(tΨ(k) + n·k)} dk| ≤ B` for every `n ∈ ℤ²`, then
`|∫_{[−π, π]²} χ(k) e^{it(Ψ(k) + p·k)} dk| ≤ D B`.

**K2-U (upper bound).** For every real α there is C with `|triKernel α t n| ≤ C t^{−triRate α}` for every real
`t ≥ 1` and every `n ∈ ℤ²`.

**K2-D (lower bound).** For every real α there are `c > 0` and T such that, for every real `t ≥ T`, some `n ∈ ℤ²` has
`|triKernel α t n| ≥ c t^{−triRate α}`.

What the statements say and do not say (modelling choices and omissions, for the reviewer).
1. **Constants.** They are existential in K2-L, K2-F, K2-U and K2-D, where they depend on the phase, the point,
   the cutoff or α. They are explicit in K2-MA and K2-ML. Nothing is uniform in α: the constants of K2-U and K2-D may
   degenerate as α approaches 0 or ±a*, and no crossover is stated. No best constant is stated. The explicit
   constants of K2-MA and K2-ML are far from sharp: the true `Re C = 2Γ(1 + 1/m) cos(π/(2m))` is 30 times the bound
   `1/(12m)` at m = 2 and 129 times at m = 6.
2. **The lower bound's site.** K2-D gives some site at each time; it does not say which. In particular it says
   nothing about the site nearest a critical velocity, nor about a fixed ray.
3. **Real times.** Every time in K2-U and K2-D is real. At α = 0 this is more than T6L (integer times on the
   diagonal) gives.
4. **K2-L's hypotheses.** Only the m-th reduced derivative is assumed nonzero; lower orders are unrestricted, so
   the bound may be weaker than the true one. Nothing is assumed about `D²Ψ(k₀)[v, ·]`. The curve is data, as in
   `IsA5Point`. The spanning condition `v₁w₂ − v₂w₁ ≠ 0` restricts nothing: it follows from the other hypotheses
   (sanity theorem `span_of_hyps`, finding K-1 of the sanity agent). It is kept in the frozen text for readability.
5. **K2-MA's constant.** C is the improper integral as a symmetric limit; `∫_ℝ e^{iσx^m} dx` is not a Lebesgue
   integral. Its closed form `(2/m)Γ(1/m) e^{iσπ/(2m)}` (m even) or `(2/m)Γ(1/m) cos(π/(2m))` (m odd) is not stated.
6. **K2-F's form.** It is stated without a supremum: a bound B on every lattice coefficient gives `D B`. The
   localised integral may have any real velocity p; the cutoff's support must stay away from the box's boundary.
7. **Not stated:**
   - the convolution or ℓ¹ → ℓ^∞ operator form of K2-U and K2-D;
   - negative times;
   - uniformity over compact sets of α;
   - the product normal form and the parametric Taylor remainder (parts of the proof, not statements).

Clarifications after the blind pre-proof reviews (2026-11-28; `review/2026-11-28-K2-preproof-answers.md`). The
statement file is unchanged.
K2-a. "Every real time" in the "Why" paragraph means every real `t ≥ 1` in K2-U and every real `t ≥ T_α` in K2-D;
   negative times are not stated (modelling choice 7). The sanity layer's docstring says that the plants are not in
   the repository; since the integration of 2026-11-28 they are, in `docs/replay/plants/2026-11-28-K2/` (the sanity
   file is stamped and is not edited).
K2-b. (2026-11-28, after the proofs; `review/2026-11-28-K2-post-proof-answers.md`.)
   - K2-L's reduced curve is on `|u| < ε` with `ε > 0` (the Lean hypothesis `0 < ε`; with ε ≤ 0 the curve condition
     would be empty).
   - "The closed ball of radius δ" is the ball of the max norm on ℝ × ℝ (a square), as in every local statement of the
     repository. Since δ is existential, this is at least as strong as a Euclidean reading.
   - Modelling choice 3 compares times only. T6L gives an explicit site `(n, n)` and an explicit limit constant at
     integer times; K2-D gives neither.
   - "The claim, if proved" in the "Why" paragraph: all six are now proved in Lean. The status is in `docs/STATUS.md`,
     with the replay pending.

## Batch SPL-N: the best constant of the quadratic-phase remainder to within 10⁻⁸ (session 17, 2026-11-28)

Order. As batch K2: the statements in `OscInt/Statements/StationaryLeadingSharp.lean`, sanity theorems with planted
controls, a challenge file (`Challenge/StationaryLeadingSharp.lean`) and a comparator (`comparator-SPLN.json`), frozen
and stamped before the blind pre-proof reviews. What differs from "statement first", said plainly:
- A proof on paper predates the freeze: an external research packet (received 2026-11-28, recorded in
  `review/2026-11-28-postK2-packet-answers.md`) with the analytic route and an exact rational certificate of 40 cells,
  which the lead re-ran and re-derived before writing the statements.
- A one-point Lean prototype predates the freeze: in session 15 a proof agent proved, in scratch and about the frozen
  definitions, `72197/100000 ≤ |κ(13/8)| ≤ 360987/500000` (`review/2026-11-26-session15-gates-answers.md`, section 4).
  It is not in the repository and is not used by this batch.
- In the same session the 40-cell certificate of an earlier audit was checked in Lean by `decide +kernel` (same
  record, section 3); that file is not in the repository either.

No Lean proof of these statements is in the repository history before the stamp of the answers to the blind reviews.
The batch was requested by the owner on 2026-11-28 (session 17, `docs/progress/2026-11-28-session17-log.md`).

Why. SPL-K bounds the remainder of the quadratic-phase leading term by `(7/8) ‖g‴‖₁ λ^{−3/2}`, and SPL-A shows that no
constant below `sup |κ|` can replace `7/8`. So the best constant of SPL-K is `sup_τ |κ(τ)|`. SPL-N locates it to within
`10⁻⁸`, which is `17.5 %` below `7/8`. It does not identify the supremum, its location or its attainment.

Notation as in batch SPL: `κ = splKernel`, `R(g, λ) = splRemainder g λ`, amplitudes `SplAmplitude`.

**SPL-NU (kernel cap).** For every real τ, `|κ(τ)| ≤ 360987/500000 = 0.721974`.

**SPL-NL (kernel lower point).** `|κ(8123/5000)| > 72197399/10⁸ = 0.72197399`.

**SPL-NK (sharp remainder).** For every amplitude `(g, g₁, g₂, g₃)` of class `SplAmplitude` and every `λ > 0`,
`|R(g, λ)| ≤ (360987/500000) ‖g₃‖₁ λ^{−3/2}`.

**SPL-NC (no smaller constant).** For every real `c ≤ 72197399/10⁸` there are an amplitude of class `SplAmplitude`
and `λ > 0` with `|R(g, λ)| > c ‖g₃‖₁ λ^{−3/2}`.

What the statements say and do not say (modelling choices and omissions, for the reviewer).
1. **Two rationals, not the supremum.** SPL-NK and SPL-NC together put the best constant of SPL-K in
   `(0.72197399, 0.721974]`. The point `8123/5000` was chosen by an earlier floating-point search; nothing says the
   supremum is attained there or anywhere, nor that it is attained once.
2. **SPL-NC's form.** It negates the universal bound for each `c` up to the lower rational; it does not exhibit the
   amplitude in the statement. Its proof is expected to go through SPL-A and SPL-NL.
3. **SPL-NK** has exactly the shape of SPL-K (same hypotheses, same norm, same power of λ); only the constant differs.
   SPL-K is not edited.
4. **Negative τ** is covered in SPL-NU because κ is odd by definition.
5. **Not stated:** the value of `sup |κ|` to more digits; any bound for the remainder in terms of other norms.

## Batch A5U: decay uniform across an exceptional coupling of the triangular lattice (session 17, 2026-11-28)

Order. As batch K2: the statement in `OscInt/Statements/TriangularCrossover.lean`, sanity theorems with planted
controls, a challenge file (`Challenge/TriangularCrossover.lean`) and a comparator (`comparator-A5U.json`), frozen and
stamped before the blind pre-proof reviews. A proof route on paper predates the freeze: the external research packet
of 2026-11-28 (`review/2026-11-28-postK2-packet-answers.md`). No Lean proof of this statement is in the repository
history before the stamp of the answers to the blind reviews. Requested by the owner on 2026-11-28 (session 17).

Why. K2-U gives `|triKernel α t n| ≤ C_α t^{−triRate α}` with `C_α` depending on α in an unknown way. At the
exceptional couplings `a₀ = ±a*`, `a* = 1/(2√2)`, the rate jumps from `3/4` to `2/3`, so `C_α` must blow up as
`α → a₀`. A5U says how: with one constant for a whole window around `a₀`,
`|triKernel α t n| ≤ C t^{−2/3} E(|α − a₀| t^{1/3})`, `E(s) = min(1, s^{−1/4})`; equivalently
`C min(t^{−2/3}, |α − a₀|^{−1/4} t^{−3/4})`. The crossover time is `t ≈ |α − a₀|^{−3}`.

Notation as in batch K2, and `crossEnvelope s = 1` for `s ≤ 1`, `s^{−1/4}` for `s > 1`.

**A5U (uniform upper bound across a₀).** For each `a₀` with `|a₀| = a*` there are `r > 0` and `C` such that for every
real α with `|α − a₀| ≤ r`, every real `t ≥ 1` and every `n ∈ ℤ²`,
`|triKernel α t n| ≤ C t^{−2/3} crossEnvelope(|α − a₀| t^{1/3})`.

What the statement says and does not say (modelling choices and omissions, for the reviewer).
1. **Quantifiers.** `r` and `C` depend on `a₀` only, and are chosen before α, t and n. Applying K2-U at each α does
   not give this: its constant depends on α.
2. **Window.** Only a window around each exceptional coupling; nothing near `α = 0` (where the rate is also `2/3`,
   a D4 transition) and no global-in-α statement. The window must exclude 0: at `α = 0` K2-D forces rate `2/3`.
3. **Consistency with K2.** At `α = a₀` the bound is K2-U's `t^{−2/3}`. For fixed `α ≠ a₀` in the window and large
   t it is `t^{−3/4}`, K2-U's rate there, which K2-D shows cannot be improved. With the scaling variable
   `|α − a₀| t^{1/3}`, the exponent `−1/4` of the envelope is therefore the strongest one compatible with both ends
   (weaker envelopes, such as the exponent `−1/5` or the variable `|α − a₀| t^{1/4}`, follow from it); the sanity
   layer checks the two ends.
4. **Not stated:** a lower bound uniform in α (the lower crossover); explicit `r` or `C`; the canonical one-variable
   A5 unfolding estimate (part of the route, not a statement).

## Batch LOC2: torus Fourier localisation for C² cutoffs with an explicit constant (session 17, 2026-11-28)

Order. As batch K2: the statement in `OscInt/Statements/TorusLocalizationC2.lean`, sanity theorems with planted
controls, a challenge file (`Challenge/TorusLocalizationC2.lean`) and a comparator (`comparator-LOC2.json`), frozen
and stamped before the blind pre-proof reviews. A proof on paper predates the freeze: the external research packet of
2026-11-28 (`review/2026-11-28-postK2-packet-answers.md`). No Lean proof of this statement is in the repository
history before the stamp of the answers to the blind reviews. Requested by the owner on 2026-11-28 (session 17).

Why. K2-F turns bounds on lattice coefficients into a bound on a localised integral, for a smooth cutoff and with an
existential constant. K2-FQ does the same for a `C²` cutoff, with an explicit constant built from four `L²` norms of
the cutoff. The constant is independent of the phase, of t and of the velocity p.

Notation as in batch K2 (`torusBox = [−π, π]²`, `lin p k = p·k`), and: `boxL2 f = ((2π)^{−2} ∫_{[−π,π]²} |f|²)^{1/2}`;
`∂₁χ(k) = Dχ(k)(1, 0)`, `∂₂χ(k) = Dχ(k)(0, 1)`; `Δχ(k) = D²χ(k)[(1,0),(1,0)] + D²χ(k)[(0,1),(0,1)]`;
`locConstC2 χ = 4 ((3/2) boxL2 χ + boxL2 ∂₁χ + boxL2 ∂₂χ + boxL2 Δχ)`.

**K2-FQ (C² localisation, explicit constant).** Let `χ : ℝ² → ℂ` be `C²` with support inside the open box `(−π, π)²`.
For every continuous Ψ that is 2π-periodic in each variable, every real t, every `p ∈ ℝ²` and every real B: if
`|∫_{[−π, π]²} e^{i(tΨ(k) + n·k)} dk| ≤ B` for every `n ∈ ℤ²`, then
`|∫_{[−π, π]²} χ(k) e^{it(Ψ(k) + p·k)} dk| ≤ locConstC2 χ · B`.

What the statement says and does not say (modelling choices and omissions, for the reviewer).
1. **Regularity.** `C²` on all of ℝ² (Mathlib's `ContDiff ℝ 2`), support (closure of the nonzero set) inside the
   open box. Without the support condition the statement is false even for `χ = 1`: plant F-a of batch K2, refuted
   by a compiled witness (`docs/replay/plants/2026-11-28-K2-F-a-witness/README.md`).
2. **The constant.** Normalised `L²` norms over the box; the factor 4 dominates `√13`, the bound on
   `(Σ_n (1 + |n|²)^{−2})^{1/2}` the route uses. Not optimal.
3. **Relation to K2-F.** K2-FQ implies K2-F (a smooth χ is C²) with an explicit D; K2-F is not edited.
4. **Not stated:** `H²` or zero-trace variants; higher dimensions; optimality.
