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
