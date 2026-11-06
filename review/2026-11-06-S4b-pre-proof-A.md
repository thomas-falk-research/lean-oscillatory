<!-- Blind pre-proof review of S4.1', S4.2, S4.3, S4.4, referee A (fresh-context agent, prompt review/prompts/S4b-pre-proof.md), commit ad8e7fd. Verbatim final report. -->

`ad8e7fd18e2c2bbbb8e06008664e0825234f0950`

# Referee A: blind pre-proof review of S4.1′, S4.2, S4.3, S4.4

I found no BLOCKER or MAJOR issues. All four statements are true, non-vacuous and faithful to `docs/statements.md`. Against the brief, they are stronger in a controlled way: the widening to Disc ≠ 0, and c_C > 0 in place of c_C ≠ 0.

## What I did
- Read every file the brief allows, and nothing else. I wrote nothing in the repository.
- Compiled one scratch file, `/tmp/refA/Check.lean`, with `nice -n 10 lake env lean` (a single process). It:
  - prints the elaborated statements with `pp.numericTypes`;
  - checks the junk value `d4Constant (0,0,0,0) = 0` and `Real.zero_rpow`;
  - checks `D4BoundNeStatement → D4BoundStatement`.
  It compiled cleanly. The sanity file uses only the standard axioms `[propext, Classical.choice, Quot.sound]`.
- Wrote my own quadrature, `/tmp/refA/j.py`. It uses J = 2∫_ℝ |a + bt + ct² + dt³|^{-2/3} dt (from t = tan θ) with cube-root substitutions at the roots. For x³+y³, y³−3x²y, one generic Disc<0 cubic and one generic Disc>0 cubic, I·J/3 matches the S4.4 closed forms to about 1e-6, which is my truncation error. Two other generic Disc>0 cubics returned `inf` because of a quadrature defect in my script, so they were not checked independently.
- Ran `numerics/target/release/d4const`: RESULT PASS.
  - I matches Γ(2/3)/2 to 5.6e-15.
  - The alternating-series pattern holds (a₀+a₁ = 0.0901 > 0, |aₖ| decreasing for k ≤ 60).
  - Eight cubics, four of each sign, match the closed forms to about 7e-15.
  - The 2D limit trend agrees.

## Verdicts

| Statement | vs `docs/statements.md` | vs brief | True? |
|---|---|---|---|
| `D4BoundNeStatement` (S4.1′) | FAITHFUL | FAITHFUL-STRONGER (Disc ≠ 0 instead of < 0) | TRUE |
| `D4LimitStatement` (S4.2) | FAITHFUL | FAITHFUL-STRONGER (Disc ≠ 0); the brief's limit with its constant is S4.2 ∧ S4.4 | TRUE |
| `D4ConstantPosStatement` (S4.3) | FAITHFUL | FAITHFUL-STRONGER (c_C > 0, not just ≠ 0; I converges and I > 0) | TRUE |
| `D4ConstantClosedFormStatement` (S4.4) | FAITHFUL | FAITHFUL (the Disc<0 clause is the brief's formula; the Disc>0 clause is new and correct) | TRUE |

**S4.1′ is true.** It is the classical uniform t^{-2/3} bound for both umbilics. Uniformity in y ∈ ℝ² works because:
- for |y|/t small, tφ + y·κ is a small linear deformation of a D4 point, whose nearby singularities are A1, A2 and A3, all decaying faster than t^{-2/3};
- for large |y|/t, the phase is non-stationary.

The Lean check confirms S4.1′ ⇒ S4.1, so the widening has content, and `sanity_D4Limit_hyps_elliptic` shows Disc = 108 is admitted.

**S4.2 is true.** Proof sketch:
1. Split A = A(0)χ + B, where B ∈ C² and B(0) = 0.
2. Decompose B dyadically into annuli |z| ~ 2^{-j}, rescale by 2^{-j}, and apply non-stationary phase with N = 1 on each annulus. This uses ∇C ≠ 0 away from 0, which follows from Disc ≠ 0. The bound is Σ_j 2^{-3j} M min(1, 2^{3j}/t) = O(M log t / t) = o(t^{-2/3}). A C² amplitude is more than enough.
3. The A(0)χ term goes to c_C A(0) by the same dyadic or rescaling argument applied to φ = C + O(|z|⁴).
4. δ depends only on φ, and the ∃δ ∀A M order is correct.

## The constant (question 2)
- **Polar derivation is correct.** With u = |s| r³, r dr = (1/3)|s|^{-2/3} u^{-1/3} du, which gives the factor 1/3 and the exponents −1/3 and −2/3. Since C(−ω) = −C(ω) and |C| is even, the term ±i∫ sin u · u^{-1/3} du, weighted by |C(ω)|^{-2/3} sgn C(ω), integrates to 0 over θ. So c_C = I·J/3 is real.
- **The sign convention does not matter.** The real part is even in the sign of i, so `exp(Q*I)` versus `e^{-iQ}` gives the same c_C.
- **Closed forms are correct.**
  - I = Γ(2/3)cos(π/3) = Γ(2/3)/2.
  - The constant is invariant under C ↦ λ·C∘L, because Disc scales by λ⁴ det(L)⁶ while c scales by |λ|^{-2/3}|det L|^{-1}.
  - Disc < 0 has one real root, with normal form x³+y³ and Disc = −27. Then √3·27^{1/6} = 3 and c = Γ(1/3)²/3 = 2.39224.
  - Disc > 0 has three real roots, with normal form x³−3xy² = cos 3θ in polar form. Then J = 2√πΓ(1/6)/Γ(2/3) and c = √πΓ(1/6)/3. Duplication and reflection give Γ(1/3)²/(2^{1/3}3^{1/2}) = Γ(1/3)²/108^{1/6}. The signs and the √3 are right.
  - Applying the brief's formula to Disc > 0 would be off by a factor √3. The statement correctly does not do that.
- **No junk values.**
  - `limUnder` gives a junk value only if the limit fails. It does not fail, and S4.3 asserts `Tendsto`. S4.4 cannot be proved through a junk value, because the limit's value is then unspecified.
  - `angularMoment` gives a junk value of 0 only when Disc = 0 (non-integrable, or q = 0). Every use is guarded by `disc ≠ 0` or a sign condition.
  - None of the four statements becomes trivially true or false.
- **S4.3 is Gamma-free as a statement.** It uses only `cos`, `rpow`, `Real.pi`, `intervalIntegral` and `limUnder`.

## Conventions and vacuity (question 3)
- `Real.rpow`:
  - u ∈ (0, R): positive base.
  - `0 ^ (-2/3) = 0` on a null set.
  - R < 0 (negative base) is irrelevant along `atTop`.
  - t > 0 eventually in the limit.
  - `|disc q|` and `disc q > 0` are positive.
- The numeric literals elaborate as reals: `Real.Gamma (2 / 3 : ℝ)` and `(1 / 6 : ℝ)`.
- `fderiv ℝ φ 0 = 0` is a genuine hypothesis for a C⁴ φ. Together with `φ 0 = 0` it is needed: without them the limit would be false or would pick up a factor e^{itφ(0)}.
- The quantifier order (∃ δ before ∀ A M) is right.
- An amplitude supported up to ∂B̄(0, δ) is harmless, since the prover chooses δ.
- The coercion `↑(t ^ (2/3 : ℝ)) : ℂ` is a real rpow cast to ℂ, not `cpow`.
- `oscInt2` is integrable, because A is continuous with compact support.

## Encoding (question 4)
- Defining c_C by the Gamma-free formula faithfully encodes the brief. It is the only choice under which "c_C ≠ 0 by alternating series, not Gamma" has content. S4.2 ∧ S4.4 recovers the brief's limit with its closed-form constant exactly when Disc < 0.
- Widening to Disc ≠ 0 is consistent with the brief: "isolated critical point" is equivalent to Disc ≠ 0 for a binary cubic, and the brief's "negative discriminant" served only its closed form. S4.1 is kept unchanged.

## Findings

**MINOR 1 (claim scope).** `D4LimitStatement` alone is not the brief's S4 limit. The brief's limit, "t^{2/3}∫ → c_C A(0) with c_C = Γ(1/3)²/(√3|Disc C|^{1/6})", is `D4LimitStatement ∧ D4ConstantClosedFormStatement`, and the constant clause is `∀ q, disc q < 0 → d4Constant q = Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * |disc q| ^ ((1 : ℝ) / 6))`. Any status line or citation must name both. A combined corollary statement would make the citation a single object.

**MINOR 2 (proof constraint not enforceable by the statement).** The brief says "do not rely on Mellin/Gamma identities", and `docs/statements.md` S4.3 says "checked mechanically once proved". This is a constraint on the proof, not on the statement. The mechanical criterion should be fixed before any proof exists, for example: no `Real.Gamma`, `Complex.Gamma`, `Real.Beta`/`Complex.betaIntegral` or `mellin` constants in the transitive dependencies of the S4.3 proof term, apart from those Mathlib's own basic API needs.

**NIT 3.** The header of `D4Limit.lean` says `angularMoment q` is "finite iff `C` has only simple real linear factors, i.e. `disc q ≠ 0`". In Lean, `angularMoment 0 = 0` (checked) even though disc 0 = 0, and for a non-integrable integrand the interval integral is also 0, so it is always finite. Suggested wording: "the integrand is integrable iff disc q ≠ 0; otherwise the Lean value is the junk 0".

**NIT 4.** `D4ConstantClosedFormStatement` read alone does not assert that the improper integral converges. Its first conjunct is about the `limUnder` value, so "I = Γ(2/3)/2" in the improper-integral sense needs S4.3's first conjunct as well. A docstring remark would help.

**NIT 5.** There is no sanity witness for S4.2 with A(0) ≠ 0 supported in an arbitrary B̄(0, δ). `sanity_ampBound_exists` covers radius 1 only. It is mathematically obvious by rescaling, but it is the witness that makes the S4.2 conclusion non-trivial for whatever δ the prover picks.
