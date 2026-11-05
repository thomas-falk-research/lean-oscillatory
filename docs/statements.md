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
