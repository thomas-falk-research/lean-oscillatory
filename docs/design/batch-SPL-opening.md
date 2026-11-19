<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL, opening note: the one-variable stationary-phase leading term with an explicit remainder

Status: design note, written 2026-11-19 (session 13) by the lead. Nothing here is a frozen statement; every statement
derived from it goes through the full procedure of `CONTRIBUTING.md`. Opened by owner decision
(`docs/decisions/2026-11-19-next-batch-spl.md`) on the branch `claude/batch-sp-leading-term`. The lead and every
prover and referee of this batch are from one model family.

Labels used below: PROVEN-ON-PAPER (derived here, not refereed, not machine-checked), EXPLORED (a number from an
exploratory run, not a registered test), CONJECTURED, CITED (read in the source named), NOT READ.

## 1. The question

The library proves upper bounds for oscillatory integrals. A consumer that needs an asymptotic formula needs more:
the leading term, and a bound on what is left that holds for every value of the large parameter and has a stated
constant. The open item "Asymptotic expansions" of `docs/ROADMAP.md` asks for this; `docs/design/leading-term.md`
drafts it in two variables with a constant that is not explicit. This batch takes the one-variable case and asks
for the constant.

Conventions. `λ > 0` is the large parameter. `g : ℝ → ℂ` is the amplitude, three times continuously differentiable,
with `g, g′, g″, g‴` integrable on ℝ (every compactly supported C³ function and every Schwartz function qualifies).
`‖g‴‖₁ = ∫ |g‴|`. The normal form of the phase is `u²/2`. The remainder is

    R(g, λ) := ∫_ℝ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}.

## 2. The statement aimed at (normal form)

With `F(x) := ∫₀ˣ e^{iv²/2} dv` (so `F(∞) = √π (1 + i)/2`) define for `τ ≥ 0`

    κ(τ) := F(τ)/2 + τ e^{iτ²/2}/2 + (iτ²/2) (F(∞) − F(τ)),      κ(−τ) := −κ(τ).

- **SPL-S (bound).** For every `g` as above and every `λ > 0` there is `τ ≥ 0` with
  `|R(g, λ)| ≤ |κ(τ)| · ‖g‴‖₁ · λ^{−3/2}`.
- **SPL-N (number).** `|κ(τ)| ≤ 73/100` for every `τ`.
- **SPL-K (consumer form).** `|R(g, λ)| ≤ (73/100) ‖g‴‖₁ λ^{−3/2}`.
- **SPL-A (attained).** For every `τ ≥ 0` and `ε > 0` there is a compactly supported smooth `g`, not identically
  zero, with `|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g‴‖₁`. With SPL-S this says that `K* := sup |κ|` is the best constant in
  `|R| ≤ K ‖g‴‖₁ λ^{−3/2}`.

The quantifier order of SPL-S ("there is τ", after `g` and `λ`) is the form batch VC2 used for a constant that is a
supremum of a profile; it avoids a real-number supremum in the statement.

Status of these four sentences on 2026-11-19: SPL-S and SPL-A are PROVEN-ON-PAPER in outline (section 3), not
refereed; SPL-N and the decimal of `K*` are EXPLORED (section 5). None is a theorem of the library.

## 3. Why it should be true (outline, PROVEN-ON-PAPER, not refereed)

Write `e(u) = e^{iλu²/2}` and `h(u) := (g(u) − g(0))/u = ∫₀¹ g′(su) ds`. Since `u e(u) = (e(u)/(iλ))′`, one
integration by parts gives `R = (i/λ) ∫ h′ e` (the boundary terms vanish because `h → 0` at infinity). With
`Fr(u) := ∫₀ᵘ e`, which is bounded, a second integration by parts gives `∫ h′ e = −∫ h″ Fr`. Now
`h″(u) = ∫₀¹ s² g‴(su) ds`, and exchanging the order of integration,

    R(g, λ) = −(i/λ) ∫_ℝ g‴(t) k(t) dt,      k(t) := ∫₀¹ s Fr(t/s) ds = λ^{−1/2} κ(√λ t),

where the closed form of κ in section 2 comes from `∫₀¹ s F(τ/s) ds = τ² ∫_τ^∞ F(x) x^{−3} dx` and two integrations
by parts. Hence `|R| ≤ λ^{−3/2} ‖g‴‖₁ sup |κ|`. The supremum is a maximum: κ is continuous, `κ(0) = 0`, and
`κ(τ) → F(∞)/2` as `τ → ∞` with `|F(∞)|/2 = √(2π)/4 = 0.6267` below the value 0.72 that κ takes near `τ = 1.62`.

For SPL-A take `g‴` close to `(δ_τ − δ_{−τ})/2 − (τ/T)(δ_T − δ_{−T})/2`: its moments of order 0, 1, 2 vanish, so `g`
is compactly supported (and even, with `g(0)` about `τ(T − τ)/4`); then, at `λ = 1`, `R = −i[κ(τ) − (τ/T) κ(T)]` up to
the mollification, and `‖g‴‖₁ = 1 + τ/T`. Let `T → ∞`.

Consistency with the classical expansion (CITED: Hörmander, ALPDO I, Theorem 7.7.5): the next term of the
expansion is `√(2π) e^{iπ/4} (i/2) g″(0) λ^{−3/2}`, of modulus `(√(2π)/2) |g″(0)| λ^{−3/2}`; since
`|g″(0)| ≤ ‖g‴‖₁/2`, the constant can never be below `√(2π)/4`, which is the limit of `|κ|` at infinity.

Points a referee should attack: the boundary terms and the exchange of integrals under the stated integrability
only; the closed form of κ and its odd extension; whether the maximum of `|κ|` is at the first local maximum;
whether "integrable derivatives" is the right class or compact support should be the frozen hypothesis.

## 4. Prior art (gate of 2026-11-19; log `numerics/results-spl-prior-art-search-2026-11-19.txt`)

Sixteen logged queries (arXiv, zbMATH Open, Crossref, MathOverflow; the MathOverflow queries returned nothing, which
the log shows and which may be a failure of the query form). Closest results found:

- F. W. J. Olver, *Error bounds for stationary phase approximations*, SIAM J. Math. Anal. 5 (1974) 19–29
  (zbMATH 0239.65028, doi:10.1137/0505003). Title and bibliographic data CITED from zbMATH and Crossref; the text is
  NOT READ (no open copy found). It must be read before any novelty wording is frozen.
- F. Ali Mehmeti and F. Dewez, arXiv:1412.5789, arXiv:1412.5792 and arXiv:1512.05940 (2014–2015), completing a
  theorem of A. Erdélyi (*Asymptotic Expansions*, 1956, section 2.8; NOT READ). CITED from the first and third
  preprints, read in part: one variable, stationary points of real order at the end points of the interval,
  amplitudes with integrable singularities, remainders with explicit constants. For a regular amplitude at a
  stationary point of order two their remainder after the first term is `O(ω^{−δ})` with `δ < 1` (their Theorems 1.7
  and 2.4). The integral is split at the stationary point, so each half has a term of order `ω^{−1}`; the
  two-sided remainder of order `ω^{−3/2}` with a constant is not stated there.
- Hörmander, ALPDO I, Theorem 7.7.5, and the texts cited in `docs/design/leading-term.md`: the expansion with a
  remainder constant that is not explicit.
- No formalisation of a stationary-phase leading term in a proof assistant was found (one arXiv query; Mathlib and
  the upstream repository of this library were not searched in this gate and must be before the freeze).

Wording that this gate supports: "we did not find the bound of SPL-S, with its kernel κ and the constant `sup |κ|`,
in the literature searched on 2026-11-19 (queries and hits in the log); the closest results are the three above".
It does not support "new": the identity of section 3 is two integrations by parts and may well be known, and
Olver's paper is unread.

## 5. Exploration (EXPLORED, 2026-11-19; `numerics/review/spl_explore_kappa.py`, output
`numerics/results-spl-explore-kappa-2026-11-19.txt`)

The closed form of κ and a direct quadrature of its definition agree to about 10⁻⁶ at five values of τ (the
quadrature is the less accurate of the two). On a grid of step 0.001 on (0, 30] the largest `|κ|` is at the first
local maximum, `τ* = 1.62460`, with `K* = 0.7219740` to seven places; the later local maxima decrease toward
0.6267. The crude bound from batch VC2 (half of `sup A/2`, 0.8411) is 16 % larger. These numbers steer the batch
and prove nothing; the registered test is `docs/prereg/2026-11-19-SPL-quadratic-remainder.md`.

## 6. Stages and stop gates

1. **Stage 1 (this batch): the normal form**, SPL-S, SPL-N, SPL-K, SPL-A. Order of work: registered numeric test;
   written proof (a file proof-SPL.md under docs/, not yet written) and a plan referee from a fresh context; statements in `docs/statements.md`
   and Lean, freeze and stamp; two blind referees; proofs. Stop gates:
   - the registered test fails on a case that is not a control: stop, find the error in section 3, re-register;
   - Olver (1974), once read, contains SPL-S with its constant: the batch continues as a formalisation of a
     classical result and every novelty sentence is withdrawn, as happened in batch VC2;
   - SPL-N needs a certified enclosure of a Fresnel-type function that the Lean development of batch VC2 cannot
     supply at reasonable cost: freeze SPL-N with a weaker rational (3/4 or 7/8, the second follows from VC2-N) and
     record the gap.
2. **Stage 2: a general phase.** For `φ` with `φ″ > 0` on an interval containing the support, the substitution
   `u = ±√(2(φ − φ(x₀)))` turns the integral into the normal form with `g = (a ∘ x) · x′`, and
   `‖g‴‖₁ = ∫ |(w (w (a w)′)′)′| dx` with the weight `w = dx/du = √(2(φ − φ(x₀)))/|φ′|`. Open design choice, for
   the plan referee: state the bound with that integral, or with a constant in sup norms of `φ‴ … φ⁽⁶⁾`, `1/φ″`
   and `a … a‴` (six derivatives of the phase are what the crude one-variable Morse lemma costs). The constants
   must show the blow-up as `φ″(x₀) → 0`: that is what uniformity toward a fold means.
3. **Stage 3: two stationary points that coalesce** (the Airy leading term, `docs/design/leading-term.md` section
   2 in one variable). Not started; no claim.

## 7. What this would and would not give the consumer that prompted it

The lemma "two-saddle steepest descent with a uniform remainder" of hexagon:2611.00174v1 (read in statement only)
has an analytic integrand containing a Hankel function, moves the contour, and bounds a relative remainder by
terms in `1/(c′ α)`, `1/(c′ α²)`, `1/(c′ α³)`, where `α` is the curvature of the phase at the stationary point. Stage 1
gives the core of such a lemma in real variables for a quadratic phase; stage 2 would give the dependence on `α`.
Neither gives the exponentially small terms that the contour produces, and neither has been checked against that
lemma's constants. No statement of this batch is a statement about that preprint.
