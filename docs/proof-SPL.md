<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route for batch SPL (SPL-I, SPL-S, SPL-K, SPL-A; SPL-N as a plan)

Written by the lead on 2026-11-19, before any statement of the batch is frozen and before any Lean text of the batch
exists. History, disclosed: the first version (commit 567bfb8) was read by a plan referee from a fresh context on
2026-11-19 (`review/2026-11-19-SPL-plan-referee-answers.md`: no FATAL finding; one MAJOR against the plan for SPL-N;
MINOR and NIT findings against constants and wording). This is the second version, which applies those findings; in
this form it has not been refereed again. Status: a proof on paper, not machine-checked, not a proof record.

Nothing is claimed as new. The identity (T2) below is the two-sided case `ρ = 2, μ = 1, N = 3` of the remainder
representation of A. Erdélyi (*Asymptotic Expansions*, 1956, section 2.8; read by the lead only in the reproduction
of Ali Mehmeti and Dewez, arXiv:1412.5789, Theorem 1.3), with the term in `g″(0)` folded into the kernel
(`docs/prior_art.md`, gate of 2026-11-19).

## 0. Notation and the class of amplitudes

`e(u) := e^{iu²/2}`. `F(x) := ∫₀ˣ e(v) dv` for real `x`; `F` is odd and `F′ = e`.

`𝒢` is the set of `g : ℝ → ℂ` of class C³ with `g, g′, g″, g‴` integrable on ℝ.

(A) If `f` is C¹ and `f, f′` are integrable, then `f(x) → 0` as `x → ±∞`. Hence for `g ∈ 𝒢`: `g, g′, g″` tend to 0 at
`±∞`. (Mathlib has this at the pin: `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` and its `Iic`
twin; signatures to be read before a blueprint is written.)

## 1. The Fresnel primitive

**Lemma 1.** For `0 < x ≤ y`: `|F(y) − F(x)| ≤ 2/x`. Hence `L := lim_{x→∞} F(x)` exists, `|F(x) − L| ≤ 2/x` for
`x > 0`, `|F(x)| ≤ 3` for all real `x`, and `|L| ≤ 3`.

*Proof.* `e(v) = (e(v)/(iv))′ + e(v)/(iv²)` for `v > 0`, so
`F(y) − F(x) = e(y)/(iy) − e(x)/(ix) + ∫ₓʸ e(v)/(iv²) dv`, of modulus at most `1/y + 1/x + (1/x − 1/y) = 2/x`.
Cauchy's criterion gives `L`; let `y → ∞`. For `0 ≤ x ≤ 1`, `|F(x)| ≤ 1`; for `x ≥ 1`, `|F(x)| ≤ |F(1)| + 2 ≤ 3`;
`F` is odd. ∎

**Lemma 1′.** For `τ > 0` put `J(τ) := ∫_τ^∞ e(v) v^{−2} dv` and `K(τ) := ∫_τ^∞ e(v) v^{−4} dv` (absolutely
convergent). Then `|J| ≤ 1/τ`, `|J| ≤ 2/τ³`, `|K| ≤ 2/τ⁵`, and

    L − F(τ) = i e(τ)/τ − i J(τ),        J(τ) = i e(τ)/τ³ − 3i K(τ).

*Proof.* `|J| ≤ ∫_τ^∞ v^{−2}`. The rest is the integration by parts of Lemma 1 with `e v^{−2} = (e/(iv³))′ + 3e/(iv⁴)`
and `e v^{−4} = (e/(iv⁵))′ + 5e/(iv⁶)`. ∎

## 2. The kernel and its primitives

For every real `u` put

    E₁(u) := F(u) − L,    E₂(u) := u (F(u) − L) + i e(u),    κ₊(u) := F(u)/2 + u e(u)/2 + (iu²/2)(L − F(u)).

The kernel is `κ(u) := κ₊(u)` for `u ≥ 0` and `κ(u) := −κ₊(−u)` for `u < 0` (odd; in one formula,
`κ(u) = F(u)/2 + u e(u)/2 + (iu²/2)(sgn(u) L − F(u))`).

**Lemma 2.** On all of ℝ: `E₁′ = e`, `E₂′ = E₁`, `(iκ₊)′ = E₂`. Values at 0: `E₁(0) = −L`, `E₂(0) = i`, `κ₊(0) = 0`.
On `[0, ∞)`: `|E₁| ≤ 6`, `|E₂| ≤ 3`, and

    κ₊′(u) = u J(u) (u > 0),    |κ₊′| ≤ 1,    |κ₊(u)| ≤ u,    κ₊(u) − L/2 = i J(u)/2 − (3iu²/2) K(u),    |κ₊(u) − L/2| ≤ 4/u³,

so `|κ| ≤ 2` on ℝ, κ is 1-Lipschitz on ℝ, and `κ(u) → L/2` as `u → +∞`.

*Proof.* `(u(F − L))′ = F − L + u e` and `(i e)′ = −u e` give `E₂′ = E₁`.
`κ₊′ = e/2 + e/2 + (iu²/2) e + iu (L − F) − (iu²/2) e = e + iu (L − F)`, so `iκ₊′ = i e + u (F − L) = E₂`. By Lemma 1′,
`iu (L − F) = −e + u J`, so `κ₊′ = u J`, of modulus at most 1 for `u > 0`; `κ₊′(0) = e(0) = 1`. With `κ₊(0) = 0`:
`|κ₊(u)| ≤ u`. Again by Lemma 1′, `F − L = −i e/u + iJ` and `(u²/2) J = i e/(2u) − (3iu²/2) K`, so in
`κ₊ − L/2 = (F − L)/2 + u e/2 + (iu²/2)(L − F)` the terms in `e/u` and in `u e` cancel, leaving
`iJ/2 − (3iu²/2) K`, of modulus at most `1/u³ + 3/u³`. For `u ≤ 2`, `|κ₊| ≤ 2`; for `u ≥ 2`,
`|κ₊| ≤ |L|/2 + 1/2 ≤ 2`. κ is continuous at 0 with one-sided derivatives both equal to 1, and odd, so it is
1-Lipschitz on ℝ. `|E₂| ≤ 2 + 1` by Lemma 1. ∎

**Lemma 2′ (an integral form, used only for the constant 7/8).** For `τ > 0`,
`κ(τ) = τ² ∫_τ^∞ F(x) x^{−3} dx`, hence `|κ(τ)| ≤ sup |F| / 2`.
*Proof.* `(−F/(2x²) − e/(2x) + (i/2) F)′ = F/x³`; the bracket tends to `(i/2) L` at infinity. ∎

## 3. The identity

**Proposition 3 (half-line).** For `g ∈ 𝒢`: `∫₀^∞ g e = L g(0) + i g′(0) − i ∫₀^∞ g‴ κ`.

*Proof.* On `[0, T]`, three integrations by parts with the primitives of Lemma 2:

    ∫₀ᵀ g e = [g E₁ − g′ E₂ + g″ (iκ₊)]₀ᵀ − ∫₀ᵀ g‴ (iκ₊).

As `T → ∞` the terms at `T` vanish by (A), because the three primitives are bounded on `[0, ∞)`; the integrals
converge because `g` and `g‴` are integrable and κ is bounded. The bracket at 0 is `−L g(0) − i g′(0) + 0`. ∎

**Proposition 3′ (the line).** For `g ∈ 𝒢`: `∫_ℝ g e = 2L g(0) − i ∫_ℝ g‴ κ`.

*Proof.* Apply Proposition 3 to `g` and to `ǧ(u) := g(−u)` (in `𝒢`; `ǧ(0) = g(0)`, `ǧ′(0) = −g′(0)`,
`ǧ‴(t) = −g‴(−t)`; `e` is even): `∫_{−∞}⁰ g e = ∫₀^∞ ǧ e = L g(0) − i g′(0) + i ∫₀^∞ g‴(−t) κ(t) dt`, and
`∫₀^∞ g‴(−t) κ(t) dt = −∫_{−∞}⁰ g‴(s) κ(s) ds` because κ is odd. Add. ∎

**Corollary 3″ (scaling).** For `g ∈ 𝒢`, `λ > 0`:
`∫ g(u) e^{iλu²/2} du = 2L g(0) λ^{−1/2} − i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt` (apply 3′ to `v ↦ g(v/√λ)`).

## 4. The value of L; SPL-I and SPL-S

**Lemma 4.** `2L = √(2π) e^{iπ/4}`, that is `L = √π (1 + i)/2`.

*Proof.* `γ(u) := e^{−u²/2}` is in `𝒢`, and `∫ γ(u) e^{iλu²/2} du = (2π/(1 − iλ))^{1/2}` (principal branch; Mathlib
`integral_gaussian_complex` with `b = (1 − iλ)/2`, `Re b = 1/2`). By Corollary 3″ and `|κ| ≤ 2`,
`|(2π/(1 − iλ))^{1/2} − 2L λ^{−1/2}| ≤ 2 ‖γ‴‖₁ λ^{−3/2}`. Multiply by `√λ` and let `λ → ∞`:
`(2πλ/(1 − iλ))^{1/2} → (2πi)^{1/2} = √(2π) e^{iπ/4}` (`2πλ/(1 − iλ) = 2πλ(1 + iλ)/(1 + λ²) → 2πi`, off the cut of
the principal square root). The argument is not circular: Proposition 3 uses `L` only as the limit of `F`. ∎

So the leading term `g(0) √(2π/λ) e^{iπ/4}` is `2L g(0) λ^{−1/2}`, and Corollary 3″ is

    R(g, λ) = −i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt        (T2; statement SPL-I).

**Theorem (SPL-S).** For `g ∈ 𝒢`, `λ > 0` there is `τ ≥ 0` with `|R(g, λ)| ≤ |κ(τ)| ‖g‴‖₁ λ^{−3/2}`.

*Proof.* If `‖g‴‖₁ = 0` then `R = 0` by (T2). Otherwise `ν := |g‴(t)| dt / ‖g‴‖₁` is a probability measure and
`f(t) := |κ(√λ t)|` is bounded and continuous; some `t₀` has `f(t₀) ≥ ∫ f dν` (else `f < ∫ f dν` everywhere and
integrating gives a contradiction; Mathlib's first-moment lemma). With `τ := √λ |t₀|` (`|κ|` is even),
`|R| λ^{3/2} ≤ ‖g‴‖₁ ∫ f dν ≤ |κ(τ)| ‖g‴‖₁`. ∎

No supremum and no numerical fact is used.

## 5. The constants

**SPL-K with 7/8 (from theorems the library has).** For `c ≥ 0`, VC2-S (`OscInt.API.secondDerivSharp`) with
`f(x) = x²/2`, `f′(x) = x`, `a = −c`, `b = c`, `λ = 1` gives `w ∈ [0, π]` with `|∫_{−c}^{c} e| ≤ A(w)/√1`, and VC2-N
(`OscInt.API.vdc2ProfileBound`) gives `A(w) ≤ 7/2`. Hypotheses to discharge, as the plan referee listed them from
the frozen text: `−c ≤ c`; `0 < 1`; `HasDerivOn` for `x²/2` on `[−c, c]`; `DerivIncreasesAtRate` for `x ↦ x` with
rate 1 (an equality); `√1 = 1`; `∫_{−c}^{c} e = 2F(c)` by evenness; oddness of `F` for `c < 0`. So `|F| ≤ 7/4` on ℝ,
and by Lemma 2′ `|κ| ≤ 7/8`: with SPL-S, `|R(g, λ)| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}`. (The true values: `sup |F| = 1.68216`,
half of it 0.84108; EXPLORED, by the referee and by the lead.)

**SPL-N (a plan, not a proof; not to be frozen before a prototype).** Numerically `max |κ| = 0.7219740` at
`τ = 1.62460`. By Lemma 2: `|κ(τ)| ≤ τ`, so nothing is needed on `[0, 0.73]`; `|κ(τ)| ≤ |L|/2 + 4/τ³`, so
`|κ| ≤ 73/100` for `τ ≥ 3.39` (`|L|/2 = 0.62666`; the threshold is 3.3827, computed by the lead; the referee's
report has 3.38, at which the bound is 0.73025); and κ is 1-Lipschitz, so on `[0.73, 3.39]` a finite set of
certified enclosures of `κ(τⱼ)` with radii matched to the local margin suffices. The plan referee's estimate
(floating point, not a tested cost): about 40 points for 73/100, about 19 for 3/4, each needing a Taylor
enclosure of `F` of degree about 41 with a rigorous remainder and an enclosure of `√π`. The library has no such
component (VC2-N uses one-sided polynomial bounds of the sine to degree 9 for a real profile). Decision: SPL-N is
not part of the first freeze of this batch; it becomes its own statement, with the rational chosen (73/100 or 3/4)
after a prototype of one certified enclosure of `F` at one point compiles.

## 6. SPL-A

**Theorem (SPL-A).** For `τ ≥ 0`, `ε > 0` there is a smooth compactly supported `g`, not identically 0, with
`|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g‴‖₁`.

*Proof.* If `τ = 0` any such `g` serves (`κ(0) = 0`). Let `τ > 0`, `T := max(8τ/ε, 2τ)`, `w := min(τ/2, ε/2)`, and
let `ψ ≥ 0` be smooth, even, of integral 1, supported in `[−w, w]`. Put

    m(t) := ½[ψ(t − τ) − ψ(t + τ)] − (τ/2T)[ψ(t − T) − ψ(t + T)],        g(x) := ∫_{−∞}^x ((x − t)²/2) m(t) dt.

`m` is smooth, odd and supported in `[−T − w, T + w]`; `g` is smooth with `g‴ = m`, and `g(x) = 0` for
`x < −T − w`. The moments of `m` of order 0 and 2 vanish because `m` is odd, and
`∫ t m(t) dt = ½(τ + τ) − (τ/2T)(T + T) = 0`; so for `x > T + w`,
`g(x) = (x²/2) ∫ m − x ∫ t m + ½ ∫ t² m = 0`: `g` has compact support. The four bumps have disjoint interiors
(`2w ≤ τ ≤ T − τ`), so `‖g‴‖₁ = 1 + τ/T`; `g` is not identically 0 because `g‴` is not. Since κ is 1-Lipschitz,
`|∫ ψ(t − a) κ(t) dt − κ(a)| ≤ w` for every `a`, and κ is odd, so

    |∫ m κ − (κ(τ) − (τ/T) κ(T))| ≤ w (1 + τ/T).

By (T2) at `λ = 1`, `|R(g, 1)| = |∫ m κ| ≥ |κ(τ)| − 2τ/T − w(1 + τ/T)` (using `|κ(T)| ≤ 2`), hence

    |R(g, 1)| / ‖g‴‖₁ ≥ (|κ(τ)| − 2τ/T)/(1 + τ/T) − w ≥ |κ(τ)| − 4τ/T − w ≥ |κ(τ)| − ε. ∎

The amplitude of case G5 of the registered test is of this form with a cosine bump (`T = 400`, `w = 0.01`); its
measured ratio 0.71652 agrees to five places with `|κ(τ) − (τ/T) κ(T)| / (1 + τ/T) = 0.7165254` (computed by the lead
in mpmath on 2026-11-19; not a registered number). The plan referee ran the same construction with another
mollifier and other parameters and reports agreement with the prediction.

## 7. Remarks for the statements

- The class `𝒢`, not compact support, is the hypothesis to freeze: Lemma 4 needs the Gaussian, and consumers with
  Schwartz amplitudes would otherwise be excluded. Integrability of `g′` and `g″` is believed redundant given `g`
  and `g‴` (an L¹ inequality of Kolmogorov–Stein type, from the referee's memory, not checked); the modelling notes
  must say so.
- No `g ∈ 𝒢` other than those with `g‴ = 0` has `g‴` of one sign (`∫ g‴ = 0`); the bound is not vacuous on any
  sign class.
- As `λ → 0` the bound is true and weak: `R ≈ −2L g(0) λ^{−1/2}`, consistent with (T2) because
  `κ(τ) = τ + (iL/2) τ|τ| + O(τ³)` and `∫ g‴(t) t|t| dt = −4 g(0)`.

## 8. For the formalisation (not started)

Proposition 3 is three applications of integration by parts on `[0, T]` with `HasDerivAt` everywhere (the
primitives are differentiable on all of ℝ) and three limits; the left half-line comes from the reflection. No
improper integral of a non-integrable function appears, and the value of the Fresnel integral is obtained from the
complex Gaussian integral, not assumed (Mathlib has no Fresnel integral at the pin). Names reported at the pin by
the literature reader and the plan referee, to be re-checked by `#check` before any blueprint is frozen (lessons
1): `integral_gaussian_complex`; `intervalIntegral.integral_mul_deriv_eq_deriv_mul`;
`MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`; `MeasureTheory.exists_integral_le` (first moment).
