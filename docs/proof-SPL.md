<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route for batch SPL (SPL-S, SPL-K, SPL-N, SPL-A)

Written by the lead on 2026-11-19, before any statement of the batch is frozen and before any Lean text of the batch
exists. Status of this page: a proof on paper, to be read by a plan referee from a fresh context; not refereed, not
machine-checked, not a proof record. It replaces the outline of `docs/design/batch-SPL-opening.md` section 3 (which
used a quotient `h` and an exchange of integrals); the route here needs neither. Nothing is claimed as new
(`docs/prior_art.md`, gate of 2026-11-19; Olver 1974 is unread).

## 0. Notation and the class of amplitudes

`e(u) := e^{iu²/2}`. `F(x) := ∫₀ˣ e(v) dv` for real `x`; `F` is odd and `F′ = e`.

`𝒢` is the set of `g : ℝ → ℂ` of class C³ with `g, g′, g″, g‴` integrable on ℝ.

(A) If `f` is C¹ and `f, f′` are integrable, then `f(x) → 0` as `x → ±∞` (the limit exists because `f′` is
integrable and must be 0 because `f` is). Hence for `g ∈ 𝒢`: `g, g′, g″` tend to 0 at `±∞`.

## 1. The Fresnel primitive

**Lemma 1.** For `0 < x ≤ y`: `|F(y) − F(x)| ≤ 2/x`. Hence `L := lim_{x→∞} F(x)` exists, `|F(x) − L| ≤ 2/x` for
`x > 0`, and `|F(x)| ≤ 3` for all real `x`.

*Proof.* `e(v) = (e(v)/(iv))′ + e(v)/(iv²)` for `v > 0`, so
`F(y) − F(x) = e(y)/(iy) − e(x)/(ix) + ∫ₓʸ e(v)/(iv²) dv`, of modulus at most `1/y + 1/x + (1/x − 1/y) = 2/x`.
Cauchy's criterion gives `L`; let `y → ∞`. For `0 ≤ x ≤ 1`, `|F(x)| ≤ 1`; for `x ≥ 1`, `|F(x)| ≤ |F(1)| + 2 ≤ 3`;
`F` is odd. ∎

**Lemma 1′.** For `τ > 0`: `|∫_τ^∞ e(v) v^{−2} dv| ≤ 2/τ³` (same integration by parts, with `v^{−3}` and
`3v^{−4}`), and `L − F(τ) = i e(τ)/τ − i ∫_τ^∞ e(v) v^{−2} dv`.

## 2. The kernel and three bounded primitives

For `u ≥ 0` put

    E₁⁺(u) := F(u) − L,    E₂⁺(u) := u (F(u) − L) + i e(u),    κ(u) := F(u)/2 + u e(u)/2 + (iu²/2)(L − F(u)),

and for `u ≤ 0`: `E₁⁻(u) := F(u) + L`, `E₂⁻(u) := u (F(u) + L) + i e(u)`, `κ(u) := −κ(−u)`.

**Lemma 2.** On `[0, ∞)`: `(E₁⁺)′ = e`, `(E₂⁺)′ = E₁⁺`, `(iκ)′ = E₂⁺`; on `(−∞, 0]`: `(E₁⁻)′ = e`, `(E₂⁻)′ = E₁⁻`,
`(iκ)′ = E₂⁻`. All six functions are bounded on their half-lines: `|E₁^±| ≤ 6`, `|E₂^±| ≤ 3`, `|κ| ≤ 3/2`. Values at
0: `E₁⁺(0) = −L`, `E₁⁻(0) = L`, `E₂^±(0) = i`, `κ(0) = 0`. As `u → +∞`, `κ(u) → L/2`, with
`|κ(u) − L/2| ≤ 2/u`.

*Proof.* Derivatives, for `u > 0` (one-sided at 0): `(u(F − L))′ = F − L + u e` and `(i e)′ = −u e`; and
`κ′ = e/2 + e/2 + (iu²/2) e + iu (L − F) − (iu²/2) e = e + iu (L − F)`, so `iκ′ = i e + u (F − L) = E₂⁺`. On the left
half-line use that κ is odd, so κ′ is even: `iκ′(u) = i e(u) + (−u)(F(−u) − L) = i e(u) + u (F(u) + L)`.
Bounds: `|u (F(u) − L)| ≤ 2` by Lemma 1 for `u > 0`, so `|E₂⁺| ≤ 3`; `F(u) + L = −(F(−u) − L)` for `u < 0`.
For κ on `[0, ∞)`: by Lemma 1′, `(iu²/2)(L − F) = −u e/2 + (u²/2) ∫_u^∞ e v^{−2}`, hence
`κ(u) − L/2 = (F(u) − L)/2 + (u²/2) ∫_u^∞ e(v) v^{−2} dv`, of modulus at most `1/u + 1/u`. For `u ≤ 1` use the
definition: `|κ| ≤ 1/2 + 1/2 + (1/2)·6`; this crude bound is replaced in section 5. ∎

Remark (the kernel as an average). For `τ > 0`, `κ(τ) = ∫₀¹ s F(τ/s) ds`; in particular `|κ| ≤ sup |F| / 2`.
*Proof.* Both sides are `τ² ∫_τ^∞ F(x) x^{−3} dx`: the left by Lemma 2's primitive
`(−F/(2x²) − e/(2x) + (i/2) F)′ = F/x³`, the right by `x = τ/s`. This remark is used only for the constant 7/8 in
section 5; the route of sections 3 and 4 does not use it.

## 3. The identity

**Proposition 3.** For `g ∈ 𝒢`: `∫_ℝ g(u) e(u) du = 2L g(0) − i ∫_ℝ g‴(t) κ(t) dt`.

*Proof.* On `[0, T]`, three integrations by parts with the primitives of Lemma 2:

    ∫₀ᵀ g e = [g E₁⁺ − g′ E₂⁺ + g″ (iκ)]₀ᵀ − ∫₀ᵀ g‴ (iκ).

As `T → ∞` the terms at `T` vanish by (A), because the three primitives are bounded; the integrals converge
because `g` and `g‴` are integrable and κ is bounded. The terms at 0 give `−[g(0)(−L) − g′(0) i + 0]`. So
`∫₀^∞ g e = L g(0) + i g′(0) − i ∫₀^∞ g‴ κ`. In the same way on `[−T, 0]`:
`∫_{−∞}⁰ g e = [g E₁⁻ − g′ E₂⁻ + g″ (iκ)](0) − i ∫_{−∞}⁰ g‴ κ = L g(0) − i g′(0) − i ∫_{−∞}⁰ g‴ κ`. Add. ∎

**Corollary 3′ (scaling).** For `g ∈ 𝒢` and `λ > 0`:
`∫ g(u) e^{iλu²/2} du = 2L g(0) λ^{−1/2} − i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt` (apply Proposition 3 to `v ↦ g(v/√λ)`).

## 4. The value of L, and SPL-S

**Lemma 4.** `2L = √(2π) e^{iπ/4}`, that is `L = √π (1 + i)/2`.

*Proof.* `γ(u) := e^{−u²/2}` is in `𝒢`, and `∫ γ(u) e^{iλu²/2} du = (2π/(1 − iλ))^{1/2}` (principal branch; the complex
Gaussian integral, Mathlib `integral_gaussian_complex` with `b = (1 − iλ)/2`, name to be checked at the pin). By
Corollary 3′, `|(2π/(1 − iλ))^{1/2} − 2L λ^{−1/2}| ≤ (3/2) ‖γ‴‖₁ λ^{−3/2}`. Multiply by `√λ` and let `λ → ∞`:
`(2πλ/(1 − iλ))^{1/2} → (2π i)^{1/2} = √(2π) e^{iπ/4}` (the principal square root is continuous at `2πi`). ∎

So the constant `F(∞)` of the draft statements is `L`, the leading term `g(0) √(2π/λ) e^{iπ/4}` is `2L g(0) λ^{−1/2}`,
and Corollary 3′ reads

    R(g, λ) = −i λ^{−3/2} ∫ g‴(t) κ(√λ t) dt.                                                        (T2)

**Theorem (SPL-S).** For `g ∈ 𝒢`, `λ > 0` there is `τ ≥ 0` with `|R(g, λ)| ≤ |κ(τ)| ‖g‴‖₁ λ^{−3/2}`.

*Proof.* Put `M := sup_{τ ≥ 0} |κ(τ)|` (finite; `|κ|` is even). By (T2), `|R| λ^{3/2} ≤ ∫ |g‴(t)| |κ(√λ t)| dt ≤ M ‖g‴‖₁`.
If `‖g‴‖₁ = 0` then `R = 0` and any τ serves. Otherwise: if `M` is attained at some τ, take it. If not,
`|κ(√λ t)| < M` for every `t`, so the first inequality is strict, `|R| λ^{3/2}/‖g‴‖₁ < M`, and by the definition of a
supremum some τ has `|κ(τ)|` above that ratio. ∎

(No numerical fact is used. That `M` is attained, near 1.6246, is EXPLORED and VALIDATED numerically only.)

## 5. The constants: SPL-K with 7/8 from batch VC2; SPL-N with 73/100

**SPL-K with 7/8 (from theorems the library has).** By the remark of section 2, `|κ| ≤ sup |F|/2`. For `c > 0`,
`2 F(c) = ∫_{−c}^{c} e^{iu²/2} du`, an integral with phase `u²/2`, whose second derivative is 1. VC2-S
(`OscInt.API.secondDerivSharp`) bounds its modulus by the profile `A(w)` for some `w ∈ [0, π]`, and VC2-N
(`OscInt.API.vdc2ProfileBound`) gives `A ≤ 7/2`. So `|F| ≤ 7/4` and `|κ| ≤ 7/8`:
`|R(g, λ)| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}`. To be checked against the exact hypotheses of VC2-S before the freeze (it is
stated for a phase on an interval with a lower bound on the growth of `f′`).

**SPL-N with 73/100 (not available from the library).** Numerically `M = 0.7219740`. A proof needs: (i) the tail,
`|κ(τ) − L/2| ≤ 3/(2τ) + 1/τ³` (Lemma 1′ used with its sharper form `|L − F(τ)| ≤ 1/τ + 2/τ³`), so `|κ| ≤ 0.73` for
`τ ≥ 14.6`; (ii) on `[0, 14.6]`, a certified enclosure of κ on a grid, with `|κ′| = |e + iτ(L − F)| ≤ 1 + 2/τ² + 1`
bounding the variation between grid points; the margin is 0.008 at the maximum and 0.087 at the second local
maximum. Step (ii) is a computer-assisted proof whose cost in Lean is not known. Stop gate
(`docs/design/batch-SPL-opening.md` section 6): if it is not affordable, SPL-N is not frozen, or is frozen with a
rational that the available enclosures reach, and the gap between 7/8 and 0.7220 is recorded as open.

## 6. SPL-A

**Theorem (SPL-A).** For `τ ≥ 0`, `ε > 0` there is a smooth compactly supported `g`, not identically 0, with
`|R(g, 1)| ≥ (|κ(τ)| − ε) ‖g‴‖₁`.

*Proof.* If `τ = 0` any such `g` serves (`κ(0) = 0`). Let `τ > 0` and `T > τ`. Put `c := 1/2 − τ/(2T) > 0` and let
`s` be the even step function equal to `c` on `|t| < τ`, to `c − 1/2 = −τ/(2T)` on `τ < |t| < T`, and to 0 on
`|t| > T`. Then:

- `∫ s = 2τc − 2(T − τ) τ/(2T) = 0`, so `S₁(t) := ∫_{−∞}^t s` is supported in `[−T, T]`; it is odd, so `∫ S₁ = 0` and
  `S₂(t) := ∫_{−∞}^t S₁` is supported in `[−T, T]`, even, C¹ and piecewise quadratic;
- the distributional derivative of `s` is `−μ` with `μ := ½(δ_τ − δ_{−τ}) − (τ/2T)(δ_T − δ_{−T})`, a measure of
  total mass `1 + τ/T`.

For a smooth even mollifier `ψ_w ≥ 0` of integral 1 supported in `[−w, w]`, `w < τ`, put `g := ψ_w * S₂`. It is
smooth with compact support, `g″ = ψ_w * s`, `g‴ = −ψ_w * μ`, so `‖g‴‖₁ ≤ 1 + τ/T`, and `g″(0) = c ≠ 0`, so `g` is not
identically 0 and `‖g‴‖₁ > 0`. By (T2) at `λ = 1` and because `ψ_w` is even,
`R(g, 1) = i ∫ (ψ_w * κ) dμ`, which tends to `i ∫ κ dμ = i [κ(τ) − (τ/T) κ(T)]` as `w → 0` (κ is continuous and odd).
Hence, with `η(w) → 0`,

    |R(g, 1)| / ‖g‴‖₁ ≥ (|κ(τ)| − (τ/T)(3/2) − η(w)) / (1 + τ/T),

and the right side exceeds `|κ(τ)| − ε` for `T` large and then `w` small. ∎

The amplitude of case G5 of the registered test is this `g` up to sign, with a cosine bump for `ψ_w`
(`T = 400`, `w = 0.01`); its measured ratio 0.71652 agrees to five places with
`|κ(τ) − (τ/T) κ(T)| / (1 + τ/T) = 0.7165254` (computed by the lead in mpmath on 2026-11-19; not a registered number).
The displayed lower bound, which replaces `|κ(T)|` by 3/2, is 0.71299 for these values.

## 7. What a referee should attack

1. Fact (A) and the vanishing of the boundary terms at infinity under integrability alone.
2. Lemma 2: the six derivative identities, one-sided at 0, and the boundedness claims with their constants.
3. Proposition 3: signs of the boundary terms at 0; that `g′(0)` cancels and `g″(0)` does not appear.
4. Lemma 4: is the limit argument circular (it uses Proposition 3, which does not use the value of `L`)?
5. SPL-S: the strictness argument when the supremum is not attained (measure-theoretic detail: `|g‴| |κ(√λ·)| < M |g‴|`
   pointwise where `g‴ ≠ 0` gives a strict inequality of integrals when `‖g‴‖₁ > 0`).
6. Section 5: whether VC2-S as frozen applies to `u²/2` on `[−c, c]` and yields `|2F(c)| ≤ A(w)`.
7. SPL-A: the construction (the lead's first draft of it had a wrong parity and was rewritten the same day: check
   the step function, its two primitives and the measure), the total mass, and whether "smooth compactly
   supported" or "in `𝒢`" should be the frozen class.
8. Whether `𝒢` (four integrability hypotheses) or compact support should be the hypothesis of SPL-S; what is lost.
9. Anything that makes the statement false at an extreme: `λ → 0`, `g` constant near 0, `g‴` of one sign.

## 8. For the formalisation (not started)

Proposition 3 is three applications of integration by parts on a compact interval and three limits; no improper
integral of a function that is not integrable appears, and the value of the Fresnel integral is obtained (Lemma 4)
from the complex Gaussian integral, not assumed. Names to be checked at the Mathlib pin before any plan is frozen
(lessons 1): the complex Gaussian integral; integration by parts for interval integrals with `HasDerivAt`;
`tendsto` of an integrable C¹ function at infinity (if absent, (A) is proved directly).
