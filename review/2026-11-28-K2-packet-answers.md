<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# External K2 research packet (2026-11-28): what was checked, what is accepted, what is changed

Written by the lead, in the lead's words (privacy rule 19); the packet itself is not committed. Intake, hashes and
every run: `docs/progress/2026-11-28-session16-log.md`. Earlier K2 record: `review/2026-11-27-K2-proof-answers.md`
(section 5 is its erratum, and every correction there is binding here).

**Order claim.** No K2 statement is drafted, frozen or stamped, and no K2 proof code exists, in the tree or in
scratch, at the time of this record (`docs/lessons.md`, rules 1 and 2). This file evaluates routes; it freezes
nothing.

## 1. What the packet contains

An independent author's paper-level research packet, "Version 1.0, 28 November 2026" (archive SHA-256
11d49c8314300d22385c61716e000c20f2932fb807ac4e1836c59b63eb5c068e), with:
- a report and a hand-off note;
- five candidate statement contracts in prose: K2-L (a local bound of order m, uniform in the linear term), K2-M (a
  lower bound for the monomial integral with a plateau cutoff), K2-F (Fourier localisation from a smooth bump to
  lattice sites), K2-U and K2-D (the two global fixed-coupling statements);
- an upper-bound route (U0–U4) and a lower-bound route (L1–L6) on paper;
- a formalisation plan naming repository declarations to reuse (route U-R for the upper bound, route L-R for the
  lower bound), with work packages W0–W5;
- an adversarial plan of semantic controls, referee briefs, an acceptance queue, a source register (P1–P8), a claims
  ledger, and a coverage matrix;
- seven Python scripts with exact inputs and their receipts (symbolic jets, exact rational checks, quadrature,
  FFT/Bessel kernel probes, exact finite Taylor discs with an independent verifier and corrupted inputs);
- byte copies of three earlier external notes and an extract of an earlier packet (inputs only).

The packet says itself that it ran no Lean, no kernel replay and no human review, and that its computations check
arithmetic and implementation, not K2's analytic claims. That description is accurate.

## 2. Target, as the packet states it

`p_α(k) = cos k₁ + cos k₂ + α cos(k₁ + k₂)`; normalised kernel `K_α(t, n) = (2π)^{−2} ∫_{[−π,π]²} e^{i(t p_α(k) + n·k)} dk`,
`n ∈ ℤ²`; `a* = 1/(2√2)`; `β(α) = 2/3` for `α ∈ {0, ±a*}`, else `3/4`.
- Upper: for every real α there is `C > 0` with `|K_α(t, n)| ≤ C t^{−β(α)}` for all real `t ≥ 1` and all `n`.
- Lower: for every real α there are `c > 0`, `T ≥ 1` with, for every real `t ≥ T`, some `n` with
  `|K_α(t, n)| ≥ c t^{−β(α)}`.

This is the K2 of `review/2026-11-27-K2-proof-answers.md`, section 1, with the lattice-site quantifier written out
(existential site, all real times, both signs of α). Nothing uniform in α, no sharp constant, no fixed site.

## 3. Reproduction of the packet's computations (VALIDATED, scope as stated)

All seven scripts were read before any run, then replayed with the packet's own driver in a fresh scratch
directory under `python3 -I` with the packet's pinned library versions: RESULT PASS at every stage; the exact-check
output is byte-identical to the packet's receipt; the exact finite discs are identical; the eight corrupted
certificates are rejected in normal and optimised mode. This reproduces the packet's arithmetic. It is not evidence
for the analysis, and the finite discs (times `t ≤ 4`) bear on no K2 claim; they are optional regression tooling and
are not adopted.

## 4. The lead's independent checks (VALIDATED numerically, 23 of 23)

Methods chosen to differ from the packet's (log row 00:04:35–00:06:35):
- **Witness jets.** By numerical root-solving of the transverse equation and 30–40-digit differentiation, not by
  series:
  - at `(π/2, π/2)`, `v = (1, −1)`, `w = (1, 1)`: the reduced function has derivatives 1–3 zero and 4th derivative
    `−3/α` at α = 0.25, −0.7, 2, 0.5. This agrees with `OscInt.API.ReducedBridge.bridge`: `D²Ψ[w, w] = 4α`, the
    quartic invariant is −12, and their quotient is −3/α, with no factor 24;
  - at `(θ, −θ)`, ±a*: derivatives 1–5 zero and 6th derivative `−60√2 sign α`, as TRI-W states;
  - at the anti-diagonal point, α = 0.2 and −0.45: 4th derivative `24(α − 1/(8α))`.
- **L1.** `Re C_{m,σ} = (2/m) Γ(1/m) cos(π/(2m)) > 1/(12m)` for m = 2, …, 40; the margin of the first half-period
  pair is at least 1/12 and pairs 1–5 are positive (m = 2, 3, 4, 6, 12).
- **L2.** The plateau-tail bound `4/(m t r^{m−1})` holds with a genuinely C^∞ cutoff (the packet's probe used a C¹
  one); worst error/bound 0.281 over 96 cases (m = 2, 3, 4, 6, two radii, both signs, three times).
- **L4a.** `Σ_k 1/(1 + k²) = π coth π = 3.1533 < 4` (closed form, not a partial sum).
- **Rates.** FFT scans of `t^β sup_n |K_α(t, n)|` over t ∈ [40, 300] stay in a narrow band for α = 0.3, −1, 2 (β = 3/4)
  and α = ±a*, 0 (β = 2/3), with identical values for ±a*. A negative control at α = 0.3 shows that the exponent
  2/3 there is not the rate.

None of this is an enclosure: no interval arithmetic and no rounding analysis.

## 5. Lead's verification of the packet's claims against the source (aa42df2)

Every repository declaration named below was opened and its hypotheses read, at aa42df2.

### 5.1 Upper route U-R (reuse of the transverse slice-amplitude machinery)

**Accepted.** The packet's reuse claims are correct as to names and hypotheses:
- `OscInt.StationaryPhase.CoreAux.amplitude_facts` (`OscInt/StationaryPhase/Core.lean`, line 809) gives
  `AmplitudeOn` for the inner integral and
  `ampNorm ≤ 8/√(tμ) · (1 + 4b) M (1 + 2a(1 + 24 β₀⁶))`, `β₀ = beta D μ = max 1 (max D μ⁻¹)` (line 205).
  Its hypotheses are `ContDiff ℝ 4` of the phase, `ContDiff ℝ 2` of the amplitude, the clamped root, the transverse
  lower bound μ on `[−a, a] × [−2b, 2b]`, a bound D on derivatives of order ≤ 4 there, and support in
  `[−a, a] × [−b, b]`. Nothing in it is specific to order 4 in the outer variable.
- `OscInt.Cusp.Core4Aux.oscInt2_eq_outer_linear` (`OscInt/Cusp/Core4.lean`, line 68) needs only continuity and the
  support box, and carries an arbitrary outer linear term `p`.
- The outer derivative chain is the only order-specific part. `phase_facts` (orders 1–3) and `phase_four_last`
  (order 4) derive `g⁽ʲ⁾` from `ContDiff ℝ 4 Q` and `ContDiffOn ℝ 3 ys`. The order-m chain needs `Q ∈ Cᵐ`,
  `ys ∈ Cᵐ⁻¹` and `CoreAux.hasDerivAt_iteratedDeriv_of_contDiffOn` (line 721), as the packet says.
- With `OscInt.API.vdCk` of order m (constant `5·2^{m−1} − 2`), the constant
  `8 c_m μ^{−1/2} ν^{−1/m} (1 + 4b)(1 + 2a(1 + 24β₀⁶)) M t^{−1/2−1/m}` follows by the algebra of `Core4.arith4`
  with 4 replaced by m. PROVEN by the lead on paper (one line of exponent arithmetic).
- The far branch is already proved: `OscInt.Cusp.transverseNonStat : TransverseNonStatFacts`
  (`OscInt/Cusp/Transverse.lean`, line 105), one integration by parts in the transverse variable, no condition on
  the longitudinal frequency. The packet's U1f is this lemma.
- The whole A3 assembly (`OscInt.Cusp.cuspBoundGen_of`, `OscInt/Cusp/Assembly.lean`) is the template for an order-m
  assembly: normalisation, normalised data near `q = 0`, the core estimate, the far branch, with the near/far split
  in the single transverse parameter q. Its proof text is order-independent except for the exponent and the names of
  the order-4 parts.

**Correction to the packet's plan (lead's, MINOR).** The packet proposes extending the explicit order-by-order
derivative formulas of `StationaryPhase/Implicit.lean` and `Cusp/Implicit4.lean` (`Y1`, `Y2`, `G2`, `G3`, `dddd`,
`d3Graph`) for the high-order root regularity. To order 6 that is the most expensive way. Mathlib at the pin has the
Cⁿ implicit function theorem with a parameter in any Banach space (`ContDiffAt.implicitFunction`,
`ContDiffAt.contDiffAt_implicitFunction`, `Mathlib/Analysis/Calculus/ImplicitContDiff.lean`, lines 55 and 90), and
the repository already uses it in one variable (`SliceHyps.contDiffAt`, `Implicit.lean`, line 248). Applied with the
parameter `(q, u) ∈ ℝ²`, it gives a jointly smooth root, so `(q, u) ↦ ∂ᵤᵐ G(q, u)` is continuous and the lower
bound ν on a neighbourhood follows by continuity, for every m at once, with no derivative formula. The uniqueness
argument of `SliceHyps.unique` (monotonicity on the box) glues it to the box root. This is what makes a generic
order m cheaper than a dedicated order 6.

**Two obligations the packet names only in passing (lead's, MINOR).**
1. *Existence of a reduced curve at a general point.* `OscInt.API.ReducedBridge.bridge` and any K2-L stated with
   `ReducedCurve` take a globally smooth curve as data. TRI supplies one only at the A5 points (`IsA5Point`) and
   only for `triPhase` (`TriWitness.exists_curve`). At fold, nondegenerate and A3 points a general lemma is needed:
   if `D²Ψ(k₀)[w, w] ≠ 0` then a `ReducedCurve` exists for some ε (implicit function theorem plus a cutoff, the
   pattern of `TriWitness.exists_curve`).
2. *Order 2 at nondegenerate points.* `ReducedBridge.bridge` gives orders 3 and 4 and requires the kernel
   condition. At a nondegenerate point the order-2 identity `g″(0) = D²Ψ[v, v] − D²Ψ[v, w]²/D²Ψ[w, w]` (the Schur
   complement) is a separate small lemma, unless those points are handled by an existing theorem.

### 5.2 Lower route L-R

**Mathematics accepted** (lead's check of each constant on paper and in section 4):
- L1. Positivity `Re C_{m,σ} ≥ 1/(12m)` for every integer m ≥ 2 and both signs. The real part does not depend on σ
  or on the parity of m, since `cos(σ t x^m)` is even in x.
- L2. The plateau tail `|I_b(t) − t^{−1/m} C_{m,σ}| ≤ 4/(m t r^{m−1})`, and the threshold
  `t^{1−1/m} ≥ 96 r^{1−m}` giving `|I_b(t)| ≥ t^{−1/m}/(24m)`.
- L3. The product normal form at a fixed witness.
- L4. The localisation `|L(t)| ≤ 400 B sup_n |K(t, n)|` with floor offsets: Leibniz factor `(1 + |δ|)² + 1 ≤ 5` per
  variable, `25B · 16 = 400B`; the index is `n + j`.
- L5. The three witnesses: the matching-sign A3 point for every α ≠ 0, the A5 point at ±a*, the square case.

The repository facts it relies on are correct: TRI-Q holds for every α ≠ 0, and `D²p[w, w] = 4α` at `(π/2, π/2)`
(Hessian `α·[[1, 1], [1, 1]]` there).

**Refinements proposed by the lead** (to be tested by the route referee, not assumed; see section 6):
- *R1, triangular substitution instead of a 2D change of variables.* The map `(u, s) ↦ (z(u), w(u, s))` is
  triangular. With `χ(u, s) = b₁(z(u)) z′(u) · b₂(w(u, s)) ∂ₛw(u, s)` (times the affine Jacobian), Fubini, then a 1D
  substitution `s ↦ w(u, s)` for each fixed u, then `u ↦ z`, give the exact product `e^{itc} I_{b₁,m,σ}(t) I_{b₂,2,ε}(t)`.
  This needs neither an inverse function theorem nor a 2D change of variables. Mathlib has the 1D substitution
  (`intervalIntegral.integral_comp_mul_deriv`).
- *R2, Parseval instead of pointwise reconstruction.* L4b proves pointwise Fourier reconstruction (or a Fejér
  argument). For the transfer, only `∫ a ḡ = Σ â_j conj ĝ_j` is needed, which Mathlib gives for every L² pair on the
  torus (`hasSum_prod_mFourierCoeff`, `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, line 293). Then
  `|L(t)| ≤ (Σ_j |â_j|) sup_n |K(t, n)|`, and the only analytic work is the coefficient decay by integration by
  parts. (Pointwise reconstruction is also available: `hasSum_mFourier_series_apply_of_summable`, line 330.)
- *R3, α = 0 without a Morse coordinate.* The square phase is separable: `(x − sin x) + (y − sin y)` after removing
  the tangent plane at `(π/2, π/2)`. A product cutoff `χ₁(x) χ₂(y)` with 1D normal coordinates gives a product of two
  monomial integrals of order 3. No Morse coordinate and no 2D chart are needed for this case.
- *R4, the monomial statement as asymptotics.* The owner's list (2026-11-27) names "monomial asymptotics". L2
  already is an asymptotic statement with an explicit remainder:
  `∃ C, Re C ≥ 1/(12m) ∧ ∫_{−R}^{R} e^{iσx^m} dx → C ∧ ∀ plateau b, ∀ t > 0, |I_b(t) − t^{−1/m} C| ≤ 4/(m t r^{m−1})`.
  It gives the limit `t^{1/m} I_b(t) → C` at once, and the lower bound K2-M as a corollary. The closed form
  `C = (2/m)Γ(1/m)·(phase)` is not needed by K2 and can be a separate, later statement.

**Main new generic lemma that the packet under-weights (lead's, MINOR as to plan, a real cost).** Both normal
coordinates need a smooth Taylor remainder: `F(u, s) − G(u) = (s − S(u))² R(u, s)` with R smooth (Morse coordinate)
and `G(u) − G(0) = u^m R_m(u)` with `R_m` smooth (monomial coordinate). The packet's U1c and L3 say "differentiate
under the integral over a fixed compact interval". Mathlib at the pin has no Cⁿ theorem for parametric integrals:
it has `hasFDerivAt_integral_of_dominated_of_fderiv_le` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean`,
line 206) but no `ContDiff` corollary. A reusable lemma "f ∈ Cⁿ ⇒ x ↦ ∫₀¹ f(x, τ) dτ ∈ Cⁿ" is therefore new work,
by induction on n. It is the one piece of analysis both lower-bound normal forms share.

## 6. Referee J

(To be completed when the referee reports.)

## 7. Decision record

(To be completed after section 6.)
