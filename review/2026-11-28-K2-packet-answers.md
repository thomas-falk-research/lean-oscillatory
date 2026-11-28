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

**Correction to the packet's plan (lead's, MINOR; the route chosen in section 7 is referee J's repair J-1 instead, which keeps the repository's existing uniformity lemma).** The packet proposes extending the explicit order-by-order
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

## 6. Referee J (route referee, fresh context)

Launched 00:08, finished 00:44 (harness 2146 s, 92 tool uses); brief SHA-256 9010de69…333e1a9; lead's model family;
no Lean; repository sources at aa42df2. Its report came as a hand-back and is not reproduced. Its scripts are in the
lead's scratch, not in the tree. Findings in the lead's words, with the lead's answer to each.

**Verdict: no FATAL finding.** All five of the packet's contracts are true as written. Both routes are correct,
given the frozen TRI statements and standard analysis. Every constant of L1–L5 was re-derived, and most were also
checked numerically.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| J-1 | MAJOR | The uniform lower bound on the order-m reduced derivative, uniform in the transverse velocity, is the cost centre. The repository gets uniformity from `ImplicitAux.exists_coreHyps` (`OscInt/StationaryPhase/Implicit.lean`, line 507), generic in the order and fed by an explicit formula G (G2, G3; G4 in `Implicit4.lean`). Done that way, order 6 needs explicit Y4, Y5, G5, G6. The packet costs none of this, and `CoreHyps` carries the root only as C³. Repair: with `Y1 = −Q_xy/Q_yy` and `D f = f_x + Y1 f_y`, `dʲ/dxʲ Q(x, ys x) = (D^{j−1} Q_x)(x, ys x)` for j ≥ 1, by induction from `ys′ = Y1`. Take `G := D^{m−1}Q_x` in `exists_coreHyps`, generalise `SliceHyps.contDiffAt` from C³ to Cⁿ (Mathlib's theorem takes any n), and use a hypothesis bundle that carries `ys ∈ C^{m−1}`. The identity was checked at 60 digits (relative error 1.4e−60). | **Accepted; supersedes the lead's correction of section 5.1.** It is closer to the repository than the joint implicit function theorem of section 5.1: it keeps the existing per-phase root and the existing uniformity lemma, and replaces only the order-specific formula by one operator. It is the planned route for the order-m local lemma. |
| J-2 | MINOR | `OscInt.Cusp.cuspBoundGen_of` is already K2-L at m = 4 for all y, and the packet does not name it. FE-S2.2l and FE-S3l are uniform only over a compact set of linear terms, and need an openness lemma for `FoldOrNondeg` that the repository does not have. | Accepted. The order-m assembly is a clone of `cuspBoundGen_of` with the exponent generalised; the far branch is `transverseNonStat`. |
| J-3 | MINOR | Nothing frozen supplies a reduced curve at Morse, fold or A3 points; the bridge has no order-2 case. | Accepted; the same two lemmas as the lead's section 5.1 (existence of a reduced curve; the order-2 Schur identity) are planned parts. |
| J-4 | MINOR | L3 asserts a 2D diffeomorphism and its inverse without showing them. | Answered by J's question 5, below. |
| J-5 | MINOR | L4b ignores Mathlib's multivariate torus Fourier series (`AddCircleMulti.lean`: `mFourierCoeff_eq_integral`, Parseval `hasSum_prod_mFourierCoeff`, `hasSum_mFourier_series_apply_of_summable`). | Accepted; agrees with the lead's R2. |
| J-6 | MINOR | The packet's "explicit coefficient" variant at A5 is not supported by the frozen text. TRI-W gives the raw-basis sixth derivative, but no frozen statement gives the raw-basis fifth derivative. | Accepted: the lower bound at ±a* uses only the existential witness of `IsA5Point`. K2-MA and K2-ML cover both signs, so the unknown sign is no obstacle. |
| J-7 | MINOR | The product normal form, the largest new piece of the lower route, has no contract. | Answered: it becomes a blueprint interface (a part with its own proposition), not a frozen statement. The frozen set stays minimal, and the interface is checked numerically before agents are launched (`docs/lessons.md`, blueprint rules). |
| J-8 | NIT | K2-F needs only bounds on `∂₁ᵃ∂₂ᵇχ` with a, b ≤ 2, and the series proof does not use periodicity of Ψ. | Noted. The draft keeps χ C^∞ (simplest to state; every planned χ is smooth) and keeps periodicity, which a Parseval proof uses. |
| J-9 | NIT | U2's sentence on the factor 24 is garbled (correct: `G₀⁗(0) = Q/A`, Taylor coefficient `Q/(24A)`). 400B is valid but very loose (0.892 against 1.69e6 for a test bump). The L2 tail constant is a factor 2 above the indicator limit. | Noted; the constants are used existentially, except in K2-MA and K2-ML, where the stated ones are proved valid. |
| J-10 | NIT | `CosMoment` has fixed exponents (ν = 2/3, where L1's step `1 − ν ≥ 1/2` fails) and no explicit margin. | Noted; L1's margin is re-derived for ν = 1/m, as the packet itself says. |
| J-11 | NIT | In the lead's alternative, the factor is `1/J`, not "times the affine Jacobian". | Correct; the lead's wording was loose. |
| J-12 | MINOR | Exponent fits of `sup_n \|K\|` for t ≤ 256 come out steeper than −3/4 (−0.79 to −0.85). An exact one-variable Bessel representation, checked against the FFT, shows the right behaviour up to t = 2048: `t^{3/4}` times the window maximum falls toward the local cusp constant from above. A slope test at short times would falsely refute K2-D. | Accepted before the numeric registration: the lattice criterion of `docs/prereg/2026-11-28-K2.md` is a bounded band, not a slope, and says that it cannot separate 2/3 from 3/4. |

**J's question 5, the lead's alternative to L3: valid (PROVEN, VALIDATED by J).** Take
`χ̃ = J⁻¹ b₁(z(u)) z′(u) b₂(w(u, s)) ∂ₛw(u, s)`. Fubini applies, then `intervalIntegral.integral_comp_mul_deriv` in s,
which needs only a C¹ map, then the same in u. The range covers the supports once `ρ₂ < (3h/4)√(μ/2)`. χ̃ is smooth
and vanishes near the chart's edges. It is the packet's own "simpler equivalent choice": only the proof of the
identity changes. The alternative removes the 2D change of variables, the inverse map, the injectivity and image
arguments, and any inverse function theorem. It does not remove the 1D implicit function theorem for `S(u)` at the
generic witness. Numerically the identity holds to relative error 3e−12 to 6e−11 on triPhase charts at t = 7.3,
61.7 and 240.

**J's other simplification, accepted as an option.** At the A5 points the transverse root is explicit for every
transverse velocity: `h = arcsin((sin θ + q/2)/cos u) − θ`, with the other branch at θ = 3π/4. So no implicit function
theorem is needed there. It is kept as a fallback if the generic order-m lemma is delayed.

## 7. Decision record (lead, 2026-11-28; the owner may overrule before the freeze)

1. **Upper bound: reuse, route U-R.** The order-m local lemma (K2-L) is a clone of the A3 assembly
   `cuspBoundGen_of`. Its parts:
   - the existing amplitude engine (`amplitude_facts`, `oscInt2_eq_outer_linear`);
   - S1.k (`vdCk`) of order m;
   - the existing far branch (`transverseNonStat`);
   - normalised data of order m from `exists_coreHyps` with J's graph operator (J-1);
   - two small lemmas: the existence of a reduced curve, and the order-2 identity.

   The global upper bound patches K2-L by compactness with T1 and a telescoping partition. α = 0 is T6E′.
2. **Lower bound: the packet's elementary route L-R**, with three changes:
   - the lead's triangular substitution in place of the 2D change of variables (validated by J);
   - Parseval on the torus (Mathlib) in place of pointwise reconstruction or Fejér;
   - the separable product cutoff for α = 0.

   No complex Gamma formalisation is needed.
3. **Statements: six, drafted** in `OscInt/Statements/TriangularDecay.lean`:
   - K2-L, generic in m;
   - K2-MA, "monomial asymptotics" with an explicit remainder for plateau cutoffs, the owner's listed item (R4);
   - K2-ML, the monomial lower bound;
   - K2-F, the localisation, stated without a supremum;
   - K2-U and K2-D.

   The kernel is unnormalised, as `latticeKernel`. The product normal form and the parametric smoothness of
   integrals are blueprint parts, not statements.
4. **Rejected or not adopted from the packet:**
   - extending the explicit order-by-order derivative formulas to order 6 (superseded by J-1);
   - the Fejér reconstruction (superseded by Parseval);
   - the explicit raw-basis coefficient variant at A5 (J-6);
   - the normalised kernel convention (the repository's convention is kept, and the conversion is a sanity theorem);
   - the finite Taylor-disc certificates (they bear on no K2 claim);
   - "explicit 400B" as a frozen constant (existential D suffices, and J shows 400B is loose).
5. **Out of scope, unchanged:** RH/GRH; parameter-uniform crossover near α = 0 and ±a*; sharp constants; fixed
   lattice sites; SPL-N and report D.
