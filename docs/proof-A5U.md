<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route of batch A5U (`TriCrossoverUpperStatement`)

Written by the lead after the blind pre-proof reviews (answers `review/2026-11-28-SPLN-A5U-LOC2-preproof-answers.md`, stamped `stamps/20261128T154444Z-e9c0ea9fb732`). Sources: the external packet's crossover work package
(sections X0–X6, `review/2026-11-28-postK2-packet-answers.md`) and a read-only planning agent's map of the K2 code
(session 17 log). The packet's moving-centre route is replaced by a fixed chart (section 1), which the lead checked by
hand. Every K2 declaration named below is re-checked at the pin before a part is briefed; Mathlib names are
`#check`ed in `MathlibNames.lean`.

Notation. `a* = 1/(2√2)`, `a₀ ∈ {±a*}`, `θ₀ = arccos(−2a₀)` (so `cos θ₀ = −2a₀`, `sin θ₀ = 1/√2`), `k* = (θ₀, −θ₀)`,
`v = (1, 1)`, `w = (1, −1)`, `L(u, s) = u v + s w`, `ε = |α − a₀|`, `E = crossEnvelope`.

## 1. The fixed chart (the key simplification)

In the chart `k = k* + L(u, s)` we have `k₁ + k₂ = 2u`, so for every α

  `Ψ_α(k* + L(u,s)) − Ψ_α(k*) − DΨ_α(k*)·L(u,s) = F₀(u, s) + (α − a₀)·(cos 2u − 1)`,

with `F₀` the same expression at `a₀` (`DΨ_α(k*) = DΨ_{a₀}(k*)` because `∇cos(k₁+k₂) = 0` where `k₁ + k₂ = 0`). `F₀` is
even in u. The transverse equation `∂_s(F_α + q s) = 0` does not involve α. Hence the transverse critical curves
`s = ys_q(u)` are those of K2's normalised data at a₀ (part P2, `OscInt.K2.normalizedDataM`, order 6), uniform in the
tilt `|q| ≤ q₀`, and the coupling changes the reduced function only by `(α − a₀)φ(u)`, `φ(u) = cos 2u − 1`.

## 2. The jets (packet X1, via TRI-Q instead of closed forms)

Let `g_{α,q}` be the reduced function (tilt q, coupling α), `A = g″(0)`, `B = g⁗(0)`, `D = g⁽⁶⁾(0)`. Put
`y = ys_q(0)`, `α* = −cos(θ₀ + y)/2`: the point `k* + y w` is TRI-Q's degenerate point `(θ_{α*}, −θ_{α*})` of coupling
α*. From K2's P6 (kernel ⇒ `g″(0) = 0`), the reduced bridge and TRI-Q (`g⁗(0) = 12(8α*² − 1)/(4α*)`), and
`φ″(0) = −4`, `φ⁗(0) = 16`:
- `A = 4(α* − α)`, `B = B₀(α*) − 4A` with `B₀(α) = 24α − 3/α = (α − a₀)(24 + 3/(α a₀))`;
- hence `|B| ≥ 24|α − a₀| − 10|A|` on a window `α a₀ > 0` (constants `c_B = 24`, `K = 10`), and `|A| ≤ 2|q|/μ + 4ε`.
`D` is bounded away from 0 near `(α, q) = (a₀, 0)` by TRI-W (`−60√2 sign a₀`) and continuity.

## 3. Jet separation (packet X2, checked line by line)

`g` is even (odd jets at 0 vanish). With `|g⁽⁸⁾| ≤ L`, Taylor gives `|g″ − (A + Bu²/2 + Du⁴/24)| ≤ L u⁶`,
`|g‴ − (Bu + Du³/6)| ≤ L|u|⁵`, `|g⁗ − (B + Du²/2)| ≤ L u⁴`. With `ρ = max(√ε, |A|^{1/4}, |u|)` and the scaled
quantities the packet's contradiction gives: there is `η > 0`, independent of L after δ is chosen, with

  `η ε² < |g″(u)|  ∨  η ε^{3/2} < |g‴(u)|  ∨  η ε < |g⁗(u)|`  for `0 < ε ≤ δ²`, `|A| ≤ δ⁴`, `|u| ≤ δ`.

## 4. Piecewise van der Corput (packet X3)

For `ε > 0` and thresholds `l_j = η ε^{(6−j)/2}`: since `g⁽⁶⁾ ≠ 0` on the interval, each `g^{(j)} ∓ l_j` (j = 2, 3, 4)
has at most `6 − j` zeros (Rolle), so at most 18 cuts and 19 pieces; on each piece one alternative of section 3 holds
throughout (intermediate value theorem), and the frozen `vdCk` (S1.k) of order j applies with the restricted
amplitude norm (at most the full one). Sum: `19 (8 (t l₂)^{−1/2} + 18 (t l₃)^{−1/3} + 38 (t l₄)^{−1/4})·ampNorm`.
For `tε³ ≥ 1` each term is at most `const(η) ε^{−1/4} t^{−1/4}`; for `ε = 0` or `tε³ ≤ 1` the order-6 bound (K2's P1,
`coreEstimateM`, fixed ν) gives `t^{−1/6}`. Times the transverse factor `t^{−1/2}` from `amplitude_facts`
(`OscInt.StationaryPhase.CoreAux.amplitude_facts`), this is `C t^{−2/3} E(ε t^{1/3})`.

## 5. Plan of parts (blueprint `Blueprint/TriangularCrossover.lean`)

Stage A (the window at the A5 point):
- A1 Rolle zero count for a derivative chain; A2 amplitude norm on a subinterval; A3 piecewise van der Corput;
- A4 core estimate with several orders (clone of `coreEstimateM` using A3);
- A5 even-jet Taylor bounds; A6 jet separation (algebra); A7 envelope power algebra;
- A8 fixed-chart identity; A9 base data at a₀ (from P2, P3, P5, TRI-W); A10 longitudinal perturbation keeps
  `CoreHypsM`; A11 tilt jets via TRI-Q at α*; A12 the window local bound at `k*`; A13 transfer to `−k*` and
  2π-translates.
Stage B (rest of the torus): B1 K2-L uniform over a compact window of α for orders ≤ 4 (parametric
`ImplicitAux.exists_coreHyps` over `(α, q)`); B2 uniform `t^{−3/4}` at fold, nondegenerate and A3 points of a₀; B3
family torus patch; final assembly with TRI-K and TRI-X at a₀.
Estimated size 3,000–5,000 lines (planning agent: central 3,900). Riskiest: A3, A11, B1.

## 6. Open points for the route referee
- Uniqueness of the transverse critical point (needed for evenness of the curve and for A11).
- Order of choices: data at a₀ → η → δ → q₀, r → far box → ball radius; every constant before α, t, n.
- The window must exclude α = 0 and satisfy α a₀ > 0 (A11) and r ≤ 1 (B2, A7).

## Revision after the blueprint and the route referee (2026-11-28; `review/2026-11-28-A5U-route-answers.md`)

The blueprint `Blueprint/TriangularCrossover.lean` (18 interfaces, written by an architect agent from this route and
the planning report, reviewed by the lead) made the plan precise; changes against section 5:
- A1 needs `n ≥ 1` (for `n = 0`, `D 0 ≠ 0` does not bound the number of points where `D 0 = c`).
- A6 needs no upper bound `C_B` on the quartic jet; η depends on `(c_B, K, d_min, d_max)` only, δ also on L.
- A8 is stated as a closed form of the chart phase, from which evenness in u and the independence of `∂_s` from α
  follow.
- A9 cannot use K2's P2 as a black box (P2 gives no regularity of the curve in the tilt); it reopens
  `NormalizedDataMAux` and adds `Gop F 5`, `Gop F 7` to the continuity step for the q-uniform jet bounds.
- A11 holds for every coupling α given `|ys 0| < π/4`, which also gives `α* a₀ > 0`; section 2's "window α a₀ > 0"
  should read `α* a₀ > 0` (route referee, MINOR-1).
- A12 is split into A12a (the window in the chart for near tilts) and A12 (the chart change and the far tilts).
- B1 holds for every jointly smooth family and every order m ≥ 2; B3 needs only continuity of each phase.

Parts as proved, all under `OscInt/Front/TriangularCrossover*.lean`: A1–A3 (agent G1), A5, A6, A7, A10, A13 (agent
G2; A7's theorem is `crossEnvelopeFacts`), A8, A4, B3 (agent G3), A9, A11 (agent W; A11 by a direct computation of the
jets in the fixed chart instead of TRI-Q and the bridge, with the same conclusions), B1, B2 (agent B; B1 in two
modules), A12a, A12 (agent X).
