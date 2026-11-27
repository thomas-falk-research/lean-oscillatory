<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# External proof of K2 (fixed-coupling sharp decay, anisotropic triangular lattice): what was checked (2026-11-27)

Written by the lead. The owner delivered a document from an independent researcher (another model family): a proof
of K2 (227 lines, SHA-256 d352e85fa18976b7325fff2bf68e0ac1daac54c8d2ba9a473d4e3b25058ed7df). It answers the MAJOR
process finding of referee F in `review/2026-11-26-A5-handoff-answers.md`, section 2. The document is not committed;
findings are in the lead's words. Handling and hashes: `docs/progress/2026-11-26-session15-log.md`.

## 1. The claim and the route

**K2.** Fix α. Let `β(α) = 2/3` for `α ∈ {0, ±1/(2√2)}` and `β(α) = 3/4` otherwise. Then
`sup_n |K_α(t, n)| ≤ C_α t^{−β}` for t ≥ 1, and `sup_n |K_α(t, n)| ≥ c_α t^{−β}` for `t ≥ T_α`. The constants depend
on α.

The route, in its own numbering:
- **L1.** A transverse root `S(u, q_s)` by monotonicity on a box, with a fixed order of choices (r, h, then ρ, then
  the patch).
- **L2.** An explicit transverse coordinate `w = (s − S)√(2εA)`, with A the integral Taylor remainder, so that
  `Φ = g + εw²/2`, with `μ/√M ≤ ∂_s w ≤ M/√μ`. No general Morse lemma is used.
- **L3.** The transformed amplitude, supported uniformly in q.
- **L4.** Van der Corput twice:
  - the second-derivative bound in w (VC2-K, or S1.k with k = 2);
  - then S1.k of order m in u.

  This gives `t^{−1/2−1/m}` near the critical velocity.
- **L5.** One integration by parts away from it, for unbounded velocities.
- **Patching and the lower bound.**
  - A finite cover of the torus gives the upper bound (α = 0 by the existing two-dimensional cube-root bound).
  - The monomial asymptotics `t^{1/m} ∫ b e^{iσtz^m} → (2/m)Γ(1/m)·(phase) b(0)` come with an explicit tail proof.
  - An exact product normal form `const + εw²/2 + σz^m`, with a cutoff whose Jacobian cancels, gives the lower bound.
  - A Fourier localisation `L(t) = Σ_j χ̂_t(j) K(t, n(t) + j)` with `Σ_j |χ̂_t(j)| ≤ 13D` transfers it to lattice
    sites. It needs no assumption that different stationary points do not cancel.

## 2. Referee H (fresh context, lead's model family; brief SHA-256 e2bcb1c8…)

Findings in the lead's words:
- **L1 to L5: SOUND.**
  - The inequalities of L1 hold, and the order of choices is consistent.
  - The root does not depend on `q_u`, so g is affine in `q_u` and `∂_u^m g` (m ≥ 2) does not depend on it.
  - The bound of L2 was re-derived and tested on 4000 random transverse profiles of both signs, including steps
    and fast oscillations. Worst ratios: 1.019 for the lower bound (must be at least 1) and 0.980 for the upper bound
    (must be at most 1). The bound holds and is close to sharp.
  - The uses of S1.k and VC2-K match this repository's frozen hypotheses: real phase, complex amplitude, amplitude
    term `|ψ(b)| + ∫|ψ′|`, `|D_k| ≥ μ` in absolute value. The constant of L4 is right (`c₆ = 158`).
  - L5: the formula for DV and `|tr| ≤ 2‖·‖` are right, and no bound on p is needed.
  - NIT: the derivative bounds of all orders in L1 and L3 are described, not computed. That is the most expensive part
    of a formalisation.
- **Patching: SOUND, with one MINOR gap.**
  - For α ≠ 0 there are no rank-0 points.
  - For α = 0, the frozen T6E′ gives `(2π)^{−2} C*² t^{−2/3}`, with matching normalisation. T6E′ is the better
    citation (stated on ℤ × ℤ).
  - Gap (MINOR): the step "m = 3, 4, 6 by K1/K3" needs a bridge lemma. K1/K3 state types through jet invariants,
    the frozen `D²Ψ[w, w] D⁴Ψ[v⁴] − 3(D³Ψ[v, v, w])²`, while the proof uses its own elimination g. The identity of
    the two, and for the sextic their independence of the coordinates, is asserted, not proved.
- **Monomial asymptotics: SOUND.**
  - The tail bound and the Laplace evaluation were re-derived.
  - Numerically, with an asymmetric bump, the scaled integrals converge to `c_{m,σ}` for m = 2, 3, 4, 6 and both
    signs. For example, at m = 6: 1.700, 1.750, 1.773 + 0.46i, against 1.792 + 0.480i.
- **Product normal form and Fourier localisation: SOUND.** The Jacobian cancels, the factor √2 is the Fresnel
  constant at t/2, the signs of δ are right, and `13D` is right.
- **Numerical falsification at ±α*.**
  - Lattice kernel by FFT on a 2048² grid, at the site nearest to the A5 velocity: `t^{2/3}|K|` is 0.288 to 0.309
    for t from 50 to 700.
  - The predicted local A5 constant is `(2π)^{−2}√(2π/λ)(1/3)Γ(1/6)|a₆|^{−1/6} = 0.283`.
  - The oscillation of about ±10% is consistent with Morse points at the same velocity, smaller by `t^{−1/3}`.
  - The results for +α* and −α* are identical.
  - MINOR: the lower bound should cite the explicit A3 witness `(±π/2, ±π/2)` for non-exceptional α, rather than
    "matching-sign cusps exist". It is exactly what TRI-Q states, with reduced quartic −12.
- **Weakest step:** the bridge in the patching above.

## 3. Verdict

**K2: PROVEN (on paper; one fresh adversarial referee of the lead's family; no error found), conditional on two
items:**
1. a bridge lemma: the order of the first nonzero derivative of the proof's reduced function g equals the type given
   by the frozen jet invariants. For A3 this is the identity `24 F_ss g⁗(0) = D²Ψ[w, w] D⁴Ψ[v⁴] − 3(D³Ψ[v, v, w])²`
   in orthogonal eigen-coordinates. For A5 it is TRI-W's sextic, stated for every reduced curve;
2. K1 and K3, which batch TRI states.

Not machine-checked. No human has read it. Novelty: as K2 in section 5 of `review/2026-11-26-A5-handoff-answers.md`.

## 4. What follows

- **K2 becomes its own batch after TRI** (owner decision 2026-11-27). Its statements:
  - a generic local lemma of order m, uniform in the velocity, which is reusable beyond this lattice;
  - the monomial asymptotics;
  - the Fourier localisation lemma, also reusable;
  - the two global statements.
- The bridge lemma of section 3 is a part of the K2 route, not of TRI.
- TRI-W is stated for every reduced curve, so the sextic is available in any transverse coordinates the K2 proof
  chooses. The quartic invariant of TRI-Q is coordinate-free for the A3 case.
