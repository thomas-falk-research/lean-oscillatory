<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# HOP and PDE: scoping after the post-K2 packet (2026-11-28, session 17)

Written by the lead. Nothing is frozen, stated in Lean or proved here. This note records what the lead checked in
the packet's two work packages HOP (a finite-range unitary group with certified open-device comparison) and PDE
(non-endpoint Strichartz estimates and small-data quintic scattering from K2's decay). It also gives the plan for
the batches that would follow and why neither was started in session 17. The packet is identified in
`review/2026-11-28-postK2-packet-answers.md`.

## 1. Why not started

Session 17 took batches SPL-N, A5U and LOC2 through the whole protocol: freeze, blind reviews, routes, proofs,
post-proof reviews and the final replay. HOP and PDE are each a new batch with their own freeze. HOP alone needs
several new Lean layers: an operator on `ℓ²(ℤ^d; ℂ^m)`, compression to a finite set, and Taylor remainders in
operator norm. Starting either one without the freeze and review steps would break the statement-first rule.
Starting one and leaving it half-way would leave an unreviewed draft in the tree. So both are left for later
sessions, with the checks below as the starting point.

## 2. What the lead checked (paper and numerics; `numerics/review/pde_constants_check.py`)

Labels: VALIDATED means checked by the script, whose output is in
`numerics/results-pde-constants-check-2026-11-28.txt`. CHECKED means re-derived by hand by the lead; it is not
machine-checked.

- **P1 constant (VALIDATED, CHECKED).** For `k(t) = min(1, C|t|^{−σ})` with `C ≥ 1` and `σ > 1/2`, the packet gives
  `‖k‖₂² = 2 C^{1/σ}(1 + 1/(2σ − 1))`. The crossover point is `t₀ = C^{1/σ}`, and
  `C² t₀^{1−2σ}/(2σ − 1) = C^{1/σ}/(2σ − 1)`. The script integrated `k²` at 50 digits for 16 pairs `(σ, C)`
  (σ ∈ {0.55, 2/3, 3/4, 1}); the worst relative error was 5·10⁻⁵¹. The TT* step is then
  `|⟨F(t), U(t−s)F(s)⟩| ≤ a(t) k(t−s) a(s)`, followed by Young's inequality with `1 + 1/4 = 1/2 + 3/4`. It gives
  `‖T‖ ≤ ‖k‖₂^{1/2} = A`, as the packet states.
- **P3 threshold (VALIDATED in exact rationals, CHECKED).** The packet's choices are:
  - the norm `X = max(‖u‖_{L∞ℓ²}, A^{−1}‖u‖_{L⁴ℓ∞})`;
  - the difference bound `‖N(u) − N(v)‖_{L¹ℓ²} ≤ 80 A⁴R⁴ ‖u − v‖_X` on the ball of radius `R`;
  - `R = 2ε` and `ε₀ = (2560|λ|A⁴)^{−1/4}`.

  At `ε = ε₀` the Duhamel map has Lipschitz constant exactly 1/2. The self-map ratio is
  `(ε + |λ|A⁴R⁵)/R = 81/160 < 1`. The script found no violation of the pointwise bound
  `||u|⁴u − |v|⁴v| ≤ 5 max(|u|, |v|)⁴ |u − v|` in 200 000 seeded complex samples.
- **H2 tail (VALIDATED in exact rationals, CHECKED).** For `R < b + 1`,
  `Σ_{k ≥ b} R^k/k! ≤ R^b/(b!(1 − R/(b + 1)))`, because consecutive terms have ratio at most `R/(b + 1)`. The script
  found no violation for `b = 1, …, 24` on a grid of `R` with step 1/4. The Taylor radius `R^{N+1}/(N+1)!` without a
  factor `e^R` is correct for a self-adjoint generator: the integral remainder contains `e^{isH}`, which is unitary.
  The packet itself says that this fails for a non-self-adjoint generator.
- **Bridge to K2 (CHECKED against the frozen definitions).** The hopping amplitudes `1/2` on `±e₁, ±e₂` and `α/2` on
  `±(e₁ + e₂)` have symbol `cos k₁ + cos k₂ + α cos(k₁ + k₂)`, which is `triPhase α` of
  `OscInt/Statements/TriangularDecay.lean`. The kernel is then `triKernel/(2π)²`. K2-U gives decay for real `t ≥ 1`
  only. The packet handles `t ≤ −1` by conjugation (`U(−t) = U(t)*`) and `|t| < 1` by the trivial bound 1; both
  steps would be new lemmas.

Not checked here: the packet's HOP certificate code beyond what the intake reproduced (normal and `-O` runs, 14 and
5 negative controls, byte-identity of 8 models; `review/2026-11-28-postK2-packet-answers.md`); the measurability and
Bochner bookkeeping of P1 and P3; prior art for the triangular case (the packet names lattice Strichartz work such as
Stefanov–Kevrekidis; a sweep is owed before any statement).

## 3. Plan, in the protocol's order

1. **HOP-1 (scalar first).** Statements: the finite-range group on `ℓ²(ℤ^d)` (H1), extending
   `OscInt/Statements/LatticeGroup.lean` by new definitions without touching the frozen ones. Then the
   open-device comparison (H2) with the two-leg exit bound. The registered controls are the packet's list: a
   nonsymmetric Jordan block, an asymmetric scalar `h`, duplicate offsets, `t < 0`, `R = b + 1` (refused) and
   wrap-around versus an open `D`. Reuse `OscInt/Front/LatticeGroupOp.lean`, `LatticeGroupExp.lean`,
   `LatticeGroupFourierStencil.lean` and `LatticeGroupUnique.lean`. Matrix coefficients come after the scalar case.
2. **PDE-1 (P1 only).** Homogeneous and retarded `L⁴ℓ∞` estimates for an abstract unitary group with
   `‖U(t)‖_{1→∞} ≤ min(1, C|t|^{−σ})`, `σ > 1/2`, by the packet's elementary TT* route: Hölder (2, 4, 4) on the
   product measure, and finite site sets and time intervals with a monotone limit, so no `ℓ∞` dual is needed.
   Instantiate it at the nearest-neighbour lattice (batch LS) and at K2 once HOP-1 gives the group.
3. **PDE-2 (P3).** Small-data quintic scattering with the explicit `ε₀`, frozen separately from P1.

Each starts with prose in `docs/statements.md`, a prior-art sweep and a registered numerical test where one applies.
