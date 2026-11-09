# Pre-registration: numeric classification of non-separable band functions (batch VV acceptance model)

Registered 2026-11-08 (session 7), before the program `numerics/src/bin/classify_vv.rs` exists and before any Lean
statement of batch VV exists. Numerics are tooling, never evidence for a Lean theorem (README). Purpose: decide, before
freezing, which non-separable model can serve as the owner's acceptance test for batch VV ("a non-separable two-band
lattice model compiles end to end", `docs/ROADMAP.md`, session-7 order), i.e. whose band function satisfies the GD
hypothesis "every point of the torus is nondegenerate or a fold, except finitely many D4 points"
(`docs/design/vector-amplitudes.md`). Changing the protocol after the run is a new registration with its own date; the
first run's output is kept.

## Phases (fixed now), all on the torus [−π, π)²; c₁ = cos x, c₂ = cos y
- **Q(m)**, the upper band of the Qi–Wu–Zhang model: ω = √P, P = 2 + m² + 2m(c₁ + c₂) + 2c₁c₂, for m ∈ {1, 0.5, 3}
  (gapped: P > 0 on the torus for m ∉ {0, ±2}; the program reports min P).
- **T**, the triangular-lattice symbol: c₁ + c₂ + cos(x + y) (scalar; the fallback non-separable test of GD).
- **Control S(m)**, the separable-band trap at m = 0.5: ω = √((c₁ + c₂)² + m²). Must NOT be classified NFD4 (its
  gradient vanishes on the curve c₁ + c₂ = 0, where the band is constant: every point of that curve is of type X).
- **Control C**, the cusp control of P1: x²y + y² on [−1, 1]², must be classified CUSP with the X point within 1e−6 of
  the origin (re-run to show the copied classifier still discriminates).

## Classification and criteria
Identical to `docs/prereg/2026-11-08-P1-classify.md` (definitions N, F, D4, X; grid 2048 × 2048; bisection;
Hessian-zero candidates by Newton; verdicts NFD4 / CUSP / UNCLEAR with the same thresholds). The program is a copy of
`numerics/src/bin/classify.rs` with the phase set replaced; the classifier functions are copied unchanged.
Derivatives: closed form by the chain rule from the closed-form first, second and third derivatives of P (for Q, S) or
of the trigonometric polynomial itself (for T), with g = √· (g′ = 1/(2√P), g″ = −1/(4P^{3/2}), g‴ = 3/(8P^{5/2})) or
g = identity.

Added check (fixed now), run before the classification: **derivative self-test.** At 200 points of the torus from a
fixed linear congruential generator (seed 20261108, x_{n+1} = (6364136223846793005 x_n + 1442695040888963407) mod 2⁶⁴,
coordinate = −π + 2π · (x_n >> 11) / 2⁵³, x then y), the closed-form Hessian and third derivatives of every phase are
compared, along the four directions at angles 0, 0.7, 1.9, 2.6 (which determine both symmetric tensors), with central
finite differences of the closed-form *function value* s ↦ ω(k + s·u): fourth-order stencils, step 1e−3 for
uᵀHu and 1e−2 for T[u, u, u]. Criterion: max |closed − FD| / max(1, |closed|) below 1e−5 (Hessian) and 1e−4
(third derivatives); otherwise the run stops and is reported as DERIVATIVES WRONG.

Decision rule (fixed now, the lead's next step, not a claim):
- if some Q(m) is NFD4: the acceptance model is Q(m) for the smallest such m in the order 1, 0.5, 3;
- else if T is NFD4: the acceptance test of GD on a non-separable symbol is T (scalar), and VV is accepted on the
  componentwise corollary only (`docs/design/vector-amplitudes.md`, §2, item 3), reported to the owner as a fallback;
- else: no acceptance model; report to the owner with the numbers.
The run is NOT DISCRIMINATING (and no decision is taken) unless S(0.5) is not NFD4 and C is CUSP as stated.

## Program
`numerics/src/bin/classify_vv.rs` (Rust, no dependencies; `cargo run --release --bin classify_vv`), output saved
verbatim to `numerics/results-classify-vv-2026-11-08.txt`.
