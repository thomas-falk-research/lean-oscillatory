<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Pre-registration: numeric test of the quadratic-phase leading term with its remainder constant (SPL)

Registered 2026-11-19, before the test program has been run and before any Lean statement or proof of batch SPL
exists. Numerics are tooling, never evidence for a Lean theorem (README); this test exists to catch a wrong
statement (constant, sign, phase factor, order of the remainder, the kernel) before it is frozen. Changing the
protocol after the run is a new registration with its own date; the first run's output is kept.

What was already known when this was registered (exploration, `docs/design/batch-SPL-opening.md` section 5,
`numerics/results-spl-explore-kappa-2026-11-19.txt`): the location and value of the maximum of `|κ|` from the closed
form, and its agreement with a coarse quadrature of the definition at five points. The program below had been
written and compiled, not run. No case of this protocol had been computed.

## Claims under test (the draft statements of `docs/design/batch-SPL-opening.md`, section 2)

For `g` three times continuously differentiable with `g, g′, g″, g‴` integrable, `λ > 0`,
`R(g, λ) = ∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}` and the kernel κ of that section:

- **T1 (bound).** `|R(g, λ)| ≤ K ‖g‴‖₁ λ^{−3/2}` with `K = 0.7219740`.
- **T2 (identity).** `R(g, λ) = −(i/λ^{3/2}) ∫ g‴(t) κ(√λ t) dt`.
- **T3 (the constant).** `sup |κ| = K* = 0.72197400` to eight places, attained at the first local maximum
  (`τ*` near 1.6246), and the bound is attained in the limit, so no smaller constant works.

## Cases (fixed now)

- G1: `g = e^{−u²/2}` (closed form for `R`).
- G2: `g = (1 + 0.7u + 0.4u²) e^{−u²/2}` (closed form; not even).
- G3: `g = u e^{−(u − 0.6)²}` (closed form; `g(0) = 0`, stationary point off the centre of the amplitude).
- G4: `g = (1 − (u/3)²)⁴ (1 + u/2)` on `[−3, 3]`, zero outside (compact support, exactly C³).
- G5 (near-extremal, `λ = 1` only): `g‴ = ½[φ_w(t − τ*) − φ_w(t + τ*)] − (τ*/2T)[φ_w(t − T) − φ_w(t + T)]` with
  `φ_w(t) = (1 + cos(πt/w))/(2w)` on `|t| ≤ w`, `T = 400`, `w = 0.01`, `τ*` as computed in T3; `g` is its third
  antiderivative from −∞, compactly supported in `[−T − w, T + w]`, given in closed form in the program;
  `‖g‴‖₁ = 1 + τ*/T`.

`λ ∈ {1, 4, 16, 64, 256}` for G1–G4; `λ = 4096` in addition for criterion (b) on G1–G3 (closed forms only).

## Method (fixed now)

IEEE-754 binary64, round to nearest. Composite Gauss–Legendre quadrature, 12 nodes per panel, panels no wider than
`min(0.02, 1/(λ L))` with `L` the larger end point in modulus (so the phase `λu²/2` changes by at most one radian
across a panel), split at the zeros of `g‴`, at 0 and at the breakpoints of G5; every quadrature is repeated with
half the panel width and the difference is reported. `R` is computed (i) directly from its definition by
quadrature of `g(u) e^{iλu²/2}` (Gaussians truncated at `|u| = 12`, G3 at `[−8, 9]`), (ii) from the closed form for
G1–G3, (iii) from the right side of T2. Fresnel integrals from SciPy. `K*` (i) by maximising the closed form in
mpmath at 30 digits from a grid of step 0.001 on (0, 40], (ii) from `τ² ∫_τ^∞ F(x) x^{−3} dx` by quadrature to
`X = 1000` plus the tail `τ² F(∞)/(2X²)`, whose error is at most `τ²/X³`. No random numbers.

## Criteria (fixed now)

With `ρ := λ^{3/2} |R| / ‖g‴‖₁`, `R` from (i):
- (a) `ρ ≤ K` in all 20 cases G1–G4 (tolerance 10⁻⁹);
- (x) for G1–G3, `λ^{3/2} |R(i) − R(ii)| < 10⁻⁶` at every λ (the direct quadrature is right);
- (c2) `λ^{3/2} |R(i) − R(iii)| < 10⁻⁶` in all 20 cases, and `|R(i) − R(iii)| < 10⁻⁴` for G5 (T2);
- (b) `λ^{3/2} |R| / (√(2π) |g″(0)|/2)` within 5 % of 1 at `λ = 4096` for G1–G3 and at `λ = 256` for G4 (order of the
  remainder and the next coefficient of the classical expansion);
- (c) for G5: `0.985 K ≤ ρ ≤ K`, with a quadrature difference below 10⁻⁵ (the prediction of the outline is
  `ρ ≥ 0.7165`);
- (e) the two values of `K*` agree within 10⁻⁷ and `0 ≤ K − K* < 10⁻⁷`; (e′) on (2.6, 40] the grid maximum of `|κ|`
  is below `K* − 0.05`.

Controls, each of which must come out as stated or the run is NOT DISCRIMINATING:
- C1: G1 at `λ = 256` with the factor `e^{iπ/4}` of the leading term replaced by 1 gives `ρ > K`;
- C2: G5 gives `ρ > √(2π)/4 = 0.62666` (the constant of the classical next term does not bound the remainder);
- C3: with κ extended to negative arguments as an even function, T2 fails by more than 10⁻³ on G2 or G3 at `λ = 1`;
- C4: on G1, `λ² |R|` grows by more than a factor 3 from `λ = 16` to `λ = 256` (the remainder is not `O(λ^{−2})`).

Overall PASS iff every criterion and every control line is PASS. Any other outcome is reported as it is, with the
numbers; the draft statements are then revised before any freeze, and the revision cites this record.

## Program

`numerics/review/spl_remainder_checks.py` (Python 3 with NumPy, SciPy and mpmath; versions are printed by the run),
output saved verbatim under numerics/ as results-spl-remainder-checks-2026-11-19.txt (the file does not exist at
registration). The SHA-256 of the program at
registration is recorded in `docs/prereg/LEDGER.md`.
