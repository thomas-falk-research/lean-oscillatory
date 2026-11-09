# Pre-registration: explicit constants for the 1D and 2D lattice kernels (batch LE)

Registered 2026-11-08 (session 7), before the check program has been written or run and before any Lean statement or
proof of batch LE exists. Numerics are tooling, never evidence for a Lean theorem (README); this check exists to catch
a wrong draft statement (constant, exponent, normalisation, the factorisation) before it is frozen. Changing the
protocol after the run is a new registration with its own date; the first run's output is kept.

## Claims under test (the draft statements)
Notation: `I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk` (t, ξ real) and `K(t, x) = ∫_{[−π, π]²} e^{i(t(cos k₁ + cos k₂) +
x·k)} dk`, the kernel of T6 (`latticeKernel`, `OscInt/Statements/Global.lean`).
- **T0E** For every `t > 0` and every real `ξ`:
  `|I(t, ξ)| ≤ A t^{−1/2} + B t^{−1/3}`, `A = 24 · 2^{1/4}`, `B = 36 · 2^{1/6}`.
  Route (paper, PROVEN modulo the frozen S1 statements): split `[−π, π]` at `±π/4, ±3π/4`; on the three pieces where
  `|cos k| ≥ 1/√2`, S1.2 (`8/√μ`, `μ = t/√2`); on the two where `|sin k| ≥ 1/√2`, S1.3 (`18 μ^{−1/3}`); amplitude 1.
- **T6F** For every real `t` and `x ∈ ℤ²`: `K(t, x) = I(t, x₁) · I(t, x₂)`.
- **T6E** For every `t ≥ 1` and `x ∈ ℤ²`: `|K(t, x)| ≤ (A + B)² t^{−2/3}`. (`A + B ≈ 68.95`, `(A + B)² ≈ 4754`.)
External reference (not checked by us in the literature beyond its citation, `docs/prior_art.md`): Landau (2000),
`sup_{ν ≥ 0, x > 0} x^{1/3} |J_ν(x)| ≈ 0.7858`, and `I(t, n) = 2π iⁿ Jₙ(t)` for integer `n`.

## Two independent computations (fixed now)
- **Q1 trapezoid** for integer `n` (periodic integrand, spectrally accurate): `N = 2(⌈t⌉ + |n|) + 256` nodes on
  `[−π, π)`.
- **Q2 composite Gauss–Legendre**, 16 nodes per panel, `P = ⌈4(t + |ξ|)⌉ + 64` equal panels on `[−π, π]`, nodes
  computed by Newton iteration on the Legendre polynomial (no table copied). Used for integer and non-integer `ξ`.
- Summation in index order, f64, no parallelism (bitwise reproducible on one machine).
- Agreement: on every pair computed by both, `|Q1 − Q2| ≤ 1e−9`, else the run is reported as UNRESOLVED.

## Grid (fixed now)
`t`: 120 points log-spaced in `[0.1, 2000]`. For each `t`, Q1 over `n = 0, …, ⌈1.2t⌉ + 30` (|I(t, −n)| = |I(t, n)| is
checked at `n = 1, 2, 3, ⌊t⌋` by Q2); Q2 over `n ∈ {0, 1}` and the band `|n − t| ≤ 5t^{1/3} + 5`, and over the
non-integer `ξ ∈ {0.5, √2, t/2 + 0.3, t + 0.37, t + 2t^{1/3} + 0.11}`.
2D check of T6F: Q1 tensor trapezoid (`N × N`, same `N` rule with `|n| = |x₁| + |x₂|`) for `t ∈ {0.7, 3, 25}` and
`x ∈ {(0,0), (1,−2), (3,3), (−5,2)}` against `Q1(t, x₁) · Q1(t, x₂)`.

## Criteria (fixed now)
- (a) **T0E holds on the grid**: `max |I| / (A t^{−1/2} + B t^{−1/3}) < 1` over all computed (t, ξ). Required.
- (b) **Exponent**: least-squares slope of `log sup_n |I(t, n)|` against `log t` over `t ∈ [100, 2000]` lies in
  `[−0.36, −0.31]`. Required.
- (c) **Landau comparison**: `max_{t, n} t^{1/3} |I(t, n)| / (2π) ≤ 0.7858 + 1e−4`, argmax reported. Required (a larger
  value means our quadrature or the citation is wrong).
- (d) **T6F**: every 2D value agrees with the product to `1e−9` (absolute). Required.
- (e) **T6E holds on the grid**, via (a) and the factorisation: `max_{t ≥ 1} (sup_n |I(t, n)|)² / ((A + B)² t^{−2/3}) < 1`.
- Controls that must FAIL, else the run is NOT DISCRIMINATING:
  - (c1) exponent −1/2: the slope in (b) lies outside `[−0.55, −0.45]`;
  - (c2) a constant below the truth: `sup |I(t, n)| ≤ 0.9 · 2π · 0.7858 · t^{−1/3}` fails at some grid point;
  - (c3) a wrong factorisation: `K(t, x) = I(t, x₁ + x₂) · I(t, 0)` fails (d) at some 2D point with `x₁x₂ ≠ 0`.
- Reported, no criterion: the ratio `(A + B) / (2π · 0.7858)` (how far T0E is from sharp at large t).
Overall PASS iff (a)–(e) pass and (c1)–(c3) fail. Any other outcome is reported with the numbers and the draft is
revised before freezing (the revision cites this record).

## Program
`numerics/src/bin/lattice1.rs` (Rust, no dependencies; `cargo run --release --bin lattice1`), output saved verbatim to
`numerics/results-lattice1-2026-11-08.txt`.

## Amendment 1 (2026-11-08, after registration d814381, before the program was written or run)
Found by the lead on re-reading: any tensor-product rule (trapezoid or Gauss–Legendre in each variable) factorises
algebraically, `Σ_{j,l} f(k₁ⱼ) g(k₂ₗ) = (Σⱼ f)(Σₗ g)`, so criterion (d) computed with the tensor trapezoid would pass
whatever the integral is: it could not detect a wrong factorisation statement, only a normalisation bug. Replacement
for the 2D computation in (d) and (c3): a **rank-1 Fibonacci lattice rule** on the torus, `N = F₂₆ = 121393` points
`kⱼ = 2π(j/N, {j F₂₅/N}) − (π, π)`, `F₂₅ = 75025`, weight `4π²/N`; it is not a product rule. Its error is the sum of the
integrand's Fourier coefficients on the nonzero dual-lattice points `h₁ + F₂₅h₂ ≡ 0 (mod N)`, whose shortest vectors
have length about `√N ≈ 350`, far beyond the frequencies `|h| ≲ t + |x| + 40 ≤ 75` that carry non-negligible weight
for the registered `(t, x)`. The 1D factors on the right of (d) stay Q1. Tolerance unchanged (`1e−9`); everything else
unchanged.
