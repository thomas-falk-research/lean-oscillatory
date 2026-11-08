# Pre-registration: numeric check of the 2D nondegenerate stationary-phase leading term (P3b)

Registered 2026-11-08, before the check program has been run and before any Lean statement or proof of P3b exists.
Numerics are tooling, never evidence for a Lean theorem (README); this check exists to catch a wrong statement
(constant, sign convention, power of 2π, remainder order) before it is frozen. Changing the protocol after the run
is a new registration with its own date; the first run's output is kept.

## Claim under test (the draft statement P3b)
For Ψ: ℝ² → ℝ smooth, A: ℝ² → ℂ smooth with compact support, and k₀ the only critical point of Ψ in supp A, with
H = D²Ψ(k₀) invertible:

  I(m) = ∫ e^{imΨ(k)} A(k) dk = (2π/m) |det H|^{−1/2} e^{iπ sgn(H)/4} e^{imΨ(k₀)} A(k₀) + R(m),
  |R(m)| ≤ C m^{−2} for m ≥ 1,

where sgn(H) is the signature (number of positive minus number of negative eigenvalues). This is the standard
form (Hörmander, ALPDO I, Thm 7.7.5; Stein, Harmonic Analysis, Ch. VIII, Prop. 3) for n = 2.

## Cases (fixed now)
Amplitude a(x, y) = b(x) b(y), b(s) = exp(−1/(1 − s²)) on (−1, 1), 0 outside, unless stated. Domain [−1, 1]².
- C1 elliptic, sgn = +2: Ψ = x² + 2y² + 0.3x³ + 0.2xy² (k₀ = 0, H = diag(2, 4)).
- C2 hyperbolic, sgn = 0: Ψ = x² − 3y² + 0.4x²y (k₀ = 0, H = diag(2, −6)).
- C3 negative definite, sgn = −2: Ψ = −(x² + xy + y²) + 0.25x⁴ (k₀ = 0, H = [[−2, −1], [−1, −2]], det 3).
- C4 shifted critical point and non-even amplitude: Ψ = (x − 0.2)² − 2(y + 0.1)² + 0.3(x − 0.2)³ + 0.7,
  a(x, y) · (1 + 0.5x + 0.3y) (k₀ = (0.2, −0.1); checks e^{imΨ(k₀)} and A(k₀) evaluated at k₀, not at 0).
- C5 control that must FAIL the leading-term check: C1 with the phase factor e^{iπ sgn/4} replaced by 1.
In every case the critical point is unique in [−1, 1]² (checked by the program on a 401 × 401 grid of |∇Ψ| with a
lower bound away from k₀).

## Method (fixed now)
Trapezoid rule on [−1, 1]² with n × n panels, n = 4096 (and n = 8192 for the convergence check), f64, summation in
row order (the integrand vanishes to all orders on the boundary, so the trapezoid rule converges faster than any power
once π/h exceeds the largest frequency m·max|∇Ψ| ≈ 2600 at m = 640; π/h = 6434 at n = 4096; Simpson's rule was
considered and rejected before the run because its error term is O(1) at m = 640 with this n); m ∈ {10, 20, 40, 80, 160, 320, 640}. Quadrature error is estimated as |I_n − I_{2n}| and must
be below 10⁻³ · |R(m)| for every reported m (otherwise that m is reported as UNRESOLVED and excluded, with the count
stated).

## Criteria (fixed now)
For C1–C4, with R(m) = I(m) − leading term:
- (i) leading term: |R(m)| / |leading term| < 0.05 at m = 640;
- (ii) order: the least-squares slope of log|R(m)| against log m over the resolved m ≥ 40 lies in [−2.2, −1.8];
For C5: criterion (i) must fail (|R(640)| / |leading| > 0.5), otherwise the check cannot detect a wrong phase factor and
the whole run is reported as NOT DISCRIMINATING.
Overall PASS iff C1–C4 pass (i) and (ii) and C5 fails (i). Any other outcome is reported as it is, with the numbers,
and the statement draft is revised before freezing (the revision cites this record).

## Program
`numerics/src/bin/spleading.rs` (Rust, no dependencies; `cargo run --release --bin spleading`), output saved verbatim
to `numerics/results-spleading-2026-11-08.txt`.
