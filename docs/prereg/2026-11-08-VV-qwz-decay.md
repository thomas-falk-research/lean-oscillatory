# Pre-registration: decay rate of the QWZ (m = 3) propagator kernel (batch VV model statement)

Registered 2026-11-08 (session 7), before the program `numerics/src/bin/qwz_decay.rs` exists and before any Lean
statement of batch VV exists. Numerics are tooling, never evidence (README). Purpose: the planned model statement says
`sup_x ‖G(t, x)‖ ≤ C t^{−5/6}` for `t ≥ 1`, from the classification "nondegenerate or fold everywhere"
(`numerics/results-classify-vv-2026-11-08.txt`) and GD-F. This check tests the rate before it is frozen. Changing the
protocol after the run is a new registration; the first run's output is kept.

## Objects (fixed now)
- `H(k) = sin k₁ σ_x + sin k₂ σ_y + (m + cos k₁ + cos k₂) σ_z`, m = 3; `ω(k) = |d(k)|`, `ω² = 11 + 6(c₁ + c₂) + 2c₁c₂`.
- `U(t, k) = cos(tω) 1 − i (sin(tω)/ω) H(k)` (= e^{−itH(k)}, since H² = ω² 1).
- `G(t, x) = ∫_{[−π, π]²} e^{i x·k} U(t, k) dk` for x ∈ ℤ² (2×2 complex matrix); norm: max over the four entries of |G_ij|.
- Controls: (L) the scalar lattice Laplacian kernel `∫ e^{i(x·k − t(c₁ + c₂))} dk` (known rate t^{−2/3}); (S) the
  separable-band trap, `H_S(k) = (c₁ + c₂) σ_z + 0.5 σ_x`, with U and G as above (critical curve; expected slower decay).

## Method (fixed now)
G(t, ·) on the N × N grid of x by the inverse 2D DFT of the samples of e^{...}U(t, k) at k = −π + 2πj/N (trapezoid rule
on the torus, spectrally accurate), N = 1024, radix-2 FFT written in the program, f64. Accuracy check at the largest t:
recompute with N = 2048; the max over x of the entrywise difference must be below 1e−8, else UNRESOLVED.
`sup_x` is the max over the grid x ∈ [−N/2, N/2)²; the program reports the max |x|∞ at which the sup is attained, which
must be below N/2 − 32 (no aliasing near the edge), else UNRESOLVED.
Times: t ∈ {1, 1.5, 2, 3, 4, 6, 8, 11, 16, 23, 32, 45, 64}.

## Criteria (fixed now)
- (a) **rate**: least-squares slope of log sup_x ‖G(t, x)‖ against log t over t ∈ [8, 64] lies in [−0.92, −0.75]
  (predicted −5/6 ≈ −0.833).
- (b) **bounded profile**: over t ∈ [8, 64], max / min of t^{5/6} sup_x ‖G‖ is at most 3.
- Controls that must be distinguished, else NOT DISCRIMINATING: the slope for (L) over t ∈ [8, 64] lies outside
  [−0.92, −0.75] (it should be near −2/3); the slope for (S) lies outside [−0.92, −0.75].
Overall PASS iff (a), (b), both controls outside, and no UNRESOLVED. The sup bound's constant is reported, no criterion.

## Program
`numerics/src/bin/qwz_decay.rs` (Rust, no dependencies), output saved verbatim to
`numerics/results-qwz-decay-2026-11-08.txt`.
