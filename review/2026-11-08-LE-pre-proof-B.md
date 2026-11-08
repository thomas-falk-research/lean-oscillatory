ec9899adf7faf50bf64aab6d6a0d99d6e8a706b1

# Referee B: blind pre-proof review of batch LE (T0E, T6F, T6E)

**HEAD.** HEAD moved from af2a6e8 to ec9899a while I was reviewing (lessons 16). The three new commits (69b82f4, 68cddb1, ec9899a) touch only CI, `tools/` and `docs/design/vector-amplitudes.md`. `git diff --stat af2a6e8 HEAD` shows no reviewed file changed, so this review applies to af2a6e8 as briefed.

**Proofs.** I did not prove any of the three statements, not even in scratch. My work was:
- Lean checks of definitions and parsing.
- Lean compiles of extra planted copies against the sanity theorems.
- Two independent numerical computations: composite 16-node Gauss–Legendre, and composite Simpson with N = 200000.

No proof exists in the repository. The statement constants appear only in `Challenge/`, `OscInt/Front/LatticeExplicitSanity.lean` and `examples/api/Snippets.lean`. Scratch files are in `/tmp/refereeB/`.

## 1. Verdicts

| Statement | vs `docs/statements.md` | vs classical facts | TRUE? |
|---|---|---|---|
| T0E `LatticeKernel1ExplicitStatement` | FAITHFUL | Integer ξ: weaker than Landau (`B ≈ 40.4` against `2π·0.7858 ≈ 4.94`). Real ξ: Landau does not apply (see MINOR-1) | TRUE |
| T6F `LatticeKernelFactorStatement` | FAITHFUL | Fubini on `[−π, π]²` | TRUE for every real t |
| T6E `LatticeLaplacianExplicitStatement` | FAITHFUL; FAITHFUL-STRONGER than T6 (implies T6 with `C = (A+B)²`) | — | TRUE (also for every `0 < t`, see MINOR-2) |

### Elaboration, checked in Lean (`/tmp/refereeB/Parse.lean`)
- **Integrand.** `#print latticeKernel1` shows `∫ k in -π..π, exp (↑(t * cos k + ξ * k) * I)`. The cast is `Complex.ofReal` of the whole real phase, not `↑t * …`.
- **Orientation.** Since `-π ≤ π`, the oriented interval integral is the Lebesgue integral over `Ioc (-π) π`, which is also the integral over `Icc` (`intervalIntegral.integral_of_le`, `integral_Icc_eq_integral_Ioc`). Reversing the orientation would not change `‖·‖` in T0E or T6E, nor the product in T6F.
- **Exponents.** `-(1 : ℝ) / 3 = -(1/3)`, `-(2 : ℝ) / 3 = -(2/3)` and `-(1 : ℝ) / 2 = -(1/2)` all check by `norm_num`. The powers are `Real.rpow`, and `(2 : ℝ) ^ ((1 : ℝ) / 4)` is 2^{1/4}.
- **T0E at t = 0.** `(0 : ℝ) ^ (-(1 : ℝ) / 2) = 0` by `Real.zero_rpow`. So the hypothesis `0 < t` is necessary: at t = 0, ξ = 0 the left side is 2π and the right side is 0.
- **Measure.** `volume` on `ℝ × ℝ` is `volume.prod volume` by `rfl`. The casts `(x.1 : ℝ)` from ℤ in T6F are the same casts as in `latticeKernel`.
- **Uniformity.** Every constant is an explicit numeral; there is no `∃ C`. All of t, ξ and x are universally quantified.
- **Constant sizes.** A = 28.5410, B = 40.4086, A + B = 68.9496, (A + B)² = 4754.048. These match the docs and `latticeConst_bounds`.

### Classical facts, checked numerically
- **Bessel's integral.** The docstring identity `I(t, n) = 2π iⁿ Jₙ(t)` holds:
  - `I(3, 1) = 2.130370i = i·2π·J₁(3)`;
  - `I(3, 2) = −3.054201 = −2π·J₂(3)`.
- **Reduction for t < 0.** `I(−t, ξ) = conj I(t, −ξ)` (modelling choice 2) holds: checked at (3, 0.7).
- **T0E for real ξ** (`/tmp/refereeB/scan.py`). I scanned t from 0.01 to 300 over dense real ξ, with ξ near ±t for large t. The largest ratio `|I| / (A t^{−1/2} + B t^{−1/3})` was 0.0826, at (t, ξ) = (300, 295.25).

I found no counterexample to any of the three statements.

## 2. Derivability

### T0E from S1.2 and S1.3
The documented route works; I checked every step on paper.

- **Pieces.** Split at ±π/4 and ±3π/4. Use `φ = t·cos`, `φ' = −t·sin`, `φ'' = −t·cos`, `φ''' = t·sin`. Each is smooth, so `HasDerivOn` holds on every closed piece.
- **S1.2 pieces.** On `[−π, −3π/4]`, `[−π/4, π/4]` and `[3π/4, π]`, `|φ''| = t|cos k| ≥ t/√2 = μ`. The bound holds even on the closed piece; equality at ±π/4 is fine because the hypothesis is `μ ≤ |φ''|`. This gives `8/√(t/√2) = 8·2^{1/4}·t^{−1/2}` per piece, and 3 · 8 · 2^{1/4} = 24 · 2^{1/4}.
- **S1.3 pieces.** On `[−3π/4, −π/4]` and `[π/4, 3π/4]`, `|φ'''| = t|sin k| ≥ t/√2`. This gives `18·(t/√2)^{−1/3} = 18·2^{1/6}·t^{−1/3}` per piece, and 2 · 18 · 2^{1/6} = 36 · 2^{1/6}.
- **Amplitude.** `ψ = 1`, `ψ' = 0`. `sanity_amplitude_one` gives `AmplitudeOn` and `ampNorm = 1`.
- **Integrand match.** `oscInt (fun x => t * cos x + ξ * x) (fun _ => 1) a b` equals the `latticeKernel1` integrand up to `* 1`, with p = ξ.
- **Assembly.** The integrand is continuous, so `integral_add_adjacent_intervals` adds the five pieces, followed by the triangle inequality.

The route works for every μ > 0, so it covers every t > 0 with no lower threshold.

### T6F
TRUE for every real t, including t ≤ 0; no hypothesis is needed.
- The phase `t(cos k₁ + cos k₂) + (x₁k₁ + x₂k₂)` regroups as `(t cos k₁ + x₁k₁) + (t cos k₂ + x₂k₂)`.
- Then `ofReal_add`, `add_mul` and `exp_add` give a product `f k.1 * g k.2`.
- `MeasureTheory.setIntegral_prod_mul` (exists at the pin; signature checked) needs no integrability. Converting `Icc` to the interval integral finishes it.

### T6E from T0E and T6F, for t ≥ 1
It follows:
- `‖K‖ = ‖I₁‖‖I₂‖ ≤ (A t^{−1/2} + B t^{−1/3})²`;
- `t^{−1/2} ≤ t^{−1/3}` for t ≥ 1;
- `(t^{−1/3})² = t^{−2/3}` by `rpow_natCast` and `rpow_mul` with t ≥ 0.

No step fails.

## 3. Vacuity and usefulness

- **Nothing vacuous.**
  - T0E is a genuine decay bound and holds uniformly in real ξ.
  - T6E improves T6 by making the constant explicit.
  - T6F ties `latticeKernel1` to the frozen `latticeKernel`. Once T6F is proved, the values `I(t, n)` at integer n are determined up to one sign per t. So T0E at integer ξ is about the right object even against a mis-typed definition.
- **Downstream use.** For `e^{itH}` with `H = 2cos k₁ + 2cos k₂`, the ℓ¹ → ℓ^∞ norm is at most `4754.05/(4π²)·t^{−2/3} ≈ 120.4·t^{−2/3}` for t ≥ 1. For `e^{−itΔ}`, with time scale 2, it is about `75.9·t^{−2/3}` for t ≥ 1/2. The docs say the `(2π)^{−2}` factor, time scale and phase are omitted, as in T6.
- **What a user loses.**
  - Small t: the restriction is unnecessary (MINOR-2).
  - Non-integer x is not possible, because `latticeKernel` takes ℤ²; this is harmless since T0E itself is stated for real ξ.
- **Non-sharpness.** Modelling choice 3 describes the constants honestly as non-sharp; one comparison needs qualifying (MINOR-1). The "factor of at least 200" claim concerns integer x only, which is all T6E needs, and agrees with criterion (e): 1/0.0048 ≈ 208.

## 4. Sanity theorems and planted controls

The sanity theorems go through the statement constants (lessons 33). Their data separate the roles (lessons 17):
- `8^{−1/3} = 1/2` separates the two exponents;
- ξ = 1/2 is not an integer;
- x = (1, −2) has distinct coordinates;
- t = 1 sits at the threshold.

I compiled four more planted copies against copies of the real sanity theorems (`/tmp/refereeB/Plants.lean`):

| Plant | Effect on the statement | Sanity result |
|---|---|---|
| T0E constant `24 ↦ 23` (smaller) | conclusion strengthened | **rejected** (linarith, line 14) |
| T0E `0 < t ↦ 0 ≤ t` | statement becomes **FALSE** (t = 0, ξ = 0) | **accepted, not detected** |
| T6E `1 ≤ t ↦ 0 < t` | true strengthening | rejected, only because `le_rfl : 1 ≤ 1` no longer fits |
| T6E constant `(A+B)² ↦ (A+B)` | conclusion strengthened | rejected |

What the sanity theorems would miss:
- **Hypotheses restricted for T0E** (e.g. `0 < t ↦ 1 < t`) or loosened to `0 ≤ t`. The first is a provable weakening; the second makes the statement false and would show up only when the proof fails.
- **Any edit to the body of `latticeKernel1`.** The generator mutates only the `Statement` definitions. The unconditional `I(0, 0) = 2π` and `I(0, 1) = 0` pin the interval length and the ξk term, but not the `t·cos k` part:
  - `cos ↦ sin` leaves `|I(t, n)|` unchanged for integer n, since `J₋ₙ = (−1)ⁿJₙ`;
  - it makes T6F false when x₁ + x₂ is odd, which only the proof would catch;
  - a shift to `[0, 2π]` changes nothing at integer ξ.

The plants that matter most here are a loosened T0E hypothesis and a weakened `latticeKernel1` definition. A smaller constant is already caught, because the conclusions spell out the numerals.

## 5. Findings

There are no BLOCKER or MAJOR findings.

**MINOR-1.** Modelling choice 3 in `docs/statements.md` says: "at large t the truth is about 2π · 0.675 t^{−1/3} (Landau's constant 0.7858 is the sup over all t > 0), so B is about 9.5 times too large". This is true for integer ξ only. T0E quantifies `∀ t ξ : ℝ`, and for non-integer ξ, `I(t, ξ)` is not `2π i^ξ J_ξ(t)` (it is Anger-type), so Landau's bound does not apply.
- **Counterexample to the sup claim for real ξ:** (t, ξ) = (5.7972479262309164, 4.404) gives `|I| = 2.810911` and `t^{1/3}|I|/(2π) = 0.80366 > 0.785746`.
- Two methods agree to 1e−14 (Gauss–Legendre and Simpson). The integer-n maximum at the same t is 0.6809.
- Prereg criterion (c) tested integer n only, so it could not see this.
- T0E itself is unaffected: the ratio there is 0.082.
- **Suggested fix:** clarify that the 0.675/0.7858 comparison is for integer ξ, and that the real-ξ supremum is at least 0.8037.

**MINOR-2.** In T6E, `∀ (t : ℝ) (x : ℤ × ℤ), 1 ≤ t → … t ^ (-(2 : ℝ) / 3)`, the threshold costs nothing to drop. For 0 < t ≤ 1, `|K| ≤ 4π² ≈ 39.48 < 4754 ≤ (A+B)²·t^{−2/3}`, so the statement is true with `0 < t`. That would give the dispersive estimate for every t > 0 (with t < 0 by `K(−t, x) = conj K(t, −x)`). It matches T6, so this is not a fidelity issue. Suggest a consumer note or a follow-on corollary, not a re-freeze. The proof for t < 1 needs the trivial bound, not T0E.

**MINOR-3.** The `latticeKernel1Explicit_eight` docstring in `OscInt/Front/LatticeExplicitSanity.lean` says: "Not detected: a strengthened bound (e.g. smaller constants)". This is inaccurate: the `24 ↦ 23` plant is rejected, because the conclusion spells out the numerals and linarith has no sign fact for the rpow product. What is actually not detected is `0 < t ↦ 0 ≤ t` (accepted although the statement becomes false) and any change to the body of `latticeKernel1`. Suggest:
- add the `0 ≤ t` plant to the record;
- correct the docstring;
- optionally add a sanity value at t ≠ 0 that separates `cos` from `sin`.

**NIT-1.** The T6E-threshold plant (`1 ≤ t ↦ 2 ≤ t`) and my true strengthening `0 < t` are both rejected for the same reason: `le_rfl` stops matching. The record should not present the rejection as a fidelity test of the threshold.

**NIT-2.** The `latticeKernel1` docstring identity `2π iⁿ Jₙ(t)` is correct, checked numerically at n = 1 and 2 with t = 3.
