# Route: batch LE2 (T0E′, T6E′)

Lead, session 10, after the pre-proof reviews were answered (`review/2026-11-10-LE2-pre-proof-answers.md`).
Blueprint: `Blueprint/LatticeCubeRoot.lean` (one `…Facts` proposition per part). Assembly:
`OscInt/Front/LatticeCubeRootAssembly.lean`, compiled against the blueprint before any part is proved. Every Mathlib name
below was `#check`ed at the pin and is added to `MathlibNames.lean`.

Mathematics: `docs/statements.md`, Batch LE2 (route sketch), and the lead's re-derivation in
`review/2026-11-10-external-followup-answers.md` (Result 1). Notation: `I(t, ξ) = latticeKernel1 t ξ`,
`J(a, b) = ∫_a^b e^{i(t cos k + ξk)} dk`, `g(k) = ξ − t sin k` (the phase derivative), `v = ξ/t`, `C* = 8(1 + √7)/3`.
Every bound is proved for `ξ = t·v` with `v ≥ 0`; symmetry gives `ξ < 0`.

## Parts

- **P-ibp** `IbpFacts` (general, any phase). For `a ≤ b`, `φ′ = g` and `g′` on `[a, b]` (`HasDerivAt` at every point of
  `Icc a b`, `g′` continuous on it) and `g ≠ 0` there:
  `‖∫_a^b e^{iφ}‖ ≤ 1/|g a| + 1/|g b| + ∫_a^b |g′|/g²`.
  The function `F(x) = e^{iφ(x)}/(i g(x))` has derivative `e^{iφ} − e^{iφ} g′/(i g²)`
  (`HasDerivAt.cexp`, `HasDerivAt.ofReal_comp`, `HasDerivAt.div`); `intervalIntegral.integral_eq_sub_of_hasDerivAt`
  (integrability from continuity, `ContinuousOn.intervalIntegrable`), `norm_sub_le`, `norm_add_le`,
  `intervalIntegral.norm_integral_le_integral_norm`, `Complex.norm_exp_ofReal_mul_I`.
- **P-var** `VarFacts` (the lattice phase). For `0 < t`, `a ≤ b`, `g ≠ 0` on `[a, b]`:
  on `[a, b] ⊆ [−π/2, π/2]`, `∫_a^b |t cos k|/g² = 1/g b − 1/g a`; on `[a, b] ⊆ [π/2, 3π/2]` or `⊆ [−3π/2, −π/2]`,
  it is `1/g a − 1/g b`. The derivative of `1/g` is `t cos k/g²` (`HasDerivAt.inv`, `Real.hasDerivAt_sin`); the sign of
  `cos` (`Real.cos_nonneg_of_mem_Icc`, `Real.cos_nonpos_of_pi_div_two_le_of_le`, and `cos (k + 2π) = cos k` for the
  negative interval); `intervalIntegral.integral_congr` to drop the absolute value; FTC.
- **P-band** `BandLowFacts`, `BandHighFacts`. With `p = arcsin(v − δ)`, `q = arcsin(v + δ)`, `0 < t`, `0 < δ`,
  `−1 < v − δ`, `v + δ < 1`:
  - `v ≤ δ` (so `p ≤ 0`): split `[−π, π]` at `−π − p, p, q, π − q` (`intervalIntegral.integral_add_adjacent_intervals`);
    `[−π, −π − p]`, `[p, q]`, `[π − q, π]` by their lengths (`intervalIntegral.norm_integral_le_of_norm_le_const`; total
    `2(q − p)`); `[−π − p, p]` (`g ≥ tδ`, turning point `−π/2`) and `[q, π − q]` (`g ≤ −tδ`, turning point `π/2`) by
    P-ibp with the variation split at the turning point by P-var. Result:
    `‖I‖ ≤ 2(q − p) + 8/(tδ) − 4/(t(1 − v²))`.
  - `δ ≤ v`, `0 < v` (so `p ≥ 0`): split at `p, q, π − q, π − p`; `[−π, p]` (turning point `−π/2`), `[q, π − q]`,
    `[π − p, π]` by P-ibp and P-var; the two bands by length. Result: the same plus `2/(tv)`.
  - The values `g(p) = tδ`, `g(q) = −tδ`, `g(±π) = tv`, `g(∓π/2) = t(v ± 1)` from `Real.sin_arcsin`, `Real.sin_pi_sub`,
    `Real.sin_neg`; the sign of `g` on each piece from the monotonicity of `sin` on `[−π/2, π/2]`
    (`Real.strictMonoOn_sin`) and `sin (π − x) = sin x`.
- **P-cap** `CapLowFacts`, `CapHighFacts`, `WholeFacts`.
  - `v ≤ δ`, `−1 < v − δ`: the set `g ≤ tδ` has length `π − 2p` and the rest `[−π − p, p]` is one positive piece:
    `‖I‖ ≤ π − 2p + 4/(tδ) − 2/(t(1 + v))`.
  - `0 ≤ v − δ < 1`, `0 < v`: `‖I‖ ≤ π − 2p + 4/(tδ) + 2/(tv(v + 1))`.
  - `1 < v`: `g > 0` on `[−π, π]`; P-ibp on the whole interval, P-var split at `±π/2`:
    `‖I‖ ≤ 2/(t(v − 1)) + 2/(tv(v + 1))`.
- **P-arc** (real analysis only; no integrals; lemmas inside the P-r8 and P-r38 part files, not separate `…Facts`).
  1. Chord through 0: `0 ≤ y ≤ b ≤ 1`, `0 < b` ⇒ `arcsin y ≤ (y/b) arcsin b`. From `strictConcaveOn_sin_Icc` (with
     `sin 0 = 0`): `sin(λu) ≥ λ sin u` for `u = arcsin b`, `λ = y/b`; then `Real.arcsin_le_iff_le_sin`.
  2. Rational arcsine bounds: `arcsin(3/4) ≤ 6/7`, `arcsin(7/8) ≤ 11/10`, `arcsin(1/4) ≤ 1/3` from `Real.sin_ge_sub_cube`
     and `Real.arcsin_le_iff_le_sin`; `1/8 ≤ arcsin(1/8)` from `Real.sin_le`; `arcsin(√2/2) = π/4`
     (`Real.sin_pi_div_four`, `Real.arcsin_sin`).
  3. Square-root comparison (regime 2.2): `1/8 ≤ x ≤ y ≤ 1` ⇒ `arcsin y − arcsin x ≤ (4√2/3)(√(1 − x) − √(1 − y))`:
     `s ↦ arcsin s + (4√2/3)√(1 − s)` is antitone on `[1/8, 1]` (`antitoneOn_of_deriv_nonpos`, `Real.hasDerivAt_arcsin`,
     `Real.hasDerivAt_sqrt`): its derivative `(1 − s)^{−1/2}((1 + s)^{−1/2} − 2√2/3) ≤ 0` since `1 + s ≥ 9/8`.
  4. Window monotonicity (regime 2.3): `h(s) = (1 − s²)^{−1/2}` has `h′(s) = s(1 − s²)^{−3/2}`, which is monotone on
     `(−1, 1)` (elementary by sign cases), so for fixed `w ≥ 0`, `s ↦ h(s + w) − h(s)` is monotone
     (`monotoneOn_of_deriv_nonneg`). Hence (`MonotoneOn.convexOn_of_deriv`):
     `v ↦ 2(arcsin(v + δ) − arcsin(v − δ))/τ + 2τ²/v` is convex on `[δ, 1/2]` (`δ ≤ 3/8`), so it is at most its larger
     end value (`ConvexOn.le_max_of_mem_Icc`); and `Q(d) = arcsin(1/2 + d) − arcsin(1/2 − d)` is convex on `[0, 3/8]`
     with `Q(0) = 0`, so `Q(d) ≤ (8d/3) Q(3/8)` (the definition of `ConvexOn`).
  5. The decreasing function of regime 2.2: for `Δ ≥ 2`,
     `(8√2/3)(√(Δ + 3/2) − √(Δ − 3/2)) − 2/Δ ≤ (8/3)(√7 − 1) − 1` (`antitoneOn_of_deriv_nonpos` on `[2, ∞)`, the
     rationalisation bound of the derivative).
- **P-r8** `Regime8Facts`: `8 ≤ t`, `0 ≤ v` ⇒ `‖I(t, tv)‖ ≤ C* t^{−1/3}`. With `τ = t^{−1/3}` (`t τ³ = 1`, `τ ≤ 1/2`):
  `v ≥ 1 − 2τ²` by P-cap (`δ = 2τ²`, or P-cap whole when `v − δ ≥ 1`) and P-arc 1–2 (`arcsin(√2τ) ≤ πτ/2`);
  `1/2 ≤ v < 1 − 2τ²` by P-band high (`δ = (3/2)τ²`), P-arc 3 and P-arc 5 (the extremal regime, equality at `Δ = 2`);
  `0 ≤ v ≤ 1/2` by P-band (both forms, `δ = (3/2)τ²`), P-arc 1, 2 and 4 (`max(191/21, 277/30) < 97/10 < C*`).
- **P-r38** `Regime38Facts`: `3 ≤ t ≤ 8`, `0 ≤ v`, `δ = 1/2`: P-cap high or whole (`v ≥ 1/2`: `π + 32/(3t)`), P-cap low
  (`1/4 ≤ v ≤ 1/2`: `π + 2/3 + 20/(3t)`), P-band low (`v ≤ 1/4`: `50/21 + 12/t`), each term of each bound taken at its own
  worst `v` in the sub-range (no joint monotonicity in `v` is needed; pre-proof review A, finding 5). This is the
  tightest step of the route (`t = 3`, `v ↓ 1/2`: `3^{1/3}(π + 32/9) ≈ 9.659 < 97/10`; pre-proof answers, finding 4); with `s = t^{1/3} ∈ [3^{1/3}, 2]`, `As + Bs^{−2}` is convex (`convexOn_zpow`), so its
  maximum is at an end (`ConvexOn.le_max_of_mem_Icc`); the six end values are below `97/10`.
- **P-sym** `SymFacts`: `I(t, −ξ) = I(t, ξ)` (`intervalIntegral.integral_comp_neg`, `Real.cos_neg`).

## Assembly (lead)
- **T0E′** from P-sym, P-r8, P-r38: reduce to `ξ ≥ 0`, put `v = ξ/t`; `t ≥ 8` and `3 ≤ t ≤ 8` by the regimes;
  `0 < t ≤ 3` by `‖I‖ ≤ 2π` (`intervalIntegral.norm_integral_le_of_norm_le_const`) and
  `2π ≤ 2π·3^{1/3}·t^{−1/3} < C* t^{−1/3}` (`3^{1/3} < 13/9`, `π < 22/7`).
- **T6E′** from T6F (`OscInt.API.latticeKernelFactor`, proved) and T0E′: `norm_mul`, `mul_le_mul`, and
  `(t^{−1/3})² = t^{−2/3}` (`Real.rpow_natCast`, `← Real.rpow_mul`).

## Revision after the route referee (2026-11-11, at 41d91b2)
A fresh-context route referee read the route, the blueprint and the compiled assembly before any part was written. Its
verdict: all ten `…Facts` are true exactly as stated; Band, Cap and Whole follow from P-ibp and P-var with the stated
splits (it re-derived each piece and checked every sub-interval against the branch of P-var it uses); the assembly
proves exactly the frozen statements (a renamed copy compiles; axioms propext, Classical.choice, Quot.sound). One MAJOR
finding, six MINOR, one NIT; the lead's answers:
- **MAJOR, agreed: P-r38's band piece needs monotonicity in v as written.** For `0 ≤ v ≤ 1/4`, `δ = 1/2`, the term
  `arcsin(1/2 − v)` is worst at `v = 0` (`π/6`), so taking each summand at its own worst `v` gives `≈ 9.726 > C*` at
  `t = 3`; the value `50/21` assumed `v ↦ arcsin(v + δ) − arcsin(v − δ)` increasing. Pre-proof referee A had said this
  (finding 5) and the lead's answer was wrong; corrected in `review/2026-11-10-LE2-pre-proof-answers.md`. **Fix:** split at
  `v = 1/8`. On `[0, 1/8]`: `2(arcsin(5/8) + arcsin(1/2)) + 12/t` with `arcsin(5/8) ≤ 17/25` (`Real.sin_ge_sub_cube`) and
  `arcsin(1/2) = π/6 < 11/21`; on `[1/8, 1/4]`: `2(arcsin(3/4) + arcsin(3/8)) + 12/t` with `arcsin(3/8) ≤ 2/5`. End values
  `43732/4725, 4103/525, 988/105, 281/35`, all `< 97/10` (`numerics/review/le2_interface_checks.py` E1, exact). No
  derivative is needed.
- **MINOR, agreed: P-r8 for `0 ≤ v ≤ δ`.** By the chord bound (P-arc 1, `b = 3/4`) on each summand,
  `2(arcsin(v + δ) + arcsin(δ − v))/τ ≤ (8/7)·2·(2δ)/τ = (48/7)τ`; with `−4τ²/(1 − v²) ≤ −4τ²` the total is
  `≤ (48/7)τ + 16/3 − 4τ²`, increasing in `τ ≤ 1/2`, so `≤ 24/7 + 13/3 = 163/21 < 97/10`. No convexity there.
- **MINOR, agreed: the cap step for `v ≥ 1 − 2τ²`.** `π − 2 arcsin(v − δ) ≤ 4 arcsin(√2 τ)` when `v − δ ≥ 1 − 4τ²`: with
  `u = arcsin(√2 τ) ∈ [0, π/4]`, `sin(π/2 − 2u) = cos 2u = 1 − 4τ²` (`Real.cos_two_mul` or `Real.cos_sq'`,
  `Real.sin_pi_div_two_sub`), then `Real.le_arcsin_iff_sin_le`; and `arcsin(√2τ) ≤ πτ/2` by the chord with
  `b = √2/2`. Names added to `MathlibNames.lean`.
- **MINOR, adopted: P-arc 5 without derivatives.** With `S(Δ) = √(Δ + 3/2) + √(Δ − 3/2)`, the first term of `F` is
  `8√2/S(Δ)`; `S(Δ)²/Δ = 2 + 2√(1 − 9/(4Δ²)) ≥ S(2)²/2` for `Δ ≥ 2`; with `x = √(2/Δ) ∈ (0, 1]` and
  `A = (8/3)(√7 − 1) = 8√2/S(2)`, `F(Δ) ≤ Ax − x² ≤ A − 1` since `(1 − x)(A − 1 − x) ≥ 0` (`A ≥ 2`).
- **MINOR, adopted: P-arc 4 on `[0, 1)` only.** Every use has its lower argument `≥ 0`, so `h′(s) = s(1 − s²)^{−3/2}` is
  needed only on `[0, 1)`, where it is a product of nonnegative increasing factors. The referee checked that convexity in
  `v` cannot be avoided cheaply for `v ∈ [δ, 1/2]`, `t ≥ 8` (one first-derivative bound gives `10.32 > 97/10`).
- **MINOR, adopted: shared pieces.** The positive pieces `[−π − p, p]` (Band/Cap low), `[−π, p]` and `[π − p, π]`
  (Band/Cap high) and the length pieces are each proved once as a lemma and reused.
- **MINOR, done: interface numerics.** `numerics/review/le2_interface_checks.py` (record
  `numerics/results-le2-interface-checks-2026-11-11.txt`): Band, Cap and Whole against `|I(t, tv)|` at 7500 seeded points
  (no violation; tightest Whole, margin 0.005), P-var to 3e−12, the regime-3–8 band piece, and the exact steps above.
- **NIT, noted:** `BandLowFacts` omits `−1 < v − δ`, which follows from its hypotheses.

## The parts as proved (2026-11-11)
Proof agents wrote the parts in scratch after the route referee was answered (41d91b2 and its revision); the lead
integrated each (`lake build`, guard, `#print axioms`: propext, Classical.choice, Quot.sound; per-module `leanchecker`).
- P-ibp, P-var, P-sym: `OscInt/Front/LatticeCubeRootIbp.lean`, as routed (P-var's negative branch via `Real.cos_neg`).
- P-band, P-cap, P-whole: `OscInt/Front/LatticeCubeRootPieces.lean`, as routed, with the shared pieces proved once.
- P-r38: `OscInt/Front/LatticeCubeRootRegime38.lean`, with the referee's split at `v = 1/8` and the end-point argument by
  convexity of `As + Bs^{−2}` in `s = t^{1/3}`.
- P-r8: `OscInt/Front/LatticeCubeRootRegime8.lean`. **One deviation, in the sub-case `δ ≤ v ≤ 1/2`:** no convexity in
  `v`. Instead, arcsine is convex on `[0, 1]` (from `strictConcaveOn_sin_Icc`), so its window increments are monotone
  (`ConvexOn.secant_mono`): `arcsin(v + δ) − arcsin(v − δ) ≤ Q(δ)`; and `Q(d) ≤ (673/250) d` for `0 < d ≤ 3/8` from the
  chord on `[1/2, 7/8]` (`arcsin(7/8) ≤ 11/10`, `arcsin(1/2) = π/6`) and the tangent at `1/2`
  (`ConvexOn.slope_le_of_hasDerivAt`). Total `≤ (8.076τ − 4τ² + 20/3)τ ≤ 9.7047τ < C*τ`: this sub-case is now the
  tightest margin of the proof (≈ 0.017), uniform in `τ ∈ (0, 1/2]`. The `v ≤ δ` sub-case drops the negative term
  (`≤ (184/21)τ`). The other sub-cases are as routed; the extremal one gives exactly `C*τ`.
- Final: `OscInt/Front/LatticeCubeRootFinal.lean` (`OscInt.API.latticeKernel1CubeRoot`, `latticeLaplacianCubeRoot`),
  types asserted in `StatementTypes.lean`.
