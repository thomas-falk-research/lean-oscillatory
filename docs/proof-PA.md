# Proof route for batch PA (PA-C, PA-T, LC-1)

Written by the lead on paper before the blind pre-proof reviews were answered and kept outside the repository until
the answers were stamped (`stamps/20261116T152412Z-9c9a8767b806`, 2026-11-16 15:24:19Z; rule 1: no proof code before
that, and this file contains none). Committed after that stamp, with the blueprint section revised once (the alias
step became a part of its own, so that the lead's assembly is short). Statements: `docs/statements.md`, Batch PA;
Lean text `OscInt/Statements/PeriodicAnalytic.lean`. Mathlib names are `#check`ed at the pin in `MathlibNames.lean`
(section PA); a name this page says is absent is absent there. The mathematics is classical (Davis 1959;
Trefethen–Weideman 2014, section 3). Status of this page: a route on paper (L3 when refereed), not a proof record.

Notation: S_a the open strip, v periodic-analytic on S_a with bound M, a > 0. Write e_k(z) = e^{−ikz}.

## Part P-shift (the contour shift)
**Claim.** For every real b with |b| < a and every integer k,
`∫_0^{2π} v(θ) e_k(θ) dθ = ∫_0^{2π} v(θ + ib) e_k(θ + ib) dθ`.

*Proof.* g(z) = v(z) e_k(z) is complex-differentiable on S_a and g(z + 2π) = g(z) there (e_k has period 2π because k
is an integer: `Complex.exp_int_mul_two_pi_mul_I`). The closed rectangle with corners 0 and 2π + ib lies in S_a.
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` with z = 0, w = 2π + ib gives
`(∫_0^{2π} g(x) dx) − (∫_0^{2π} g(x + ib) dx) + i ∫_0^{b} g(2π + iy) dy − i ∫_0^{b} g(iy) dy = 0`,
and the last two integrals are equal by periodicity (the points iy, |y| ≤ |b|, are in S_a). ∎

## Part P-coeff (PA-C)
For k = 0 the bound is `|∫ v| ≤ 2πM` (`intervalIntegral.norm_integral_le_of_norm_le_const`; real points are in S_a).
For k ≠ 0 take 0 < b < a and shift by −sgn(k)·b: on the shifted line
`|v(θ − i sgn(k) b) e_k(θ − i sgn(k) b)| ≤ M · |e^{−ik(θ − i sgn(k) b)}| = M e^{−|k| b}` (`Complex.norm_exp`: the real part
of −ik(θ − i s b) is −k s b = −|k| b). Hence `|∫_0^{2π} v e_k| ≤ 2π M e^{−|k| b}` for every b in (0, a). The right-hand side
is continuous in b, so letting b ↑ a gives `≤ 2π M e^{−|k| a}` (in Lean: `le_of_tendsto` / `ge_of_tendsto` along b → a⁻,
or directly: for every ε, pick b with e^{−|k|b} ≤ e^{−|k|a} + ε). M ≥ 0 because 0 ∈ S_a.
Direction check (the paper's sentence after its (3.18) names the wrong direction for negative indices): for k > 0
the contour moves DOWN (b' = −b), because |e^{−ik(θ + ib')}| = e^{k b'}.

## Part P-series (the Fourier series of the restriction converges to it)
Let c_k = (2π)^{−1} ∫_0^{2π} v(θ) e^{−ikθ} dθ. By PA-C, |c_k| ≤ M e^{−a|k|}, summable over ℤ (two geometric series,
ratio e^{−a} < 1: `summable_geometric_of_lt_one`, `Summable.of_nat_of_neg_add_one` or `summable_int_iff_summable_nat_and_neg`).
The restriction θ ↦ v(θ) is continuous and 2π-periodic on ℝ, so it defines `f : C(AddCircle (2π), ℂ)`
(`Function.Periodic.lift`, continuity through the quotient map; compare Mathlib's Poisson-summation file). Its
Mathlib Fourier coefficients are `fourierCoeff f k = c_k` (`fourierCoeff_eq_intervalIntegral` with a = 0 and
`fourier_coe_apply`: `fourier (−k) θ = e^{2πi(−k)θ/(2π)} = e^{−ikθ}`). `has_pointwise_sum_fourier_series_of_summable` then
gives, for every real θ, `HasSum (fun k => c_k e^{ikθ}) (v θ)`.

## Part P-alias (PA-T)
For N ≥ 1 and θ_j = 2πj/N: `Σ_{j<N} e^{ikθ_j} = N` if N | k and 0 otherwise (a finite geometric sum of an N-th root of
unity: `Finset.geom_sum_eq` is not at the pin under that name; use `geom_sum_eq` / `mul_geom_sum` or
`IsPrimitiveRoot.geom_sum_eq_zero`; the route referee and the proof agent pick whichever `#check`s). Summing the N
pointwise series (finitely many `HasSum`s: `hasSum_sum`) gives
`Σ_{j<N} v(θ_j) = Σ_k c_k · (N if N | k else 0)`, that is `HasSum (fun m : ℤ => N · c_{mN}) (Σ_{j<N} v(θ_j))`
(reindex the multiples of N by m; injectivity of m ↦ mN and vanishing off its range: `Function.Injective.hasSum_iff`).
Hence `I_N = (2π/N) Σ_j v(θ_j) = 2π Σ_m c_{mN}` and `I = 2π c_0`, so
`|I_N − I| = 2π |Σ_{m ≠ 0} c_{mN}| ≤ 2π Σ_{m ≠ 0} M e^{−a|m|N} = 4πM Σ_{m ≥ 1} e^{−amN} = 4πM e^{−aN}/(1 − e^{−aN}) = 4πM/(e^{aN} − 1)`.
In Lean: split the ℤ-sum into m = 0, m ≥ 1 and m ≤ −1 (`HasSum.of_nat_of_neg_add_one`, or `hasSum_int_iff…`), bound the two
tails by `tsum_geometric_of_lt_one` with ratio r = e^{−aN} ∈ (0, 1): `Σ_{m ≥ 1} r^m = r/(1 − r) = 1/(e^{aN} − 1)`.

## Part P-lc (LC-1)
v_t(z) = e^{it cos z} is entire and 2π-periodic. With z = x + iy, `cos z = cos x cosh y − i sin x sinh y`
(`Complex.cos_add_mul_I`), so `|v_t(z)| = e^{t sin x sinh y} ≤ e^{|t| sinh |y|}`; on S_η (η > 0) this is at most
`e^{|t| sinh η}` (sinh is increasing). So v_t is periodic-analytic on S_η with bound e^{|t| sinh η}.
The kernel: `latticeKernel1 t n = ∫_{−π}^{π} e^{i(t cos k + nk)} dk`. The integrand is 2π-periodic in k (n is an integer),
so the integral over [−π, π] equals the integral over [0, 2π] (`Function.Periodic.intervalIntegral_add_eq`), which is
`∫_0^{2π} v_t(θ) e^{−i(−n)θ} dθ`. PA-C with k = −n gives `≤ 2π e^{|t| sinh η} e^{−η|n|}` for η > 0. For η = 0 the claim is
`|I(t, n)| ≤ 2π`, the trivial bound (integrand of modulus 1 on an interval of length 2π).

## Blueprint and assembly
`Blueprint/PeriodicAnalytic.lean` (definitions only):
- `ContourShiftFacts` (P-shift, for `PeriodicAnalyticOn v a M`, |b| < a, k : ℤ, with the shifted integrand written
  `v(θ + b i) · exp(−(k (θ + b i)) i)`);
- `FourierSeriesFacts` (P-series: for `PeriodicAnalyticOn v a M`, 0 < a, given the coefficient bound of PA-C for this
  v as a hypothesis, for every real x: `HasSum (fun k : ℤ => (2π)⁻¹ (∫_0^{2π} v e_k) · exp(i k x)) (v x)`);
- `AliasBoundFacts` (P-alias as a statement about sequences, with no integral in it: if 0 < a, N ≥ 1,
  `|c_k| ≤ M e^{−a|k|}` for all k : ℤ and `HasSum (fun k => c_k exp(i k 2πj/N)) (f j)` for every j < N, then
  `|N⁻¹ Σ_{j<N} f j − c_0| ≤ 2M/(e^{aN} − 1)`);
- `KernelIntegrandFacts` (P-lc's two facts: `PeriodicAnalyticOn (fun z => exp(t cos z · i)) η (exp(|t| sinh η))` for
  η > 0, and `latticeKernel1 t n = ∫_0^{2π} exp(t cos θ · i) · exp(↑(−((−n : ℤ) : ℝ) θ) i) dθ`, the shape PA-C takes).
Assembly `OscInt/Front/PeriodicAnalyticAssembly.lean`, by the lead, compiled before any part is proved:
- `fourierCoeffStrip_of : ContourShiftFacts → FourierCoeffStripStatement` (P-coeff);
- `trapezoidalRule_of : FourierCoeffStripStatement → FourierSeriesFacts → AliasBoundFacts → TrapezoidalRuleStatement`
  (c_k = (2π)⁻¹ ∫ v e_k, f j = v(2πj/N); `I_N − I = 2π (N⁻¹ Σ f j − c_0)`);
- `latticeKernel1LightCone_of : FourierCoeffStripStatement → KernelIntegrandFacts → LatticeKernel1LightConeStatement`.
Parts for proof agents: `ContourShiftFacts` (agent 1), `FourierSeriesFacts` (agent 2), `AliasBoundFacts` and
`KernelIntegrandFacts` (agent 3).

## Interface checks (numerical, run before the route referee)
`numerics/review/pa_kl_interface_checks.py`, results `numerics/results-pa-kl-interface-checks-2026-11-16.txt`: each
blueprint proposition tested on samples in the shape the blueprint states it, in ball arithmetic, with three
controls that must fail. 13 of 13 checks pass. They test the propositions, not their proofs (L2 on samples).

## Risks
- The AddCircle plumbing of P-series (lifting a periodic function to `C(AddCircle (2π), ℂ)` and matching Mathlib's
  normalisation of `fourierCoeff`) is the fiddliest step; fallback: prove P-alias directly from PA-C without the
  Fourier series, by the residue-free "discrete orthogonality" argument on trigonometric partial sums, is NOT
  available (it needs the series). No cheaper fallback is known; if P-series stalls, PA-C and LC-1 still stand.
- `IsPrimitiveRoot` API names for the geometric sum must be `#check`ed.

## Revision after the route referee (2026-11-16)

One fresh-context route referee (an AI agent of the same model family as the lead; its brief and report are not
recorded verbatim, rule 19) read this route, the blueprint and the assembly in a snapshot, before any part was
proved. Verdict: sound; no BLOCKER, no MAJOR; answers `review/2026-11-16-PA-KL-route-answers.md`. The text above is
unchanged; the corrections and additions are these.
1. P-alias, roots of unity: `IsPrimitiveRoot.geom_sum_eq_zero` does NOT fit. For ζ = e^{2πik/N} with
   1 < gcd(k, N) < N (for example N = 4, k = 2, ζ = −1) the order of ζ is N/gcd(k, N), and that lemma sums over
   `range` of the order, not over `range N`. Use `geom_sum_eq` or `mul_geom_sum` with ζ^N = 1 and the case split
   ζ = 1 or ζ ≠ 1. Only one implication is needed: ζ = 1 implies N ∣ k (`Complex.exp_eq_one_iff`), because a majorant
   supported on the nonzero multiples of N dominates in either case.
2. P-alias, the split of the sum over ℤ: "`hasSum_int_iff…`" is not a Mathlib name. The lemma with the route's shape
   is `HasSum.of_add_one_of_neg_add_one` (from the sums over n + 1 and over −(n + 1) to the sum over ℤ with the term
   at 0). `tsum_geometric_of_lt_one` is the sum from n = 0, so the shift to r/(1 − r) is one more step.
3. P-coeff, the limit b ↑ a: the lemma that applies is `ge_of_tendsto` (the assembly uses it), not `le_of_tendsto`.
4. Header: "Mathlib names are `#check`ed" was too strong for the two names this revision corrects; the names of
   items 1 and 2, as the referee confirmed them in the Mathlib sources, are added to `MathlibNames.lean` when the
   parts are integrated.
5. Interface checks: of the checks in the script, eight are for this batch (I1 to I4, two of them controls); the
   rest are for batch KL. I2 tests a truncated sum against a geometric tail: a proxy for `FourierSeriesFacts`, since a
   `HasSum` cannot be sampled. After the KL referee's findings the script has 17 checks; all pass.
6. Risks, first item, restated: there is no fallback for P-series. The alias identity needs pointwise convergence
   of the Fourier series at the nodes (or a residue theorem, which Mathlib does not have in usable form). If
   P-series stalls, PA-T stalls with it; PA-C and LC-1 do not depend on it.
7. Feasibility notes from the referee, for the parts: P-shift needs care only with casts (ℤ to ℝ to ℂ on the left,
   ℤ to ℂ on the right) and an `add_comm` on the vertical sides; P-series has the normalisation frictions listed in
   the proof brief (precedent: `Mathlib/Analysis/Fourier/PoissonSummation.lean`); P-lc is easy.

## Parts as integrated (2026-11-16)

Five proof agents (AI agents of the same model family as the lead), one per part, were launched together after the
route answers were committed (launch record with the SHA-256 of each brief: session log, 15:57:32Z). Each worked in
the lead's scratch from the blueprint, this route with its revision section and its brief, and wrote one Lean file;
none wrote in the repository. The lead recompiled each file, checked that its last theorem has the blueprint
proposition as its type, printed its axioms, and copied it in unchanged.

| Part | File | Lines | SHA-256 of the file as delivered | Deviations from the route (agent's report, in the lead's words) |
|---|---|---|---|---|
| P-shift `ContourShiftFacts` | `OscInt/Front/PeriodicAnalyticShift.lean` | 97 | 58d7685ab4973e4ce4d13aa5e873205872dbc87781b1d2d5feb70a7a8650ed16 | none in the mathematics; Cauchy on the rectangle and the cancellation are proved for a general periodic function and specialised at the end |
| P-series `FourierSeriesFacts` | `OscInt/Front/PeriodicAnalyticSeries.lean` | 106 | 691cc582938b538e5481a296e469cc21f0f2e4526cf184d0487f04682c31d57b | `M ≥ 0` is not needed (a summable majorant suffices); the coefficient lemma is stated for any periodic function |
| P-alias `AliasBoundFacts`, P-lc `KernelIntegrandFacts` | `OscInt/Front/PeriodicAnalyticAlias.lean` | 258 | d77c56234256554f109bd559a7271bf5474fb24890286fef8cdc3bcefc7146f8 | the roots-of-unity sum is used only off the multiples of N (`mul_geom_sum`, as the referee advised); the split of ℤ is made on the real majorant only; `M ≥ 0` is not needed; the periodic-analytic property of the kernel integrand holds for every real η |

Final theorems: `OscInt/Front/PeriodicAnalyticFinal.lean`. Checks by the lead at integration: `lake build` completed;
`#print axioms` of `OscInt.API.fourierCoeffStrip`, `trapezoidalRule`, `latticeKernel1LightCone`: propext,
Classical.choice, Quot.sound; `StatementTypes.lean` asserts the three types; `leanchecker` on each of the five PA
modules and on the blueprint module: exit code 0. Not yet done at this point: the post-proof reviews and the
isolated replay.
