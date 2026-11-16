# Proof route for batch KL (KL-D, KL-C, KL-F)

Written by the lead on paper before the blind pre-proof reviews were answered and kept outside the repository until
the answers were stamped (`stamps/20261116T152412Z-9c9a8767b806`, 2026-11-16 15:24:19Z; rule 1; no proof code here).
Committed after that stamp, with the blueprint section revised once (two Facts instead of three: the weight and
summation-by-parts lemmas are internal to the core part). Statements: `docs/statements.md`, Batch KL; Lean text
`OscInt/Statements/KusminLandau.lean`. The proof is Landau's (1928) as rendered by Hiary–Patel–Yang (section 4) and
Elkies's notes: summation by parts with collinear weights. Status of this page: a route on paper (L3 when refereed),
not a proof record.

Notation: e(x) = e^{2πix}; d_n = c_{n+1} − c_n for n < N; E_n = e(c_n).

## Part K-reduce (k = 0)
Replace c_n by c_n − k·n: every E_n is unchanged (e(k n) = 1: `Complex.exp_int_mul_two_pi_mul_I` after casts), the
differences become d_n − k ∈ [λ, 1 − λ], monotonicity is unchanged. So assume k = 0.

## Part K-weights
For x ∈ (0, 1): `e(x) ≠ 1`, and with `ζ(x) = 1/(e(x) − 1)`:
`ζ(x) = −(1 + i cot(πx))/2`, hence (i) `|ζ(x)| = 1/(2 sin πx)`, (ii) `|1 + ζ(x)| = 1/(2 sin πx)`,
(iii) `ζ(x) − ζ(y) = (i/2)(cot πy − cot πx)`, so `|ζ(x) − ζ(y)| = |cot πx − cot πy|/2`.
(From `e(x) − 1 = e(x/2) · 2i sin(πx)`.) On (0, 1), cot(π·) is strictly decreasing, so for a monotone sequence
x_0, …, x_{N−1} in [λ, 1 − λ] the sum `Σ_{n=1}^{N−1} |cot πx_n − cot πx_{n−1}|` telescopes to `|cot πx_{N−1} − cot πx_0|`.

## Part K-abel (KL-D for N ≥ 1, k = 0)
`E_n = ζ(d_n)(E_{n+1} − E_n)` for n < N. Therefore
`Σ_{n=0}^{N} E_n = E_N + Σ_{n=0}^{N−1} ζ(d_n)(E_{n+1} − E_n)
               = (1 + ζ(d_{N−1})) E_N − ζ(d_0) E_0 − Σ_{n=1}^{N−1} (ζ(d_n) − ζ(d_{n−1})) E_n`
(summation by parts; `Finset.sum_range_by_parts` or a direct induction on N, which is cleaner here). With |E_n| = 1:
`|S| ≤ 1/(2 sin πd_{N−1}) + 1/(2 sin πd_0) + |cot πd_{N−1} − cot πd_0|/2`.
If d is nondecreasing: cot πd_0 ≥ cot πd_{N−1}, and the bound is
`(1/2)(1/sin πd_0 + cot πd_0) + (1/2)(1/sin πd_{N−1} − cot πd_{N−1}) = (1/2) cot(πd_0/2) + (1/2) tan(πd_{N−1}/2)`
(half-angle identities `1/sin x + cot x = cot(x/2)`, `1/sin x − cot x = tan(x/2)` for 0 < x < π).
Since λ ≤ d_0 and d_{N−1} ≤ 1 − λ: `cot(πd_0/2) ≤ cot(πλ/2)` and `tan(πd_{N−1}/2) ≤ tan(π(1 − λ)/2) = cot(πλ/2)`.
So |S| ≤ cot(πλ/2). If d is nonincreasing the roles of d_0 and d_{N−1} swap and the same bound results.
N = 0: |S| = 1 ≤ cot(πλ/2) because πλ/2 ≤ π/4.

## Part K-two (KL-C from KL-D)
`cot x ≤ 1/x` for 0 < x ≤ π/2 (from `x ≤ tan x`: `Real.lt_tan` for 0 < x < π/2; at x = π/2, cot = 0). With x = πλ/2:
`cot(πλ/2) ≤ 2/(πλ)`.

## Part K-deriv (KL-F from KL-D)
Let m = ⌈a⌉, M = ⌊b⌋. If m > M the sum is empty. Otherwise put c_j = f(m + j), 0 ≤ j ≤ N := M − m (reindex
`Finset.Icc m M` by j ↦ m + j). For j < N, [m + j, m + j + 1] ⊆ [a, b], f is continuous on it and differentiable in its
interior, so by the mean value theorem (`exists_hasDerivAt_eq_slope`) d_j = f′(ξ_j) with ξ_j ∈ (m + j, m + j + 1) ⊆ (a, b);
hence d_j ∈ [k + λ, k + 1 − λ], and ξ_j < ξ_{j+1} gives the monotonicity of d from that of f′ on (a, b). Apply KL-D.

## Blueprint and assembly
`Blueprint/KusminLandau.lean` (definitions only):
- `KLCoreFacts` (KL-D with k = 0: K-weights and K-abel; the weight identities and the summation-by-parts identity are
  lemmas inside this part);
- `KLDerivFacts` (`KusminLandauStatement → KusminLandauDerivStatement`: K-deriv).
Assembly `OscInt/Front/KusminLandauAssembly.lean`, by the lead, compiled before any part is proved:
- `kusminLandau_of : KLCoreFacts → KusminLandauStatement` (K-reduce);
- `kusminLandauTwoOverPi_of : KusminLandauStatement → KusminLandauTwoOverPiStatement` (K-two);
- `kusminLandauDeriv_of : KLDerivFacts → KusminLandauStatement → KusminLandauDerivStatement`.
Parts for proof agents: `KLCoreFacts` (agent 1), `KLDerivFacts` (agent 2).

## Interface checks (numerical, run before the route referee)
`numerics/review/pa_kl_interface_checks.py`, results `numerics/results-pa-kl-interface-checks-2026-11-16.txt`: each
blueprint proposition tested on samples in the shape the blueprint states it, in ball arithmetic, with three
controls that must fail. 13 of 13 checks pass. They test the propositions, not their proofs (L2 on samples).

## Revision after the route referee (2026-11-16)

One fresh-context route referee (an AI agent of the same model family as the lead; its brief and report are not
recorded verbatim, rule 19) read this route, the blueprint and the assembly in a snapshot, before any part was
proved. Verdict: sound after corrections; no BLOCKER, no MAJOR; answers `review/2026-11-16-PA-KL-route-answers.md`.
The text above is unchanged; the corrections and additions are these.
1. K-deriv, empty sum (m > M): this case is not an instance of KL-D (`expSum` always has at least one term). The bound
   is then `0 ≤ cos(πλ/2)/sin(πλ/2)`, true because `0 < πλ/2 ≤ π/4`. One extra branch in Lean.
2. K-weights and K-abel, feasibility. Mathlib at the pin has no monotonicity lemma for `Real.cot` and no half-angle
   lemma in the form `1/sin x ± cot x`. The part therefore works with `cos/sin` throughout (the frozen right-hand
   side is written that way): the two brackets are `(1 + cos πd)/(2 sin πd)` and `(1 − cos πd)/(2 sin πd)`; signs of
   differences come from `cos x / sin x − cos y / sin y = sin(y − x)/(sin x · sin y)` (`Real.sin_sub`); the final
   comparisons from `Real.sin_two_mul`, `Real.cos_two_mul` at half the angle, or through `Real.strictMonoOn_tan` and
   `Real.tan_pi_div_two_sub`. For the weight, `Re ζ = −1/2` and `Im ζ = −cos πx/(2 sin πx)` follow from
   `ζ · (e(x) − 1) = 1`. The summation by parts is proved by induction, stated for `N + 1` so that no natural
   subtraction appears; `Finset.sum_range_by_parts` is in a scalar-action, partial-sum form that fits badly.
3. K-deriv, reindexing: `Int.Icc_eq_finset_map` turns `Finset.Icc m M` into the image of
   `Finset.range (M + 1 − m).toNat` under `j ↦ m + j`, then `Finset.sum_map`; only `ξ_n ≤ ξ_{n+1}` for `n + 1 < N` is
   needed for `DiffsMonotoneIn`.
4. K-two: the end-point remark (x = π/2) is not used; `x = πλ/2 ≤ π/4`.
5. Interface checks: the referee found that the first version tested the core proposition and its internal lemmas
   but not `KLDerivFacts`, and never sampled the ends of the cell, where the bound is attained. The script now has
   boundary-heavy sequences, Landau's sequences (ratio 1 at λ = 1/3, 1/5, 1/7, 3/7, 1/2) and a check J5 of the
   derivative form with its own control: 17 of 17 checks pass (the section above says 13 of 13, the count before
   this revision).
