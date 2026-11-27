<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch TRI: answers to the route referee (2026-11-27)

Written by the lead. The route referee read `docs/proof-TRI.md` as of 8d07a15, after the answers to the blind
pre-proof reviews were stamped (`stamps/20261127T070956Z-e692d7e55078`). It ran in a fresh context, of the lead's
model family; harness 972 s, 37 tool uses. Brief SHA-256 7158a6353b8d971cde39f66d32c697f05c7bf0a4478b1debbb78e6bf083fdeb4.
It compiled probes in its own scratch, one Lean process at a time, and wrote nothing in the repository. The report is
not reproduced; findings are in the lead's words.

**Verdict: proceed after changes. No FATAL and no MAJOR finding.**

What it re-derived independently, in SymPy from the phase itself rather than from the sanity layer's forms:
- the explicit derivative forms;
- the identities I1 to I7, with remainder 0 modulo the circle relations;
- cross-checks: the resultant of E and G in P is `4Q²(Q − 1)(2Q − 1)F`, and F has real roots 0.1106 and 0.9813;
- the boundary cases;
- the exhaustiveness of the case analysis. `c = d = 0` cannot occur on D = 0. With cd ≠ 0, V ≠ 0 because
  `V₁ + V₂ = 2cd`. The kernel is spanned by V through `D²[z, W] = −z₁ cos x + z₂ cos y`, with `V = (cos y, cos x)`;
- the invariance step;
- the locus extraction for both signs of α;
- the bridge's derivatives (series check at α = 1/4: `g⁗(0) = −6 = Qinv/D²[w, w]`);
- every step of the witness: `δ⁽⁴⁾(0) = 3/α` and `g⁽⁶⁾(0) = ∓60√2`. The series solution of the reduced curve is
  `h = ∓(u²/2 + u⁴/3 + 49u⁶/180)`, which agrees with blind referee A's;
- the values of TRI-Q.

On fidelity, the assembly of section 7 proves the four statements as written. The `FoldOrNondeg` conversion is
available in a proof module (`OscInt.API.dd_iteratedFDeriv`, `ddd_iteratedFDeriv`).

It found every Mathlib name the plan needs at this toolchain. Compiled probes:
- the sign value;
- smoothness of `arcsin ∘ z`;
- the bump construction;
- Leibniz by `iteratedDeriv_fun_mul`;
- `EventuallyEq.iteratedDeriv_eq`;
- the fourth derivative of `sin⁴` at 0, which is 24;
- the curried chain rule along a curve;
- `iter4_eq`;
- full symmetry of D³ for analytic functions.

| # | Severity, section | Finding (lead's words) | Answer |
|---|---|---|---|
| M1 | MINOR, 4 and risks | The stated risk is misplaced. Mathlib's full permutation symmetry needs analyticity (`ContDiffAt 𝕜 ω`), but the bridge needs only symmetry of orders 2 and 3: D⁴ appears only as `D⁴[v⁴]`. Those already exist in a proof module: `OscInt.API.DerivAux.symm2`, `symm3`, `iter3_eq`. | Accepted. Route section 9, item 1. The bridge stays general, for `ContDiff ℝ ∞`. |
| M2 | MINOR, 4 step 4 | The fixed-slot chain rule does not by itself cover A′, A″ and A‴, whose slots hold γ′(u) and γ″(u). Expand the slots multilinearly (`γ′ = v + h′w`, `γ″ = h″w`) into fixed-slot evaluations along γ times scalar functions of u. Then use one chain-rule lemma, the curried form with `HasDerivAt.clm_apply`, which needs `set_option maxSynthPendingDepth 2`. | Accepted. Route section 9, item 2, and the bridge brief. |
| M3 | MINOR, missing | The owed bite `¬ IsA5Point (triPhase (1/4)) (π/2, π/2)` and the plant re-runs are not in the route. The bite follows from TRI-X in three lines and needs no uniqueness of the reduced curve, because the bridge holds for every reduced curve. That contradicts answer A2 of `review/2026-11-27-TRI-preproof-answers.md`. | Accepted: answer A2's "needs the uniqueness of the reduced curve" was wrong. The bite is in the assembly (`quarter_halfPi_not_isA5_of`, compiled against the blueprint). The plant re-runs are route section 9, item 3. |
| M4 | MINOR, 1 and 8 | I1 to I5 hold only modulo the circle relations, so `linear_combination` needs explicit cofactors, and polyrith is not available offline. The cofactors are small. | Accepted. The P-alg brief carries the lead's SymPy scripts, so the agent computes cofactors by Gröbner reduction. |
| M5 | MINOR, 5 | TRI-K needs the witness at every shifted locus point, so the device must be fixed. Recommended: `x₀ = σθ + 2πj₁`, `y₀ = −x₀ + 2π(j₁ + j₂)`, `w = (σ, −σ)`, one base curve. Cheaper alternative: invariance of `IsA5Point` under translations and swaps that preserve Ψ. | Accepted. The interface `WitA5` is stated over all of `InLocus`, and the device is the part agent's choice between these two, named in the brief. |
| N1 | NIT, 2 | The lemma "the Hessian is not zero" is never used; each case has its own witness for `∃ v w, dd ≠ 0`. | Agreed; dropped (section 9). |
| N2 | NIT, 2 | `V = (cos y, cos x)` gives the kernel argument with no half-angle variables. | Adopted in the brief. |
| N3 | NIT, 5 | The Leibniz argument on δ·E needs no derivatives of E beyond `ContDiffAt`. | Noted in the brief. |
| N4 | NIT, P-alg | `Real.cos_eq_cos_iff` yields `2kπ + x`; turning `α² = 1/8` into `\|α\| = a*` needs `sq_eq_sq'` and abs handling. | Noted in the brief. |
| N5 | NIT, 8 | `triPhase_contDiff`, `triD*`, `vec*_const`, `third_polar` and `triExceptional_*` must be re-proved outside the sanity modules. | Done: `OscInt/Front/TriDeriv.lean`, a proof module with the same proofs under new names. |

Because the bridge holds for every reduced curve, the bite needs no uniqueness of the curve. Clarification TRI-b of
`docs/statements.md` says the opposite; it is corrected by an addendum there.
