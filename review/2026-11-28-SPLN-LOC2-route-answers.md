<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batches SPL-N and LOC2: answers to the route referees, and the proofs (2026-11-28, session 17)

Written by the lead. Two fresh-context route referees of the lead's model family, no Lean, numerics only. Their briefs
are outside the tree and identified by SHA-256 in `docs/progress/2026-11-28-session17-log.md`; reports are not
reproduced; findings are in the lead's words. Isolation by instruction (lessons 61).

**Order, said plainly.** The review answers of the six statements were stamped at 15:44:53Z
(`stamps/20261128T154444Z-e9c0ea9fb732`). The SPL-N route and blueprint were committed at b17ec90 (15:48Z) and the
route referee was launched at 15:56:33Z on that commit. The SPL-N proof agents had been launched at 15:47:36Z and
worked in scratch while the referee read; the LOC2 blueprint and route were never in the tree before this commit, and
the LOC2 proof agents (launched 15:59Z) and the LOC2 route referee (launched 16:13:38Z, on a snapshot packet) also
overlapped. Lessons 42 allows proof drafts outside the repository while a route referee reads; so no part was proved
in the repository before its route was reviewed, but the parts were written before the route reviews ended. No
part changed after a route review.

## 1. SPL-N route referee

Launched 15:56:33Z at b17ec90 (brief SHA-256 70e1b14d77dfbb78e037eaab7fbca9cf494c2efb93c7f27e1acc38ea3dede893), task
record 1580 s. Python 3.13.18, mpmath 1.4.1.

Verdict: every part TRUE (Taylor ratio at most 0.5000 of the bound on 801 points; `x‖L − F(x)‖ → 1 < 2`; the
interpolation lemma sharp at the midpoint; small-branch maximum 0.39973, tail maximum 0.63863 at x = 4; its own exact
re-run of the 40 cells with the factor-2 remainder: minimum squared slack 9.0926·10⁻¹⁰; lower-point margin
1.2993·10⁻⁸); the assembly is faithful to SPL-S and SPL-A. No FATAL, no MAJOR.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| R-1 | MINOR | The riskiest part is the soundness of the rational checker against `splnCentre` (powers of i, casts, large rationals); the kernel cost of the 40 cells should be measured on this table. | Done by agent C: the centre is written as `A(x) + s D(x)` and the checker is proved sound; kernel time of the 40 cells and the cover about 2.1–2.4 s; four negative controls evaluate to `false`. |
| R-2 | MINOR | Simpler routes for N1+N2 (three derivative-boundary steps), N5 (one-sided convexity) and N8 (from `splKer_integral_eq`). | Noted; N5 was proved by the convexity route the referee suggests; N1+N2 and N8 by the route's argument with explicit primitives on finite intervals (no improper integrals), as the referee also recommends for N8. |
| R-3 | NIT | The route's table names propositions that the blueprint merged (`SplnFormulaFacts`, `SplnSqrtPiFacts`, `SplnCellFacts`), omits N10, and says SPL-NK comes from SPL-I where the assembly uses SPL-S; the commit said "8 parts" for 7. | Accepted; the revision section of `docs/proof-SPLN.md` gives the parts as proved. |
| R-4 | NIT | `Real.pi_lt_d2` suffices for the constants 4/3 and 63/100. | Accepted; the parts use it. |

## 2. LOC2 route referee

Launched 16:13:38Z on a snapshot of the route, blueprint and assembly (brief SHA-256
36690f6ce412376de7ccd54563782bab9f78b8110d43455375eb10c256336882), task record 605 s. Python 3.13.18, numpy 2.5.3.

Verdict: all six blueprint propositions TRUE (identity of Q1 to 10⁻¹¹; Bessel is exact Parseval; shell sum 3.22658;
the 3/2 of Q5 attained at `δ = (±1/2, ±1/2)`; the expansion holds for a Lipschitz cutoff; the coefficient bound with
ratio 0.075–0.20); `LocCombineFacts` follows; the assembly is faithful (end-to-end ratio at most 0.033). No FATAL.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| L-1 | MAJOR (against the route's plan, not a proposition) | Q2's plan reuses K2's `lift` and `mFourierCoeff_lift`, which need support inside the open box, but Q2 is stated for every continuous g; a second box–torus identity for `∫ \|lift\|²` is also needed. | Correct about the plan. The Lean proof of Q2 does not use K2's lift: agent B defined its own lift through `measurableEquivPiIoc`, proved it in L² and applied Mathlib's `UnitAddTorus.hasSum_sq_mFourierCoeff`, with both box–torus identities and the null set between `Ioc²` and `Icc²`. The proposition is proved as stated (kernel-checked, section 3). The route's revision section records this. |
| L-2 | MINOR | Q1 needs a C¹ integration by parts, the passage from set integral to integral, and the bridge to `iteratedFDeriv ℝ 2`. | All three are in agent A's proof (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, `iteratedFDeriv_two_apply`). |
| L-3 | MINOR | Integrability on the box is load-bearing (a non-integrable Bochner integral is 0). | Proved in the parts (continuous on a compact set). |
| L-4 | NIT | The periodicity hypotheses on Ψ are unused. | Noted (also the sanity agent's NIT); the frozen statement is not changed. |
| L-5 | NIT | The route and the blueprint use `j` and `n` the other way round. | Accepted; the revision section says so. |

## 3. The proofs (all in scratch, then integrated by the lead)

| Part | Agent | File | Lines | SHA-256 |
|---|---|---|---|---|
| N1, N2, N4, small branch | T | `OscInt/Front/StationaryLeadingSharpTaylor.lean` | 239 | 8c7eae3f… |
| tail branch | L | `OscInt/Front/StationaryLeadingSharpTail.lean` | 243 | f3f243d6… |
| N5 | C | `OscInt/Front/StationaryLeadingSharpInterp.lean` | 101 | e5e9a7be… |
| N10 | C | `OscInt/Front/StationaryLeadingSharpThird.lean` | 66 | 82f411c1… |
| N3, N6, N9 | C | `OscInt/Front/StationaryLeadingSharpCellsCore.lean` | 321 | 4f6ec9fd… |
| N7 (40 cells, `decide +kernel`) | C | `OscInt/Front/StationaryLeadingSharpCellsData.lean` | 44 | 66addeb3… |
| final parts | C | `OscInt/Front/StationaryLeadingSharpCells.lean` | 46 | ce42885e… |
| Q1, Q5 | QA | `OscInt/Front/TorusLocalizationC2Ibp.lean` | 314 | 4ddbab85… |
| Q2, Q3, Q4, Q6 | QB | `OscInt/Front/TorusLocalizationC2Fourier.lean` | 395 | 1437a79d… |

The lead's assemblies (`OscInt/Front/StationaryLeadingSharpAssembly.lean`, `OscInt/Front/TorusLocalizationC2Assembly.lean`)
and final files (`…SharpFinal.lean`, `…C2Final.lean`) were compiled against the parts in a scratch mirror of the
build: every module exit 0 with empty output; `#print axioms` of `OscInt.API.splKernelCap`, `splKernelLower`,
`stationaryLeadingSharp`, `stationaryLeadingSharpness`, `torusLocalizationC2`: propext, Classical.choice,
Quot.sound; `leanchecker` on each of the thirteen new modules: exit 0, empty output. The tree checks (`make quick`,
guard, audit) follow in the integration commit.
