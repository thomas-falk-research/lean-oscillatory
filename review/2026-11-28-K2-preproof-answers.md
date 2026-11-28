<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch K2: answers to the blind pre-proof reviews (2026-11-28)

Written by the lead. Two referees from fresh contexts, both of the lead's model family, reviewed the six statements
of batch K2 after the freeze. The freeze is stamp `stamps/20261128T013824Z-c5c04f495284` on c5c04f4, pinned in
db43739. The briefs are outside the tree (privacy rule 19) and identified by SHA-256 in
`docs/progress/2026-11-28-session16-log.md`. Their reports are not reproduced; findings are in the lead's words.

**Outcome: six FAITHFUL (referee A), six TRUE with no counterexample (referee B); no BLOCKER, no MAJOR. The
statements stand.** No Lean proof of any K2 statement exists at the time of these answers.

**Process deviation of the lead, recorded here (rule 4 of `docs/lessons.md`).** While both referees ran, the lead
committed and pushed ac65d22 (the session-16 block of `docs/HANDOFF.md`) and ce39fcb (the launch row of the session
log). The tree was not frozen as rule 4 requires. Both commits change documentation only. Referee A checked with
`git diff --stat` that the files it was allowed to read are identical at db43739. Referee B could not check this
(its brief allowed only `git log -1`). The lead checked afterwards that the SHA-256 of every file B hashed equals
the file at db43739: `TriangularDecay.lean` 32b99c38, `TriangularAniso.lean` 3218aaeb, `Global.lean` 15b29a8e,
`StationaryPhase.lean` a7ff7032, `docs/statements.md` 8b49098a. Also, `git diff --stat db43739 ac65d22` lists only
`docs/HANDOFF.md` and the session log. So both reviews read the frozen text. B's finding MINOR-1 is answered by this
check.

## 1. Referee A (fidelity)

Launched at ce39fcb, after the freeze db43739; harness 456 s, 19 tool uses; brief SHA-256 8cf2b5fc…bf79fc. It ran one
Lean probe in its scratch, the only Lean process while it ran, and wrote nothing in the repository. It found HEAD at
ce39fcb, checked with `git diff --stat` that the files it was allowed to read are identical at db43739, and confirmed
the SHA-256 of the statement file, the sanity layer and the plant generator against the plant record.

What its probe settled (`pp.explicit`):
- `x ^ m` in K2-MA and K2-ML is the monoid power, not `Real.rpow`, so negative x is handled as intended;
- `r ^ (m - 1)` uses natural-number subtraction, harmless for `m ≥ 2`;
- K2-L's exponent is the real `−(1/2 + 1/m)`;
- `ContDiff ℝ ∞` is C^∞, not analytic;
- every other `rpow` has a positive base;
- `triKernel 0 = latticeKernel` holds by `funext` and `simp`, compiled; `triRate (1/2) = 3/4`, compiled;
- every integrand is integrable on its domain, so Lean's value 0 for a non-integrable function is never reached.

**Verdicts: six FAITHFUL** (K2-L, K2-MA, K2-ML, K2-F, K2-U, K2-D). None is UNFAITHFUL, FALSE or FAITHFUL-WEAKER. No
BLOCKER, no MAJOR. For each statement A sketched why it is true on paper. For K2-U and K2-D it added that the global
statements cannot be checked from the statement text alone (marked "plausibly true").

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| A1 | MINOR | No plant exercises K2-L's reduced-curve conditions or its order hypothesis. A concrete false plant: replace `ReducedCurve` by `ContDiff ℝ ∞ h ∧ h 0 = 0`. Datum: `x⁶ + y²/2` at 0, v = (1, 0), w = (0, 1), h(u) = u², so g = u⁶ + u⁴/2 and g⁽⁴⁾(0) = 12. The plant then claims `t^{−3/4}`, but the factorised integral is about `t^{−2/3}`. This is detectable relative to K2-ML. | Accepted as a gap of the frozen sanity layer (the same kind as TRI-b). The plant and its relative witness are owed with the proofs, recorded with the closed plants of the batch. The frozen text does not contain the mutation. |
| A2 | MINOR | Plant F-a (support condition of K2-F dropped) is NOT DETECTED, and no plant drops `ContDiff ℝ ∞ χ`. So the plants do not show that the cutoff hypotheses have bite. | Accepted; a plant without C^∞ and a decision on F-a are owed with the proofs. On paper A's own remark applies: for χ = 1 the coefficients of the box indicator times `e^{iq·k}` decay only like `1/\|n − q\|`, so the ℓ¹ route fails. |
| A3 | NIT | Continuity and biperiodicity of Ψ in K2-F are not needed for truth. | Already disclosed (sanity agent K-3); kept. |
| A4 | NIT | `2 ≤ m` in K2-L restricts nothing. | Already disclosed (K-2). |
| A5 | NIT | In K2-MA, `2 ≤ m` and `σ = ±1` have bite on the statement, but no plant exercises them. The plateau conjuncts are bitten only on data. | Noted. |
| A6 | NIT | K2-D has no unconditional detection, and `c > 0` is never exercised. | Inherent and disclosed in the plant record. |
| A7 | NIT | The prose's "for every real time" should read "every real `t ≥ 1` / `t ≥ T_α`". | Accepted; clarification K2-a of `docs/statements.md`. |
| A8 | NIT | The sanity layer's docstring says the plants are "not in the repository"; they are in `docs/replay/plants/2026-11-28-K2/`. | Accepted; the file is stamped, so this is a record note (K2-a). |

## 2. Referee B (truth and counterexamples)

Launched at ce39fcb; harness 1622 s, 76 tool uses; brief SHA-256 610d1391…7a233c; no Lean; scripts in the lead's
scratch, not in the tree.

**Verdicts: six TRUE** (no counterexample, vacuity or hidden assumption found). The evidence, in the lead's words:
- **K2-L.** Read as text: the spanning hypothesis is redundant; `g″(0)` is the Schur complement. Numerically, the
  supremum over linear terms is computed by zero-padded FFT for t = 10 to 1000 on four model phases, one with
  non-orthogonal v and w at m = 5 and one with a curved reduced curve. Each scaled supremum converges or flattens.
- **K2-MA.** Closed forms against oscillatory quadrature for m = 3 to 7. A sweep over:
  - m = 2 to 7 and both signs;
  - r from 0.05 to 1.7, ramps from 1e−3 to 5 long, three ramp shapes;
  - t from 1e−3 to 1e4.

  Worst error/bound 0.4995, with the steep-ramp limit 1/2 derived analytically. So the constant 4 is within a factor
  of about 2 of the best for this argument.
- **K2-ML.** Worst ratio 84.98, including at the exact threshold.
- **K2-F.** Supports up to `[−3.1, 3.1]²`, random trigonometric phases and `triPhase`, t from 0 to 25, velocities up
  to about 40 in modulus, including negative ones: worst `L/(D B)` = 0.37.
- **K2-U, K2-D.** The main attack is a search for an A4 or worse point, which would make the rate 7/10 at that α.
  - Every solution of `det = cubic = quartic invariant = 0` in (x, y, α) is at α = ±a*, near (θ, −θ): 452 solutions
    from 20 000 random starts, |α| ≤ 50.
  - A sign scan of the invariant over all A3 points for α from 0.005 to 3, and for large |α| up to 1e5, found nothing
    either.
  - A Gröbner elimination did not finish and was stopped, so there is no algebraic certificate. TRI-K, TRI-X and the
    TRI-c lemmas already carry this in Lean.
  - The global kernel was computed by FFT, validated against a Bessel expansion, with a stated alias bound, for
    non-integer t from 10 to 5700 and 15 couplings:
    - α = 0: `t^{2/3} sup_n |K|` is 17.98 ± 0.03, the predicted 4π² · 0.6749²;
    - ±a*: flat with exponent 2/3;
    - 0.05, 0.25, 0.7, 1: flat with exponent 3/4;
    - near the exceptional couplings and at α = 10: still drifting at the times reached (NIT-3).
  - At the lattice site nearest the critical velocity, up to t = 1e5, the values approach the predicted local A5 and
    A3 constants. For example α = 10 gives 4.29 against 4.30.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| B-MINOR-1 | MINOR | HEAD was not the commit named in the brief, so B could not check that its files are those of db43739. | Answered by the lead's check above: identical. Recorded as the lead's deviation from rule 4. |
| B-NIT-1 | NIT | K2-ML is a corollary of K2-MA, and its constant is loose by a factor of 85 or more. | Known and disclosed (prose, modelling choice 1). K2-ML is kept as its own statement for direct use by K2-D. |
| B-NIT-2 | NIT | Continuity and periodicity of Ψ in K2-F are unused. | As A3. |
| B-NIT-3 | NIT | Near the exceptional couplings, finite times cannot show the asymptotic rate (crossover scale about 660 at α = 0.34). | Consistent with the non-uniform constants that the prose discloses. The parameter-uniform crossover is out of scope (owner). |
| B-NIT-4 | NIT | B did not open `Cusp.lean` (`IsA3Point`), and relied on the prose for its meaning. | Noted; referee A read it. |

## 3. What changes

- No statement changes. Clarification K2-a in `docs/statements.md` (findings A7 and A8). The statement file is
  unchanged.
- Owed with the proofs, recorded with the batch's closed plants:
  - A1: a plant that replaces `ReducedCurve` by smoothness and `h 0 = 0`, with its witness relative to K2-ML on
    `x⁶ + y²/2`, `h(u) = u²`;
  - A2: a plant without `ContDiff ℝ ∞ χ` in K2-F, and a decision on F-a.
- STATUS rows: "pre: FAITHFUL (referee A), no counterexample found (referee B)".
