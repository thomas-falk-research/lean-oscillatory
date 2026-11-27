<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch TRI: answers to the blind pre-proof reviews (2026-11-27)

Written by the lead. Step 5 of `CONTRIBUTING.md`, quoted before it is applied: "Two fresh-context referees review
the statement against `docs/statements.md` without seeing any proof. … A BLOCKER or MAJOR means a new statement (back
to 2), never an edit. A MAJOR whose finding is only against the prose of `docs/statements.md` (not the Lean text, not
the sanity layer) is answered by a dated clarification there".

Reviewed: the four statements of `OscInt/Statements/TriangularAniso.lean` (frozen text SHA-256
3218aaeb07e577b46ea1f833b40bcf65d136a31d427fa609089d19b99190c7a2, stamped `stamps/20261127T060115Z-bb3a05c4b143`,
06:01:23Z) against the section "Batch TRI" of `docs/statements.md` as of 2ce8a68. Two referees from fresh contexts,
both of the lead's model family, launched after the freeze and after the launch was logged and pushed (12d1bc7).
Brief SHA-256 values are in the session log. The reports are not reproduced; every finding below is in the lead's
words.

## Blindness and its limits

The referees worked from a packet outside the repository: the statement file, the prose section, the sanity file and
the plant record. They were told which files they could open and which not. Each listed the files it opened.

- Referee A's list has no forbidden file. It also grepped the imports of `OscInt/Front/CuspSanity.lean` and grepped
  `docs/statements.md` once (three lines about the forms of A3). Neither path was forbidden.
- Referee B's list has no forbidden repository file. It read the output files of its own background jobs under the
  session's task directory. That is outside the letter of the brief ("nothing under /tmp other than the packet and a
  scratch directory of your own"), and those files hold only its own computations.

This is blindness by instruction and by self-report, not by a sandbox. The prose they read says that a proof on paper
and registered tests exist. No proof text, Lean or paper, is in any file they were allowed to open. No Lean proof of
a statement of the batch existed while they ran.

**Result: no BLOCKER and no MAJOR finding, from either referee, against the Lean text, the prose or the sanity
layer. Step 5 asks for no new statement. The statements stand as frozen.**

## Referee A (fidelity; harness: 671 s, 37 tool uses)

Verdicts: TRI-K, TRI-X, TRI-W and TRI-Q each FAITHFUL.

Method reported:
- Elaboration probes with `pp.coercions` and `pp.numericTypes`. The value of TRI-W is `−60 · √2 · ↑(sign α)`, with
  the sign cast to ℝ. `Finset.Icc 1 5` is over ℕ. The shifts in TRI-X are `2π·↑j` with `j : ℤ`. The `∞` of
  `ReducedCurve` is the smooth index. The `let θ` is a non-dependent binder.
- Its own SymPy computation of both values of TRI-Q for symbolic α, with the pieces `D²[w, w] = 4α`,
  `D³[v, v, w] = 2√(1 − 4α²)` and `D⁴[v⁴] = 12α` at `(θ, −θ)`.
- A series solution of the reduced curve at ±a* (`h = −u²/2 − u⁴/3 − 49u⁶/180` at +a*), giving the sixth derivative
  `∓60√2`.
- A paper argument, by the implicit function theorem and the Morse lemma with parameters, that the order of the
  reduced function depends on none of the choices of v, w and h, so `IsA5Point` holds exactly at corank-one A5
  points.
- A least-squares search of `det H = 0`, cubic `= 0`, quartic `= 0` over (x, y, α) from 9000 starts with initial |α|
  from e^−14 to e^10. Every solution found is one of the four points of TRI-X's locus.
- Two mutations of the definitions, compiled against the whole sanity layer in its own scratch (finding A2).

| # | Severity, target | Finding (lead's words) | Answer |
|---|---|---|---|
| A1 | MINOR, Lean against prose (TRI-Q) | The prose says "v spans the Hessian kernel". The Lean text says only that v lies in the kernel (`∀ z, D²Ψ[v, z] = 0`), which a zero Hessian would also satisfy. Rank one, `D²Ψ[w, w] = 4α ≠ 0`, is not part of TRI-Q, so TRI-Q alone does not give `IsA3Point`; the sanity layer computes `D²Ψ[w, w]` separately. | True. The Lean text is what was frozen and is the weaker claim; the prose overstated it. Answered by clarification TRI-a in `docs/statements.md`: TRI-Q states that v lies in the kernel; that it spans it (rank one) is not part of TRI-Q. |
| A2 | MINOR, sanity layer | No sanity theorem tests the transverse equation of `ReducedCurve` or the range of orders in `IsA5Point`. The referee compiled the whole layer against two mutated definitions. M1 replaces the equation of `ReducedCurve` by `True`; the layer compiles after a one-line proof edit, with the theorem statement unchanged. M2 changes `Icc 1 5` to `Icc 1 4`; it compiles unchanged. M1 is a real loophole: with a free curve, an indefinite A3 point counts as A5, for example (π/2, π/2) for α = 1/4, which would make TRI-X false. M2 lets A4 points count as A5. A bite of the form `¬ IsA5Point` at an A3 or A4 point would catch both. It needs the uniqueness half of the implicit function theorem, which the proofs need anyway. | Accepted as a limit of the layer, not repaired before the proofs. The layer was frozen with the statements, and a MINOR does not reopen it (the precedent of SPL, finding A1). The frozen definitions contain the equation and the range 1 to 5, so neither mutation is in the frozen text; the finding is that the layer would not have caught them. Recorded in clarification TRI-b. Owed with the proofs: a theorem `¬ IsA5Point (triPhase (1/4)) (π/2, π/2)`, proved from TRI-Q and the uniqueness of the reduced curve. It is recorded as an open item of the proof batch, and the plant record is to be re-run against it. |
| A3 | MINOR, sanity layer and plants | No unconditional `IsA5Point` and no `ReducedCurve` of `triPhase` exist in Lean. So nothing in Lean shows that the "every reduced curve" clause of TRI-W is non-vacuous or that the hypothesis of TRI-X can hold. Plant TRI-W-a (the sign of the sextic) is not detected, as the plant record says. The local curve given there, `h(u) = π/4 − arcsin(1/(√2 cos u))`, agrees with the referee's own derivation. | Agreed; it is what the plant record says. The proof of TRI-W's first two conjuncts constructs the A5 points and their reduced curves, and after that the plant TRI-W-a becomes detectable. To be re-run then. |
| A4 | NIT, prose | The notation paragraph describes `FoldOrNondeg` as "a nonzero cubic along every kernel vector"; the Lean text says every nonzero kernel vector. | Clarification TRI-a. |
| A5 | NIT, plant record | TRI-X-c (dropping `\|α\| = a*`) is recorded as a true weakening, but it is equivalent. For \|α\| > 1/2 the arccos clamps to the points (0, 0) and (π, −π), whose Hessian determinants `1 ± 2α` are nonzero. For \|α\| ≤ 1/2 the quartic `12(8α² − 1)` at (θ, −θ) forces \|α\| = a*. | Accepted as a reading of the record: the plant cannot be refuted by any datum because it is equivalent to the frozen statement, given the other facts. The plant record is not edited (it is a run record); this answer is its correction. |
| A6 | NIT, Lean | `let θ` displays as `have θ`. | No action. |

Referee A could not check: a rigorous proof of TRI-K or TRI-X (its support is numerical); a construction of a
reduced curve in Lean; the implicit-function uniqueness in Lean (its invariance argument is on paper). The challenge
file, the comparator and the stamps were out of its scope.

## Referee B (truth; harness: 1634 s, 32 tool uses; no Lean)

Verdicts: NO COUNTEREXAMPLE FOUND for each of the four.

Method reported:
- **Two facts from the Lean definitions.** Whether the quartic of `IsA3Point` is zero does not depend on the choice
  of w. On every reduced curve, `h′(0) = 0`, `h″(0) = −D³Ψ[v, v, w]/D²Ψ[w, w]`, `g‴(0) = D³Ψ[v³]`, and `g⁗(0)` is the
  quartic divided by `D²Ψ[w, w]`. So `IsA5Point` forces rank one, a zero cubic and a zero quartic.
- **An exact classification of the degenerate points with zero cubic, of its own.**
  - The case `cos(x + y) = 0` gives A3 points at α = ±1 only (quartic `−3α²`).
  - Otherwise, eliminating α from the degeneracy condition gives a factorisation, verified in SymPy, into
    `sin(x + y)` times a trigonometric polynomial R. The branches are:
    - `x + y ≡ π`: only `(±π/2, ±π/2)`, which are A3 or folds;
    - the antidiagonal: `(θ, −θ)` and `(−θ, θ)`, with quartic `12(8α² − 1)`;
    - the curve `R = 0`.
  - On `R = 0`, an exact resultant and gcd in `X = e^{ix}`, `Y = e^{iy}` find common zeros of the quartic only at the
    four A5 points of TRI-X, at α = ±1/(2√2), apart from spurious and already-treated points.
- **Cross-checks.**
  - Scans of the `R = 0` curve at 20 to 40 digits on all eight branches show the quartic strictly negative, tending
    to zero only at the A5 end.
  - A Newton search in double precision from 97,200 starts at 17 values of α agrees with the classification: 4
    points for |α| < a*, 8 for a* < |α| ≤ 1/2, 6 beyond.
- **TRI-W and TRI-Q.**
  - TRI-W: exact series at both points for both signs: `g⁽⁶⁾(0) = −60√2 · sign α`. The value is unchanged for two
    other choices of w.
  - TRI-Q: confirmed at 30 digits by numerical differentiation of the phase itself, for 12 values of α including
    ±1/2.
- **Junk values.** None reachable: arccos is evaluated only on [−1, 1]; the sign only at α ≠ 0; `reducedFn` is
  smooth.

No findings against the statements. Its side observation: off-axis A3 points exist exactly for |α| > a*, four for
each α, and merge with the antidiagonal pair into the A5 points at |α| = a*. That is consistent with the registered
run TRI-3 (8 solutions at a = 0.4, 4 at a = 0.3).

Referee B could not check:
- No Lean was run.
- The curve scans are sampled, not certified. The exact resultant closes that gap, but its unit-circle roots come
  from 30-digit `nroots` with a test `||z| − 1| < 1e−12`.
- A Gröbner-basis cross-check did not finish within about 13 minutes and was stopped.
- The existence of a globally smooth reduced curve was argued by a standard cutoff, not constructed.

## What follows

- **For the proof of TRI-K and TRI-X:** referee B's elimination is an independent route, different from the proof on
  paper (`review/2026-11-26-A5-handoff-answers.md`). It is not a proof as written: its unit-circle root test is
  numerical. Turned into an exact argument, for example by certified root isolation of the resultant, it is a
  candidate route for a Lean proof that avoids case analysis on the torus.
- **Owed with the proofs:** the bite of A2, then a re-run of plants TRI-W-a and TRI-X-a/b.
- **Next steps:**
  1. stamp of these answers (`make stamp`);
  2. only then Lean proofs;
  3. a route referee before the parts, as in batch SPL.
- **Detection rate unmeasured:** no calibration copy with planted errors was reviewed for this batch
  (`docs/calibration.md`), so the detection rate of these reviews on these statements is unmeasured.
