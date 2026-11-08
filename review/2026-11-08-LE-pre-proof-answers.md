# Answers to the LE pre-proof reviews (lead, 2026-11-08, before any proof of an LE statement)

Reports: `review/2026-11-08-LE-pre-proof-A.md` (at af2a6e8), `review/2026-11-08-LE-pre-proof-B.md` (at ec9899a; B checked
that no reviewed file changed since af2a6e8). Both: FAITHFUL and TRUE on T0E, T6F, T6E; no BLOCKER; derivations from
S1.2/S1.3, Fubini and t^{-1/2} ≤ t^{-1/3} checked step by step. No statement text changes.

## Referee A
- **MAJOR (presentation): the explicit bounds beat the trivial ones only for large t.** Agreed and recomputed (bisection:
  T0E below 2π for t > 518.53; T6E below 4π² for t > 1321.47). Answered in `docs/statements.md`, Batch LE,
  clarification 6, and in the API annotation of T6E. The finding is against the documentation, not the statement text;
  both referees judged the text FAITHFUL. **Process note for the owner:** CONTRIBUTING step 5 reads "A BLOCKER or
  MAJOR means a new statement (back to 2), never an edit". This MAJOR asks for no statement change and the referee
  says "docs change only, no re-freeze"; the lead did not re-freeze. This is a third kind of MAJOR (documentation),
  next to the test-layer MAJOR of API3 (memo `docs/decisions/2026-11-08-step5-memo.md`); the owner's step-5 decision
  should say whether it covers this case. The STATUS rows will carry "owner decision pending" until then.
- **MINOR (T6E loses up to a factor 2.9 against composing T6F and T0E).** Clarification 8.
- **MINOR (user normalisation; negative times).** Clarification 9 (75.9 t^{-2/3} for e^{itH}, H = 2cos k₁ + 2cos k₂,
  t ≥ 1/2; the reduction for t < 0 stated as not formalised).
- **MINOR (sanity coverage of added restrictions on t).** Fixed: `latticeKernel1Explicit_eighth` (t = 1/8) and
  `latticeKernelFactor_neg` (t = −2); plants T0E-threshold (`1 < t`) and T6F-tpos (`0 < t`) now rejected
  (`docs/replay/2026-11-08-LE-sanity-plants.txt`, second run).
- **NIT (what I(0,0), I(0,1) pin).** Reworded in the sanity file header ("the length 2π and the integer frequency scale").
- **NIT ("a changed constant").** Superseded by B's compiled plant: a smaller constant (`24 ↦ 23`) is also detected;
  docstring now says "larger or smaller" and names the actual blind spot.
- **NIT (`_proof_k` auxiliary lemmas in the elaborated T6E).** No action (cosmetic, as A says).

## Referee B
- **MINOR-1 (Landau's constant is for integer ξ; real-ξ sup ≥ 0.80366).** Agreed; the lead recomputed B's point
  (t, ξ) = (5.7972479262309164, 4.404) with Simpson's rule, N = 200000: t^{1/3}|I|/(2π) = 0.80366. Clarification 7.
  The pre-registered criterion (c) was over integer n only, as B notes; it was the right check for Landau's integer
  statement and says nothing about real ξ.
- **MINOR-2 (T6E holds for all t > 0).** Agreed (trivial bound for t ≤ 1); clarification 8; a corollary may be added
  with the proofs, not a re-freeze.
- **MINOR-3 (docstring wrong about smaller constants; `0 ≤ t` blind spot; `latticeKernel1` body not planted).** Docstring
  corrected. The `0 < t ↦ 0 ≤ t` plant is now in the record as an expected and observed blind spot (accepted). The
  body of `latticeKernel1` (e.g. `cos ↦ sin`) is not covered by the conditional form; it is tied to the frozen
  `latticeKernel` only by T6F's proof (B's own observation: once T6F is proved, `I(t, n)` at integer `n` is fixed up to
  one sign per t). An unconditional sanity value separating `cos` from `sin` at t ≠ 0 would need a Bessel value in
  Lean; not attempted (recorded).
- **NIT-1 (the threshold plant is rejected only through `le_rfl`).** Docstring of `latticeLaplacianExplicit_one` and
  the record say so.
- **NIT-2.** No action.
