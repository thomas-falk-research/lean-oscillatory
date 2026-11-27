<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch TRI: answers to the post-proof reviews (2026-11-27)

Written by the lead. Three referees from fresh contexts, all of the lead's model family, reviewed commit 0f1fe0a
(HEAD 2c376d8 differs only in the session log): A fidelity, B soundness, C adversarial. Launches were recorded and
pushed before they were made (2c376d8); brief hashes are in `docs/progress/2026-11-26-session15-log.md`. Each worked
in its own scratch directory and wrote nothing in the repository. The reports are not reproduced; findings are in the
lead's words.

**Result: no BLOCKER and no MAJOR.**
- **A:** TRI-K, TRI-X, TRI-W, TRI-Q each FAITHFUL, scope full.
- **B:** SOUND.
- **C:** claims SUPPORTED on every mathematical point, with one MINOR overstatement in the records (shared with A).

The findings are against records and wording, not against a statement or a proof.

## What the referees established

**A (harness 305 s, 26 tool uses).**
- The stored type of each final theorem is the bare frozen constant (`ci.type == Expr.const …`).
- The frozen statement, challenge and definition files match the stamped manifest.
- The helpers `InLocus` and `qinv` equal the statement's expressions by `Iff.rfl` and `rfl`.
- The assembly uses the parts with exactly the data of `IsA5Point`.
- TRI-W's "every reduced curve" clause is non-vacuous: a `ReducedCurve` at `(θ, −θ)` with ε = 1/8 was built from the
  proved witness.
- The bite is tested at a genuine A3 point.
- Plant TRI-W-a (the sign of the sextic) is now refuted by the proved theorems (probe).
- "No point with Hessian zero" follows formally from TRI-K.

**B (harness 455 s, 24 tool uses).**
- No forbidden token and no `set_option` in the 18 OscInt modules of the import closure.
- No sanity module in the closure or among the constants used.
- `leanchecker` exit 0 on the eight batch modules and six dependencies.
- Re-elaboration from source without warnings.
- Axioms: propext, Classical.choice, Quot.sound for the four theorems, the bite and every part.
- Each route step is mapped to a Lean lemma, and each deviation from the route is listed and judged valid.

**C (harness 2322 s, 28 tool uses; no Lean beyond probes).** Independent SymPy and mpmath computations from the phase itself:
- A locus search from 20,000 random seeds with α ∈ [−3, 3] finds exactly TRI-X's four points at |α| = a*.
- An exact series of the reduced function gives `g⁽¹⁻⁵⁾(0) = 0` and `g⁽⁶⁾(0) = −60√2 · sign α`, for both signs, at
  `(θ, −θ)`, at `(−θ, θ)` and at shifted points.
- The values of TRI-Q are confirmed.
- No junk value is reachable.
- No degenerate witness is possible: by the bridge, A1, A2 and A3 points cannot satisfy `IsA5Point` with any curve.

## Findings and answers

| # | Severity, target | Finding (lead's words) | Answer |
|---|---|---|---|
| A-M1 = C-F1 | MINOR, records and frozen docstrings | "In particular there is no A4 point" (TRI-K prose; frozen module docstring and `TriClassificationStatement` docstring) is not a consequence of the Lean theorems. TRI-K's disjunction is not exclusive and `IsA5Point` is existential over (v, w, ε, h), so nothing proved rules out another (v, w, curve) at a locus point with `g⁽⁵⁾(0) ≠ 0`. Machine-checked, through internal lemmas: (i) every reduced curve with `g‴ = g⁗ = 0` lies on the locus (`ReducedBridge.bridge` with `TriAlg.algA5`); (ii) at locus points every curve for `v = (1, 1)`, `w = (1, −1)` has `g⁽¹⁻⁵⁾ = 0` (`TriWitness.gW_derivs`). C checked numerically that `g⁽⁵⁾(0) = 0` for five other choices of w. "No point with Hessian zero / no D-type point" does follow. | Accepted. The frozen docstrings cannot change (lessons rule 11). Clarification TRI-c in `docs/statements.md` states what is and is not a Lean consequence. A Lean "no A4" in the form "`g‴ = g⁗ = 0` on a reduced curve implies `g⁽⁵⁾ = 0`" needs the bridge to order 5; it is recorded as a follow-up, not claimed. |
| A-N1, B-NIT | NIT, `docs/proof-TRI.md` | The route still lists `g′(0) = g″(0) = 0` in the bridge. Section 8 marks files "(planned)" and names a file `TriEG.lean` that does not exist (P-EG is `eg_false` in `TriAlg.lean`). Section 9 names a `set_option` that nothing uses. The witness uses neither device of section 9, item 4. | Section 10 "As proved" added to the route. |
| A-N2 | NIT, records | The plant re-runs owed by section 9, item 3 are not done. STATUS still says TRI-W-a is not detected. | TRI-W-a is now refuted by referee A's compiled probe, recorded here. A compiled plant-closure record for TRI-W-a and TRI-X-a/b, as for batch SPL, remains owed. Until it exists STATUS keeps "not detected" with a pointer to this answer. |
| B-NIT | NIT, evidence | `leanchecker` ran without `--fresh`, replaying only each module's own declarations. | The full replay (`make verify-all`: per-module `leanchecker`, a kernel export re-checked by six kernels, the comparator) is the acceptance record. It runs next. |
| C-F2 | NIT, frozen docstring | The `TriQuarticStatement` docstring says "v spans the Hessian kernel". | Already clarification TRI-a. The frozen file stays. |
| C-F3 | NIT, records | "The case α = 0 is not stated" understates: TRI-X quantifies over all α, so there is no A5 point at α = 0 (probe). | Clarification TRI-c. |
| C-F4 | NIT, records | TRI-b's first paragraph still says the bite needs uniqueness; only the addendum corrects it. | The addendum stands; TRI-c repeats it. |
| C-F5 | NIT, STATUS | The TRI-Q row omits α ≠ 0 and \|α\| ≤ 1/2 and calls the jet invariant a "reduced quartic". The invariant is `D²[w, w] · g⁗(0)`. | Row reworded. |

## What follows

1. The full replay `make verify-all` on a clean tree, with no other Lean process. Only after it passes do the rows
   say "machine-checked as stated".
2. The plant-closure record.
3. The follow-up "no A4 in Lean", optional.

No calibration copy with planted errors was reviewed for this batch, so the detection rate of these reviews is
unmeasured. Every referee, prover and the lead are AI agents of one model family.
