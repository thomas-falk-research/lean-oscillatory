# Answers to the batch-A3 pre-proof reviews (lead, 2026-11-09, before any proof of an A3 statement)

Reports: `review/2026-11-09-A3-pre-proof-A.md` and `review/2026-11-09-A3-pre-proof-B.md`, both on c7282ab (prompt
`review/prompts/A3-pre-proof.md`; two fresh-context referees of the same model family as the lead, run in parallel, each
blind to the other). Both: S1.k, S5.1, S5.1′ FAITHFUL to `docs/statements.md` and TRUE; `DerivChain`, `IsA3Point`,
`IsStableA3Point` FAITHFUL; no BLOCKER, no MAJOR. Every finding concerns the sanity layer or the prose. **No statement
text changes, no re-freeze.** Answered in `OscInt/Front/CuspSanity.lean` (new data and theorems, all compiled; the file
is not stamped), `docs/replay/2026-11-09-A3-sanity-plants.txt` (planted controls), and `docs/statements.md`, Batch A3,
"Clarifications after the pre-proof reviews".

## Sanity layer
- **Kernel condition (i) not separated** (A MINOR 1, B MINOR 1; the same finding). Agreed: `x² + y²` fails (iv) through
  vanishing derivatives, whatever (i) says; B is right that the header overstated it. Fixed: bite `x² + y² + x²y`
  (`nondegCubic_not_isA3`; rank two, nonzero cubic part). Plant `no-kernel` rejected, and the witness file shows the planted
  predicate accepts that datum (v = e₁, w = e₂, reduced quartic −12), so the rejection is semantic. Header corrected.
  The referees' counterexamples to a planted S5.1′ ((y + x²)² + x⁵ − 2y³, A; y² + y⁴ + x⁶, B) are recorded here; they are
  arguments about the planted text and were not re-checked by the lead.
- **All data at 0 with axis-aligned v, w** (A MINOR 2, B MINOR 3). Fixed: `obl_isStableA3` (the generic datum composed
  with (x, y) ↦ (x, x + y); kernel (1, −1), invariants unchanged: D²[w, w] = 4, D³[v, v, w] = 2, D⁴[v⁴] = 72, reduced
  quartic 276), `isStableA3_translate` and `oblShift_isStableA3` (the same point moved to (1, 1)). Plants `axis-fixed` and
  `at-zero` rejected, semantically (witness file; exact Hessian det −676 at (−1, −1)).
- **Stability condition (v) not separated from D³[v, w, w]** (A NIT 5, B MINOR 2). Fixed: `nonvCubic_isA3`,
  `nonvCubic_vww` (D³[e₁, e₂, e₂] = 2) and `nonvCubic_not_isStableA3` for x⁴ + y² + xy². Plant `stable-vww` rejected,
  semantically (witness file).
- **S1.k pinned only at k = 2, 3** (A NIT 6, B MINOR 4). Fixed: `vdCk_chain4` (k = 4, constant 38). Plant
  `const-larger-at-4` (40 at k = 4) rejected, semantically. Not detected, and recorded as such: a smaller constant
  (`10k − 12`) and B's `j < min k 3` in `DerivChain` (a weakened hypothesis that makes S1.k false at k = 4). Both are the
  structural limit of sanity theorems (they detect plants that make a hypothesis harder or a conclusion weaker); they
  rest on the reviews, which read the frozen text.
- **No plant record** (A MINOR 3). Fixed: `docs/replay/2026-11-09-A3-sanity-plants.txt`, files
  `docs/replay/plants/2026-11-09-A3/`. **Deviation:** lessons 33 asks for plants before the stamp; for this batch they
  were run after the stamp and after the reviews, in answer to them. The frozen statements did not change, so the stamp
  and the reviews remain valid for them.
- **`ContDiff ℝ ∞` ↦ `ω` (or 4) not caught** (A NIT 4). Not fixed. Both referees checked in Lean that the frozen text is
  the smooth index (`∞ ≠ ω`). A non-analytic C^∞ datum would pin it (a flat bump added to the generic quartic); it costs
  derivative computations of `expNegInvGlue` at 0 that the repository does not have. Recorded as a known gap of the
  sanity layer.

## Prose (`docs/statements.md`, dated clarification; the stamped Lean file is unchanged)
- **C⁴ suffices for the rescaled family** (A NIT 8, B NIT 1). Both referees give the weighted Taylor argument. The
  modelling-choice text "CONJECTURED: C⁵ suffices" is superseded by "C⁴ suffices (argued by both pre-proof referees; to
  be checked by the route referee)"; the frozen statements keep C^∞.
- **S1.k proof sketch mixes threshold and radius** (A NIT 7). Corrected (radius r = μ^{−1/(k+1)}, threshold μr).
- **The vector v behind the QWZ value** (B NIT 2). Stated (v = (8√65/12675)·(1, −1), w = (1, 0)); B's normalised values
  with v = (1, −1) added (D³ω[v, v, w] = 6√130/65, g₄ = −13992/4225), and A's and B's discrete Klein–Gordon values
  (v = (1, −1), w = (1, 0): D³ω[v, v, w] = −√5/5, g₄ = −3/5).
- **A cheaper S5.1′ route that also proves S5.1** (B NIT 3; A §2). Recorded for the route document: one-dimensional
  stationary phase in the transverse variable with parameters (u, y₂/t) and a C² remainder, then S1.k at k = 4; no Morse
  lemma with parameters is needed, and the route never uses condition (v). The missing tool is that parametrised 1D
  stationary-phase lemma.

## For the next batch (global assembly), from both reports
Non-stable A3 points can form curves (x⁴ + y² is A3 at every (0, s)); stable A3 points are isolated (E1 plus continuity).
A global theorem should therefore take a pointwise classification plus compactness and a partition of unity, not a
finite set of A3 points. Also named as lost by the current statements: compact families of phases (e.g. the
Klein–Gordon band uniformly in the mass), uniformity over non-linear perturbations, a general point k₀ (a translation
lemma; `isStableA3_translate` is the definitional half).
