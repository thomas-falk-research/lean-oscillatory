# Answers to the blind pre-proof reviews of batch LE2 (T0E′, T6E′)

Two fresh-context referees, A and B, reviewed the frozen statements at 18d22ec (stamp
`stamps/20261110T234417Z-0532b1cf8880`) against `docs/statements.md`, Batch LE2. Neither saw a Lean proof (none existed). A hand proof did exist (the external reviewer's, re-derived by the lead); both
were told not to read it (the external material or `review/2026-11-10-external-followup-answers.md`), but they saw the
route sketch in `docs/statements.md`, and referee A hand-checked its first step (adversarial review, 2026-11-11). Their prompts
and reports are not recorded (owner privacy rule, lessons 46). Each finding is restated below in the lead's words, with
its severity and the lead's answer. Written by the session-10 lead.

## Verdicts

| Statement | Referee A | Referee B |
|---|---|---|
| T0E′ | FAITHFUL, TRUE (strong numerical evidence and a hand check of the route's step 1) | FAITHFUL, TRUE (strong numerical evidence; route checked regime by regime) |
| T6E′ | FAITHFUL, TRUE (from T0E′ and the proved T6F) | FAITHFUL, TRUE (from T0E′ and the proved T6F) |

No BLOCKER and no MAJOR. So, by CONTRIBUTING step 5, no statement changes. The stamp stands.

## The referees' evidence, in brief

Both computed sup t^{1/3}|I(t, ξ)| independently.
- A used Gauss–Legendre quadrature, cross-checked against a Bessel-series formula to 1e−14, over 760 values of t up
  to 400.
- B used a grid up to t = 120, 3000 Nelder–Mead starts, and a 30-digit mpmath check of the maximiser.

Both found the global maximum 5.0496 at (t, ξ) ≈ (5.795, ±4.403). That is 0.519 C*. Neither found anything near C*,
whether at non-integer ξ, the caustic, small t, large t (the values tend to the Airy limit ≈ 4.24), or negative ξ.
This agrees with the lead's own scan (max 5.0495 at (5.786, 4.40)).

## Findings and answers

1. **T6E′ had no bite, and two false strengthening plants went undetected (A and B, MINOR).** The two plants were the
   unsquared constant C* and `0 ≤ t`. A also noted that the faster rate t^{−1/2} in T0E′ is false, and that robust
   closings of the sanity theorems compile from it.
   - **Done.** The sanity file now proves three unconditional T6E′ bites through the proved T6F, using `K(t, 0) = I(t, 0)²`:
     - `laplacianCubeRoot_false_at_zero`: the bound is false at t = 0;
     - `laplacianCubeRoot_unsquared_false`: at t = 1, ‖K‖ ≥ (3π/2)² > C*;
     - `laplacianCubeRoot_half_const_false`: at t = (7/8)³, the constant (C*/2)² fails.
   - The second plant run refutes the plants "unsquared", "quarter constant" and `0 ≤ t` for T6E′ with compiled
     witnesses (`docs/replay/2026-11-10-LE2-sanity-plants.txt`, second run).
   - The faster rate is recorded as **NOT DETECTED**. A witness would need a lower bound for |I| at large t near the
     caustic. It rests on the reviews (both checked it numerically) and on the proof.
2. **The threshold data at t = 1/8 are in the trivial regime (A and B, MINOR/NIT).** There, 2C* > 2π and 4C*² > 4π².
   So the sanity conclusions hold for a trivial reason, and the threshold plants were rejected only at instance level.
   - **Done.** New sanity theorems at t = (31/20)³ ≈ 3.724 (`latticeKernel1CubeRoot_thr`, `latticeLaplacianCubeRoot_thr`),
     just above the usefulness threshold 3.7045. There both conclusions are below the trivial bounds (`thr_nontrivial`,
     compiled). The threshold plants were rerun there.
3. **"Semantic evidence" in the first plant record overstates (A and B, MINOR).** The ξ ≥ 0 plant is equivalent to T0E′,
   since I(t, −ξ) = I(t, ξ), so its rejection is syntactic. The threshold rejections at t = 1/8 are instance-level.
   - **Agreed.** The record gains a "Corrections" section that classifies every plant: semantic (exact), instance-level
     or syntactic, refuted by a witness, or not detected. The first run's lines are kept as recorded.
4. **Which step sets C* (A NIT, B NIT).** With the exact band expression, the regime where C* arises (Δ → 2, t ≥ 8)
   peaks at about 8.76, not at C*. C* comes from the relaxed bound 1/√(1 + s) ≤ 2√2/3. The tightest step of the route is
   3 ≤ t ≤ 8 at t = 3, v ↓ 1/2 (cap bound, the 2/(tv) branch): 3^{1/3}(π + 32/9) ≈ 9.659, against 97/10.
   - **Agreed.** It is recorded as a dated clarification in `docs/statements.md`. The rational check of that end point is
     `numerics/review/followup_checks.py` R1c-cap (5486/567 < 97/10, exact). Both referees note that the same route
     gives a constant of about 9.66; C* is what is frozen.
5. **Step 3 needs monotonicity in v (A, MINOR).** A computed that bounding the arcsine and the −4/(t(1 − v²)) terms
   separately can give about 10.3 at t = 3.
   - **The lead's reading.** The route's step-3 bounds already take each term at its own worst v within each sub-range
     (v ≥ 1/2; 1/4 ≤ v ≤ 1/2; v ≤ 1/4). The six end values are checked exactly (R1c), and all are below 97/10. So no
     joint monotonicity in v is needed there.
   - A's split must have been coarser than the route's three sub-ranges. The lead did not reproduce the 10.3.
   - Step 2, for 0 ≤ v ≤ 1/2, does need convexity in v. The route document plans it from the monotonicity of h′ for
     h(s) = (1 − s²)^{−1/2} (route document, part P-arc 4).
   - Lean pain points the route must answer: integration by parts on pieces whose end points depend on the data, with
     the exact end-point terms kept (S1.1 cannot be reused); arccos/arcsin inequalities; the rpow algebra in τ = t^{−1/3}.
6. **The cap bound's range is not stated (A NIT).** It needs −1 < v − δ, and when v − δ ≥ 1 the whole-interval branch
   applies.
   - **Agreed.** This is a clarification in `docs/statements.md`. The route states both ranges.

## What the referees did not check

- No interval-certified numerics: the sups are floating point, with resolution checks.
- The exact derivation of 277/30. The lead's R1b checks it.
- Stamps and hashes. The lead ran `stamp verify` on the LE2 stamp: 774 file hashes match commit 0532b1c, and the three
  RFC 3161 tokens are OK.

## Correction (2026-11-11, after the route referee)

The lead's answer to finding 5 was **wrong**. Referee A was right that step 3 needs monotonicity in v for the band piece
(0 ≤ v ≤ 1/4, δ = 1/2).
- The term arcsin(1/2 − v) is worst at v = 0, where it equals π/6.
- Taking each summand at its own worst v gives about 9.726 at t = 3. That is above C*.
- The value 50/21 assumed the band length is increasing in v. That assumption is **true** (for v ≥ 0, the derivative
  of the band length is 2(h(v + 1/2) − h(v − 1/2)) ≥ 0, since h(s) = (1 − s²)^{−1/2} is even and increasing in |s|; the
  true maximum of t^{1/3}·(band bound) over v ∈ [0, 1/4] at t = 3 is about 8.82; adversarial review, 2026-11-11), but
  neither the reviewer's text nor the route justified it.

The route referee found the same; `docs/proof-LE2.md` ("Revision after the route referee") splits that sub-range at
v = 1/8. The new end values are exact and below 97/10. No statement is affected: the gap was in the route's bookkeeping,
not in T0E′.
