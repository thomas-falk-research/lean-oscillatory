# Answers to the post-proof and adversarial reviews of batch LE2 (T0E′, T6E′)

Three fresh-context referees read the proved batch at 48e7f24. Two were post-proof referees, A (fidelity) and
B (mathematical content). The third was an adversarial referee covering the batch and the session.
- None ran Lean, because a replay was planned on the same machine (lessons 28). The replay is recorded separately
  (`docs/STATUS.md`).
- All referees are instances of Claude (Anthropic), the lead's own tool, in fresh contexts.
- Their prompts and reports are not recorded (owner privacy rule, lessons 46). Each finding is restated below in the
  lead's words. Written by the session-10 lead.

## Verdicts

| | Referee A (fidelity) | Referee B (mathematics) |
|---|---|---|
| T0E′ | FAITHFUL, scope full | FAITHFUL; every part SOUND |
| T6E′ | FAITHFUL, scope full | FAITHFUL |

**Referee A.** It checked that:
- the frozen file is unchanged since the stamp (its hash is in `stamps/statements.json`);
- the final theorems have exactly the statement types (`#assert_type_is` is syntactic);
- every blueprint proposition is discharged by a proved part, with no hidden hypothesis, `variable`, instance or
  `sorry`.

It also re-checked P-r8's deviation numerically (40-digit mpmath):
- Q(d)/d ≤ 2.507 on (0, 3/8];
- no window violation in 2·10⁵ points;
- the margin 9.70467 against C* > 9.7218.

**Referee B.** It re-derived every piece bound on paper. It checked every rational constant exactly, and the piece
bounds against quadrature at 6000 points. It walked every case boundary: v = 1/2, v = 1 − 2τ², v − δ = 1, t = 3, t = 8.

**Adversarial referee.**
- It confirmed both stamps: the freeze stamp covers 0532b1c, and the review stamp covers bf8af89 and precedes the
  route commit.
- It reproduced the key constants at 30 digits.
- It raised three MAJOR findings (below).

## Findings and answers

### Post-proof referee A

1. **MINOR: the per-module `leanchecker` claim had no record.** Agreed. The full replay (verify-all, which runs
   `leanchecker` on every module) is the record. Its log goes to `docs/replay/` and the STATUS rows cite it.
2. **MINOR: the "tightest margin" sentence and the route's `97/10` were out of date.** Agreed and fixed.
   - `docs/proof-LE2.md` now marks the first-routed P-r8 and P-r38 text as superseded where the proof differs.
   - It now says the δ ≤ v ≤ 1/2 sub-case has the smallest margin after the extremal one, which is exactly C*τ by
     construction.
   - `docs/statements.md` gains clarification 4.
3. **NIT: two Mathlib names were missing.** Fixed: `ConvexOn.slope_le_of_hasDerivAt`,
   `antitoneOn_of_hasDerivWithinAt_nonpos` and `convexOn_id` are now in `MathlibNames.lean`.
4. **NIT: the superseded P-arc 4 text, and the rounding 9.705 versus 9.7047.** Noted. Both round 9.70467.

### Post-proof referee B

1. **MINOR: the window constant 673/250 is only 1.5e−4 above its derived value.** Agreed and recorded in
   `docs/proof-LE2.md`. The value is (8/3)(11/10 − π/6) + 1/0.866 with π > 3.1415. It holds exactly, and the kernel
   checks it. It is fragile only against future edits of that lemma.
2. **NIT: the route text read first was out of date.** Fixed, as A2.
3. **NIT: `BandLowFacts` omits −1 < v − δ.** This was already noted as implied.

### Adversarial referee

1. **MAJOR: "the replay is running on a dirty tree".** Not so: the process it saw was `make quick`, not the replay. The
   first replay attempt was killed by a container restart before its kernel steps. Its point is the rule, and it is
   followed: the replay runs on the committed tree that includes these answers.
2. **MAJOR: three "no proof exists" claims contradicted the record.** Agreed: a complete **hand** proof existed
   throughout. The correct claim is "no **Lean** proof" (lessons 29).
   - `docs/statements.md` (Batch LE2, "Order") and `review/2026-11-10-LE2-pre-proof-answers.md` are corrected. The
     latter now also states what the blind referees did see: the route sketch, of which referee A hand-checked step 1.
   - The frozen file's docstring (`OscInt/Statements/LatticeCubeRoot.lean`) says "before any proof of these statements
     exists". It cannot be edited (lessons 39). It is to be read as "any Lean proof", as recorded here.
3. **MAJOR: the Result 1 record was never corrected.** Agreed.
   - `review/2026-11-10-external-followup-answers.md` now carries a dated correction. The lead's "no gap" was wrong to
     the extent that one step was unjustified.
   - The disclosure in `docs/prior_art.md` cites that correction.
   - The referee also showed the step's assumption is **true**: the band length is increasing in v for v ≥ 0, and the
     true maximum is about 8.82 at t = 3. So the correction in the pre-proof answers now says "true but unjustified",
     not "wrong".
4. **MINOR: the "within a factor 2" wording.** Agreed and made precise.
   - Rigorously, C*/C_opt ≤ 1.9706. The rational arithmetic is exact; the sign of the alternating-series remainder is a
     hand step.
   - Numerically, C*/C_opt ≈ 1.925.
   - In Lean, the bite proves only C_opt > C*/2, a 0.4% margin.
5. **MINOR: commits during referee runs (lessons 16).** True, and disclosed here.
   - 90e6ac8 (the photon consumer and a Makefile line) was committed while the pre-proof referees ran.
   - d42d8ea (documentation) was committed while the route referee ran.
   - Neither touched a file under review (the statements, the sanity layer, the route, the blueprint, the assembly).
   - Referee start and end times were not recorded.
   - Lesson for the next batch: no commits while a referee reads the tree.
6. **MINOR: "route reviewed before the parts" rests on git order and the lead's session record.** True. No stamp lies
   between the route-referee answers (f8deca9) and the first part commit (b16a523). The claim is worded "by git order
   and the lead's session record", as for batch LE.
7. **MINOR: the plant record classified inconsistently, and the sanity-file bytes were not hashed at run time.** Fixed
   in `docs/replay/2026-11-10-LE2-sanity-plants.txt` ("Corrections after the adversarial review").
   - T0Ep-int is instance-level.
   - The SHA-256 of the sanity file as committed after each run is given there. That the runs used those bytes rests on
     the session record.
8. **MINOR: stale status text after 48e7f24.** Fixed in `docs/prior_art.md`, `docs/ROADMAP.md` (I4) and
   `docs/applications.md`. The answers file's "nothing is proved in Lean" is now dated.
9. **MINOR: ROADMAP overstated the QWZ check.** Fixed. The row now says the checker was of the same model family, the
   evidence is floating point, the sup over x ran only to t = 8000, and the uniform constants and ρ₀ were not checked.
10. **MINOR: the AI-use disclosure named only the external tool.** Agreed and fixed in `docs/prior_art.md`:
    - the lead, all referees and the proof agents are Claude (Anthropic) instances;
    - "independent" means fresh-context;
    - "found TRUE" means numerics plus hand checks;
    - the ChatGPT 6 version is as given by the owner and not verified;
    - the novelty search was not re-run.
11. **MINOR: a review was cited before its answers file existed (lessons 36).** Agreed. This file is committed together
    with the edits that cite it.
12. **NIT: the consumer docstring.** Fixed in `examples/consumer/ConsumerPhotonLattice.lean`.
    - The hopping sign follows the published negative-hopping convention; positive hopping gives conj U(s, −n), with the
      same norm.
    - The round-trip evolution is approximated by continuous time.
    - "Right to the integer" is replaced by "s ≥ 519 suffices; b(518) > 1 is a Python rational check, not proved here".
13. **NIT: privacy.** No prompts or verbatim reports were found. The packet SHA-256 prefixes in the follow-up answers
    identify unpublished packets. They stay unless the owner decides otherwise (owner item).

## What the referees did not check

- No Lean was run by them. The replay covers this.
- The OpenTimestamps proofs and the TSR signature chains: only the times were read. `make verify-all` runs
  `stamp-verify`.
- The QWZ and plasma mathematics: this batch's referees did not re-check it. It was checked by fresh-context checkers
  earlier (`review/2026-11-10-external-followup-answers.md`).
- Prior art for real-ξ (Anger-function) bounds.
