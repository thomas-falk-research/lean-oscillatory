# Answers to the post-proof reviews of batch A3 (S1.k, S5.1, S5.1′), 2026-11-12/13

Subject: the A3 parts integrated at 93a8a8d (`review/2026-11-12-A3-packet-answers.md`), read at e814510.
- The three referees are fresh-context Claude instances: A (fidelity), B (mathematics) and an adversarial referee.
- Their reports are not reproduced (owner privacy rule, lessons 46). Each finding is restated below in the lead's words,
  with the answer.
- Written by the session-10 lead.

## Times (lessons 48)

From the session record (transcript timestamps, UTC). All three were launched at e814510.

| Referee | Launched | Last action | Run time | Lean run? |
|---|---|---|---|---|
| A, fidelity | 23:11:40 | 23:13:48 | 127 s | no (read files, `git`, `grep`) |
| B, mathematics | 23:11:40 | 23:15:13 | 213 s | no |
| adversarial | 23:11:40 | 23:18:31 | 411 s | no |

They were launched 47 s after `make verify-all` started on e814510 (23:10:53). They only read files, so they did not
contend with it. A fourth referee, for the LS route, was launched at the same time and did run Lean. That replay is
therefore not an acceptance record: see `docs/replay/2026-11-12-session10-e814510-partial.txt`.

## Verdicts

- **A (fidelity):** FAITHFUL for all three statements, full scope.
  - Every public name has the frozen type (`StatementTypes.lean`).
  - The proofs use no new instances, attributes or option changes that could change what a statement means.
  - No BLOCKER or MAJOR.
- **B (mathematics):** every part SOUND, and the constants 38, 304 and 4ab(1/c + D/c²) match the proofs.
  - B checked symbolically that the reduced fourth derivative G4 of P3 is g'''' identically.
  - B checked the packet's three falsification examples, and all are correct:
    - (y + x²/2)² has a nonzero raw quartic, but its reduced quartic vanishes;
    - x⁴ + ((1 + x)/2)y² + qy has reduced fourth derivative 24 − 12q² along its critical curve at (0, −q), which
      vanishes at q = √2;
    - (y + x + x³)².
  - No BLOCKER or MAJOR.
- **Adversarial:** three MAJOR, several MINOR and NIT. Answered below.

## Answers to the adversarial referee

**MAJOR 1. The STATUS rows said "machine-checked by build …" before any replay record existed.**
Agreed in part.
- The wording is the project's interim form between a proof and its replay. It was used for HC at 5a5f714, and
  `tools/check_docs.py` requires it: a row with `proved_by` set must begin "machine-checked". The rows did not
  claim "as stated".
- The referee is right that one of the three listed checks, the axiom audit, had run only in the isolated worktree.
  The main tree had run only the build and the type assertions.
- **Fix:**
  - `make lean` and `make guard` were run in the main tree on e814510, 2026-11-13 from 00:22:30 UTC. That covers the
    build, the axiom audit, the type assertions, the Mathlib name checks and the Gamma-free check. The log is
    summarised in `docs/replay/2026-11-12-session10-e814510-partial.txt`.
  - The rows now name where each check ran.
  - The "as stated" label waits for the isolated replay of the commit that records these answers.

**MAJOR 2. S1.k did not follow a refereed route, and the route revisions of b719ba4 were never re-refereed.** Agreed.
- `docs/proof-A3.md` lists S1.k under "Not needed": the cusp route uses only its order-four case (P1). The general
  `OscInt/Cusp/VdCk.lean` had no route review.
- Its review is the post-proof one: A read it for fidelity and B for mathematics, both with no BLOCKER or MAJOR.
- The b719ba4 revisions:
  - B checked that P3 follows the revised route, with the explicit G4.
  - P4 deviates, as the packet answers already said: one global directional integration by parts instead of the cut.
- **Fix:**
  - The S1.k STATUS row and the prior-art row now say so.
  - `docs/proof-A3.md` gains a section "Parts as proved".

**MAJOR 3. "The LS sanity extension cannot have been written after referee A finished."** Refuted by the session
record, which is the primary evidence here.
- The LS pre-proof referee A sent its report at 22:18:24 UTC.
- The sanity file was then edited in four tool calls: 22:19:23, 22:19:38, 22:19:47 and 22:20:01.
- The plant script was edited at 22:20:25 and run at 22:20:35.
- Before 22:18:24, only route drafts in the scratchpad, outside the tree, were written.
- The referee could not see this record. Its inference from the commit order alone was reasonable but wrong.

**MINOR 4. The plant D-rate-natdiv is called "genuinely detected" without the argument.** Agreed. The argument:
- The planted copy writes the exponent with natural-number division, so d/3 becomes 0 for d < 3.
- The sanity theorem `dispersive_two` uses d = 2, t = 4 and f = δ₀, where 2|t| = 8.
  - Under the plant the bound is min{1, (C*/(2π))²·8⁰} = min{1, 2.394} = 1.
  - The theorem's conclusion is the frozen bound (C*/(2π))²·8^{−2/3} ≈ 0.598.
- A bound of 1 cannot give 0.598, so the planted statement does not imply the sanity conclusion. The rejection is
  semantic, not the failure of a script step.
- This differs from D-rate, D-const-half and Dp-rate, which were reclassified NOT DETECTED: their planted bounds are
  smaller than or equal to the frozen ones on the datum.
- The plant is weaker, not false; it is detected as weaker.
- The plant record gains this paragraph.

**MINOR 5. The disclosure and the records.**
- **The tool version.** The packet named no version.
  - `docs/prior_art.md` said "the same external tool". It now says "an OpenAI model (the reviewer's tool; version not
    stated for this packet)".
  - The S1.k row gains the AI-use disclosure.
- **Stale rows and entries.** The S1.k and S5.1′ rows in `docs/prior_art.md`, README line 43 and CHANGELOG still said
  "not proved", and CHANGELOG said that no `proved_by` changed. All are updated. Batch LS is added to CHANGELOG and to
  `docs/prior_art.md`.

**MINOR 6. The packet provenance is thin.** Agreed. `review/2026-11-12-A3-packet-answers.md` now gives:
- the full archive SHA-256;
- the times, from the file times in the session scratchpad:
  - extraction at 22:38:56 UTC;
  - compilation in the worktree from 22:42:36 to 22:52:19;
  - the integration commit 93a8a8d at 23:02:13;
- which of the five fixes can be located in the integrated files:
  - all five are in `OscInt/Cusp/VdCk.lean`, `Implicit4.lean` and `Core4.lean`;
  - the removed `ring` cannot be located, because it is absent.

**MINOR 7. File headers and names.**
- `OscInt/Cusp/VdC4.lean` and `VdCk.lean` gain an "Authors" line and a "Modified/derived from" note, as
  `OscInt/VanDerCorput/Higher.lean` has.
- The P3 helpers live in the existing namespace `OscInt.StationaryPhase.ImplicitAux`; the packet answers now say so.
- The root-namespace duplicates `OscInt.vdCk` etc. are not asserted in `StatementTypes.lean`. The API names are, and
  only the API names are the public interface.

**MINOR 8. The LS interface record shows HEAD 93a8a8d with modified tracked files.** Already disclosed in the
record's header: it was run while the route files were being added, before the commit e814510.

**MINOR 9. Some route names were not `#check`ed.**
- `MathlibNames.lean` gains the names that exist at the pin: `HasSum.mapL`, `ContinuousLinearMap.map_tsum`,
  `integral_conj`, `HasDerivAt.clm_apply` and `NormedSpace.exp_eq_tsum`.
- The route also named `Complex.hasSum_exp`, which does not exist at the pin (the LS route referee found the same).
  `docs/proof-LS.md` now replaces it (section "Revision after the route referee").

**MINOR 10. The whistler example.** Agreed.
- "Disperses like τ^{−1/3}, not τ^{−1/2}" read as a sharpness claim. The example proves an upper bound only; the
  Airy-type behaviour at an inflection is classical and is not proved here.
- The Eliasson–Shukla citation had not been read by the lead. It is now marked CITED-UNREAD.
- The model's validity regime is stated: cold, collisionless, parallel propagation, frequencies between the ion and
  electron gyrofrequencies.
- `examples/consumer/ConsumerWhistler.lean` and `docs/applications.md` are reworded.

**NITs.**
- **I3 aliasing.** The I3 check of `numerics/review/ls_interface_checks.py` uses a periodic grid with 49 sites per
  axis for orders up to 60. The wrapped-around contribution was computed in exact integers by the lead: it is at most
  1.2·10⁻⁴¹. It is noted in the record.
- **The header of the frozen `OscInt/Statements/LatticeGroup.lean`** calls the statements "blind-reviewed" before the
  review existed. The file is frozen and is not edited; STATUS records the review.
- **The docstring of `kernel_deriv_zero_e1`** ("would give i/2") describes a planted variant; it is not a detection
  claim.

**NIT found by the lead (2026-11-13, main-tree build).** `OscInt/Cusp/Implicit4.lean` raises six linter
warnings, the only warnings in the build:
- line 131: `norm_num <;> ring`, where `;` would do;
- line 227: an unused `simp` argument;
- line 229: `<;> ring` after `field_simp` closed the goal, so the `ring` never runs.

They are style only. The proof text is left as integrated, so that the reviewed text and the replayed text are the
same. A cleanup is a later, separate change.

## Answers to A and B (MINOR and NIT)

- **A, "51 new declarations".** It is 51 theorems plus 10 definitions. The wording is corrected.
- **B, P4's text in `docs/proof-A3.md`.** It describes slice-wise integration by parts with Fubini and a cut, while
  the Lean proof does one global directional integration by parts in (0, 1), with no Fubini and no boundary terms.
  Recorded in "Parts as proved".
- **B, the hypothesis D³φ[v, v, v] = 0.** S5.1′ does not use it. The route's "Not needed" list now says so.
- **B, smaller points:**
  - P2 proves less than g ∈ C⁴, and what it proves is enough.
  - P4's constant is literally (1/c + D/c²)·volume.real K.
  - The base cases k = 2 and 3 of S1.k come from S1.2 and S1.3.
  
  All three are recorded in "Parts as proved".

## Status after these answers

- The proofs are unchanged. No BLOCKER remains, and every MAJOR is answered.
- The STATUS rows for S1.k, S5.1 and S5.1′ become "machine-checked as stated" only after the isolated replay of the
  commit that records these answers (lessons 28, CONTRIBUTING step 11).
