# Answers to the VT post-proof and adversarial reviews (lead, 2026-11-09)

Reports at 09e4bc7 (no Lean change since the replayed d261c19): `review/2026-11-09-VT-post-proof-A.md`,
`review/2026-11-09-VT-post-proof-B.md` (both: FAITHFUL at full scope ×4, no BLOCKER/MAJOR), `review/2026-11-09-VT-adversarial.md`
(no BLOCKER; two MAJOR, five MINOR, five NIT).

## Adversarial MAJOR
- **M1 (QWZ m = 3 has exact cusp points; the "folds only" verdict and the near-separable diagnosis are wrong).**
  Agreed and confirmed by the lead (symmetric points with H₁₁ = H₁₂ at a = 1.910633: det H ≈ 3e−18, T[v, v, v] = 0).
  Erratum `docs/design/vector-amplitudes.md` §6; §4 verdict and §5 diagnosis retracted; QWZ dropped as an acceptance model;
  records corrected (CHANGELOG, ROADMAP, prior_art, applications, STATUS, HANDOFF); lessons 43. Nothing frozen depended on
  it (the VT statements are generic).
- **M2 ('C after E' is not rejected for a semantic reason).** Agreed (also post-proof B MINOR-1, with a compiled proof).
  Retracted in the sanity docstring, the plant record and here; the two placements are provably equivalent, so no sanity
  theorem can separate them. My pre-proof answers' sentence "cannot succeed by instantiation" was wrong.

## Adversarial MINOR and NIT
- **m1 (FiniteDimensional fixed only for GD-N-V).** Fixed: `globalFold_bounded`, `globalDecay_bounded`,
  `globalDecayCrit_bounded` (E = ℕ →ᵇ ℂ); third plant run, 4/4 rejected at the instance; consumer file extended. These
  additions came after the replay; `make quick` re-run; the replayed proof files are unchanged.
- **m2 (generator verdicts are proof-shape specific).** Stated in the plant record.
- **m3 (decay prereg criterion (b) not discriminating; no positive control).** Agreed; erratum §6.
- **m4 (route order is commit order, not timestamped).** Stated in `docs/statements.md`, Batch VT, clarification 8 (also
  post-proof A MINOR-2, B NIT-1).
- **m5 (records).** QWZ overclaims corrected; VT rows added to STATUS, README, CHANGELOG; HANDOFF rewritten.
- **n1.** `VectorFinal.lean` docstrings now say `E : Type` (comment-only change after the replay). `transfer` stays in
  `OscInt.VectorAux` (internal namespace), documented in `VectorFinal.lean`.
- **n2 (`hM0` unused).** Left as is, to keep the replayed proof file byte-identical; harmless.
- **n3 (instance defeq not syntactic for `lp`).** Noted for users: use `change`/`exact` rather than `rw` when the
  ℝ-structure of `E` comes from elsewhere.
- **n4 (design §1 label stale).** Fixed ("PROVEN since: batch VT").
- **n5.** Already in STATUS; repeated in clarification 8.

## Post-proof A
- **MINOR-1 (stale user-facing docs).** Fixed: which-theorem, design doc §1, statements.md (pointer to the final file and
  replay), applications.
- **MINOR-2 (route order on lead-controlled evidence).** As adversarial m4.
- **NIT-1 (Order paragraph).** Clarification 8. **NIT-2 (no compiled nonzero amplitude).** Recorded; both post-proof
  referees compiled one in scratch (ContDiffBump • v); not added. **NIT-3 (no compiled Matrix snippet).** Recorded, not
  added. **NIT-4.** As n1.

## Post-proof B
- **MINOR-1.** As adversarial M2. **NIT-1.** As m4. **NIT-2 (sanity header stale).** Fixed. **NIT-3 (no part brief under
  `review/prompts/`).** Agreed: the lead proved the single part directly; deviation from CONTRIBUTING step 7 recorded here.
