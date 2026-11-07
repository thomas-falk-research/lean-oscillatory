# Answers to the front-end batch 1 reviews (2026-11-07)

Statement reviews `review/2026-11-07-API1-pre-proof-{A,B}.md` (FAITHFUL ×2) and post-proof reviews
`review/2026-11-07-API1-post-proof-{A,B}.md` (FAITHFUL ×2, scope full; commitments `ec40ed3e…` F1, `7db2d5f1…` F2).

## Statement referees
- A MINOR 2, B MINOR 2 (no elliptic instance of F2's hypotheses): `OscInt.API.Sanity.apiSanity_elliptic_hyps`
  (x³ − 3xy², disc 108) and `apiSanity_generic_hyps` (x³ + 2x²y + 3xy² + 5y³, disc −367).
- B MINOR 1 (no independent elliptic value): `apiSanity_elliptic_constant`, `d4ClosedConstant 108 = √π Γ(1/6)/3`,
  the off-line value J = 2B(1/2, 1/6) for x³ − 3xy², reached in Lean through duplication and reflection.
- A MINOR 1 (nothing ties `d4ClosedConstant` to `d4Constant`): S4.4 is proved; `OscInt.API.d4Constant_eq_closed`.
  (The referee's reading list did not include STATUS, so it took S4.4 to be unproved.)
- NITs on the stamped `FrontEnd.lean` (D = 0 value not documented; the F1 sanity fixed at n = 2; "S4.4's first
  conjunct is not used"): agreed; the file is frozen, so they are recorded here and not changed.

## Post-proof referees
- A MINOR 1/2, B MINOR 1 (`API.lean` said "every theorem below" has a frozen statement as type, and did not repeat the
  drafted-before-review disclosure): fixed; the docstring now says "every theorem in the table", names the helper
  `d4Constant_eq_closed` as not a frozen statement, and repeats the disclosure.
- A NIT 1, B NIT 1 (the S4.2–S4.4 row omits the elliptic branch): fixed. A NIT 2 ("re-exported"): reworded.
- B NIT 2 (where the independent value comes from; `gammaSixth` is shared with S4.4): the derivation and the shared
  lemma are now stated in `OscInt/API/Sanity.lean`.
- A NIT (the bite theorem hides A and c behind existentials): agreed; the explicit form is the consumer example
  `consumer_elliptic_limit`. A NIT (STATUS "the brief's S4 as one theorem"): reworded to "the brief's S4 limit with its
  constant as one theorem".
- B process note (two Lean processes overlapped briefly): noted; no effect on results.
