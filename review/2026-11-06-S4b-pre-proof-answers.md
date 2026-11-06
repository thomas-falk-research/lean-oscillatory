# Lead's answers to the S4.1′, S4.2–S4.4 pre-proof reviews (2026-11-06)

Verdicts (commit ad8e7fd, stamp `20261106T081634Z-e2d7771c358e`): referees A and B independently TRUE and FAITHFUL to
`docs/statements.md` for all four statements; against the brief FAITHFUL-STRONGER for S4.1′, S4.2, S4.3 (disc ≠ 0;
c_C > 0 rather than ≠ 0) and FAITHFUL for S4.4. No BLOCKER, no MAJOR. Both re-derived the polar formula and both
closed forms by hand; B checked mechanically that the closure of the S4.3 statement contains no Gamma/Beta/Mellin
constant.

- Proof-method rule for S4.3 (A MINOR 2, B MINOR 1): pre-registered now, before any proof: `GammaFree.lean`
  (run by `make lean`) fails unless the transitive closure of `OscInt.d4ConstantPos` (types and values, through every
  definition and proof) has no constant whose name has a component containing `Gamma`, `Beta`, `betaIntegral`,
  `mellin` or `Mellin`. Negative control `Real.Gamma_pos_of_pos` is rejected (7 forbidden constants); the statement's
  own closure passes; the theorem slot prints SKIPPED until proved. No exceptions without a new dated decision.
  Limitation: values of `opaque` constants are not followed (the guard forbids `opaque` in our files).
- The brief's S4 limit is the pair S4.2 ∧ S4.4, and "c_C ≠ 0" is S4.3 (A MINOR 1, B MINOR 2): stated so in
  `docs/STATUS.md` and the README; no citation names S4.2 alone as the brief's limit.
- Header wording on `angularMoment` finiteness, `limUnder` in S4.4, junk value of `d4Constant` at `disc = 0`
  (A NIT 3, 4; B NIT 5): recorded as a dated clarification in `docs/statements.md` (the stamped file is not edited).
- Witness for every δ (A NIT 5): exists, `OscInt.D4.ampBound_exists_delta` in `OscInt/D4/Bite.lean`.
- Numerics coverage (B NIT 3): added a probe with quartic terms and a non-even amplitude for both signs
  (`numerics/results-d4const-2026-11-06.txt`): real parts approach c_C A(0), imaginary parts decay like t^{-1/3}.
- a₀ + a₁ > 0 has a 6% margin (B NIT 4): noted for the S4.3 proof route (certified bounds on both integrals needed).
- No rate or uniformity in S4.2 (B NIT 6): as the brief; unchanged.

Correction (2026-11-06, lesson 18): the first version of `GammaFree.lean` did not follow theorem proofs
(`value?` returns `none` for theorems at this Lean version), so its OK lines before this date covered types and
definitions only. Fixed with `value? (allowOpaque := true)` and a proof-only negative control `gammaProofControl`,
which is rejected; `OscInt.d4ConstantPos` then passes with 43 612 constants in its closure.

Correction 2 (2026-11-06, S4b post-proof B NIT 3): with `value? (allowOpaque := true)` the check also follows
`opaque` values, so the "limitation" above no longer applies; the control now reports 33 forbidden constants.
