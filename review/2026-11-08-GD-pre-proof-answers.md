# Answers to the blind pre-proof reviews of batch GD

Reports (verbatim, both on b71615c, prompt `review/prompts/GD-pre-proof.md`): `review/2026-11-08-GD-pre-proof-A.md`,
`review/2026-11-08-GD-pre-proof-B.md`. Both: all eight statements FAITHFUL to `docs/statements.md` and TRUE; no
BLOCKER, no MAJOR; derivable along the documented route. Neither referee proved a statement or wrote in the
repository. The statement file `OscInt/Statements/Global.lean` and the stamp `20261108T094842Z-edf7787a2845` are
unchanged by everything below; the changes are sanity theorems, planted controls, docs and records, all made before
any proof of a GD statement and covered by the review stamp that follows this commit.

## Sanity layer (test layer; CONTRIBUTING step 5 does not apply: no MAJOR)
- **A m1 / B (fold points missing).** Added `hypPhase` = x³ + y³ (hyperbolic umbilic; folds on the axes) with
  `hyp_classified`, `globalDecay_hyp`, `globalDecayCrit_hyp`; plants `GD-fold-to-det`, `GDC-fold-to-det` rejected.
- **A m3, B m2 (`↑D ⊆ U` vs `↑D ⊆ K`; D4 point always at 0).** Added `globalDecay_hyp_offK` (D4 point 0 ∉ K =
  B̄((3/4, 3/4), 1/4), U = B(0, 2)) and `hypShift` = (x − 1)³ + (y − 1)³ with D = {(1, 1)} (`globalDecay_hypShift`);
  plants `GD-D-in-K` and `GD-D4-at-zero` (Hessian evaluated at 0 instead of k₀) rejected.
- **B m1 (critical-points-only hypothesis).** Added `globalDecayCrit_hyp_crit`: x³ + y³ on B̄(0, 2), K′ = {L₃},
  L₃ = −3 fst − 3 snd, D = ∅ (classified at the critical points (±1, ±1), not pointwise at 0); plant
  `GDC-crit-dropped` rejected.
- Record: `docs/replay/2026-11-08-GD-sanity-plants.txt` — 15 plants rejected at the mutated hypothesis or the
  conclusion, 15 unplanted copies accepted (generator and full compiler output in `docs/replay/plants/2026-11-08-GD/`).
- Undetectable by design (both referees list the same ones): dropping `discr ≠ 0`, dropping `IsCompact K′`,
  C⁴ ↦ C³, a different nonzero T6L constant (only the pre-registered numerics test its value; both referees
  reproduced it independently, to 5·10⁻⁶ and 7.5·10⁻⁷). These rest on the fidelity reviews.
- **B N2, N3.** Docstrings of `L₁` and `latticeLaplacianDecay_diag` corrected (sanity file, not a stamped file).

## Docs
- **A m2, B m4 (near D4 points).** `docs/statements.md` "Batch GD" said CONJECTURED. Both referees give the same
  argument (for a binary cubic with nonzero discriminant every nonzero degenerate point has rank one and is a fold;
  by continuity of D²Ψ, D³Ψ this holds in a punctured neighbourhood of a D4 point of a C⁴ phase), A with a numeric
  check. Recorded in the clarification as "argued on paper by both referees, not formalised"; the GD proof route does
  not use it (inside the D4 balls the local D4 bound needs no classification).
- **A n1.** Pointwise over all L equals critical-points-only over all L: added to the clarification.
- **A n2.** Negative times and |t| < 1: added to the clarification and to `docs/applications.md` as consumer notes.
- **B m3.** The arccos fold condition is numerical only; a Lean proof along a transcendental curve is open: stated in
  `docs/applications.md` (already "proposed") and the clarification.
- **B N1 (`↑D ⊆ U` redundant).** Not changed (the statement is frozen). It is not implied by the other hypotheses
  when D ⊄ K (`globalDecay_hyp_offK` has such data); it keeps `IsD4Point` about a point where Ψ is C⁴.
- **B N4, A n3.** Pointers added in the clarification (GD-F/GD-N for D = ∅; T6L's coefficients are D³/6, the
  `cubicCoeffs` convention).
