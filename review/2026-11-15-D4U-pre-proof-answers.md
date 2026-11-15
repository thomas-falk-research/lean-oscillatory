# Answers to the blind pre-proof reviews of batch D4U (S4.2U, S4.2O)

Two fresh-context referees read the frozen batch at 86f497f (stamp `stamps/20261115T122915Z-33c56db38f65`), before any
Lean proof of these statements existed in the repository. Referee A checked fidelity, and referee B checked the
mathematics.
- Both are Claude instances, like the lead.
- Their prompts and reports are not recorded (lessons 46). Each finding is restated below in the lead's words.
- Referee A compiled small checks of the definitions (unfolding, the empty and singleton families, `lin 0`, linearity of
  `oscInt2` in the amplitude) in its own scratch directory; referee B ran no Lean. Nothing was committed while they read
  the tree (lessons 16). Written by the session-12 lead.
- Disclosure (lessons 24): referee B's report outlines, as part of its evidence, a reduction of S4.2U to S4.1′ and S4.2
  (common radius, finite net, uniform bound on differences) and of S4.2O to S4.2U through the modulation family, without
  writing a proof. Together with the external packet disclosed in `docs/statements.md` (batch D4U), the claim "no proof
  before the reviews" holds for the repository and the lead's Lean, not for the mathematics.

| Referee | Launched at commit | Launched (UTC) | Finished (UTC) | Run time |
|---|---|---|---|---|
| A (fidelity) | 86f497f | 12:31:44 | about 12:38:24 | 399.5 s |
| B (mathematics) | 86f497f | 12:31:44 | report about 13:08:12; agent ended about 13:12:13 | 2187.5 s to the report; 2428.5 s in all |

Launch time from the lead's clock just before the two launches; run times from the session's task records.

## Verdicts

| | Referee A (fidelity) | Referee B (mathematics) |
|---|---|---|
| S4.2U | FAITHFUL, scope full | TRUE |
| S4.2O | FAITHFUL, scope full | TRUE |

No BLOCKER. One MAJOR (A, finding 1), against the sanity layer and the plant record, not against the Lean text or the
prose. The statements and the stamp `stamps/20261115T122915Z-33c56db38f65` stand.

**Referee A.**
- `D4LimitPhase` is S4.2's hypothesis list verbatim (checked by `Iff.rfl`); δ depends on φ only, T on the family (or A, M,
  R) and ε; the offset norm is the max norm; a real T with a strict inequality is the uniform `atTop` form.
- `AmpTotallyBounded` is C² total boundedness: a finite η-net drawn from the family in the sup norm of the derivatives of
  order ≤ 2, with support in K. Its first conjunct is needed (without it every singleton qualifies, whatever the
  function), the empty family is harmless, and it admits infinite families and the modulation family a proof will need.
- The limit and normalisation are S4.2's; on singletons S4.2U specialises to S4.2, and at y = 0 S4.2O's integrand is
  S4.2's.

**Referee B.**
- c_C for the generic cubic (disc −367) by the Gamma-free definition and by S4.4's closed form: 1.548533222513 against
  1.548533222517 (relative 3e−12); the same for two further cubics.
- The 1D integral ∫ e^{i(tu³ + ηu)} b(u) du by panel quadrature and by an Airy convolution agree to about 1e−15 for t up to
  1e5; the 2D generic-cubic integrals by tensor quadrature and by the factorised Airy product agree to about 1e−16, and a
  non-product radial bump by tensor and polar quadrature likewise.
- Uniformity: for fixed R the error of t^{2/3} I / (c_C A(0)) is about 0.61 R t^{−1/3} (sup over a grid of ‖y‖ ≤ R, t up
  to 1e7), uniform in ‖y‖ ≤ R and not in R; at y = t^{1/3}(1, 0) the ratio tends to 0.5945, an Airy product, not 1; at
  y = t(1, 0) the integral is non-stationary and decays to the quadrature floor.
- No family satisfying the hypothesis was found on which the convergence fails to be uniform.

## Findings and answers

1. **MAJOR (A).** The S4.2U sanity datum `scaleFamily` ({c · bump : c ∈ [1, 2]}) is linear in c, so its uniform
   conclusion follows from the single-bump case by linearity of the integral; the datum does not test uniformity over a
   family that is not finite-dimensional. Consequently the first plant record's classification of U-not-uniform (and, at
   the level of the statement, ATB-finite) was wrong. Referee B made the same observation as a NIT.
   **Answer.** Accepted. Added, before any proof (precedent: lessons 33, 38; statements unchanged):
   `seqFamily` = {(2 + i) · bump + w_n · bump_n : n ∈ ℕ} ∪ {(2 + i) · bump}, bumps of distinct radii with weights
   w_n = 1/((n + 1)(|M_n| + 1)) against each bump's own C² budget M_n; `seqFamily_totallyBounded`; and
   `uniform_seq_sanity` (S4.2U through its constant, uniformly in n). Its conclusion is not reducible to finitely many
   amplitudes by linearity. The lead chose this datum over the referee's suggestion (modulations e^{iy·κ} · bump) because
   C²-total boundedness of the modulation family is a step of the planned proof of S4.2O, which lessons 23 keeps out of
   the tree until the reviews are answered. The plant record is corrected (second run, below).
2. **MINOR (A).** O-moving and O-unbounded are stronger than S4.2O and imply `offset_sanity`'s conclusion, so their
   first-run rejections were script-only and should be NOT DETECTED (lessons 44); witnesses can be built from S2.1.
   **Answer.** Accepted. Both reclassified for the first run, and both refuted in the second run by compiled witnesses:
   at y = (100, 0) (O-moving) or y = t · (100, 0) (O-unbounded) the phase t(φ + 100κ₁) has gradient ≥ 1 everywhere, so the
   proved S2.1 (`OscInt.nonStationary`) gives t^{2/3}·|I| = O(t^{−1/3}) → 0, against the planted limit c_C ≠ 0.
3. **MINOR (A).** The C² order and the budget conjunct of `AmpTotallyBounded` have no bite; plants replacing C² by C⁰ in
   the net, or dropping the budget conjunct, were not run (both make S4.2U false: an oscillating family that is C⁰- but
   not C²-totally bounded; the constant 1, whose integral is not integrable and so is 0 in Lean).
   **Answer.** Partly accepted. Added the bite `const_not_totallyBounded` (the constant 1 has no budget on B̄(0, 1)), and
   the plant ATB-no-budget, refuted by a witness (the planted definition holds for the constant 1). The plant ATB-C0 was
   run and is recorded NOT DETECTED: no compiled witness (the oscillating counterexample needs derivative bounds of an
   oscillating family that this layer does not build); the order is pinned by the proof, which consumes the C² budget
   through S4.1′.
4. **MINOR (A).** The phase data cover only the hyperbolic umbilic (disc < 0); a plant `≠ 0` → `< 0` would pass. NIT part:
   φ(0) = 0 and Dφ(0) = 0 have no plant.
   **Answer.** Accepted for the umbilic: `phase_elliptic` (x³ + 2x²y − 3xy² − 5y³, disc = 169) and the plant P-neg, refuted
   by a witness. The NIT part is not planted (the bundle is S4.2's hypotheses verbatim, checked by referee A).
5. **MINOR (A).** The amplitude values A(0) in the sanity conclusions are real and positive, so plants replacing A(0) by
   its conjugate, real part or modulus would pass.
   **Answer.** Accepted: the new datum has A_n(0) = (2 + i)(1) + w_n, complex; the plant U-conj (conjugate) is rejected and
   refuted by a witness (on {(2 + i) · bump} the planted limit c_C (2 − i) contradicts S4.2's c_C (2 + i)). Real part and
   modulus plants are separated by the same datum and were not run separately.
6. **MINOR (A).** No plant targets S4.2O's uniformity in y (∀y∃T).
   **Answer.** Run as O-forall-y: rejected on data (`offset_sanity`'s offsets vary with t); it is a weaker, true statement,
   so no witness can refute it.
7. **NIT (A).** The section heading of batch D4U in `docs/statements.md` says "compact amplitude families"; the definition
   is total boundedness (no closedness).
   **Answer.** Accepted: dated clarification in `docs/statements.md`.
8. **NIT (B).** Modelling choice 3 names linear terms "of size t" as the case without the limit; the limit already changes
   at |y| ~ t^{1/3} (ratio 0.5945 in B's numerics), so uniformity holds for |y| = o(t^{1/3}).
   **Answer.** Accepted: dated clarification, labelled as the referee's numerics.
9. **NIT (B).** Stronger statements are plausible (uniformity over merely C²-bounded families, rate ‖A‖_{C²}(1 + |y|)t^{−1/3}).
   **Answer.** Noted as a possible later statement; not in this batch.
10. **NIT (B).** A downstream consumer that recentres at a D4 point k₀ gets a unimodular factor e^{i(tφ(k₀) + y·k₀)} that
    varies with t; harmless for a lower bound on the modulus.
    **Answer.** Noted in the clarification for consumers.
11. **MINOR (B, environment).** The brief said scipy and mpmath were available to the system python3; they were not, and
    the referee installed them in its scratch directory.
    **Answer.** Accepted for future briefs (state the interpreter that has them).

## Sanity layer after the answers

`OscInt/Front/D4UniformSanity.lean`, section "Added after the blind pre-proof reviews": `phase_elliptic`,
`const_not_totallyBounded`, `seqFamily_totallyBounded`, `uniform_seq_sanity`. Planted controls, second run
(`docs/replay/2026-11-15-D4U-sanity-plants.txt`): 9 plants; all unplanted copies accepted; 8 rejected, of which 6 are
refuted by compiled witnesses (ATB-finite-seq at the definition level, U-conj, ATB-no-budget, P-neg, O-moving,
O-unbounded) and 2 are true weakenings rejected on data (U-not-uniform-seq, O-forall-y); 1 NOT DETECTED (ATB-C0).
