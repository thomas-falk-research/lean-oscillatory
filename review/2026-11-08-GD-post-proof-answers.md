# Answers to the GD post-proof reviews (A, B) and the adversarial review

Reports (verbatim, all on c98f496): `review/2026-11-08-GD-post-proof-A.md`, `review/2026-11-08-GD-post-proof-B.md`
(both: all eight theorems FAITHFUL, scope full, no BLOCKER or MAJOR), `review/2026-11-08-GD-adversarial.md` (no BLOCKER
or MAJOR; claims (a)–(c), (f), (g) hold; (d), (e) with qualifications). No referee wrote in the repository. The
statements, stamps and the proofs of the final theorems are unchanged by everything below.

## Post-proof A and B
- **A, B MINOR (GD-C, GD-F, GD-N, T1 never applied to concrete data in a compiled file).** Added
  `examples/consumer/ConsumerGlobalChecks.lean` (in `make quick`): every conditional sanity theorem instantiated with
  the proved theorem (13 lines).
- **B MINOR 1 (no record that `ConsumerLattice.lean` compiles at the reviewed tree).** `make quick` compiles it; the run
  on the head is recorded in `docs/replay/2026-11-08-session6-final-quick.txt`.
- **B MINOR 2, adversarial p2 (ROADMAP overclaims "lattice Schrödinger operators").** Corrected: free discrete
  Laplacian, `t ≥ 1`, finitely supported data; potentials open (item unticked).
- **A MINOR (no kernel replay of HEAD).** Agreed. The local replay is of c62a621; later commits add comment-only
  headers (record `docs/replay/2026-11-08-session6-licence-headers-checks.txt`) and, after these reviews, sanity
  theorems in `OscInt/Front/GlobalSanity.lean`, which `OscInt/Front/LatticeSymbol.lean` imports. The CI `verify`
  workflow replays the pull request's head; STATUS cites both.
- **A MINOR (statement-first order not fully auditable).** Agreed; the claim is worded as in lessons 29 (review stamp
  10:26:32Z before the first proof commit; that nothing existed in scratch before it rests on the lead's statement).
  Adversarial a1 adds that the agents' scratch files on this machine start at 10:27:57Z.
- **Nits.** Stale wording in `docs/cookbook.md`, `docs/applications.md`, CHANGELOG's GD-C line and the ROADMAP SH line:
  fixed. `if_pos` deprecation: fixed. The ℓ¹ → ℓ^∞ wording: clarification (8) in `docs/statements.md`. The prompt's
  `LatticeLimitFinal.lean`: the file is `LatticeFinal.lean` (prompt left as committed).

## Adversarial
- **a1 (review stamps not re-verified; agent launch times not committed).** Not fixed here: verifying every stamp
  directory, not only pinned ones, is a tool change (`tools/src/bin/stamp.rs`); recorded as a follow-up in HANDOFF.
- **b1 (T1 conclusion-weakening plants accepted).** Fixed: `torusUnfold_moments` returns the smoothness and support
  conjuncts; the two plants (radius 400; `Continuous`) are now rejected at the conclusion (17/17 plants,
  `docs/replay/2026-11-08-GD-sanity-plants.txt`, third run).
- **b2 (C⁴ ↦ C⁵ rejected only by brittleness; `U ↦ univ` in GD-N accepted; no datum smooth only on U).** Agreed, not
  fixed: these are weakening or non-semantic cases the conditional form cannot separate (stated in the sanity file's
  header); a datum smooth only on U for GD-N is a candidate for the next batch's sanity layer.
  Follow-up (same day): added `globalNondeg_local` (`OscInt/Front/GlobalNondegLocalSanity.lean`), Ψ = x² + 3xy + 5y²
  + |x − 3|, C⁴ on U = B(0, 2) and not C¹ on ℝ² (`localPhase_not_contDiff`); the plants `ContDiffOn ℝ 4 Ψ U ↦
  ContDiff ℝ 4 Ψ` and `U ↦ Set.univ` in that hypothesis are now rejected for a semantic reason
  (`docs/replay/2026-11-08-GDN-local-sanity-plants.txt`). C⁴ ↦ C⁵ remains rejected only by brittleness.
- **c1 (snippet check was a substring test; annotations unchecked).** The snippet check is now whole-name for the
  statement constant and the proving theorem, with a planted control (`tools/test_gen_api.sh`, 7 plants). The
  hand-written prose (hypotheses, rate, uniformity) is not machine-checkable; `docs/api.json` carries the frozen Lean
  text (`lean_statement`) next to it, which is authoritative. GD-F, GD-N annotations gained "K compact".
- **d1 (only t^{-3/4} excluded).** Added `latticeLaplacian_sharp_all` (every σ′ > 2/3) and used it in the consumer
  example.
- **d2 (`propagator` only a definition; finitely supported data).** Stated in the consumer docstring and clarification
  (8).
- **e1 (release step assumed a docs-only decision).** The step now distinguishes the options.
- **f1 (AI authorship not disclosed in headers/CITATION).** The owner's call; put to the owner in the final report.
- **g1 (metadata versions vs content; codemeta not checked).** Abstracts now describe v0.3.0; the v0.4.0 text is in the
  release steps; `tools/release_preflight.sh` checks `codemeta.json`'s version (10 plants).
- **g2 (Lean 4 reference).** Collection title "Automated Deduction – CADE 28" (Crossref lists it with the LNCS series);
  the volume is not given by Crossref and is not stated.
- **g3, p1, p3, e2.** Fixed (HANDOFF, applications, README opening and DOI line, memo sentence).
- **f2 (REUSE counts).** The count of the final tree is in the final record.
- **f3 (no kernel replay on the headed tree).** As post-proof A above.
- **f4 (`stamp verify` writes `.blob` in stamp directories).** Not changed (tool change); recorded in HANDOFF.
- **f5 (pip installs without hash pins).** Not changed: versions are pinned; hash-pinning the transitive
  dependencies of `reuse` and `cffconvert` needs a lock file; recorded in HANDOFF.
- **c2 (`lean_statement` omits the docstring).** By design; the docstring is the `summary` field.
