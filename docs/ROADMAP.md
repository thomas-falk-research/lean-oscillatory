# Roadmap

From a machine-checked research library to one that others can depend on: correct, usable, maintained, citable.
Items are in priority order within each section; sections are in the recommended order of work. Tick an item only
when its evidence exists (a committed record, a green CI run, a merged change), as in `docs/STATUS.md`. Items marked
**owner** need a decision or an action by the owner.

## 1. Finish and stabilise the mathematics
- [ ] **S4.4** closed forms of c_C (statement frozen and reviewed; route in `docs/HANDOFF.md`): blueprint, route
      referee, proof agents, post-proof and adversarial review. After it, `make verify-all` must report PASS.
- [ ] Remove the duplication between `OscInt.D4.exists_piece_bound` and `d4BoundNe_of` (refactor the S4.1′
      assembly onto the lemma; the statement types are fixed, so the replay and type checks are the regression test).
- [ ] Put `GammaFree.lean` into the next stamp.
- [ ] Commitment computation time (`make commit`, minutes): profile `oscint-commit-env` and make it incremental.

## 2. A usable public API
The frozen statements use audit-friendly encodings (`oscInt2` on `ℝ × ℝ` with the max norm, `AmpBound`, `FamilyCk`,
nested-`fderiv` `dd`/`ddd`). Users write Mathlib idioms.
- [ ] **Front-end theorems** in Mathlib idioms (integrals over `EuclideanSpace ℝ (Fin n)`, `ContDiff` plus
      `HasCompactSupport` amplitudes, norms via `iteratedFDeriv`), each proved from a frozen statement by bridge
      lemmas, so it inherits the trust chain. Freeze and review the front-end statements like the others.
- [ ] **Hypothesis checkers**: lemmas and a small tactic that discharge `disc (cubicCoeffs φ) ≠ 0`,
      `FoldOrNondeg`, `GradLower` and `AmpBound` for concrete polynomial phases and standard bumps, with failure
      messages naming the condition that fails (e.g. "Hessian degenerate at k and third derivative along the kernel
      vanishes") rather than an unsolved goal.
- [ ] **Explicit constants** for S2–S4 (currently existential), at least computable upper bounds in terms of
      derivative bounds of the phase and the amplitude.
- [ ] **Generality**: dimension n for S2.1 and S2.2; families of D4 phases (uniformity in φ); further simple
      singularities (D5, E6, …) where users need them.
- [ ] Examples file (`OscInt/Examples.lean`) showing each theorem applied to a concrete integral.

## 3. Interoperability and packaging
- [ ] Mathlib `module` syntax for the library files (needed to import cleanly and to upstream; removes the build
      warnings).
- [ ] **Mathlib version policy**: a documented bump procedure; a scheduled CI job building against a newer Mathlib
      that warns early. Statement commitments depend on Mathlib's definitions, so a bump changes them: decide (and
      record) the re-freeze rule, e.g. a machine-checked equivalence between each new statement and its stamped
      predecessor, then a new stamp and pin.
- [ ] Stable public names and a deprecation policy; `CHANGELOG.md`; semantic versions.
- [ ] Consumable as a Lake dependency (`require oscint from git … @ "vX.Y.Z"`) with a tested example project in CI;
      Reservoir listing.
- [ ] **owner** Upstream the general lemmas listed in `docs/upstream.md` to Mathlib.

## 4. Developer experience
- [ ] Split CI: a fast pull-request job (build, guard, axiom audit, type checks, `GammaFree.lean`) and the full
      replay (`verify-all`) on `main` and on a schedule; `make quick` for the local loop; `verify-all --only <step>`.
- [ ] Generated API documentation (doc-gen4) published as a site; a blueprint site with the dependency graph built
      from `Blueprint/` and the route documents.
- [ ] `CONTRIBUTING.md`: how to add a statement end to end (statement file, sanity theorems, challenge, comparator
      configuration, stamp, pins, blind review, blueprint, proofs, replay, post-proof review, STATUS row).
- [ ] A scaffolder (`tools` binary) that generates the statement file, challenge, comparator configuration, sanity
      stub and pin lines for a new statement.
- [ ] Actionable error messages from the Rust tools (what failed, which file, the command to reproduce, the likely
      fix).
- [ ] Mathlib's linters (docstrings, unused hypotheses, style) in CI.

## 5. Utility and integrations
- [ ] **owner** Choose the first application. Candidates from the brief's deferred list: dispersive decay and
      Strichartz estimates via Keel–Tao, discrete Hardy–Littlewood–Sobolev, decay for lattice Schrödinger operators
      on ℤ².
- [ ] Numerics as a product: `numerics/` as a library and CLI with JSON output that checks hypotheses numerically,
      evaluates c_C and tabulates sharp rates for a given phase (tooling, never evidence).

## 6. Trust, provenance and release
- [ ] **owner** Human review of the statements: one expert reading `docs/statements.md` against
      `OscInt/Statements/` (today all fidelity readings are by AI referees).
- [ ] **owner** Mathlib built from source on a second machine (`lake build Mathlib` without the cache, then
      `make commit`), recorded in `docs/toolchain.md`.
- [ ] Upgrade the OpenTimestamps proofs in `stamps/` from pending to Bitcoin-attested, and verify them.
- [ ] **owner** Branch protection on `main` requiring CI; Dependabot for the SHA-pinned GitHub Actions.
- [ ] **First release** (`v0.2.0`), in this order:
  1. **owner** author name and ORCID iD in `CITATION.cff` (`authors: - family-names, given-names, orcid`);
  2. **owner** connect the repository to Zenodo (GitHub integration) so a release mints a DOI;
  3. tag and publish the GitHub release with release notes from `CHANGELOG.md` (owner approves the tag);
  4. add to `README.md` the Zenodo DOI badge and the ORCID badge linking `https://orcid.org/<iD>`, and the DOI to
     `CITATION.cff`;
  5. archive in Software Heritage; sign release artifacts (Sigstore).
- [ ] **owner** Publication: venue, preprint, outreach.
