# Roadmap

From a machine-checked research library to one that others can depend on: correct, usable, maintained, citable.
Items are in priority order within each section; sections are in the recommended order of work. Tick an item only
when its evidence exists (a committed record, a green CI run, a merged change), as in `docs/STATUS.md`. Items marked
**owner** need a decision or an action by the owner.

Downstream feedback (2026-11-06, from an independent session working in the same domain that could use the
library) is folded in below; items it raised are marked *(downstream)*. Its top five, in its order: explicit
constants for the 2D results; local smoothness hypotheses; asymptotic expansions; parametric uniformity everywhere;
a stable way to depend on the library. It asked not to change the trust chain.

## 1. Finish and stabilise the mathematics
- [ ] **S4.4** closed forms of c_C (statement frozen and reviewed; route in `docs/HANDOFF.md`): blueprint, route
      referee, proof agents, post-proof and adversarial review. After it, `make verify-all` must report PASS.
- [ ] Remove the duplication between `OscInt.D4.exists_piece_bound` and `d4BoundNe_of` (refactor the S4.1′
      assembly onto the lemma; the statement types are fixed, so the replay and type checks are the regression test).
- [ ] Put `GammaFree.lean` into the next stamp.
- [ ] Commitment computation time (`make commit`, minutes): profile `oscint-commit-env` and make it incremental.

## 2. A usable public API
The frozen statements use audit-friendly encodings (`oscInt2` on `ℝ × ℝ` with the max norm, `AmpBound`, `FamilyCk`,
nested-`fderiv` `dd`/`ddd`). Users write Mathlib idioms. Each new statement below is frozen, stamped and reviewed
like the existing ones; front-end versions are proved from frozen statements by bridge lemmas, so they inherit the
trust chain.
- [ ] **Explicit or effective constants** for S2–S4 *(downstream, first priority)*: C as a computable function of
      the derivative bounds of the phase, the gradient lower bound, the amplitude bound and the support size. The
      downstream project found a gap of about 20 orders of magnitude between what an existential constant allowed it
      to prove and what was observed.
- [ ] **Local smoothness hypotheses** *(downstream)*: every 2D statement now asks for a phase of class C⁴ on all of
      ℝ². Versions assuming smoothness only on a neighbourhood of the amplitude's support (natural for dispersion
      relations such as arccos-type phases, smooth only on an open set).
- [ ] **Parametric uniformity everywhere** *(downstream)*: uniformity over compact families of phases for S2.2 and
      S4 (now only S3 and S2.1 have it), and a fold statement requiring the fold-or-nondegenerate condition only at
      critical points, as in the classical statement (S3 now requires it on all of K; its referee noted this).
- [ ] **Asymptotic expansions** *(downstream)*: the leading term of nondegenerate stationary phase,
      (2π/m)^{n/2} |det D²Ψ|^{-1/2} e^{iπ sgn/4} e^{imΨ(k₀)} A(k₀) + O(m^{-n/2-1}), and the Airy leading term for folds.
- [ ] **Front-end theorems** in Mathlib idioms (integrals over `EuclideanSpace ℝ (Fin n)`, `ContDiff` plus
      `HasCompactSupport` amplitudes, norms via `iteratedFDeriv`).
- [ ] **Conversion lemmas** *(downstream)* from standard formulations (a Hessian as a `Matrix`, rank and kernel
      conditions, the classical discriminant) to `FoldOrNondeg`, `hessDet`, `cubicCoeffs`, `GradLower`, `AmpBound`.
- [ ] **Hypothesis checkers**: lemmas and a small tactic that discharge `disc (cubicCoeffs φ) ≠ 0`,
      `FoldOrNondeg`, `GradLower` and `AmpBound` for concrete polynomial phases and standard bumps, with failure
      messages naming the condition that fails rather than an unsolved goal.
- [ ] **Worked examples that double as non-vacuity checks** *(downstream)*: free Schrödinger decay, Bessel-function
      decay, an Airy-type fold, in `OscInt/Examples/`.
- [ ] **Sharpness lemma** *(downstream)*: a limit with a nonzero constant gives a matching lower bound on the decay
      rate (generalising the bite checks of S4.2 + S4.3).
- [ ] **Vector-valued amplitudes** *(downstream)* in a normed space (e.g. matrices), so spectral projections can be
      used directly instead of entry by entry.
- [ ] **Generality** *(downstream)*: dimension n for S2.1 and S2.2 (the largest audience gain); further singularity
      types — cusps (A₃, m^{-3/4}), D₅, E₆ — or, more ambitiously, the two-dimensional height / Newton-polygon bound
      of Ikromov–Müller, which covers these at once.

## 3. Interoperability and packaging
- [ ] **A stable way to depend on the library** *(downstream)*:
  - [ ] a tagged release (§6);
  - [ ] a README section on adding OscInt as a Lake dependency (`require oscint from git … @ "vX.Y.Z"`), with a tested
        example project in CI; Reservoir listing;
  - [ ] a stated Mathlib upgrade policy (below);
  - [ ] a machine-readable list of statement names with their SHA-256 commitments, stamps and statement-file hashes
        (e.g. `stamps/statements.json`, generated from `stamps/pins.txt` and the manifests and checked in CI), so a
        downstream project can check in its own CI that it depends on exactly the reviewed statements.
- [ ] **Mathlib version policy**: a documented bump procedure; a scheduled CI job building against a newer Mathlib
      that warns early. Statement commitments depend on Mathlib's definitions, so a bump changes them: decide (and
      record) the re-freeze rule, e.g. a machine-checked equivalence between each new statement and its stamped
      predecessor, then a new stamp and pin.
- [ ] Mathlib `module` syntax for the library files (needed to upstream; the statement files can only change with a
      re-freeze). Until then, `allowNonModules = true` in `lakefile.toml` (§4) would declare the mix.
- [ ] Stable public names and a deprecation policy; semantic versions (`CHANGELOG.md` exists).
- [ ] **owner** Upstream the general lemmas listed in `docs/upstream.md` to Mathlib *(downstream: partitions of unity
      with compact support, the polar-coordinates integral and the uniform Leibniz bounds first)*.

## 4. Developer experience
- [ ] Split CI: a fast pull-request job (build, guard, axiom audit, type checks, `GammaFree.lean`) and the full
      replay (`verify-all`) on `main` and on a schedule; `make quick` for the local loop; `verify-all --only <step>`.
- [ ] Generated API documentation (doc-gen4) published as a site; a browsable blueprint site with the dependency
      graph built from `Blueprint/` and the route documents *(downstream)*; statement docstrings that cite the textbook
      statement they formalise *(downstream)*.
- [ ] Build noise (seen in the CI log of PR #2): silence Lake's per-import module-system warnings with
      `allowNonModules = true` in `lakefile.toml` (Lake's documented opt-out; tested locally: 0 warnings, compilation
      unchanged); make `lean-replay`, `commit` and `comparator` depend on a `build/lean.ok` marker so `verify-all`
      runs the Lean step once instead of four times (lessons 7); replace the deprecated `if_false` in
      `OscInt/D4/LimitAssembly.lean`; install the pinned Rust toolchain explicitly in CI.
- [ ] `CONTRIBUTING.md`: how to add a statement end to end (statement file, sanity theorems, challenge, comparator
      configuration, stamp, pins, blind review, blueprint, proofs, replay, post-proof review, STATUS row).
- [ ] A scaffolder (`tools` binary) that generates the statement file, challenge, comparator configuration, sanity
      stub and pin lines for a new statement.
- [ ] Actionable error messages from the Rust tools (what failed, which file, the command to reproduce, the likely
      fix).
- [ ] Mathlib's linters (docstrings, unused hypotheses, style) in CI.

## 5. Utility and integrations
- [ ] **owner** Choose the first application. Candidates (the brief's deferred list and downstream requests):
  - [ ] **periodic and lattice settings** *(downstream)*: integrals over the torus with periodic amplitudes (the
        kernels of discrete-time dispersive problems: lattice Schrödinger, discrete wave equations, quantum walks),
        and exponential-sum versions of van der Corput;
  - [ ] **from decay to Strichartz** *(downstream)*: an abstract Keel–Tao theorem for continuous and discrete time,
        with the Hardy–Littlewood–Sobolev input;
  - [ ] decay for lattice Schrödinger operators on ℤ².
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
  1. [x] author name and ORCID iD in `CITATION.cff` and `.zenodo.json`; ORCID badge in `README.md`;
  2. [x] **owner** repository connected to Zenodo and ORCID (2026-11-06);
  3. [ ] **owner** publish the GitHub release `v0.2.0` with the notes in `CHANGELOG.md` (publishing the release is what
     makes Zenodo mint the DOI);
  4. [ ] add the Zenodo DOI badge to `README.md` and `doi:` to `CITATION.cff`;
  5. archive in Software Heritage; sign release artifacts (Sigstore).
- [ ] **owner** Publication: venue, preprint, outreach.
