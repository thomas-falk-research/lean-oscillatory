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
- [x] **S4.4** closed forms of c_C: machine-checked as stated (2026-11-07; `docs/STATUS.md`; verify-all PASS,
      `docs/replay/2026-11-06-S44-verify-all.txt`; post-proof FAITHFUL ×2; adversarial answered).
- [ ] Remove the duplication between `OscInt.D4.exists_piece_bound` and `d4BoundNe_of` (refactor the S4.1′
      assembly onto the lemma; the statement types are fixed, so the replay and type checks are the regression test).
- [x] Put `GammaFree.lean` into the next stamp: it is in `stamps/20261107T012459Z-2d5356432156` (RFC 3161 ×3) at its
      current SHA-256 `5dc19eb4…` (verified 2026-11-07, `docs/replay/2026-11-07-session4-baseline-quick.txt`).
- [ ] Commitment computation time (`make commit`, minutes): profile `oscint-commit-env` and make it incremental.

## 2. A usable public API
The frozen statements use audit-friendly encodings (`oscInt2` on `ℝ × ℝ` with the max norm, `AmpBound`, `FamilyCk`,
nested-`fderiv` `dd`/`ddd`). Users write Mathlib idioms. Each new statement below is frozen, stamped and reviewed
like the existing ones; front-end versions are proved from frozen statements by bridge lemmas, so they inherit the
trust chain.
- [ ] **Explicit or effective constants** for S2–S4 *(downstream, first priority; explored 2026-11-07,
      `docs/constants.md`: the existing route gives only crude constants)*: C as a computable function of
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
- [ ] **Front-end theorems** in Mathlib idioms (batch 1 done 2026-11-07: F1 `ContDiff`-plus-compact-support amplitudes,
      F2 the D4 limit with its closed-form constant, entry point `OscInt/API.lean`; batch 2 done 2026-11-07: S2.1, S2.2,
      S3, S4.1′ front ends for one phase, `docs/STATUS.md`; next: family versions,
      `iteratedFDeriv` conversions, `EuclideanSpace`) (integrals over `EuclideanSpace ℝ (Fin n)`, `ContDiff` plus
      `HasCompactSupport` amplitudes, norms via `iteratedFDeriv`).
- [x] **Conversion lemmas** *(downstream)*, front-end batch 2 (2026-11-07; C1–C9, C7′; `docs/STATUS.md`, record
      `docs/replay/2026-11-07-session4-final-verify-all.txt`), from standard formulations (a Hessian as a `Matrix`, rank and kernel
      conditions, the classical discriminant) to `FoldOrNondeg`, `hessDet`, `cubicCoeffs`, `GradLower`, `AmpBound`.
- [ ] **Hypothesis checkers** (lemmas done: `OscInt/Front/Poly.lean`, used by `examples/consumer/ConsumerFormula.lean`;
      tactic not started, needs a guard-policy decision): lemmas and a small tactic that discharge `disc (cubicCoeffs φ) ≠ 0`,
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
  - [x] a tagged release (`v0.2.0`, §6);
  - [x] a README section on adding OscInt as a Lake dependency, with a tested example project (`examples/consumer/`,
        built and checked locally; CI job `consumer` on main and pull requests); [ ] Reservoir listing (owner);
  - [x] a stated Mathlib upgrade policy (`docs/policy.md`; its cheap re-freeze path waits on the closure-diff tool below);
  - [x] a machine-readable list of statement names with their SHA-256 commitments, stamps and statement-file hashes
        (`stamps/statements.json`, generated and checked in verify-all), and a downstream checker
        (`tools/oscint_check.py`, hardened after the adversarial review of 2026-11-07; negative controls
        `tools/test_oscint_check.sh`). It detects drift, not tampering (README).
  - [ ] Closure-diff tool (technical debt from `docs/policy.md`): per-constant canonical hashes with local numbering
        and a listing of changed constants with old and new values, so a Mathlib upgrade can be re-frozen by one
        referee instead of a full new statement.
- [ ] **Mathlib version policy**: a documented bump procedure; a scheduled CI job building against a newer Mathlib
      that warns early. Statement commitments depend on Mathlib's definitions, so a bump changes them: decide (and
      record) the re-freeze rule, e.g. a machine-checked equivalence between each new statement and its stamped
      predecessor, then a new stamp and pin.
- [ ] Mathlib `module` syntax for the library files (needed to upstream; the statement files can only change with a
      re-freeze). Until then, `allowNonModules = true` in `lakefile.toml` (§4) would declare the mix.
- [x] Stable public names and a deprecation policy; semantic versions (`docs/policy.md`, from v0.3.0).
- [ ] **owner** Upstream the general lemmas listed in `docs/upstream.md` to Mathlib *(downstream: partitions of unity
      with compact support, the polar-coordinates integral and the uniform Leibniz bounds first)*.

## 4. Developer experience
- [x] Split CI (CI jobs `quick`, `verify`, `consumer`; `make quick`; `verify-all ONLY=`): a fast pull-request job (build, guard, axiom audit, type checks, `GammaFree.lean`) and the full
      replay (`verify-all`) on `main` and on a schedule; `make quick` for the local loop; `verify-all --only <step>`.
- [ ] Generated API documentation (doc-gen4) published as a site; a browsable blueprint site with the dependency
      graph built from `Blueprint/` and the route documents *(downstream)*; statement docstrings that cite the textbook
      statement they formalise *(downstream)*.
- [x] Build noise (seen in the CI log of PR #2; fixed in 828309a, 0 warnings): silence Lake's per-import module-system warnings with
      `allowNonModules = true` in `lakefile.toml` (Lake's documented opt-out; tested locally: 0 warnings, compilation
      unchanged); make `lean-replay`, `commit` and `comparator` depend on a `build/lean.ok` marker so `verify-all`
      runs the Lean step once instead of four times (lessons 7); replace the deprecated `if_false` in
      `OscInt/D4/LimitAssembly.lean`; install the pinned Rust toolchain explicitly in CI.
- [x] `CONTRIBUTING.md`: how to add a statement end to end (statement file, sanity theorems, challenge, comparator
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
- [ ] **First release** (`v0.2.0`; steps 1–4 done, step 5 open), in this order:
  1. [x] author name and ORCID iD in `CITATION.cff` and `.zenodo.json`; ORCID badge in `README.md`;
  2. [x] **owner** repository connected to Zenodo and ORCID (2026-11-06);
  3. [x] **owner** GitHub release `v0.2.0` published (2026-11-06); Zenodo minted 10.5281/zenodo.24021329
     (concept DOI 10.5281/zenodo.24021328);
  4. [x] Zenodo DOI badge in `README.md`; `doi:` and `identifiers:` in `CITATION.cff`;
  5. archive in Software Heritage; sign release artifacts (Sigstore).
- [ ] **owner** Release v0.3.0: prepared 2026-11-07 (`docs/release-notes/v0.3.0.md`, CHANGELOG, version 0.3.0 in
      `lakefile.toml`, `CITATION.cff`, `.zenodo.json`); CI job `release-pin` is red until the tag exists.
- [ ] **owner** Publication: venue, preprint, outreach.
