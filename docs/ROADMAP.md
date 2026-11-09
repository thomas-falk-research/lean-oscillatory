# Roadmap

From a machine-checked research library to one that others can depend on: correct, usable, maintained, citable.
Items are in priority order within each section; sections are in the recommended order of work. Tick an item only
when its evidence exists (a committed record, a green CI run, a merged change), as in `docs/STATUS.md`. Items marked
**owner** need a decision or an action by the owner.

Downstream feedback (2026-11-06, from an independent session working in the same domain that could use the
library) is folded in below; items it raised are marked *(downstream)*. Its top five, in its order: explicit
constants for the 2D results; local smoothness hypotheses; asymptotic expansions; parametric uniformity everywhere;
a stable way to depend on the library. It asked not to change the trust chain.

## Session-7 order (owner, 2026-11-08)
Agreed in chat after reconciling the session-6 brief with an external review of `main` at 96f55a2. Research, in order:
0. Session-6 review follow-ups: `stamp verify` over every stamp directory (a1), no `.blob` files in stamp directories
   (f4), hash-locked pip installs (f5), a GD-N sanity datum smooth only on U (b2).
1. **Batch LE**: explicit constants for the 1D lattice kernel, pre-registered; by the factorisation
   (`docs/prior_art.md`, "Lattice kernels") they give the 2D constant of T6 as `C₁²`. Landau's constant is the external
   reference; certified numerics (P6) fold in as the independent comparison.
2. **Batch VV**: vector-valued amplitudes, done only when a non-separable model compiles end to end; fallback a
   finite-dimensional componentwise corollary. The vector-valued transfer is done (batch VT). No acceptance model yet: QWZ (m > 2)
   has exact cusp points (erratum, `docs/design/vector-amplitudes.md` §6), QWZ m = 1, 0.5 and the triangular lattice
   have cusps. Next steps (model search done properly, closed-form classification, or Strichartz first):
   `docs/design/vector-amplitudes.md` §7.
3. Strichartz estimates, non-endpoint (TT*), planned over 2–3 sessions: blueprint, prior-art sweep, frozen statement first.
4. The D4 bound uniform over compact families (read Karpushkin and Duistermaat 1974 first), then the arccos family.
Usability, in order: a reusable `oscint-verify` action and Lake template; doc-gen4 site with `llms.txt` from
`docs/api.json` (MCP server postponed); the `HasOscDecay` facade, each lemma an `Iff` with a frozen statement or frozen
itself; `oscint check` as a Python package; one Mathlib pull request (non-stationary phase); a Mathlib compatibility
matrix after the release. Developer experience: `make ci-dry`, the statement-closure diff tool, linters (SPDX outside
`Challenge/`, docstrings), elaboration times in CI, an opt-in pre-push hook. Human expert review: deferred under
`docs/policy.md`.

## Industry programme (owner, 2026-11-09)
Agreed in chat after an external strategy review of `main` at 87a418a and the lead's answer to it. The owner's goal:
a library and toolchain for the whole industry, not for any single consumer. Two rules follow. **Which theorems come
next is decided by evidence across many models** (item I1), not by one model or one user. **The interface is frozen
only after consumers from different domains have used it** (item I5). Items I1–I3 run in parallel; none waits on
another. Nothing here is a capability until its evidence exists (`docs/STATUS.md` rule above).
- [x] **I0 Release reconciliation.** v0.4.0 is published (tag → 87a418a, Zenodo 10.5281/zenodo.24088811). The
      `post-release` pins pull request (#9, merged as 87051c9) and the DOI record pull request (#10, merged as 621cdbe)
      are on `main`. #10's `verify` run on its final head (run 42667383698) passed all 17 jobs, but its `verdict`
      job was never created and the run is marked failed with no failed job (GitHub refused a re-run); the owner merged
      it on those 17 jobs. The `verify` run on `main` after the merge is the check of the merged tree.
- [ ] **I1 Singularity census of industry dispersion relations.** Which degenerate points (A3 cusps, A≥4, D4, D≥5, E/J,
      non-isolated sets, non-smooth points) occur in 18 2D models (nine weighted families, plus one unweighted re-check) across five domains (lattice materials,
      two-band topological models, quantum walks, numerical schemes, lattice waves), classified exactly by two
      independent methods with controls. Specification `docs/prereg/2026-11-09-CENSUS-spec.md`; registration draft
      `docs/prereg/2026-11-09-CENSUS-prereg.md` (registered only after both implementations exist and their development
      runs are disclosed; no run before). Its pre-fixed decision rule ranks the candidate theorem families by the
      number of models each one unlocks. It replaces the ad-hoc model search of `docs/design/vector-amplitudes.md`
      §7 option A as the way to choose the VV acceptance model.
- [ ] **I2 LeanCert integration experiment** (independent of I1 and I3). Question: can an external proof-producing
      numerics library discharge OscInt hypotheses for a concrete admissible phase without weakening the trust chain?
      Pins: LeanCert `44b323a0d6af00211d5013f6e021432db032087c` (HEAD on 2026-11-09; same Lean v4.35.0 and Mathlib
      `56a0058` as OscInt, VALIDATED from its `lean-toolchain` and `lake-manifest.json`), OscInt v0.4.0 (87a418a).
      Tests: A, a trigonometric derivative bound on a rational interval; B, a critical-point exclusion on a box, with
      a deliberately false exclusion that must fail or stay unresolved; C, a cusp-classification component (positive
      transverse curvature and nonzero reduced quartic on a neighbourhood). Pass means: each result is a Lean theorem
      checked with LeanCert's `kernel` mode only (`native` and `auto` are recorded as separate, weaker benchmarks); its
      axioms are within OscInt's audit allowlist; the per-module kernel replay of `verify-all` accepts it; cost (time,
      memory, proof size) recorded against a hand proof. A separate pre-registration comes before the first run. No
      copy of LeanCert's engine into OscInt unless a limitation is demonstrated.
- [ ] **I3 Theorem programme, ordered by I1** (provisional until I1's result): a general k-th-order van der Corput
      bound (only k = 1, 2, 3 exist: S1.1–S1.3); the local A3 bound `t^{−3/4}` uniform in the linear term (route to be
      chosen at registration: transverse stationary phase plus fourth-order van der Corput, or a parametric normal
      form); global assembly with finitely many A3 points; leading terms with remainders (SAR and seismic steps use the
      leading term); nondegenerate stationary phase in dimension n; non-endpoint Strichartz; the Ikromov–Müller
      height bound, which covers all finite-type 2D singularities, with the A3 statements shaped to be derivable from
      it. Every batch statement-first under `CONTRIBUTING.md`.
- [ ] **I4 A "useful from" standard for every explicit constant.** Each explicit-constant statement in `docs/api.json`
      gets three fields: the parameter threshold above which it beats the trivial bound (T0E: `t > 518`; T6E:
      `t > 1321`, both from `docs/HANDOFF.md`), the best known bound for comparison with its citation (Landau's
      constant for T0E/T6E, `docs/prior_art.md`), and a checked numerical enclosure of the constant. A generator
      change (`tools/gen_api.py`, `docs/api/annotations.json`), checked by `make api-check`.
- [ ] **I5 Interface, frozen late.** One language-neutral contract (`docs/api.json` plus a certificate schema carrying
      exact constants and their enclosures) behind a CLI with JSON output, a Python package and a Rust crate. Version 1
      of the contract is frozen only after at least two consumers from different domains have used it; a C ABI and
      further languages come when a consumer asks. Trust boundary, fixed now: only the defined checker
      (`tools/oscint_check.py` or its successor) may give a result the status CERTIFIED; adapters transport and
      display evidence and can never confer that status.
- [ ] **I6 Credibility that adopters check first:** the human expert reading of the statements (owner item, §6; today
      every fidelity reading is by AI referees), a preprint, the Reservoir listing (§3), the first Mathlib pull request
      (§3).
- Input language for I1, I2 and I5: `docs/decisions/2026-11-09-input-language.md` (trigonometric polynomials with
  rational coefficients under an outer function `G` with `(G′)²` rational).

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
- [x] **Local smoothness hypotheses** *(downstream)* (front-end batch 3, 2026-11-08: FE-S2.1L/S2.2L/S3L/S4.1′L and single-phase
      forms, `docs/STATUS.md`, record `docs/replay/2026-11-08-session5-API3-verify-all.txt`; acceptance
      `examples/consumer/ConsumerLocal.lean`): every 2D statement now asks for a phase of class C⁴ on all of
      ℝ². Versions assuming smoothness only on a neighbourhood of the amplitude's support (natural for dispersion
      relations such as arccos-type phases, smooth only on an open set).
- [ ] **Parametric uniformity everywhere** *(downstream)* (done 2026-11-08 except S4: S2.2F family stationary phase,
      S3c fold with the classical hypothesis, family front ends; `docs/STATUS.md`; open: S4.1′ over a family): uniformity over compact families of phases for S2.2 and
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
- [x] **Sharpness lemma** *(downstream)* (SH `OscInt.API.sharpness`, batch GD; applied, with T6L, to the lattice kernel, `examples/consumer/ConsumerLattice.lean`; replay `docs/replay/2026-11-08-session6-GD-verify-all.txt`): a limit with a nonzero constant gives a matching lower bound on the decay
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
  - [ ] decay for lattice Schrödinger operators on ℤ²: done for the free discrete Laplacian (T6, T6L: kernel `O(t^{-2/3})` uniformly in `x` for `t ≥ 1`, sharp; ℓ¹ → ℓ^∞ for finitely supported data in `examples/consumer/ConsumerLattice.lean`; replay `docs/replay/2026-11-08-session6-GD-verify-all.txt`); with a potential: open.
- [ ] Numerics as a product: `numerics/` as a library and CLI with JSON output that checks hypotheses numerically,
      evaluates c_C and tabulates sharp rates for a given phase (tooling, never evidence).

## 6. Trust, provenance and release
- [ ] **owner** Human review of the statements: one expert reading `docs/statements.md` against
      `OscInt/Statements/` (today all fidelity readings are by AI referees).
- [ ] **owner** Mathlib built from source on a second machine (`lake build Mathlib` without the cache, then
      `make commit`), recorded in `docs/toolchain.md`.
- [ ] Upgrade the OpenTimestamps proofs in `stamps/` from pending to Bitcoin-attested, and verify them.
- [ ] **owner** Branch protection on `main` requiring CI (checks named in `docs/decisions/2026-11-08-ci-release-review.md` §4). [x] Dependabot for the SHA-pinned GitHub Actions (`.github/dependabot.yml`, session 6).
- [ ] **First release** (`v0.2.0`; steps 1–4 done, step 5 open), in this order:
  1. [x] author name and ORCID iD in `CITATION.cff` and `.zenodo.json`; ORCID badge in `README.md`;
  2. [x] **owner** repository connected to Zenodo and ORCID (2026-11-06);
  3. [x] **owner** GitHub release `v0.2.0` published (2026-11-06); Zenodo minted 10.5281/zenodo.24021329
     (concept DOI 10.5281/zenodo.24021328);
  4. [x] Zenodo DOI badge in `README.md`; `doi:` and `identifiers:` in `CITATION.cff`;
  5. archive in Software Heritage (owner, "Save code now"); [ ] sign release artifacts (Sigstore build-provenance attestation prepared in `release-candidate.yml`, session 6; not ticked until its first run).
- [x] **owner** Release v0.3.0: published 2026-11-07 (tag → 7098f09; external dry run
      `docs/replay/2026-11-08-external-downstream-dry-run-v0.3.0.txt`); prepared 2026-11-07 (`docs/release-notes/v0.3.0.md`, CHANGELOG, version 0.3.0 in
      `lakefile.toml`, `CITATION.cff`, `.zenodo.json`); CI job `release-pin` is red until the tag exists.
- [ ] **owner** Publication: venue, preprint, outreach.
