# Changelog

Versions follow semantic versioning from v0.3.0 (`docs/policy.md`): before 1.0.0, a minor version (0.y.0) may change
statements and says so under "Statement changes"; a patch (0.y.Z) changes no statement, commitment, statement file
or `proved_by` name. Every release lists its statement changes, even when there are none.

## Unreleased

Nothing yet.

## v0.3.0 — prepared 2026-11-07, not yet published

The owner publishes releases; the steps, the SHA-256 pins and (after the release commit) its full hash are in
`docs/release-notes/v0.3.0.md` and `docs/release-notes/v0.3.0.commit`. A first preparation at 2e8707a was withdrawn
after the adversarial review (`review/2026-11-07-API2-adversarial.md`, M1, M6): v0.3.0 is the session's final commit.

### Statement changes
Against v0.2.0 (`stamps/pins.txt` at tag `v0.2.0` and now): **no existing statement changed**. The eleven statement
constants of v0.2.0 keep their statement files byte for byte and their commitments (`make commit`: every commitment
equals its pinned stamp; this session's records under `docs/replay/2026-11-07-*`).
- Added (front-end batch 1): `AmpBoundOfContDiffStatement` (F1), `D4LimitClosedFormStatement` (F2), file
  `OscInt/Statements/FrontEnd.lean`, stamp `stamps/20261107T012459Z-2d5356432156`.
- Added (front-end batch 2): fourteen statements in `OscInt/Statements/Convert.lean`, stamp
  `stamps/20261107T101640Z-4acb308f54f4`: C1 `DdEqIteratedStatement`, C2 `DddEqIteratedStatement`, C3
  `HessDetEqDetStatement`, C4 `CubicCoeffsEqStatement`, C5 `DiscEqCubicDiscrStatement`, C6
  `DiscNeZeroIffIsolatedStatement`, C7 `FoldOrNondegIffStatement`, C7′ `FoldOrNondegOfHasFDerivStatement`, C8
  `GradLowerIffStatement`, C9 `AmpBoundConvStatement`, FE-S2.1 `NonStationaryFEStatement`, FE-S2.2
  `StationaryPhaseFEStatement`, FE-S3 `FoldFEStatement`, FE-S4.1′ `D4BoundFEStatement`.
- `proved_by` set: S4.4 (`OscInt.d4ConstantClosedForm`), F1, F2, and all fourteen batch-2 statements (`OscInt.API.*`).
- New: `stamps/statements.json` itself (v0.2.0 had none); 27 statements.

### Front-end batch 2 (new; statement-first order restored)
- Conversions from Mathlib's idiom to the frozen encodings: `iteratedFDeriv` ↔ `dd`/`ddd` (C1, C2), `hessDet` ↔
  `Matrix.det` of the Hessian matrix (C3), `cubicCoeffs` ↔ the coefficients of D³φ(0)[κ,κ,κ]/6 (C4), `disc` ↔
  Mathlib's `Cubic.discr` (C5), `disc ≠ 0` ↔ isolated critical point (C6), `FoldOrNondeg` ↔ kernel/rank form of the
  Hessian matrix (C7) and from `HasFDerivAt` data (C7′), `GradLower` ↔ Euclidean and max-norm bounds (C8), `AmpBound` ↔
  `ContDiff` + `HasCompactSupport` (C9).
- Front ends for S2.1, S2.2, S3, S4.1′ with `ContDiff`, `tsupport`, `iteratedFDeriv` bounds and linear terms as
  continuous linear functionals (one phase each). Entry point unchanged: `import OscInt.API` (now exposes them).
- Hypothesis helpers `OscInt/Front/Poly.lean` (P2): derivative data of explicit polynomial phases from `ring`
  identities; `examples/consumer/ConsumerFormula.lean`: FE-S3 and FE-S4.1′ on phases given only by a formula.
- Order: statements stamped (RFC 3161 ×3) and reviewed blind (FAITHFUL ×2) before any Lean proof; post-proof
  FAITHFUL ×2; adversarial review answered (`review/2026-11-07-API2-*`). What is and is not evidenced about the order:
  `docs/statements.md`, clarification of 2026-11-07 (lessons 29).

### Machine-checked as stated
- **S4.4** closed forms of the D4 constant (`OscInt.d4ConstantClosedForm`): ∫₀^∞ cos u · u^{−1/3} du = Γ(2/3)/2, and
  c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) for Disc C < 0, c_C = Γ(1/3)²/(Disc C)^{1/6} for Disc C > 0. With S4.2 this is
  the brief's S4 limit with its closed-form constant. Route `docs/proof-S44.md` (real-variable: Fubini and dominated
  convergence for the cosine moment, the chart u = tan θ, GL₂ covariance of the angular integral, reduction to two
  normal forms, Beta integrals, Legendre duplication and Euler reflection); the hand-off's Abel/complex-rate route
  was replaced because `Complex.integral_cpow_mul_exp_neg_mul_Ioi` takes a real rate (lessons 19).
- `OscInt.d4Constant_example`: the closed form on x³ + 2x²y + 3xy² + 5y³ (disc −367).
- Front-end batch 1 (`OscInt/API.lean`, the new entry point): F1 `OscInt.API.ampBoundOfContDiff` (a Cⁿ amplitude with
  compact support satisfies `AmpBound`) and F2 `OscInt.API.d4LimitClosedForm` (the D4 limit with its closed-form
  constant for one C² amplitude, both umbilics); bridges drafted before the statement review, disclosed. Non-vacuity
  and bite: `OscInt/Front/Sanity.lean`.

### Depending on OscInt (new)
- `stamps/statements.json`: every pinned statement with label, summary, proving theorem, statement file and SHA-256,
  commitment, stamp and stamped commit; generated (`make statements`) and checked in CI (`statements-check`).
- `tools/oscint_check.py`: a downstream CI checks the toolchain and Mathlib, the statement file hashes, that each
  statement constant comes from its frozen file, syntactic statement types, axioms, a kernel replay of every OscInt
  module and recomputed commitments; it detects drift, not tampering (README); negative controls, one per check, in
  `tools/test_oscint_check.sh` (the first version, found breakable by the adversarial review, is not released).
- `examples/consumer/`: a tested downstream Lake project; README section "Depending on OscInt".
- `docs/policy.md`: semantic versions from v0.3.0, the stable surface, deprecation, and the Mathlib re-freeze rule.

### Developer experience
- `make quick` (fast loop and pull-request job), `make verify-all ONLY="…"` (partial runs, labelled as such),
  a preflight in `verify-all` for missing system tools and shallow clones (lessons 21); CI split into `quick`,
  `verify` (every push, weekly), `consumer`; `CONTRIBUTING.md`.
- Build noise: `allowNonModules = true` (0 warnings), the Lean step runs once per `verify-all` (`build/lean.ok`),
  `ite_false` for the deprecated `if_false`, the Rust toolchain installed explicitly in CI.
- `tools/check_release_pin.sh` and CI job `release-pin`: CI fails while README, `docs/policy.md` or the consumer
  examples pin a release tag that does not exist, that does not point to the commit recorded in
  `docs/release-notes/<tag>.commit`, or whose notes do not give the SHA-256 of `stamps/statements.json` and
  `tools/oscint_check.py` at that commit (25 self-test cases; hardened after the adversarial review).
- `tools/check_entry_point.sh` (in `make quick`): `import OscInt.API` exposes every statement and proving theorem of
  `stamps/statements.json`.
- `examples/consumer-release/` and CI job `consumer-release`: a downstream project requiring OscInt from GitHub by its
  release tag, built and checked against the pinned SHA-256 (runs once the tag exists).

### Fixed
- `lakefile.toml` said version 0.1.0 (then 0.2.0); it, `CITATION.cff` and `.zenodo.json` now say 0.3.0.
- README told users to pin `v0.3.0` before that tag existed; this is now detected (`release-pin`), and README says
  the release is pending.
- `docs/policy.md` showed the pin in `lakefile.lean` syntax next to README's `lakefile.toml`; both use TOML now.
- `docs/ROADMAP.md` and `docs/HANDOFF.md` listed "put `GammaFree.lean` into the next stamp" as open; it already is
  (manifest of `stamps/20261107T012459Z-2d5356432156`, SHA-256 `5dc19eb4…`, the file's current hash).

### Documentation
- `docs/ROADMAP.md`: downstream feedback folded in (explicit constants, local smoothness, asymptotic expansions,
  parametric uniformity, stable dependency with a machine-readable statement list, periodic and lattice settings,
  Keel–Tao).

## v0.2.0 — 2026-11-06

DOI [10.5281/zenodo.24021329](https://doi.org/10.5281/zenodo.24021329) (all versions:
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328)). First release. Machine-checked as stated (`docs/STATUS.md`; record `docs/replay/2026-11-06-S4b-final-verify-all.txt`):

- S1 one-dimensional van der Corput lemma with amplitude, constants 3, 8, 18 (`OscInt.vanDerCorput_one/two/three`;
  proof ported from roos-j/lean-oscillatory, Mathlib PR #39406).
- S2.1 non-stationary phase, O(m^{-N}), uniform over compact families and all linear terms (`OscInt.nonStationary`).
- S2.2 nondegenerate stationary phase, O(m^{-1}), uniform in the linear term (`OscInt.stationaryPhase`).
- S3 uniform fold estimate, O(m^{-5/6}) (`OscInt.fold`).
- S4.1 uniform D4⁺ estimate t^{-2/3}, uniform in the linear term (`OscInt.d4Bound`); S4.1′ the same for both umbilics,
  `disc ≠ 0` (`OscInt.d4BoundNe`).
- S4.2 D4 limit t^{2/3}∫e^{itφ}A → c_C A(0), c_C defined without the Gamma function (`OscInt.d4Limit`).
- S4.3 c_C > 0 by an alternating-series argument, proof Gamma/Beta/Mellin-free by name (`OscInt.d4ConstantPos`).

Not yet proved: S4.4, the closed forms of c_C (statement frozen and reviewed). The brief's limit with the constant
Γ(1/3)²/(√3|Disc|^{1/6}) is S4.2 together with S4.4.

Trust chain: statements stamped (RFC 3161 ×3, OpenTimestamps pending) and blind-reviewed before proofs; axiom audit
(`propext`, `Classical.choice`, `Quot.sound` only); `lake comparator` against the frozen challenges; replay by
`leanchecker` per module and six export kernels (Lean, Lean paranoid, lean4lean, nanoda, con-leche, con-ron), with
nanoda also built from source in CI. Reviews are by AI referees (calibrated: 8/8 planted errors caught); no human
review yet. Toolchain: Lean v4.35.0, Mathlib `56a0058`.
