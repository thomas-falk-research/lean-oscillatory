# Changelog

Versions follow semantic versioning once the public API (`docs/ROADMAP.md` §2) exists; until then a minor version
marks a set of newly machine-checked statements.

## Unreleased

Planned as v0.3.0 (the owner publishes releases).

### Machine-checked as stated
- **S4.4** closed forms of the D4 constant (`OscInt.d4ConstantClosedForm`): ∫₀^∞ cos u · u^{−1/3} du = Γ(2/3)/2, and
  c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) for Disc C < 0, c_C = Γ(1/3)²/(Disc C)^{1/6} for Disc C > 0. With S4.2 this is
  the brief's S4 limit with its closed-form constant. Route `docs/proof-S44.md` (real-variable: Fubini and dominated
  convergence for the cosine moment, the chart u = tan θ, GL₂ covariance of the angular integral, reduction to two
  normal forms, Beta integrals, Legendre duplication and Euler reflection); the hand-off's Abel/complex-rate route
  was replaced because `Complex.integral_cpow_mul_exp_neg_mul_Ioi` takes a real rate (lessons 19).
- `OscInt.d4Constant_example`: the closed form on x³ + 2x²y + 3xy² + 5y³ (disc −367).

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

### Fixed
- `lakefile.toml` said version 0.1.0; now matches `CITATION.cff` and `.zenodo.json`.


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
