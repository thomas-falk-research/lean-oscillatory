# Changelog

Versions follow semantic versioning once the public API (`docs/ROADMAP.md` §2) exists; until then a minor version
marks a set of newly machine-checked statements.

## Unreleased

- Build: `allowNonModules = true` in `lakefile.toml` silences Lake's per-import module-system warnings (no change to
  compilation); `make verify-all` runs the Lean step once instead of once per later step; deprecated `if_false` in
  `OscInt/D4/LimitAssembly.lean` replaced; CI installs the pinned Rust toolchain explicitly.
- `docs/ROADMAP.md`: downstream feedback folded in (explicit constants, local smoothness, asymptotic expansions,
  parametric uniformity, stable dependency with a machine-readable statement list, periodic and lattice settings,
  Keel–Tao).

## v0.2.0 — 2026-11-06

First release. Machine-checked as stated (`docs/STATUS.md`; record `docs/replay/2026-11-06-S4b-final-verify-all.txt`):

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
