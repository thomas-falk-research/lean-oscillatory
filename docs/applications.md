# Applications

What OscInt's verified decay estimates are for. Each entry is marked **demonstrated in this repo** (with the file that
does it, compiled by `make quick` or the consumer CI job) or **proposed** (a use we expect to work but have not built;
it says what is missing). A demonstration uses only `import OscInt.API` and Mathlib, so its hypotheses are discharged
in Lean; numerics in `numerics/` are tooling and are never cited as evidence.

## Lattice and photonic dispersion; discrete Schrödinger and quantum walks
- **Dispersive decay of the 2D lattice Schrödinger group**, `|K(t, x)| ≤ C t^{-2/3}` uniformly in `x ∈ ℤ²`, sharp on the
  diagonal: statements T6, T6L (`OscInt/Statements/Global.lean`). *Status: statements frozen and reviewed in session 6;
  proofs and the consumer example `examples/consumer/ConsumerLattice.lean` are the acceptance of ROADMAP P3 — see
  `docs/STATUS.md` for whether they exist yet.*
- **Arccos-type dispersion relations** `arccos(a cos x + b cos y)` (split-step quantum walks, photonic lattices):
  non-stationary decay uniform over a compact set of parameters, **demonstrated** (`examples/consumer/ConsumerLocal.lean`,
  FE-S2.1L). The global `t^{-2/3}` bound for one fixed `(a, b)` follows from GD once the classification (four D4 points
  at `(±π/2, ±π/2)`, folds elsewhere; numerically confirmed, `numerics/results-classify-2026-11-08.txt`) is discharged
  in Lean: **proposed**. Uniformly over `(a, b)`: needs a family D4 statement, **proposed** (open analysis).
- **Quantum-walk spreading bounds** (ballistic spreading with `t^{-2/3}` decay of return amplitudes): **proposed**; needs
  vector-valued (matrix) amplitudes for the coin space (ROADMAP P5) and the two-band symbol's classification.

## Diffraction and caustics in optics
- **Fold caustics** (rainbow, Airy-type): the uniform `m^{-5/6}` bound with the classical critical-points-only
  hypothesis, **demonstrated** on explicit phases (`examples/consumer/ConsumerLocal.lean`, `foldOn`; the bite
  `foldCrit_fold_bite`).
- **Umbilic caustics (D4)**: the uniform `t^{-2/3}` bound and the exact leading term with constant
  `Γ(1/3)²/(√3 |Disc|^{1/6})`, **demonstrated** (`OscInt.API.d4LimitClosedForm`, F2; `examples/consumer/ConsumerFormula.lean`).
- **Diffraction integrals with explicit error bars**: **proposed**; needs explicit constants (`docs/constants.md`:
  the general route gives only crude constants; a certified-numerics demonstrator is ROADMAP P6).

## Radar / SAR and seismic imaging
- **Stationary-phase steps** in range-Doppler and migration formulas (replacing an integral by its stationary-phase
  value with an error term): the **bounds** `O(m^{-1})` uniformly over the linear term are available (S2.2, FE-S2.2l);
  the **leading term** with an `O(m^{-2})` remainder, which these steps actually use, is **proposed** (draft
  `docs/design/leading-term.md`; pre-registered numerics `numerics/results-spleading-2026-11-08.txt`).

## Numerical-PDE error analysis
- **Decay estimates for semi-discrete schemes** (dispersive decay of a finite-difference Schrödinger or wave equation
  on a grid is exactly a lattice kernel bound like T6): **proposed** beyond the 2D Laplacian; each new symbol needs its
  classification discharged (the Lean side is the recipe of `docs/cookbook.md`, "a lattice symbol").
- **Strichartz estimates from decay** (Keel–Tao, discrete and continuous time): **proposed**, design doc pending
  (ROADMAP P5).

## Verified reference targets for AI theorem provers
- Every statement in `stamps/statements.json` is a frozen, reviewed `Prop` with a machine-checked proof and a
  commitment (SHA-256 of its definitional closure); the `Challenge/` files are the same statements with `sorry`
  proofs, accepted by `lake comparator` only for a proof whose statement matches. **Demonstrated** as a mechanism
  (`comparator-*.json`, `make comparator` in `make verify-all`); use as a benchmark (strip a proof, ask a prover to
  re-prove the statement, judge with the comparator) is **proposed**.
