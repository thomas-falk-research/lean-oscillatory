<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Applications

What OscInt's verified decay estimates are for. Each entry is marked **demonstrated in this repo** (with the file that
does it, compiled by `make quick` or the consumer CI job) or **proposed** (a use we expect to work but have not built;
it says what is missing). A demonstration uses only `import OscInt.API` and Mathlib, so its hypotheses are discharged
in Lean; numerics in `numerics/` are tooling and are never cited as evidence.

Entries marked **[v0.7.0]** use theorems of batches PA, KL, FR, VC2 and HW, which are new in release v0.7.0.

## Lattice and photonic dispersion; discrete Schrödinger and quantum walks
- **Dispersive decay of the 2D lattice Schrödinger group**, `|K(t, x)| ≤ C t^{-2/3}` uniformly in `x ∈ ℤ²`, sharp on the
  diagonal: statements T6, T6L (`OscInt/Statements/Global.lean`), **demonstrated** (proved; `docs/STATUS.md`) with the
  ℓ¹ → ℓ^∞ estimate for finitely supported data in `examples/consumer/ConsumerLattice.lean` (free discrete Laplacian,
  `t ≥ 1`; a potential is not covered).
  The 2D kernel factorises into two 1D Bessel kernels, so T6 and T6L are classical and do not show that the global
  theorems reach non-separable symbols (`docs/prior_art.md`, "Lattice kernels"); a non-separable model is **proposed**
  (session-7 batch VV).
- **Arccos-type dispersion relations** `arccos(a cos x + b cos y)`, `|a| + |b| < 1`: non-stationary decay uniform over
  a compact set of parameters, **demonstrated** (`examples/consumer/ConsumerLocal.lean`, FE-S2.1L). Physical models: the
  2D quantum walks of Watabe, Kobayashi, Katori and Konno (Phys. Rev. A 77, 062331 (2008), eq. (7); the Grover walk at
  p = 1/2) have `cos ω = −(p cos x + q cos y)` with `p + q = 1`, the boundary case `|a| + |b| = 1`, where the phase is not
  smooth at two points; and the 2D Yee scheme is `arccos(1 − 2S² + S²(cos x + cos y))` (`docs/prereg/2026-11-09-CENSUS-spec.md`
  §3). For `|a| + |b| < 1` with no constant term, no physical model has been verified (an earlier version of this entry
  named split-step walks and photonic lattices without a checked source; logged sweep
  `review/2026-11-09-CENSUS-prior-art-sweep.md`). The global `t^{-2/3}` bound for one fixed `(a, b)` follows from GD once
  the classification (four D4 points at `(±π/2, ±π/2)`, folds elsewhere; numerically confirmed by a grid method,
  `numerics/results-classify-2026-11-08.txt`, which cannot see sub-grid cusps, lessons 43; re-examined by the census,
  model M11) is discharged in Lean: **proposed**. Uniformly over `(a, b)`: needs a family D4 statement, **proposed** (open analysis).
- **Single-photon transition probabilities on a cosine-band photonic lattice** (for example a synthetic orbital-angular-momentum lattice): every single-site probability is at most `min(1, b(2κt))²`, with `b` the T0E envelope divided by `2π`, nontrivial for `2κt ≥ 519` (machine-checked threshold), **demonstrated** (`examples/consumer/ConsumerPhotonLattice.lean`; the identification of the amplitude with the physical model is a paper step, `review/2026-11-10-external-followup-answers.md`). With T0E′ (batch LE2, machine-checked) the envelope becomes `(C*/(2π)) (2κt)^{−1/3}` with `C*/(2π) = 1.54730… < 1.548`, below 1 for every `2κt ≥ 4`: **demonstrated** in the same file (`amp_le_cubeRoot`, `amp_cubeRoot_lt_one`). Loss, input/output coupling and control are not covered; finite rings and chains are the next entry.
- **[v0.7.0] Finite devices: a ring of `N` sites and an open chain of `M` sites** (batch FR, one dimension): the ring
  kernel and the chain kernel are the propagators (FR-K, FR-U, FC-K, FC-U), the ring kernel is the line kernel summed
  over the images `r + Nℤ` (FR-S), and each differs from the kernel of the infinite line by an explicit bound with a
  free parameter `η > 0` (FR-P, FC-P). FR-P, FC-P and FC-U are **demonstrated**
  (`examples/consumer/ConsumerFiniteRing.lean`: both bounds at `η = 1`, and the chain of two sites in closed form). The chain has identical sites and Dirichlet walls; a chain
  with free ends is not covered. The bounds say nothing useful once the wave has reached a wall, and the step from
  amplitudes to populations is not stated (`docs/statements.md`, Batch FR, items 6, 7 and 9).
- **[v0.7.0] Light cone of the 1D lattice kernel** (LC-1): `|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}` for integer `n` and
  every `η ≥ 0`: **demonstrated** at `η = 1` (`examples/consumer/ConsumerPeriodicAnalytic.lean`,
  `lightCone_unit_rate`). It bounds the kernel, not solutions.
- **[v0.7.0] The Hadamard walk on the line** (batch HW): each amplitude of the walk from a point state `(a, b)` is at most
  `39 (|a| + |b|) t^{−1/3}` for `t ≥ 1` (HW-D): **demonstrated** (`examples/consumer/ConsumerHadamardWalk.lean`). The
  ℓ¹ → ℓ^∞ form for finitely supported initial states is HW-L (no consumer example). Upper bounds only, for the Hadamard coin only;
  the constants are explicit and not sharp, and HW-D and HW-L have content only for `t > 59319` (`docs/STATUS.md`,
  paragraph "Batch HW").
- **Quantum-walk spreading bounds in two dimensions** (ballistic spreading: the bound `t^{-2/3}` uniform over all sites in 2D; the return amplitude at the starting site
  decays faster, like `t^{-1}`, since its stationary points are nondegenerate): **proposed**; needs
  vector-valued (matrix) amplitudes for the coin space (done for the global theorems: batch VT) and a classified two-band
  symbol (none found yet: `docs/design/vector-amplitudes.md` §6).

## Plasma physics (linear pieces only)
- **Cold-plasma transverse waves**: a wave packet of the electromagnetic branch ω = (ω_p² + c²|k|²)^{1/2} of a linear,
  cold, collisionless electron plasma (fixed ions, no background field, E along z) decays like `τ^{−1}` at every
  observation point, uniformly in the point, for one frequency branch (`e^{−iτω}`) and a fixed amplitude: **demonstrated** (`examples/consumer/ConsumerColdPlasma.lean`, GD-N with the
  phase `−(1 + κ₁² + κ₂²)^{1/2}`, Hessian determinant `(1 + |κ|²)^{−2}` computed in Lean; the physics reduction is a paper
  step, `review/2026-11-10-external-followup-answers.md`). No damping, nonlinear, kinetic, control or explicit-constant
  claim.
- **Phase mixing of free streaming** (the linear core of Landau damping), two-dimensional velocity: each density Fourier
  mode decays faster than any power of `t`, uniformly over velocity profiles supported in a fixed compact set with a fixed `C^N` budget, and wave vectors
  bounded away from 0: **demonstrated** (`examples/consumer/ConsumerPhaseMixing.lean`, FE-S2.1). Self-consistent fields
  (Vlasov–Poisson), Landau damping rates and three-dimensional velocities are **proposed** (ROADMAP I3).
- **Whistler waves at the inflection of the parallel branch** `ω ∝ k²/(1 + k²)` (cold plasma, frozen background): a
  packet band-limited to `ck/ω_pe ∈ [1/2, 2/3]`, which contains the inflection `1/√3`, satisfies
  `‖E(τ, ζ)‖ ≤ 18 (43740 τ/28561)^{−1/3} (|A(2/3)| + ∫|A′|)` uniformly in the position `ζ`: **demonstrated**
  (`examples/consumer/ConsumerWhistler.lean`, S1.3; the third-derivative bound is proved there). An explicit, valid
  bound, not a sharp one (with `A = 1` it beats the trivial bound only for `τ ≳ 8.2·10⁵`). Source: Track C, item C1, of
  `review/2026-11-12-DNLS-packet-answers.md`. An upper bound only: that the packet decays like `τ^{−1/3}` and no
  faster at the inflection is classical (Airy-type behaviour) and is not proved here. Validity regime of the model: cold
  collisionless electrons, parallel propagation, immobile ions (frequencies far above the ion gyrofrequency) and
  `ω_pe² ≫ ω(Ω − ω)`; on the band, `ω/Ω = q²/(1 + q²) ∈ [0.2, 0.31]`. The cited Eliasson–Shukla paper is CITED-UNREAD
  by the lead.
- **Gyroaverage**: `|J₀(z)| ≤ 1.548 z^{−1/3}` for every `z > 0` follows from T0E′ (`latticeKernel1 z 0 = 2π J₀(z)`, the
  Bessel identification not formalised); valid but weaker than the classical `(2/(πz))^{1/2}`; no consumer yet.

## Diffraction and caustics in optics
- **Fold caustics** (rainbow, Airy-type): the uniform `m^{-5/6}` bound with the classical critical-points-only
  hypothesis, **demonstrated** on explicit phases (`examples/consumer/ConsumerLocal.lean`, `foldOn`; the bite
  `foldCrit_fold_bite`).
- **Umbilic caustics (D4)**: the uniform `t^{-2/3}` bound and the exact leading term with constant
  `Γ(1/3)²/(√3 |Disc|^{1/6})` for `Disc < 0` and `Γ(1/3)²/Disc^{1/6}` for `Disc > 0`, **demonstrated** (`OscInt.API.d4LimitClosedForm`, F2; `examples/consumer/ConsumerFormula.lean`).
  The limit also holds uniformly over C²-totally bounded families of amplitudes (S4.2U) and over linear offsets
  `y·κ` with `‖y‖ ≤ R`, not multiplied by `t` (S4.2O); S4.2O is **demonstrated** along offsets that change with `t`
  (`examples/consumer/ConsumerD4Uniform.lean`). No rate of convergence is stated.
- **Diffraction integrals with explicit error bars**: **proposed**; needs explicit constants (`docs/constants.md`:
  the general route gives only crude constants; a certified-numerics demonstrator is named in ROADMAP,
  "Session-7 order", item 1, where it is called P6).

## Radar / SAR and seismic imaging
- **Stationary-phase steps** in range-Doppler and migration formulas (replacing an integral by its stationary-phase
  value with an error term): the **bounds** `O(m^{-1})` uniformly over the linear term are available (S2.2, FE-S2.2l);
  the **leading term** with an `O(m^{-2})` remainder, which these steps actually use, is **proposed** (draft
  `docs/design/leading-term.md`; pre-registered numerics `numerics/results-spleading-2026-11-08.txt`).

## Numerical-PDE error analysis
- **Decay estimates for semi-discrete schemes** (dispersive decay of a finite-difference Schrödinger or wave equation
  on a grid is exactly a lattice kernel bound like T6): proved for the free Laplacian on ℤ^d (TdE′ for the kernel,
  batch LS for solutions on ℓ²(ℤ^d); `docs/STATUS.md`) and, since v0.7.0, on a ring or an open chain in one dimension
  (batch FR, above); **proposed** for other symbols; each new symbol needs its
  classification discharged (the Lean side starts from the rows "Periodic integrals over `[−π, π]²`" and "The 2D
  lattice Laplacian" of `docs/cookbook.md`).
- **[v0.7.0] Sampling error of a periodic analytic integrand** (the trapezoidal rule, which for a periodic function is the
  rectangle rule): for `v` 2π-periodic, analytic and bounded by `M` on the strip `|Im z| < a`, the `N`-point sum
  differs from `∫_0^{2π} v` by at most `4πM / (e^{aN} − 1)` (PA-T), and `|∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}`
  (PA-C): **demonstrated** (`examples/consumer/ConsumerPeriodicAnalytic.lean`: normalised coefficients, and a
  stopping rule for the sum). Classical (Trefethen–Weideman 2014, Theorem 3.2, as cited in `docs/statements.md`,
  Batch PA); the claim is "machine-checked".
- **Strichartz estimates from decay** (Keel–Tao, discrete and continuous time): **proposed**, design doc pending
  (ROADMAP §5, "from decay to Strichartz").

## One-dimensional integrals and exponential sums with explicit constants
- **[v0.7.0] The second-derivative test with the constant 7/2** (batch VC2): `|∫_a^b e^{if}| ≤ A(w)/√λ` for some
  `w ∈ [0, π]` when `f′` increases at rate at least `λ > 0` (VC2-S), and `A ≤ 7/2` on `[0, π]` (VC2-N):
  **demonstrated** (`examples/consumer/ConsumerSecondDerivSharp.lean`: the bound `(7/2)/√λ`, and every partial
  integral of the Fresnel phase `e^{iλx²/2}`). VC2-K, S1.2 with 7/2 in place of 8, has no consumer example. The
  constant is classical, and the theorem is classical for f″ ≥ λ by citation, the originals unread; nothing is
  claimed as new (`docs/STATUS.md`, paragraph "Batch VC2").
- **[v0.7.0] The Kusmin–Landau inequality for exponential sums** (batch KL; used in explicit analytic number theory):
  `|Σ_{n=0}^{N} e(c_n)| ≤ cot(πλ/2)` when the differences of `c` are monotone and lie in one cell
  `[k + λ, k + 1 − λ]`, `0 < λ ≤ 1/2` (KL-D), with the forms `2/(πλ)` (KL-C) and for a monotone derivative (KL-F):
  **demonstrated** for a linear phase (`examples/consumer/ConsumerKusminLandau.lean`). The second- and
  third-derivative tests for sums are not stated.

## Verified reference targets for AI theorem provers
- Every statement in `stamps/statements.json` is a frozen, reviewed `Prop` with a commitment (SHA-256 of its
  definitional closure). All 86 have a proof with the status "machine-checked as stated" in `docs/STATUS.md`, which gives
  each one's replay record and what it rests on (updated 2026-11-19: the four batch-LS statements, the exception
  noted here on 2026-11-13, were proved on 2026-11-14). The `Challenge/` files are the same statements with `sorry`
  proofs, accepted by `lake comparator` only for a proof whose statement matches. **Demonstrated** as a mechanism
  (`comparator-*.json`, `make comparator` in `make verify-all`); use as a benchmark (strip a proof, ask a prover to
  re-prove the statement, judge with the comparator) is **proposed**.
