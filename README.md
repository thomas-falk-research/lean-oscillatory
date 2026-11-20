<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# OscInt

[![DOI](https://zenodo.org/badge/1447411529.svg)](https://doi.org/10.5281/zenodo.24021328)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--9478--6061-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0001-9478-6061)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](lean-toolchain)
[![Code: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-blue)](LICENSE)
[![Docs: CC BY 4.0](https://img.shields.io/badge/docs-CC%20BY%204.0-lightgrey)](LICENSE-docs)

**Machine-checked uniform estimates for oscillatory integrals, in Lean 4 and Mathlib.**

OscInt formalises the estimates that dispersive PDE, semiclassical analysis and lattice dynamics rest on, with
explicit constants. Each statement is written, timestamped and reviewed blind before its Lean proof, and every proof
is replayed by six kernel checkers. A downstream project can check in CI that it depends on exactly the reviewed
statements.

| | |
|---|---|
| **Proved** | 90 pinned statements, all machine-checked as stated ([`docs/STATUS.md`](docs/STATUS.md)); 86 are in release v0.7.0, the 4 of batch SPL are on the development branch only |
| **Use it** | `import OscInt.API`. Which theorem: [`docs/which-theorem.md`](docs/which-theorem.md). Recipes: [`docs/cookbook.md`](docs/cookbook.md). Machine-readable index: [`docs/api.json`](docs/api.json) |
| **Built with** | Lean package `OscInt`; toolchain v4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag v4.35.0) |
| **Releases** | v0.7.0 has 86 statements (all but the 4 of batch SPL); v0.6.0 had the first 65 ([`docs/release-notes/`](docs/release-notes/), [`CHANGELOG.md`](CHANGELOG.md)) |
| **Reviewed by** | AI referees only, not yet a human expert: read [Known caveats](#known-caveats) before relying on a result |
| **Cite** | [10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328) (all versions); see [How to cite](#how-to-cite) |

**Contents:** [What is proved](#what-is-proved) · [Quick start](#quick-start) ·
[Depending on OscInt](#depending-on-oscint) · [How it is checked](#how-it-is-checked) ·
[Known caveats](#known-caveats) · [Documents](#documents) · [How to cite](#how-to-cite) · [Licence](#licence)

## What is proved

Highlights:

- **van der Corput's lemma for every derivative order**, with explicit constants, and the second-derivative bound
  with its sharp constant.
- **Non-stationary and nondegenerate stationary phase**, and uniform decay at degenerate critical points: the fold
  (A2, m^{−5/6}), the cusp (A3, t^{−3/4}) and the umbilics (D4, t^{−2/3}, with the exact leading term and its
  Γ(1/3) constant).
- **Global decay** assembled from a pointwise classification of the phase, also for vector-valued amplitudes.
- **The free discrete (lattice) Schrödinger equation**: on ℤ, |∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 8(1 + √7)/3 ·
  t^{−1/3} for all t > 0 and real ξ (for integer ξ the kernel is 2π i^ξ J_ξ(t), a Bessel function); on ℤ^d the
  kernel is bounded by (8(1 + √7)/3)^d t^{−d/3}; the solution group on ℓ²(ℤ^d), on a ring of N sites and on an
  open chain.
- **New in v0.7.0:** the sharp second-derivative van der Corput bound; the exponentially convergent trapezoidal
  rule for periodic analytic functions, with the Fourier-coefficient bound behind it; the Kusmin–Landau inequality
  for exponential sums in Landau's sharp form; the Schrödinger group on a ring and on an open chain, with explicit
  finite-size bounds; the Hadamard quantum walk on the line, with an explicit t^{−1/3} bound.
- **Not released yet (development branch, batch SPL):** the leading term of a quadratic-phase integral with an
  explicit remainder, `|∫ g(u) e^{iλu²/2} du − g(0) √(2π/λ) e^{iπ/4}| ≤ (7/8) ‖g‴‖₁ λ^{−3/2}`, with the kernel
  identity behind it, the bound with the kernel's supremum in place of 7/8, and the proof that this supremum
  (numerically 0.722) and no smaller constant is the best one; 7/8 itself is not sharp. Frozen, blind-reviewed,
  proved and replayed on 2026-11-20 (`docs/replay/2026-11-20-SPL-verify-all.txt`; post-proof reviews answered,
  `review/2026-11-20-SPL-post-proof-answers.md`; reviewed by AI agents of one model family only, with no
  calibration round). The identity is classical in substance, the bounds with this kernel were not found in the
  literature searched, and nothing is claimed as new.

The bounds at degenerate points and the global bounds are uniform over all linear terms of the phase, which is what
dispersive estimates need; stationary phase and the fold bound are uniform over compact sets of linear terms.

| Area | Results (statement labels) | Entry theorems |
|---|---|---|
| One variable | van der Corput for k = 1, 2, 3 (constants 3, 8, 18) and for every k ≥ 2 (constant 5·2^{k−1} − 2), uniform in a linear term (S1, S1.k) | `OscInt.vanDerCorput_one/two/three`, `OscInt.API.vdCk` |
| Sharp second-derivative bound | the bound with its sharp constant sup A (numerically 3.3643…; in Lean 3.35 < sup A ≤ 7/2), attained by the quadratic phase; 7/2 in place of 8 in the test with amplitude (VC2) | `OscInt.API.secondDerivSharp`, `secondDerivAttained`, `vdc2ProfileBound`, `secondDerivSevenHalves` |
| Two variables, local | non-stationary phase; nondegenerate stationary phase; the fold, m^{−5/6} (S2.1, S2.2, S3) | `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold` |
| Cusp (A3) | t^{−3/4} for C² amplitudes supported in a small ball around the point, uniform in the linear term (S5.1, S5.1′) | `OscInt.API.cuspBound`, `OscInt.API.cuspBoundGen` |
| Umbilics (D4) | the uniform bound t^{−2/3}; the limit t^{2/3}∫e^{itφ}A → c_C A(0) with c_C > 0 and its closed forms in Γ(1/3); the limit uniformly over amplitude families and bounded linear offsets (S4.1–S4.4, S4.2U, S4.2O) | `OscInt.d4Bound`, `d4BoundNe`, `d4Limit`, `d4ConstantPos`, `d4ConstantClosedForm`, `OscInt.API.d4LimitUniform`, `d4LimitOffset` |
| Global decay | decay from a pointwise classification of the phase, also for amplitudes in any complex Banach space; sharpness; torus unfolding (GD-…, SH, T1) | `OscInt.API.globalDecay`, … |
| Lattice kernels | the 2D lattice Laplacian, t^{−2/3}, sharply; the cube-root constant 8(1 + √7)/3 on ℤ and its d-th power on ℤ^d; explicit constants (T6, T6L, T0E, T6F, T6E, T0E′, T6E′, TdF, TdE′) | `OscInt.API.latticeLaplacianDecay`, `latticeKernel1CubeRoot`, `latticeLaplacianCubeRoot`, `hypercubicKernelFactor`, `hypercubicCubeRoot`, … |
| Lattice Schrödinger group | on ℓ²(ℤ^d): existence, kernel representation, uniqueness, dispersive decay with explicit constants (LS) | `OscInt.API.latticeSchrodingerExists`, `latticeSchrodingerKernel`, `latticeSchrodingerDispersive`, `latticeSchrodingerDecay` |
| Rings and chains | the kernel of i u′ + Δu = 0 on a ring of N sites and on an open chain; uniqueness; the ring kernel as a sum over images; finite-size bounds against the infinite line (FR) | `OscInt.API.ringKernelSolves`, `ringUnique`, `ringCosetSum`, `ringFiniteSize`, `chainKernelSolves`, `chainUnique`, `chainFiniteSize` |
| Hadamard quantum walk | amplitudes from a point state through one scalar kernel; the kernel bound 7 t^{−1/2} + 12 t^{−1/3}; decay like t^{−1/3} of every amplitude; the ℓ¹ → ℓ^∞ estimate for finitely supported states (HW) | `OscInt.API.hadamardKernelFormula`, `hadamardKernelBound`, `hadamardDecay`, `hadamardDispersive` |
| Periodic analytic functions | Fourier coefficients of a function analytic in a strip; the N-point trapezoidal rule with error at most 4πM/(e^{aN} − 1); the light cone of the 1D lattice kernel (PA) | `OscInt.API.fourierCoeffStrip`, `trapezoidalRule`, `latticeKernel1LightCone` |
| Exponential sums | the Kusmin–Landau inequality with Landau's sharp bound cot(πλ/2), the constant 2/π, and the textbook derivative form (KL) | `OscInt.API.kusminLandau`, `kusminLandauTwoOverPi`, `kusminLandauDeriv` |
| Front ends in Mathlib's idiom | the theorems above with `ContDiff`, `iteratedFDeriv`, Hessian matrices, `Cubic.discr` and `HasCompactSupport`; conversions C1–C10; compact-family and local-smoothness forms | `OscInt.API.*` |

"Machine-checked as stated" means every row of the trust chain ([below](#how-it-is-checked)) exists for that
statement, with the hypotheses in [`docs/statements.md`](docs/statements.md), for example derivatives continuous up
to the endpoints, as in the source's C^k assumption. The status of each statement, with its evidence, prior art and
disclosures, is in [`docs/STATUS.md`](docs/STATUS.md).

<details>
<summary><b>The same table with status, prior art and disclosures per row</b></summary>

| Statements | Lean names | Status |
|---|---|---|
| **One variable.** S1: van der Corput for k = 1, 2, 3 (constants 3, 8, 18). S1.k: every k ≥ 2, constant 5·2^{k−1} − 2, uniform in a linear term | `OscInt.vanDerCorput_one/two/three`, `OscInt.API.vdCk` | machine-checked as stated; S1.k AI-assisted, disclosed. S1 is ported from roos-j/lean-oscillatory (Roos–Praveen, Mathlib PR #39406), which also anticipates S1.k (`docs/prior_art.md`) |
| **Two variables, local.** S2.1 non-stationary phase; S2.2 nondegenerate stationary phase; S3 the fold, m^{−5/6} | `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold` | machine-checked as stated (S3: fold condition on all of K) |
| **Cusp (A3), local.** S5.1 stable cusp and S5.1′ any A3 point: t^{−3/4} for C² amplitudes supported in a small ball around the point, uniform in the linear term | `OscInt.API.cuspBound`, `OscInt.API.cuspBoundGen` | machine-checked as stated (2026-11-13); AI-assisted proof, disclosed |
| **Umbilics (D4).** S4.1, S4.1′ the uniform bound t^{−2/3}; S4.2 the limit t^{2/3}∫e^{itφ}A → c_C A(0); S4.3 c_C > 0 with a Gamma-free proof; S4.4 the closed forms Γ(1/3)²/(√3\|Disc\|^{1/6}) and Γ(1/3)²/Disc^{1/6} | `OscInt.d4Bound`, `d4BoundNe`, `d4Limit`, `d4ConstantPos`, `d4ConstantClosedForm` | machine-checked as stated |
| **Front ends in Mathlib's idiom.** F1, F2; conversions C1–C10, C7′ (`iteratedFDeriv`, Hessian matrices, `Cubic.discr`, kernel and rank forms of the fold condition, norms, `HasCompactSupport`); FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′; compact families S2.2F, S3c; local smoothness (…L forms) | `OscInt.API.*` | machine-checked as stated (front-end batch 3 under a one-time waiver, ratified by the owner 2026-11-09) |
| **Global decay** from a pointwise classification (GD-C, GD, GD-F, GD-N), also for amplitudes in any complex Banach space (GD-…-V); sharpness (SH); torus unfolding (T1) | `OscInt.API.globalDecay`, … | machine-checked as stated |
| **Lattice kernels.** T6, T6L: the 2D lattice Laplacian decays like t^{−2/3}, sharply (classical and separable). T0E, T6F, T6E: explicit but weak constants (content only for t > 518 and t > 1321). T0E′, T6E′: the cube-root constant 8(1 + √7)/3, within a factor 2 of the best, useful from t ≈ 3.70 (AI-assisted, disclosed). TdF, TdE′: the d-dimensional hypercubic kernel factorises and is bounded by (8(1 + √7)/3)^d t^{−d/3} | `OscInt.API.latticeLaplacianDecay`, `latticeKernel1CubeRoot`, `latticeLaplacianCubeRoot`, `hypercubicKernelFactor`, `hypercubicCubeRoot`, … | machine-checked as stated. The rates are classical (Stefanov–Kevrekidis 2005); for lattice sites (integer ξ) a smaller explicit constant is in print (Korotyaev–Møller, from Landau's Bessel bound); T0E′ holds for every real ξ, which that bound does not cover (`docs/prior_art.md`) |
| **Batch LS.** LS-E, LS-K, LS-D, LS-D′: existence of the free lattice Schrödinger group on ℓ²(ℤ^d), its kernel representation, uniqueness, and dispersive decay with explicit constants | `OscInt.API.latticeSchrodingerExists`, `latticeSchrodingerKernel`, `latticeSchrodingerDispersive`, `latticeSchrodingerDecay` | machine-checked as stated (replay of 35dc5c0). AI-drafted proofs, disclosed |
| **Batch D4U.** S4.2U, S4.2O: the D4 limit t^{2/3}∫e^{itφ}A → c_C A(0) uniformly over C²-totally bounded amplitude families and over bounded linear offsets y·κ (each fixed bound) | `OscInt.API.d4LimitUniform`, `d4LimitOffset` | machine-checked as stated (replay of 720363d). Proof idea and decomposition from an external packet, disclosed |
| **Batch PA.** PA-C, PA-T, LC-1: Fourier coefficients of a periodic function analytic in a strip are bounded by 2πM e^{−a\|k\|} (for the unnormalised integral ∫_0^{2π} v e^{−ikθ} dθ); the N-point trapezoidal rule has error at most 4πM/(e^{aN} − 1) (Trefethen–Weideman 2014, Theorem 3.2); the 1D lattice kernel is at most 2π e^{\|t\| sinh η − \|n\| η} | `OscInt.API.fourierCoeffStrip`, `trapezoidalRule`, `latticeKernel1LightCone` | machine-checked as stated (replay of fafd5b8, 2026-11-19; post-proof reviews answered). Classical mathematics; AI-written proofs, disclosed |
| **Batch KL.** KL-D, KL-C, KL-F: the Kusmin–Landau inequality for exponential sums, with Landau's sharp bound cot(πλ/2) on differences, the constant 2/π, and the textbook derivative form | `OscInt.API.kusminLandau`, `kusminLandauTwoOverPi`, `kusminLandauDeriv` | machine-checked as stated (replay of fafd5b8, 2026-11-19; post-proof reviews answered). Classical mathematics; a weaker-constant form exists in Lean elsewhere (`docs/prior_art.md`); AI-written proofs, disclosed |
| **Batch FR.** FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P: the kernel of i u′ + Δu = 0 on a ring of N sites and on an open chain of M identical sites; each is the propagator (uniqueness); the ring kernel is the line kernel summed over images; explicit finite-size bounds against the infinite line | `OscInt.API.ringKernelSolves`, `ringUnique`, `ringCosetSum`, `ringFiniteSize`, `chainKernelSolves`, `chainUnique`, `chainFiniteSize` | machine-checked as stated (replay of fafd5b8, 2026-11-19; post-proof reviews answered). Classical mathematics; AI-written proofs, disclosed |
| **Batch VC2.** VC2-S, VC2-A, VC2-N, VC2-K: the second-derivative van der Corput bound with its sharp constant sup A (the largest modulus of the two-sided Fresnel integral ∫_{−c}^{c} e^{ix²/2} dx, numerically 3.3643…; in Lean 3.35 < sup A ≤ 7/2; classical for f″ ≥ λ by citation, originals unread), its attainment by the quadratic phase, the number 7/2, and the test with amplitude with 7/2 in place of 8 | `OscInt.API.secondDerivSharp`, `secondDerivAttained`, `vdc2ProfileBound`, `secondDerivSevenHalves` | machine-checked as stated (replay of fafd5b8, 2026-11-19; frozen: stamp `20261116T222541Z-5b72549117b1`; blind-reviewed: FAITHFUL, no counterexample found; post-proof reviews answered: FAITHFUL, SOUND, no failing regime found). Nothing claimed as new |
| **Batch HW.** HW-R, HW-K, HW-D, HW-L: the Hadamard walk on the line; its amplitudes from a point state through one scalar kernel, the kernel bound 7 t^{−1/2} + 12 t^{−1/3}, the decay 39 (\|a\| + \|b\|) t^{−1/3} of every amplitude, and the dispersive estimate ℓ¹ → ℓ^∞ for finitely supported initial states (the rate is known, with implicit constants in print; these constants are explicit and not sharp: content only for t > 1679 in HW-K and t > 59319 in HW-D and HW-L) | `OscInt.API.hadamardKernelFormula`, `hadamardKernelBound`, `hadamardDecay`, `hadamardDispersive` | machine-checked as stated (replay of fafd5b8, 2026-11-19; frozen: stamp `20261116T225756Z-5792039264f0`; blind-reviewed: FAITHFUL, no counterexample found; post-proof reviews answered: FAITHFUL, SOUND, no failing regime found). Known mathematics |

</details>

<details>
<summary><b>Replay history of the latest batches</b></summary>

**The latest batches.** The last 21 statements, proved in
session 13 and machine-checked as stated since the isolated replay of fafd5b8 on 2026-11-19 (six kernels;
`docs/replay/2026-11-19-session13-verify-all.txt`; a clean-runner run on the same commit also passed), and
replayed again together with every other statement by the isolated replay of 2113b54 with the corrected driver
(`docs/replay/2026-11-19-v0.7.0-verify-all.txt`): batch VC2,
the second-derivative van der Corput bound with its sharp constant sup A (numerically 3.3643…, the classical
constant; that decimal is not a Lean theorem: in Lean 3.35 < sup A ≤ 7/2) and the constant 7/2 in place of 8 in
the second-derivative test with amplitude (classical for f″ ≥ λ by citation, the originals unread; nothing
claimed as new); batch HW, the Hadamard walk on the line with an explicit, not sharp, t^{−1/3} bound for its
amplitudes (content only for t > 1679 for the kernel and t > 59319 for the amplitudes); batch FR, the Schrödinger
group on a ring of N sites and on an open chain of M sites with explicit finite-size bounds against the infinite
line; and batches PA and KL: the exponentially convergent trapezoidal rule with its Fourier-coefficient bound, the
light cone of the lattice kernel, and the Kusmin–Landau inequality in Landau's sharp form. All five batches were
frozen and blind-reviewed before their Lean proofs and post-proof reviewed after them; every referee, prover and
the lead are AI agents of one model family, and no human has read these 21 statements. Of the earlier 65, the last two, batch D4U (S4.2U, S4.2O: the D4 limit
uniformly over C²-totally bounded amplitude families and bounded linear offsets), were stated, frozen,
blind-reviewed and proved in Lean on 2026-11-15 and are machine-checked as stated since the isolated replay of
720363d (six kernels; `docs/replay/2026-11-15-session12-D4U-verify-all.txt`). Before them, batch LS (the free lattice
Schrödinger group on ℓ²(ℤ^d)), were proved in Lean on 2026-11-14 and are machine-checked as stated since the isolated
replay of 35dc5c0 (six kernels; `docs/replay/2026-11-14-session11-LS-final-verify-all.txt`).

</details>

Worked examples, which also check that the hypotheses can be met (`examples/consumer/`): the lattice Schrödinger
kernel, single photons on a cosine-band lattice, cold-plasma waves, phase mixing, whistler waves, matrix-valued
amplitudes, phases given by formulas, finite rings and chains, the Hadamard walk, a stopping rule for the
trapezoidal rule, exponential sums, and the sharp second-derivative bound. Where the results apply:
`docs/applications.md`.

## Quick start

Add OscInt to your Lake project and pin a release (Mathlib comes with it, at the revision OscInt was checked with;
use the same `lean-toolchain`, `leanprover/lean4:v4.35.0`):

```toml
# lakefile.toml
[[require]]
name = "oscint"
git = "https://github.com/thomas-falk-research/lean-oscillatory"
rev = "v0.7.0"   # a release tag (pins and notes: docs/release-notes/v0.7.0.md)
```

```bash
lake update oscint
lake exe cache get
lake build
```

```lean
import OscInt.API

open OscInt.Statements in
example : D4LimitStatement := OscInt.d4Limit

-- the D4 limit with its closed-form constant, for one C² amplitude (no `AmpBound`)
example : OscInt.Statements.D4LimitClosedFormStatement := OscInt.API.d4LimitClosedForm
```

Use the theorems by their statement names; their types *are* the reviewed statements. `OscInt.API` is the entry
point: every theorem with the textbook statement it formalises, and front-end forms in Mathlib's idiom
(`tools/check_entry_point.sh` checks that it exposes every name in `stamps/statements.json`). For a phase given by
a formula, see `examples/consumer/ConsumerFormula.lean` (front ends FE-S3, FE-S4.1′ with Mathlib-only hypotheses,
derivative data from `OscInt.API.Poly`).

## Depending on OscInt

The tag in the line above is the latest published release (the release procedure moves it after each release). Each
release's notes say which statements it has: v0.6.0 the first 65, v0.7.0 the first 86 (`docs/release-notes/`). To use
work that is not in a published release, set `rev` to a full commit hash and take the SHA-256 of
`stamps/statements.json` at that commit as your pin. From v0.7.0 use the
checker shipped with the release: an older copy of `tools/oscint_check.py` reports every statement file as edited
(`CHANGELOG.md`, "Attribution"). More on depending on OscInt: `docs/downstream.md`.

**Check in CI that you depend on exactly the reviewed statements.** `stamps/statements.json` lists every pinned
statement with its label, summary, proving theorem, statement file, the commitment to its definitional closure and
the stamp that froze it, and every statement file with its SHA-256. After `lake build`:

```bash
lake build OscInt Blueprint   # the check replays every OscInt and Blueprint module, not only those you import
python3 .lake/packages/oscint/tools/oscint_check.py \
  --statement OscInt.Statements.D4LimitStatement \
  --expect-sha256 <sha256 of stamps/statements.json, from docs/release-notes/<tag>.md>
```

<details>
<summary><b>What the check does, and what it does not give you</b></summary>

It checks that your toolchain and Mathlib are the ones OscInt was checked with, that no statement file was edited,
that each statement constant comes from its frozen file, that the proving theorem's type is syntactically the
statement and its axioms are only `propext`, `Classical.choice`, `Quot.sound`, it replays every OscInt module in
Lean's kernel (`leanchecker`), and it recomputes each commitment (about 20 minutes in all; `--fast` skips the last
two and reports PARTIAL, never PASS). Its negative controls are `tools/test_oscint_check.sh`, run in CI on
`examples/consumer/`.

What it does not give you: run from inside the package, the checker and `oscint-commit-env` are the package's own,
so it detects accidental drift (another version, an edited file, a stale build, another Mathlib), not deliberate
tampering. Against tampering, keep your own copy of `tools/oscint_check.py` at a reviewed version (its SHA-256 and
that of `stamps/statements.json` are in the release notes) and pin the release by commit hash. Independent kernels
and the statement reviews are this repository's trust chain (`make verify-all`, "What stays trusted" below).
Versioning, stable names, deprecation and the Mathlib-upgrade rule: `docs/policy.md`.

</details>

<details>
<summary><b>Release history of the downstream interface</b></summary>

v0.3.0 is the first release with `OscInt.API`, `stamps/statements.json` and `tools/oscint_check.py` (v0.2.0 has none
of them). Published 2026-11-07 (GitHub release `v0.3.0`, tag on the release commit recorded in
`docs/release-notes/v0.3.0.commit`; CI job `release-pin` checks this, and that `main` contains it). External dry run
with these exact steps: `docs/replay/2026-11-08-external-downstream-dry-run-v0.3.0.txt` (build and checker PASS).
A tested project of this shape: `examples/consumer-release/`.

</details>

## How it is checked

A statement counts as machine-checked as stated only when the whole chain holds:

1. **Frozen first.** The statement is a `def … : Prop` in `OscInt/Statements/`, timestamped by three RFC 3161
   authorities and OpenTimestamps before any Lean proof of it exists (exceptions are disclosed per batch).
2. **Reviewed blind.** Referees read the frozen statement against its prose without seeing a proof.
3. **Proved as stated.** The proving theorem's type is syntactically the statement constant; its axioms are only
   `propext`, `Classical.choice`, `Quot.sound`.
4. **Replayed by six kernels.** Lean's own kernel in two modes and four independent implementations re-check an
   export of every proof.
5. **Compared with the frozen challenge.** `lake comparator` checks the proofs against a `sorry` challenge whose
   export hash was stamped with the statement.
6. **Recorded.** The status of each statement is derived from these records, not typed as a claim
   ([`docs/STATUS.md`](docs/STATUS.md)).

To re-check everything yourself:

```bash
lake exe cache get
make verify-all
```

Needs elan, Rust ≥ 1.97, `bubblewrap`, `zstd`, `openssl`, `curl`. A full run takes about three hours on four cores
and needs the free disk space that `python3 tools/replay_preflight.py check` asks for; which commit the replay of
record covers is in `docs/STATUS.md`.

<details>
<summary><b>What <code>make verify-all</code> runs</b></summary>

`verify-all` runs: `verify-toolchain` (hash pins; installed toolchain byte-identical to the pinned archive),
`tools-test`, `guard` (forbidden tokens, statement pins), `lean` (build; axiom audit N/N against the guard's
theorem count; statement-type check; Mathlib name check), `lean-replay` (`leanchecker` per module; export
re-checked by Lean's kernel, its paranoid mode, nanoda, con-leche, con-ron and, via `lake check --paranoid`,
lean4lean), `commit` (statement commitments from the environment and from the export must agree),
`comparator` (frozen challenge, hash-checked against the stamp), `stamp-verify`. It prints PASS, FAIL, or
INCOMPLETE when a step had nothing to check; INCOMPLETE is never reported as PASS.

</details>

### What stays trusted

- Lean's kernel and the v4.35.0 toolchain archive, from which every local checker above comes. In CI one checker,
  nanoda (`nanoda_lib` 0.4.31 at commit `8de7e0c`), is additionally built from source on a fresh runner and run on the
  same export (`docs/toolchain.md`).
- The Mathlib binary cache for the proofs: a source build (CI run 18) reproduced the six statement commitments that existed on 2026-11-05, but
  the replay still uses cache-built `.olean` files (`docs/toolchain.md`).
- The fidelity readings of statements: AI referees, no human reviewer yet.
- The newest line of `stamps/pins.txt` is written after the stamp it pins, so no timestamp covers it; its
  integrity rests on git history.
- The roots of the three RFC 3161 timestamp authorities (`stamps/roots/`); the FreeTSA root is trust on first use.

## Known caveats

Read these before relying on a row of the table; each is documented where the link points.

- **Reviewed by AI only.** Proofs and reviews are by AI agents directed by the owner (for the 21 statements of
  batches PA, KL, FR, VC2, HW and the 4 of batch SPL, all of one model family); no human expert has read the
  statements for fidelity. On 2026-11-19 an AI system of another model family reviewed the 21 statements of
  batches PA, KL, FR, VC2, HW (it could not run Lean; for batch SPL its sessions bore on the draft statements and
  the proof on paper only, not on the Lean proofs): it found them faithful and true
  by its own arguments, and its findings against records, tools and process were checked and corrected
  (`docs/STATUS.md`, "External reviews of 2026-11-19"; `review/2026-11-19-*-external-review-answers.md`).
- **The replay driver had a hole.** Until 2026-11-19 its scan of checker output for errors could be switched off by
  a checker's success phrase. It is fixed and tested, and every one of the 86 statements of v0.7.0 was replayed again with the corrected
  driver and the raw output kept (`docs/replay/2026-11-19-v0.7.0-verify-all.txt`). Replay records made before that
  date used the old rule; the paragraph of `docs/STATUS.md` named above says what a rerun showed about them.
- **A review rule was not followed in six batches.** Findings against the sanity layer were answered without a
  re-freeze of the statement; the owner ratified this afterwards as a one-time waiver, marked on the 23 rows
  (`docs/STATUS.md`, "Step 5 in six batches").
- **Statement before proof** means: no Lean proof text before the statement was frozen and reviewed. For classical
  theorems, and where the lead had a plan on paper, the proof idea is older; each batch says so in `docs/STATUS.md`.
- **Constants are explicit, not always sharp.** The table and `docs/statements.md` say from which parameter value a
  bound beats the trivial one (for the Hadamard walk only for t > 59319).
- **What stays trusted** after all checks: section "What stays trusted" above.

## Layout

- `OscInt/` library: `OscInt/Statements/` frozen statements, `OscInt/VanDerCorput/` (S1),
  `OscInt/StationaryPhase/` (S2, S3), `OscInt/D4/` (S4), `OscInt/Cusp/` (S1.k, S5.1, S5.1′), `OscInt/Front/` (front
  ends, conversions, hypothesis helpers, global decay, lattice kernels; entry point `OscInt/API.lean`).
- `Blueprint/` intermediate propositions (definitions only); `Challenge/` `sorry` theorems over the statement modules
  for `lake comparator` (never imported; frozen by the stamped export hash and the pinned statement-file hashes,
  `stamps/pins.txt`); one `comparator*.json` per milestone.
- Checks run by `make lean`: `Axioms.lean` (axiom audit), `StatementTypes.lean` (final types are the frozen
  constants), `MathlibNames.lean` (names the plan relies on), `GammaFree.lean` (S4.3 proof method).
- `tools/` Rust binaries, Python and shell tools, and the Lean commitment producer; `numerics/` numerical checks in
  exact, ball and floating-point arithmetic (tooling, never evidence); `stamps/` timestamp records and `anchors/`
  their Bitcoin anchors; `review/` the lead's answers to every review (`review/README.md`; older verbatim reports
  are in history only, owner privacy rule).
- `examples/` consumer projects and worked examples; `python/` and `rust/` two independent checkers for the
  experimental certificate contract (`docs/contract/`); `experiments/` a pre-registered experiment package.

## Documents

| File | Content |
|---|---|
| `docs/README.md` | index of all documents, with the statement labels |
| `docs/which-theorem.md`, `docs/cookbook.md`, `docs/api.json` | which theorem to use; copy-paste recipes; machine-readable API index |
| `docs/applications.md` | where the results apply (models and domains), with worked examples |
| `docs/statements.md` | the mathematics of every statement, with dated clarifications |
| `docs/STATUS.md` | evidence-derived status per statement |
| `docs/HANDOFF.md` | state and next steps for the next session |
| `docs/ROADMAP.md` | the path to a production-ready library, as a checklist |
| `docs/proof-*.md` | refereed proof routes, one per batch (S2S3, S4, S42, S43, S44, API2, API3, GD, VT, LE, LE2, HC, A3, LS, D4U, PA, KL, FR, VC2, HW) |
| `docs/downstream.md` | depending on OscInt from another Lake project, and checking that dependency in CI |
| `docs/policy.md`, `CONTRIBUTING.md` | versions, stable names, deprecation, Mathlib re-freeze rule; adding a statement end to end |
| `docs/decisions/` | dated decision records |
| `docs/lessons.md` | lessons, each with a rule and (where possible) a check |
| `docs/calibration.md` | referee calibration rounds (planted errors, sealed keys) |
| `docs/progress.md`, `docs/progress/` | chronological log of sessions 1–3; the log of session 13; sessions 7–13 are in `docs/HANDOFF.md`, sessions 4–6 in its history and in `CHANGELOG.md` |
| `CHANGELOG.md`, `docs/release-notes/` | released versions; per-release pins of the trust chain |
| `docs/toolchain.md`, `docs/dependencies.md`, `docs/commitment-format.md` | toolchain, pins, commitment format |
| `docs/prior_art.md`, `docs/upstream.md` | prior-art gate; Mathlib candidates (no PR without the owner) |
| `docs/replay/` | committed `verify-all` and replay records |

## Authorship, acknowledgements, availability

- **Author and maintainer:** Thomas Falk III ([ORCID 0009-0001-9478-6061](https://orcid.org/0009-0001-9478-6061)),
  who conceived and directs the project, took the decisions recorded under `docs/decisions/`, and is responsible
  for its content.
- **AI use.** Statements, proofs, tools, reviews and documents were drafted by AI agents under the author's
  direction; the commit trailers record it, and work drafted with other tools is named in `docs/prior_art.md`.
  The checks that do not depend on who wrote a proof are the kernel replay, the axiom audit and the statement pins.
- **Acknowledgements.** The one-dimensional van der Corput proofs derive from the formalisation of J. Roos and
  M. Praveen. The library stands on Lean 4 and Mathlib and on the work of their developers and community, and its
  replay on the independent kernel checkers shipped with the toolchain.
- **Availability.** Sources, statements, proofs, verification records, review answers and release notes are in this
  repository; releases are archived at Zenodo under the concept DOI below. Nothing needed to re-run the checks
  lives outside the repository and the pinned toolchain.
- **Funding and competing interests.** This work received no funding. The author declares no competing interests.

## How to cite

Cite the software through its concept DOI, which always resolves to the latest version:
[10.5281/zenodo.24021328](https://doi.org/10.5281/zenodo.24021328). To cite the exact version you used, take its
version DOI:

| Version | DOI |
|---|---|
| v0.6.0 | [10.5281/zenodo.24263138](https://doi.org/10.5281/zenodo.24263138) |
| v0.5.0 | [10.5281/zenodo.24205167](https://doi.org/10.5281/zenodo.24205167) |
| v0.4.0 | [10.5281/zenodo.24088811](https://doi.org/10.5281/zenodo.24088811) |
| v0.3.0 | [10.5281/zenodo.24045231](https://doi.org/10.5281/zenodo.24045231) |
| v0.2.0 | [10.5281/zenodo.24021329](https://doi.org/10.5281/zenodo.24021329) |

GitHub's "Cite this repository" button reads `CITATION.cff`, and `codemeta.json` carries the same metadata for
software indexes.

```bibtex
@software{FalkIII_OscInt,
  author    = {Falk III, Thomas},
  title     = {{OscInt}: uniform oscillatory-integral estimates in {Lean} 4 and {Mathlib}},
  publisher = {Zenodo},
  year      = {2026},
  doi       = {10.5281/zenodo.24021328},
  url       = {https://github.com/thomas-falk-research/lean-oscillatory},
  note      = {ORCID 0009-0001-9478-6061}
}
```
(`@software` is biblatex; with classic BibTeX use `@misc` and the same fields.) If you use the one-dimensional van der
Corput results, please also cite J. Roos and M. Praveen, [`roos-j/lean-oscillatory`](https://github.com/roos-j/lean-oscillatory),
from which they are derived.

Work that is not in a release yet has no version DOI: cite the concept DOI and name the commit hash. Please also cite the mathematics a statement formalises; the works behind each statement are in
`docs/statements.md` and `docs/prior_art.md`, and collected, with identifiers checked against Crossref and arXiv, in
`docs/references.bib`.

Questions, a phase that no statement covers, or a suspected error in a statement or a record: open an issue on the
repository (there is a template for "my phase does not fit"). A way around the trust chain is a security report:
`SECURITY.md`.

## Licence

Copyright 2026 Thomas Falk III. Code, configuration and data: Apache-2.0 (`LICENSE`). Documentation: CC BY 4.0
(`LICENSE-docs`). `NOTICE` is the attribution file that section 4(d) of the Apache License requires a
redistribution to carry; it also gives the requested form of attribution. Per-file licensing follows the
[REUSE specification 3.3](https://reuse.software/spec-3.3/): a comment header, or an attribution block at the end
of frozen statement files and of records, in every file that can carry one; `REUSE.toml` for machine output,
tokens and JSON; `LICENSES/`; checked by `reuse lint` in CI. `make sbom` writes an SPDX document listing every file
with its copyright text, licence and checksum. The one-dimensional van der Corput proofs are derived from
`roos-j/lean-oscillatory` (Apache-2.0) and keep its copyright notice. Citation metadata: `CITATION.cff`,
`codemeta.json`, `.zenodo.json`.
