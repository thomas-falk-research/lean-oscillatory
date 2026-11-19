<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Which theorem do I use?

A decision tree for a user with a concrete oscillatory integral. Every name below is a theorem whose type is a frozen
statement (`stamps/statements.json`, `docs/STATUS.md` for its status); `import OscInt.API` exposes all of them. The
copy-paste recipes are in `docs/cookbook.md`; the machine-readable index is `docs/api.json`.

Release note: the 21 theorems of batches PA, KL, FR, VC2 and HW, marked **[v0.7.0]** below, are new in release
v0.7.0; a project pinned to v0.6.0 or earlier does not have them.

Conventions used by every two-dimensional front end: points of the plane are `ℝ × ℝ` with Mathlib's **max norm**
(`‖(x, y)‖ = max |x| |y|`, so `Metric.closedBall 0 r` is a square); the integral is written out,
`∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k`; linear terms are functionals
`L : (ℝ × ℝ) →L[ℝ] ℝ` (a vector `x` becomes `x.1 • fst + x.2 • snd`); amplitudes are `ContDiff ℝ n A`,
`tsupport A ⊆ K`, `‖iteratedFDeriv ℝ j A k‖ ≤ M` for `j ≤ n` (F1 `ampBoundOfContDiff` gives such an `M` for any `Cⁿ`
amplitude with compact support). Dimension two only; `EuclideanSpace ℝ (Fin n)` is not covered yet.

## 1. One variable
`∫_a^b e^{iλφ(x)} ψ(x) dx` with `|φ^{(k)}| ≥ 1` on `[a, b]` (k = 1 with φ′ monotone, k = 2, k = 3):
`OscInt.vanDerCorput_one/two/three` (S1; constants 3, 8, 18). For any k ≥ 2, with a linear term `p x` added to the
phase and the derivatives given as a chain `D₀, …, D_k`: `OscInt.API.vdCk` (S1.k; constant 5·2^{k−1} − 2, bound
`c_k μ^{−1/k}`).

For k = 2 there is a smaller constant (batch VC2, **[v0.7.0]**):
- `OscInt.API.secondDerivSevenHalves` (VC2-K): as S1.2 with 7/2 in place of 8, with a linear term `p x`:
  `|∫_a^b e^{i(φ(x) + px)} ψ(x) dx| ≤ (7/2) μ^{−1/2} (|ψ(b)| + ∫_a^b |ψ′|)` when `|φ″| ≥ μ > 0` on `(a, b)`. It keeps
  the hypotheses of S1.2, so it can replace S1.2 where S1.2 is used.
- `OscInt.API.secondDerivSharp` (VC2-S), no amplitude: for `a ≤ b` and `f` continuous on `[a, b]` whose derivative `f′` on `(a, b)`
  increases at rate at least `λ > 0` (`f′(y) − f′(x) ≥ λ (y − x)`; no second derivative needed), there is `w ∈ [0, π]`
  with `|∫_a^b e^{if(x)} dx| ≤ A(w)/√λ`, where `A` is the profile `vdc2Profile`.
- `OscInt.API.vdc2ProfileBound` (VC2-N): `A(w) ≤ 7/2` for `0 ≤ w ≤ π`. `OscInt.API.secondDerivAttained` (VC2-A):
  `A(w) ≤ |∫_{−√(2w)}^{√(2w)} e^{ix²/2} dx|`. The decimal 3.3643… of sup A is not a Lean theorem (`docs/STATUS.md`,
  row VC2-S).

Worked example: `examples/consumer/ConsumerSecondDerivSharp.lean`.

## 2. Two variables: first classify the points of the amplitude's support
For your phase Ψ (smooth on an open set `U` containing the compact support `K` of the amplitude) and the linear terms
`L` you need, classify each point `k ∈ K`:
- **non-critical** for `Ψ + L` (`fderiv ℝ Ψ k + L ≠ 0`);
- **nondegenerate**: `(hessianMatrix Ψ k).det ≠ 0`;
- **fold**: Hessian of rank one, third derivative nonzero along its kernel (`FoldOrNondegMatrix Ψ k`, C7 for the
  rank form, C7′ from `HasFDerivAt` data);
- **D4**: Hessian zero, cubic part with nonzero discriminant (`IsD4Point Ψ k`; C5/C6 relate the discriminant);
- **cusp (A3)**: Hessian of rank one with kernel vector `v`, `D³Ψ[v, v, v] = 0` and a nonzero reduced quartic
  (`IsA3Point Ψ k₀`; `IsStableA3Point` adds the coupling condition D³Ψ[v, v, w] ≠ 0). Only a **local** bound exists
  (row below); global assembly with A3 points is not yet available (ROADMAP I3);
- anything else (D₅, A₄, …): **not covered**; open an issue (template "my phase doesn't fit a statement").
`numerics/src/bin/classify.rs` classifies the points of the lattice Laplacian and of arccos dispersion relations numerically (tooling only; a command-line classifier for user phases is open, ROADMAP §5).

Then pick by what you need:

| You have | You need the bound for | Use | Rate |
|---|---|---|---|
| no critical point: `‖DΨ(k) + L‖ ≥ c > 0` on `K` | those `L` | `nonStationaryOn` (one phase), `nonStationaryLocal` (compact family), `nonStationaryFE` (Ψ smooth on ℝ²) | `m^{-N}` |
| every critical point of `Ψ + L`, `L ∈ K′` compact, nondegenerate | `L ∈ K′` | `stationaryPhaseOn`, `stationaryPhaseLocal` (family), `stationaryPhaseFamily` (internal encoding) | `m^{-1}` |
| every point of `K` nondegenerate | **all** `L` | `globalNondeg` (GD-N) | `m^{-1}` |
| every critical point for `L ∈ K′` nondegenerate or fold | `L ∈ K′` | `foldOn`, `foldLocal` (family), `foldCrit` (internal) | `m^{-5/6}` |
| every point of `K` nondegenerate or fold | **all** `L` | `globalFold` (GD-F) | `m^{-5/6}` |
| finitely many D4 points `D`, everything else nondegenerate or fold at critical points for `L ∈ K′` | `L ∈ K′` | `globalDecayCrit` (GD-C) | `m^{-2/3}` |
| finitely many D4 points `D`, every other point of `K` nondegenerate or fold | **all** `L` | `globalDecay` (GD) | `m^{-2/3}` |
| one D4 point, amplitude in a small ball around it | all `L` | `d4BoundLocal` (FE-S4.1′L), `d4BoundFE` (Ψ smooth on ℝ²) | `t^{-2/3}` |
| an A3 point at the origin, phase `ContDiff ℝ ∞` on all of ℝ², C² amplitude in a small ball around the point, `t ≥ 1` (the statements are at 0: for a point `k₀`, apply them to `k ↦ Ψ (k + k₀)`; `OscInt/Front/CuspSanity.lean` checks the A3 conditions for explicit quartics) | all `L` | `cuspBoundGen` (S5.1′, any A3 point), `cuspBound` (S5.1, stable A3 points) | `t^{-3/4}` |
| a D4 point, exact asymptotics | — | `d4LimitClosedForm` (F2): `t^{2/3} I(t) → c_C A(0)`, `c_C = Γ(1/3)²/(√3 \|Disc\|^{1/6})` or `Γ(1/3)²/Disc^{1/6}` | — |
| a D4 point, the same limit uniformly over a C²-totally bounded family of amplitudes (`AmpTotallyBounded`), or over linear offsets `y·κ` with `‖y‖ ≤ R` (the offset is not multiplied by `t`; uniform for each fixed `R`) | — | `d4LimitUniform` (S4.2U), `d4LimitOffset` (S4.2O); no rate and no effective `T`; example `examples/consumer/ConsumerD4Uniform.lean` | — |
| a limit `m^σ I(m) → c ≠ 0` | a matching lower bound | `sharpness` (SH) | — |

"All `L`" matters for dispersive estimates: `sup_x |∫ e^{i(tω(k) + x·k)} A(k) dk|` is the sup over `L = x/t`.

## 3. Periodic problems (lattices, quantum walks, Floquet)
Integrals over the torus `[−π, π]²` of a 2π-biperiodic integrand: `torusUnfold` (T1) gives a smooth compactly
supported weight `η` with `∫_{[−π,π]²} g = ∫_{ℝ²} η g`; then apply a row of the table to the amplitude `η · a`.
Ready-made: `latticeLaplacianDecay` (T6, the 2D lattice Schrödinger kernel is `O(t^{-2/3})` uniformly in `x ∈ ℤ²`) and
`latticeLaplacianLimit` (T6L, the rate is attained on the diagonal; with SH it is sharp).

Explicit constants, valid for every `t > 0`:
- one dimension: `latticeKernel1CubeRoot` (T0E′), `|∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 8(1 + √7)/3 · t^{−1/3}` for
  every real `ξ` (useful from `t ≈ 3.70`; T0E, `latticeKernel1Explicit`, is weaker);
- two dimensions: `latticeLaplacianCubeRoot` (T6E′), the constant squared;
- `d` dimensions: `hypercubicKernelFactor` (TdF, the kernel on ℤ^d is a product of 1D kernels) and
  `hypercubicCubeRoot` (TdE′, `(8(1 + √7)/3)^d t^{−d/3}`).

These bound the kernel. The statements about solutions of the lattice Schrödinger equation on ℓ²(ℤ^d) (batch LS:
existence, kernel representation, decay of solutions) are machine-checked as stated
(`OscInt.API.latticeSchrodingerExists` and its three siblings; `docs/STATUS.md`). Worked examples: `examples/consumer/ConsumerPhotonLattice.lean` (T0E′), `ConsumerLattice.lean`
(T6, T6L).

Outside the light cone (batch PA, **[v0.7.0]**): `latticeKernel1LightCone` (LC-1),
`|I(t, n)| ≤ 2π e^{|t| sinh η − |n| η}` for every real `t`, every integer `n` and every `η ≥ 0`, with `I` the 1D kernel
of T0E′. Integer `n` only; no content inside the cone `|n| ≤ |t|` or at `η = 0`.

Finite lattices in one dimension (batch FR, **[v0.7.0]**), for `i u′ + Δu = 0` with `(Δu)(x) = u(x + 1) + u(x − 1) − 2u(x)`:
- ring of `N ≥ 1` sites (functions on ℤ of period `N`): `ringKernelSolves` (FR-K, the kernel `R_N` solves the
  equation, is the unit datum at `t = 0` and has period `N`), `ringUnique` (FR-U, every solution of period `N` is
  `Σ_{y=0}^{N−1} R_N(t, x − y) u(0, y)`), `ringCosetSum` (FR-S, `R_N(t, r)` is the line kernel
  `G(t, n) = (2π)^{−1} e^{−2it} I(2t, n)` (`lineKernel`) summed over `r + Nℤ`),
  `ringFiniteSize` (FR-P, `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every `η > 0`);
- open chain of `M` sites `1, …, M` with `u = 0` at the walls `0` and `M + 1` and the same diagonal `−2` at every
  site: `chainKernelSolves` (FC-K), `chainUnique` (FC-U, `u(t, x) = Σ_{y=1}^{M} C_M(t; x, y) u(0, y)`),
  `chainFiniteSize` (FC-P, for sites `1 ≤ x, y ≤ M` and every `η > 0`,
  `|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`).
  A chain with free ends (diagonal `−1` at the end sites) is not covered.

Worked example: `examples/consumer/ConsumerFiniteRing.lean`.

The Hadamard walk on the line (batch HW, **[v0.7.0]**; Hadamard coin only, time a natural number):
`hadamardKernelFormula` (HW-R, the walk from a point state `(a, b)` at the origin in terms of a scalar kernel `K(t, x)`),
`hadamardKernelBound` (HW-K, `|K(t, x)| ≤ 7 t^{−1/2} + 12 t^{−1/3}` for `t ≥ 1` and every site `x`),
`hadamardDecay` (HW-D, each component of the walk from a point state is at most `39 (|a| + |b|) t^{−1/3}` for `t ≥ 1`),
`hadamardDispersive` (HW-L, the same with `39 t^{−1/3} Σ_y (|ψ₀,₁(y)| + |ψ₀,₂(y)|)` for finitely supported initial
states). Upper bounds only; the constants are not sharp (§6). Worked example:
`examples/consumer/ConsumerHadamardWalk.lean`.

## 4. Families of phases
Phases depending on a parameter in a compact set `S` of a normed space, smooth jointly on `V ×ˢ U`:
`nonStationaryLocal`, `stationaryPhaseLocal`, `foldLocal`; C10 `familyCk_of_uncurry` converts joint smoothness to the
internal `FamilyCk`. **Not covered:** a D4 bound uniform over a family (the D4 normal form uniformly in the parameter is
open, ROADMAP §2), so GD/GD-C are for one phase.

## 5. Periodic analytic functions, the trapezoidal rule, exponential sums
All **[v0.7.0]**. Batch PA, for `v : ℂ → ℂ` complex-differentiable, 2π-periodic and bounded by `M` on the open strip
`|Im z| < a` (`PeriodicAnalyticOn v a M`, `a > 0`):
- `fourierCoeffStrip` (PA-C): `|∫_0^{2π} v(θ) e^{−ikθ} dθ| ≤ 2π M e^{−a|k|}` for every integer `k` (the integral is
  unnormalised; the Fourier coefficient `c_k = (2π)^{−1}∫` then satisfies `|c_k| ≤ M e^{−a|k|}`);
- `trapezoidalRule` (PA-T): `|I_N(v) − ∫_0^{2π} v(θ) dθ| ≤ 4πM / (e^{aN} − 1)` for every `N ≥ 1`, with
  `I_N(v) = (2π/N) Σ_{j=0}^{N−1} v(2πj/N)` (`trapezoidalSum`).

Worked example: `examples/consumer/ConsumerPeriodicAnalytic.lean`.

Batch KL, for the sum `S = Σ_{n=0}^{N} e(c_n)`, `e(x) = e^{2πix}` (`expSum c N`, `N + 1` terms), when the differences
`c_{n+1} − c_n` are monotone and lie in one cell `[k + λ, k + 1 − λ]`, `k` an integer, `0 < λ ≤ 1/2`
(`DiffsMonotoneIn c N k lam`):
- `kusminLandau` (KL-D): `|S| ≤ cot(πλ/2)`;
- `kusminLandauTwoOverPi` (KL-C): `|S| ≤ 2/(πλ)` (a corollary of KL-D, weaker everywhere);
- `kusminLandauDeriv` (KL-F): for `f` continuous on `[a, b]` with derivative `f′` on `(a, b)`, `f′` monotone with
  `k + λ ≤ f′(x) ≤ k + 1 − λ` on `(a, b)` (the same `k` and `λ`): `|Σ_{n ∈ ℤ, a ≤ n ≤ b} e(f(n))| ≤ cot(πλ/2)`.

The second- and third-derivative tests for sums are not stated. Worked example:
`examples/consumer/ConsumerKusminLandau.lean`.

## 6. Explicit constants
Every number in this table is copied from the place named in the last column (`docs/STATUS.md` or
`docs/statements.md`); an empty cell means that no such number is stated there. "Has content" is where the bound
is below the trivial bound that the source names.

| Label | Theorem | Bound or constant | Has content | Source |
|---|---|---|---|---|
| S1.1, S1.2, S1.3 | `OscInt.vanDerCorput_one/two/three` | constants 3, 8, 18 | | `docs/STATUS.md`, paragraph "S1 (2026-11-05)" |
| S1.k | `vdCk` | constant 5·2^{k−1} − 2 | | `docs/STATUS.md`, row S1.k |
| VC2-S, VC2-N **[v0.7.0]** | `secondDerivSharp`, `vdc2ProfileBound` | `A(w)/√λ` for some `w ∈ [0, π]`; `A(w) ≤ 7/2` on `[0, π]` | | `docs/STATUS.md`, rows VC2-S, VC2-N |
| VC2-K **[v0.7.0]** | `secondDerivSevenHalves` | 7/2 in place of the 8 of S1.2 | | `docs/STATUS.md`, row VC2-K |
| T0E | `latticeKernel1Explicit` | `A t^{−1/2} + B t^{−1/3}`, A = 24 · 2^{1/4} ≈ 28.541, B = 36 · 2^{1/6} ≈ 40.409, `t > 0` | t > 518.5 (against 2π) | `docs/statements.md`, Batch LE, T0E and clarification 6 |
| T6E | `latticeLaplacianExplicit` | `(A + B)² t^{−2/3}`, (A + B)² ≈ 4754, `t ≥ 1` | t > ((A + B)²/(4π²))^{3/2} ≈ 1321.5 (against 4π²) | `docs/statements.md`, Batch LE, T6E and clarification 6 |
| T0E′ | `latticeKernel1CubeRoot` | `C* t^{−1/3}`, C* = 8(1 + √7)/3 ≈ 9.72200, `t > 0` | t > (C*/(2π))³ ≈ 3.7045 (against 2π) | `docs/statements.md`, Batch LE2, T0E′ and clarification 4 |
| T6E′ | `latticeLaplacianCubeRoot` | `C*² t^{−2/3}`, C*² ≈ 94.517, `t > 0` | the same t (against 4π²) | `docs/statements.md`, Batch LE2, T6E′ and clarification 4 |
| TdE′ | `hypercubicCubeRoot` | `C*^d t^{−d/3}`, `t > 0` | t > (C*/(2π))³ ≈ 3.70 in every dimension (against (2π)^d) | `docs/STATUS.md`, row TdE′; `docs/statements.md`, Batch HC, modelling choice 4 |
| LS-D | `latticeSchrodingerDispersive` | `min{1, (C*/(2π))^d (2\|t\|)^{−d/3}} ‖f‖₁`, `t ≠ 0` | \|t\| > τ, τ = (C*/(2π))³/2 ≈ 1.852 | `docs/statements.md`, Batch LS, LS-D, modelling choice 4 and clarification 1 |
| LS-D′ | `latticeSchrodingerDecay` | `(1 + τ)^{d/3} (1 + \|t\|)^{−d/3} ‖f‖₁` | \|t\| > τ ≈ 1.852 | `docs/statements.md`, Batch LS, LS-D′ and clarification 1 |
| PA-C **[v0.7.0]** | `fourierCoeffStrip` | `2π M e^{−a\|k\|}` | no content at k = 0 | `docs/statements.md`, Batch PA, PA-C and clarification 4 |
| PA-T **[v0.7.0]** | `trapezoidalRule` | `4πM / (e^{aN} − 1)` | no content for aN ≤ ln 2 | `docs/statements.md`, Batch PA, PA-T and clarification 4 |
| LC-1 **[v0.7.0]** | `latticeKernel1LightCone` | `2π e^{\|t\| sinh η − \|n\| η}`, `η ≥ 0` | no content inside the light cone \|n\| ≤ \|t\| and at η = 0 | `docs/statements.md`, Batch PA, LC-1 and clarification 4 |
| KL-D, KL-F **[v0.7.0]** | `kusminLandau`, `kusminLandauDeriv` | `cot(πλ/2)` | KL-D: no content when N + 1 ≤ cot(πλ/2) | `docs/statements.md`, Batch KL, KL-D, KL-F and clarifications 1 and 4 after "Proved" |
| KL-C **[v0.7.0]** | `kusminLandauTwoOverPi` | `2/(πλ)` | weaker than KL-D everywhere | `docs/statements.md`, Batch KL, KL-C and clarification 1 after "Proved" |
| FR-P **[v0.7.0]** | `ringFiniteSize` | `2 e^{2\|t\| sinh η} cosh(rη) / (e^{ηN} − 1)`, every `η > 0` | while the right side is below 2 | `docs/statements.md`, Batch FR, FR-P and clarification k (2) |
| FC-P **[v0.7.0]** | `chainFiniteSize` | `e^{2\|t\| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`, every `η > 0` | | `docs/statements.md`, Batch FR, FC-P |
| HW-K **[v0.7.0]** | `hadamardKernelBound` | `7 t^{−1/2} + 12 t^{−1/3}`, `t ≥ 1` | t > 1679 | `docs/STATUS.md`, paragraph "Batch HW (2026-11-16/19), what the rows rest on" |
| HW-D, HW-L **[v0.7.0]** | `hadamardDecay`, `hadamardDispersive` | `39 (\|a\| + \|b\|) t^{−1/3}`; `39 t^{−1/3} Σ_y (\|ψ₀,₁(y)\| + \|ψ₀,₂(y)\|)`; `t ≥ 1` | t > 59319 | `docs/STATUS.md`, the same paragraph |

The two-dimensional local and global theorems of §2 have existential constants only.

## 7. Not (yet) covered
Dimension `n ≥ 3` (except the separable lattice kernels of §3); vector-valued (matrix) amplitudes for the local theorems (the global ones are covered: GD-C-V, GD-V, GD-F-V, GD-N-V); global decay with cusp points, and higher singularities; leading terms of nondegenerate
stationary phase (draft: `docs/design/leading-term.md`); explicit constants for the two-dimensional local and global
theorems (`docs/constants.md`; the explicit constants that exist are in §6).
