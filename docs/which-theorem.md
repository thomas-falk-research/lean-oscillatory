# Which theorem do I use?

A decision tree for a user with a concrete oscillatory integral. Every name below is a theorem whose type is a frozen
statement (`stamps/statements.json`, `docs/STATUS.md` for its status); `import OscInt.API` exposes all of them. The
copy-paste recipes are in `docs/cookbook.md`; the machine-readable index is `docs/api.json`.

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
existence, kernel representation, decay of solutions) are stated and reviewed but **not proved yet**
(`docs/STATUS.md`). Worked examples: `examples/consumer/ConsumerPhotonLattice.lean` (T0E′), `ConsumerLattice.lean`
(T6, T6L).

## 4. Families of phases
Phases depending on a parameter in a compact set `S` of a normed space, smooth jointly on `V ×ˢ U`:
`nonStationaryLocal`, `stationaryPhaseLocal`, `foldLocal`; C10 `familyCk_of_uncurry` converts joint smoothness to the
internal `FamilyCk`. **Not covered:** a D4 bound uniform over a family (the D4 normal form uniformly in the parameter is
open, ROADMAP §2), so GD/GD-C are for one phase.

## 5. Not (yet) covered
Dimension `n ≥ 3` (except the separable lattice kernels of §3); vector-valued (matrix) amplitudes for the local theorems (the global ones are covered: GD-C-V, GD-V, GD-F-V, GD-N-V); global decay with cusp points, and higher singularities; leading terms of nondegenerate
stationary phase (draft: `docs/design/leading-term.md`); explicit constants (`docs/constants.md`).
