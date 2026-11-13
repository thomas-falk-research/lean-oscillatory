# Route: batch LS (LS-E, LS-K, LS-D, LS-D′)

Lead, session 10, after the pre-proof reviews were answered (`review/2026-11-12-LS-pre-proof-answers.md`).
- **Blueprint:** `Blueprint/LatticeGroup.lean`, one `…Facts` proposition per part, and the definition `stencil`.
- **Assembly:** `OscInt/Front/LatticeGroupAssembly.lean`, compiled before any part is proved:
  - `lsE_of (hOp : LapOpFacts) (hExp : ExpSolutionFacts) : LatticeSchrodingerExistsStatement`;
  - `lsK_of hOp hExp (hU : UniqueFacts) (hConv : KernelConvFacts) : LatticeSchrodingerKernelStatement`;
  - `lsD_of (hK : LatticeSchrodingerKernelStatement) (hB : KernelBoundFacts) : LatticeSchrodingerDispersiveStatement`;
  - `lsDp_of (hD : LatticeSchrodingerDispersiveStatement) (hEnv : EnvelopeFacts) : LatticeSchrodingerDecayStatement`.

## Why this route

This also answers pre-proof referee B's finding 2 (`review/2026-11-12-LS-pre-proof-answers.md`): the ℓ¹ bound on
G_d(t, ·) comes from the series in P-conv, ‖G_d(t, ·)‖₁ ≤ Σₙ |t|ⁿ/n! (4d)ⁿ = e^{4d|t|}, not from TdE′.


Two alternatives were rejected:
- **Differentiating the kernel convolution in ℓ² directly.** This needs ℓ¹ control of G_d(t, ·) and its time
  derivatives, uniformly on compact time sets, and a Taylor remainder in the ℓ² norm.
- **Plancherel on the torus.** Mathlib has Fourier series on `AddCircle`, but not the d-dimensional unitary bridge.

The route below needs only:
- the operator exponential in the Banach algebra of bounded operators (Mathlib's `NormedSpace.exp` and
  `hasDerivAt_exp_smul_const`);
- uniqueness for a Lipschitz ODE (`ODE_solution_unique_univ`);
- one Fourier fact, orthogonality of e^{iz·k} on the box. This follows from the proved Fubini part of batch HC
  (`OscInt.HypercubicAux.hcFubiniFacts`) and the 1D integral ∫_{−π}^{π} e^{imk} dk = 0 for integers m ≠ 0;
- absolutely convergent double series (`summable_prod_of_nonneg`, `Summable.tsum_comm'`).

## The parts

**P-op `LapOpFacts`.** There is a bounded A on ℓ²(ℤ^d) with (Ag)(x) = (Δg)(x) and ‖A‖ ≤ 4d.
- Construct the shift S_z g = g(· + z) as an isometry. Membership in ℓ² and the norm are invariant under reindexing by
  the equivalence `Equiv.addRight z`: `memℓp_gen_iff`, `Equiv.summable_iff`, `lp.norm_rpow_eq_tsum`.
- Then A = Σ_j (S_{e_j} + S_{−e_j}) − 2d·id.
- Norm bound: ‖A‖ ≤ Σ_j (1 + 1) + 2d = 4d.

**P-exp `ExpSolutionFacts`.** Put B = i·A and u(t) = exp(t·B) f.
- `hasDerivAt_exp_smul_const B t` (𝕂 = ℝ; the instance `NormedAlgebra.complexToReal` exists, checked) gives the
  derivative exp(tB)·B.
- Applying it at f (`HasDerivAt.clm_apply` with a constant operator, or `ContinuousLinearMap.apply`) and using
  `Commute.exp_left` (B commutes with itself) gives u′(t) = B u(t).
- Its coordinates are i (A u(t))(x) = i (Δ u(t))(x), by P-op's formula.
- u(0) = exp(0) f = f (`NormedSpace.exp_zero`).

**P-unique `UniqueFacts`.** If u and v are solutions with datum f:
- both have derivative B u(t) and B v(t). The derivative w(t) given by the predicate equals B u(t) by `lp.ext` on
  coordinates, using P-op's formula.
- The field x ↦ Bx is `LipschitzWith ‖B‖₊`.
- `ODE_solution_unique_univ`, with s t = univ and t₀ = 0, gives u = v.

P-unique uses P-op. It is stated without the operator, so the assembly takes it as is.

**P-stencil `StencilFacts`.** Let Lₙ = `stencil d n`, so L₀ = δ₀ and Lₙ₊₁ = Δ Lₙ. Then:
- Lₙ ∈ ℓ¹ and Σ_z |Lₙ(z)| ≤ (4d)ⁿ. By induction: Σ_z |Δg(z)| ≤ 4d Σ_z |g(z)| for g ∈ ℓ¹, reindexing each shift
  (`Equiv.summable_iff`, `Equiv.tsum_eq`).
- (Aⁿ f)(x) = Σ_y Lₙ(x − y) f(y), absolutely convergent. By induction:
  - the base case is the single-term tsum (`tsum_eq_single`);
  - in the step, A applied to the convolution is a finite sum of shifted convolutions, and each shift reindexes the
    tsum over y.
  - Summability: |Lₙ(x − y) f(y)| ≤ ‖f‖ |Lₙ(x − y)| (`lp.norm_apply_le_norm`), and Lₙ ∈ ℓ¹.

**P-fourier `FourierStencilFacts`.** Lₙ(z) = (2π)^{−d} ∫_{box} (2Σ_j cos k_j − 2d)ⁿ e^{iz·k} dk.
- **Base case n = 0.** ∫_{box} e^{iz·k} dk = ∏_j ∫_{−π}^{π} e^{i z_j k} dk, by `hcFubiniFacts` with continuous factors.
  This equals (2π)^d if z = 0 and 0 otherwise, since ∫_{−π}^{π} e^{imk} dk = 0 for an integer m ≠ 0
  (antiderivative e^{imk}/(im), and e^{imπ} = e^{−imπ}).
- **Step.** Δ_z of the right side equals the right side with one more factor (2Σ_j cos k_j − 2d):
  - by linearity of the integral (finitely many integrable terms);
  - by e^{i(z ± e_j)·k} = e^{iz·k} e^{±i k_j};
  - and by e^{ik_j} + e^{−ik_j} = 2 cos k_j.

**P-series `KernelSeriesFacts`.** G_d(t, z) = Σₙ (it)ⁿ/n! Lₙ(z).
- Rewrite G_d(t, z) as (2π)^{−d} ∫_{box} e^{it(2Σcos k_j − 2d)} e^{iz·k} dk. The gauge e^{−2idt} and the factor 2 in
  K_d(2t, ·) combine exactly into this.
- Expand the exponential (`Complex.exp` power series, `NormedSpace.exp_eq_tsum` or `Complex.hasSum_exp`) and
  integrate term by term with `MeasureTheory.hasSum_integral_of_dominated_convergence`. The majorant is (4d|t|)ⁿ/n!, constant in k
  and integrable on the finite box.
- Each term is (it)ⁿ/n! times Lₙ(z) by P-fourier.

**P-conv `KernelConvFacts`.** (exp(tB) f)(x) = Σ_y G_d(t, x − y) f(y), absolutely convergent.
- exp(tB) = Σₙ (n!)⁻¹ (tB)ⁿ (`NormedSpace.exp_series_hasSum_exp'`). Evaluate at f, then at x (continuous linear maps;
  `ContinuousLinearMap.map_tsum` or `HasSum.mapL`). This gives a HasSum over n of (it)ⁿ/n! (Aⁿ f)(x), using
  (tB)ⁿ = (it)ⁿ Aⁿ (`smul_pow`).
- By P-stencil this is Σₙ Σ_y cₙ Lₙ(x − y) f(y), with cₙ = (it)ⁿ/n!.
- The double family is absolutely summable: Σₙ Σ_y |cₙ| |Lₙ(x − y)| |f(y)| ≤ ‖f‖ Σₙ (4d|t|)ⁿ/n! = ‖f‖ e^{4d|t|}
  (`summable_prod_of_nonneg`).
- Exchange the sums (`Summable.tsum_comm'`) and use P-series for the inner sum over n.
- Summability of y ↦ |G_d(t, x − y) f(y)| follows from |G_d(t, z)| ≤ Σₙ |cₙ| |Lₙ(z)| (`norm_tsum_le_tsum_norm`) and
  comparison.

**P-bound `KernelBoundFacts`.** For t ≠ 0, |G_d(t, z)| ≤ min{1, (C*/(2π))^d (2|t|)^{−d/3}}.
- |G_d| = (2π)^{−d} |K_d(2t, z)|, since the gauge has modulus 1.
- |K_d(s, z)| ≤ (2π)^d: the integrand has modulus 1 and the box has measure (2π)^d (`hypercubeBox_volume` in the HC
  sanity layer).
- **For t > 0:** TdE′ (`OscInt.API.hypercubicCubeRoot`) at s = 2t gives C*^d (2t)^{−d/3}.
- **For t < 0:** K_d(2t, z) = conj K_d(−2t, −z), by conjugating the integrand: the conjugate of
  e^{i(sΣcos k_j + z·k)} is e^{i(−sΣcos k_j − z·k)}, and `integral_conj`. Then apply TdE′ at −2t = 2|t| > 0.

**P-envelope `EnvelopeFacts`.** Pure real analysis.
- (C*/(2π))^d (2|t|)^{−d/3} = (τ/|t|)^{d/3} with τ = (C*/(2π))³/2, by `Real.rpow_natCast`, `Real.mul_rpow` and
  `Real.rpow_mul`.
- **If |t| ≤ τ:** min ≤ 1 ≤ ((1 + τ)/(1 + |t|))^{d/3}.
- **If |t| ≥ τ:** τ/|t| ≤ (1 + τ)/(1 + |t|), and rpow is monotone (`Real.rpow_le_rpow`).

## Order and dependencies

- P-op is needed for the assembly. P-unique uses P-op internally.
- P-stencil, P-fourier and P-series are needed for P-conv. P-fourier needs `hcFubiniFacts` (proved).
- P-bound needs TdE′ (proved). P-envelope stands alone.
- Final file OscInt/Front/LatticeGroupFinal.lean (to be written after the parts):
  - `latticeSchrodingerExists := lsE_of lapOp expSolution`;
  - `latticeSchrodingerKernel := lsK_of lapOp expSolution unique (kernelConv_of stencilFacts (kernelSeries_of fourierStencil))`;
  - `latticeSchrodingerDispersive := lsD_of latticeSchrodingerKernel kernelBound`;
  - `latticeSchrodingerDecay := lsDp_of latticeSchrodingerDispersive envelope`.

## Interface checks (numerical, before the parts)

The lead's `numerics/review/dnls_checks.py` (record `numerics/results-dnls-checks-2026-11-12.txt`) already checks:
- the kernel identity against a matrix exponential (D1);
- the envelope constant (D3).

The route's own interfaces are checked in `numerics/review/ls_interface_checks.py` (record
`numerics/results-ls-interface-checks-2026-11-12.txt`):
- the stencil ℓ¹ bound, exact in integers; it is attained: Σ_z |Lₙ(z)| = (4d)ⁿ;
- the Fourier representation of Lₙ;
- the series P-series against the Bessel form of G_d.

## Risks known now

- **P-op:** Mathlib has no ready-made shift operator on `lp`. Constructing the isometry by reindexing is routine but
  verbose.
- **P-conv:** the type of the exponential series (`(n!)⁻¹ • B^n` with ℝ- or ℂ-smul) must match `exp(t • B)` with
  t : ℝ. Use `NormedSpace.exp_series_hasSum_exp'` with 𝕂 = ℝ, and convert (t • B)ⁿ = tⁿ • Bⁿ.
- **P-fourier:** the d-dimensional orthogonality needs `hcFubiniFacts` applied to the factors k ↦ e^{i z_j k}. TdF's
  proof already does this kind of rewrite.
- **P-bound:** the conjugation step for t < 0 needs the measure of the box to be invariant under k ↦ −k, or the
  pointwise conjugate identity with `integral_conj`. The latter avoids the change of variables.

## Revision after the route referee (2026-11-12/13)

A fresh-context route referee (a Claude instance) read this route at e814510. It was launched at 23:11:40 UTC, and its
last action was at 23:19:24. Its verdict: every part TRUE, the assembly sufficient, no BLOCKER.
- The referee compiled four small probe files against the pinned Mathlib, eleven Lean runs from 23:14:12 to 23:17:40.
- That was during a full replay, against lessons 28. That replay is therefore not an acceptance record
  (`docs/replay/2026-11-12-session10-e814510-partial.txt`).

**Count of parts.** The route has nine parts, P-op to P-envelope, and `Blueprint/LatticeGroup.lean` has nine `…Facts`
propositions. The message of commit e814510 says "eight parts"; that is wrong. The commit message is not rewritten.

**MAJOR, P-conv: the series step fails at the pin as written.** With 𝕂 = ℝ, `exp_series_hasSum_exp'` gives the series
of (n!)⁻¹ • (t • B)ⁿ with an ℝ-action on `LatticeL2 d →L[ℂ] LatticeL2 d`. Rewriting (t • B)ⁿ = tⁿ • Bⁿ then meets
`Complex.coe_smul`, `IsSMulApply` and the `IsScalarTower` instance that `smul_pow` needs. Replacement, compiled by the
referee (probe 4):
- rewrite t • (I • A) = (I * t) • A: `ext` and `simp [ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
  smul_eq_mul, Complex.real_smul]`, then `ring`;
- use `exp_series_hasSum_exp'` with 𝕂 = ℂ;
- prove (c • A)^m = c^m • A^m by induction with `ext`;
- evaluate with `HasSum.mapL` at `(lp.evalCLM ℂ _ 2 x).comp (ContinuousLinearMap.apply ℂ _ f)`. `lp.evalCLM` takes p
  explicitly.

**MINOR, P-exp.**
- `HasDerivAt.clm_apply` does not fit: the operator is ℂ-linear, while the derivative is in a real variable.
- `Commute.exp_left` is unnecessary.
- Use `hasDerivAt_exp_smul_const'` (𝕂 = ℝ) at `I • A`, composed with
  `((ContinuousLinearMap.apply ℂ _ f).restrictScalars ℝ).hasFDerivAt` (probe 1 compiles).

**P-unique.** `ODE_solution_unique_univ` with `v := fun _ => B`, `s := fun _ => univ`, `K := ‖B‖₊`, `t₀ := 0` and
`B.lipschitzWith.lipschitzOnWith` compiles.

**MINOR, P-series names.**
- `Complex.hasSum_exp` does not exist at the pin.
- Use instead:
  - `NormedSpace.expSeries_div_hasSum_exp` with `Complex.exp_eq_exp_ℂ`;
  - `integral_const_mul`;
  - `Real.summable_pow_div_factorial`.

**MINOR, P-conv exchange.** Use `Summable.tsum_comm`, which takes one summability hypothesis. Get it from
`summable_prod_of_nonneg` on the norms, then `.of_norm`.

**NITs.**
- **P-op.** The bound ‖A‖ ≤ 4d is unused downstream. It is kept, because `LinearMap.mkContinuous` needs a bound;
  ‖Δ‖ = 4d exactly. The shift API is absent from Mathlib, about 100 lines.
- **P-op.** `latticeLaplacian` uses x − e_j. Rewrite it with `sub_eq_add_neg`.
- **P-stencil.** The convolution step needs no reindexing: Aⁿ⁺¹ = A · Aⁿ (`pow_succ'`), the coordinate formula at
  g = Aⁿ f, and the induction hypothesis at x ± e_j. Reindexing, by `(Equiv.addRight e).tsum_eq`, is needed only for
  the ℓ¹ bound.
- **P-bound.** `hypercubeBox_volume` is in `OscInt/Front/HypercubicSanity.lean`. Import it (a library file already
  imports a sanity file) or copy its three lines.
- **Deprecations.** `ContinuousLinearMap.lipschitz` becomes `lipschitzWith`.

**The lead's interface check I3** (`numerics/review/ls_interface_checks.py`) uses a periodic grid with 49 sites per
axis for orders up to 60, so periodic images enter. The lead computed their contribution in exact integers, at the I3
times and sites: at most 1.2·10⁻⁴¹. The recorded PASS stands. A note is added to the record.

The names above are `#check`ed in `MathlibNames.lean`.
